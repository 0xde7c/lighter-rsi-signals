#!/usr/bin/env python3
"""
LighterRSI Signal Bot v2.4 — Trend-Aware Staged RSI alerts for ETH/BTC/SOL on Lighter DEX.
Read-only (no orders). Pulls candles directly from Lighter's REST API.

v2 additions:
  - Trend state engine (5 states from 4H EMA + 1H RSI)
  - Adaptive RSI thresholds per trend state
  - RSI velocity filter (15+ pts in 3 candles)
  - Momentum persistence filter (10+ candles one-sided)
  - Signal classification (WITH-TREND / COUNTER-TREND / NEUTRAL)
  - Counter-trend signals require Grade A minimum

v2.1 additions:
  - Funding rate as confluence factor (Binance perpetual funding rate)
  - SOL-specific wider RSI thresholds (+5 pts)
  - Cardwell divergence reclassification (bearish div in strong uptrend = continuation)
"""

import asyncio
import json
import logging
import math
import time
import urllib.request
from collections import deque
from datetime import datetime, timezone
from functools import partial

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, ContextTypes

# --- Config -------------------------------------------------------------------

BOT_TOKEN = "YOUR_TG_BOT_TOKEN"
CHAT_ID = "YOUR_TG_CHAT_ID"

LIGHTER_URL = "https://mainnet.zklighter.elliot.ai/api/v1/candles"

ASSETS = {
    "ETH": {"market_id": 0, "priority": "PRIMARY",   "emoji": "\U0001f7e6", "rsi_ob": 70, "rsi_os": 30, "vol_spike": 5.0},
    "BTC": {"market_id": 1, "priority": "SECONDARY",  "emoji": "\U0001f7e8", "rsi_ob": 75, "rsi_os": 25, "vol_spike": 6.0},
    "SOL": {"market_id": 2, "priority": "TERTIARY",   "emoji": "\U0001f7ea", "rsi_ob": 70, "rsi_os": 30, "vol_spike": 5.0},
}
ASSET_NAMES = list(ASSETS.keys())  # ETH first

RSI_APPROACH_BUFFER = 5  # approach zone = threshold +/- 5

# Timeframes per indicator
RSI_TIMEFRAMES = ["1m", "5m", "15m", "30m", "1h", "4h", "1d", "1w"]
EMA_TIMEFRAMES = ["4h"]
MACD_TIMEFRAMES = ["1h", "4h"]
BOLLINGER_TIMEFRAMES = ["1h", "4h"]
DIVERGENCE_TIMEFRAMES = ["1h", "4h"]
VOLUME_TIMEFRAMES = ["5m", "15m", "1h"]
VOLUME_SPIKE_MULT = 3.0

TF_ORDER = ["1m", "5m", "15m", "30m", "1h", "4h", "1d", "1w"]
ALL_TIMEFRAMES = sorted(
    set(RSI_TIMEFRAMES + EMA_TIMEFRAMES + MACD_TIMEFRAMES
        + BOLLINGER_TIMEFRAMES + DIVERGENCE_TIMEFRAMES + VOLUME_TIMEFRAMES),
    key=lambda t: TF_ORDER.index(t),
)

TF_SECONDS = {
    "1m": 60, "5m": 300, "15m": 900, "30m": 1800, "1h": 3600,
    "4h": 14400, "1d": 86400, "1w": 604800,
}

TF_POLL_INTERVALS = {
    "1m": 15, "5m": 30, "15m": 60, "30m": 120, "1h": 300, "4h": 900, "1d": 3600, "1w": 3600,
}

SWING_COOLDOWN = 1800  # 30 min between swing alerts per asset

POLL_INTERVAL = 30

# --- Funding Rate Config -----------------------------------------------------

BINANCE_FUNDING_URL = "https://fapi.binance.com/fapi/v1/fundingRate"
BINANCE_SYMBOLS = {"ETH": "ETHUSDT", "BTC": "BTCUSDT", "SOL": "SOLUSDT"}
FUNDING_CACHE_TTL = 300  # refresh every 5 min (rate updates every 8h but we want freshness)
FUNDING_EXTREME_THRESHOLD = 0.0005  # 0.05% = extreme funding (annualized ~18%)
FUNDING_CONFLUENCE_THRESHOLD = 0.0003  # 0.03% = mild confluence signal

# --- Binance Volume Context Config --------------------------------------------

BINANCE_KLINES_URL = "https://fapi.binance.com/fapi/v1/klines"
VOLUME_CACHE_TTL = 60  # refresh every 60s (5m candles update frequently)
# Median 5m volumes from research (USD quote volume, Binance Futures, Mar 2026)
VOLUME_MEDIANS = {
    "BTC": 27_700_000,  # $27.7M
    "ETH": 23_400_000,  # $23.4M
    "SOL":  4_400_000,  # $4.4M
}
VOLUME_WARNING_MULT = 5    # 5x median = warning line on signals
VOLUME_HEAVY_MULT = 8      # 8x median = "HEAVY" label
VOLUME_EXTREME_MULT = 10   # 10x median = "EXTREME" label

# --- Trend-Aware Config -------------------------------------------------------

# Adaptive RSI thresholds per trend state: (long_entry, short_entry)
# Tighter thresholds — only deep extremes trigger. No side fully suppressed.
TREND_THRESHOLDS = {
    "STRONG_UPTREND":   {"long": 33, "short": 78},
    "MILD_UPTREND":     {"long": 30, "short": 75},
    "NEUTRAL":          {"long": 28, "short": 72},
    "MILD_DOWNTREND":   {"long": 25, "short": 68},
    "STRONG_DOWNTREND": {"long": 22, "short": 65},
}

# Per-asset threshold offsets: widen RSI bands for more volatile assets
# Positive = wider bands (long threshold lower, short threshold higher)
ASSET_THRESHOLD_OFFSET = {
    "ETH": 0,
    "BTC": 0,
    "SOL": 5,  # SOL is ~2x ETH vol, needs wider bands to avoid noise
}

# EMA proximity threshold for NEUTRAL classification
EMA_NEUTRAL_PCT = 0.005  # 0.5%

# RSI velocity: minimum points moved in 3 candles to fire alert
RSI_VELOCITY_MIN = 6

# Deep extreme: skip velocity check and allow Grade C at these levels
RSI_DEEP_EXTREME_LOW = 25   # RSI below this = fire regardless of velocity/grade
RSI_DEEP_EXTREME_HIGH = 78  # RSI above this = fire regardless of velocity/grade

# Momentum persistence: consecutive candles above 60 or below 40
MOMENTUM_PERSISTENCE_THRESHOLD = 10

# --- State --------------------------------------------------------------------

candle_cache = {}        # (asset, tf) -> [candle_dicts]
alert_state = {}         # (indicator, tf, asset) -> state_string
last_fetch = {}          # (asset, tf) -> timestamp

# Staged RSI state
staged_state = {}        # asset -> "neutral"/"approach_long"/"approach_short"/"triggered_long"/"triggered_short"
staged_5m_prev = {}      # asset -> previous 5M RSI value

# Standalone 5m RSI alerts (all assets now, not just ETH)
rsi_5m_state = {}        # asset -> "neutral" / "oversold" / "overbought"
rsi_5m_last_alert = {}   # asset -> timestamp
RSI_5M_COOLDOWN = 300    # 5 min cooldown between 5m RSI alerts

# Swing state
last_swing_alert = {}    # asset -> timestamp

user_selected_asset = {} # chat_id -> "BTC"/"ETH"/"SOL"

# Trend state
trend_state = {}         # asset -> "STRONG_UPTREND"/"MILD_UPTREND"/"NEUTRAL"/"MILD_DOWNTREND"/"STRONG_DOWNTREND"

# RSI history for velocity calculation
rsi_history = {}         # (asset, tf) -> deque(maxlen=5) of RSI values

# Momentum persistence counters
momentum_above = {}      # asset -> count of consecutive 5M candles with RSI > 60
momentum_below = {}      # asset -> count of consecutive 5M candles with RSI < 40
momentum_warned = {}     # asset -> "above"/"below"/None — track if warning was sent

# Funding rate state
funding_rates = {}           # asset -> {"rate": float, "time": timestamp}
funding_last_fetch = 0       # timestamp of last Binance API call
binance_volume_cache = {}    # asset -> {"candles": [...], "time": timestamp}
binance_volume_last_fetch = 0  # timestamp of last Binance volume API call

# Context alert state
context_cooldowns = {}       # (alert_type, asset) -> last_fire_timestamp
context_flags = {}           # (alert_type, asset) -> condition key for dedup/reset
pending_trend_changes = []   # [(asset, old_state, new_state)] — drained by context alerts

# Trend debounce — require N consecutive checks before confirming state change
trend_debounce_pending = {}   # asset -> {"state": new_state, "count": int}
# v2.3: Active signal tracking for exit/hold alerts
active_signals = {}       # asset -> {"direction", "entry_time", "entry_price", "entry_rsi_5m/15m/30m", "time_warned_5/15"}

# v2.3: RSI direction tracking for 15m and 30m
rsi_history_15m = {}      # asset -> deque(maxlen=8) of RSI values
rsi_history_30m = {}      # asset -> deque(maxlen=8) of RSI values

# v2.3: Exit signal cooldowns
exit_alert_cooldowns = {} # (alert_type, asset) -> last_fire_timestamp

# v2.3: Repeated signal tracking
signal_history = {}       # asset -> deque of {"direction": str, "time": float, "grade": str}

TREND_DEBOUNCE_CHECKS = 3    # require 3 consecutive checks (~90s at 30s poll)

# v2.4: Market regime detection (fast overlay on slow trend engine)
market_regime = {}           # asset -> "WATERFALL_DOWN"|"WATERFALL_UP"|"NORMAL"
regime_debounce = {}         # asset -> {"regime": str, "count": int}
pending_regime_changes = []  # [(asset, old, new)] for context alerts
bounce_state = {}            # asset -> "idle"|"watching"|"ready"
bounce_rsi_low = {}          # asset -> lowest 5M RSI seen in current waterfall
REGIME_DEBOUNCE_CHECKS = 2  # fast — regime must react quickly
WATERFALL_1H_RSI_DOWN = 35  # 1H RSI below this = potential waterfall down
WATERFALL_1H_RSI_UP = 65    # 1H RSI above this = potential waterfall up
WATERFALL_15M_CEILING = 50  # if 15M RSI max stays below this = confirmed waterfall
WATERFALL_ROC_PCT = 2.5     # 6-hour price rate of change threshold (%)
BOUNCE_FADE_ENTRY = 40      # 5M RSI level where bounce-fade short can fire
BOUNCE_FADE_TURN = 2        # 5M RSI must drop this many pts to confirm turn
# --- v2.3: Multi-TF Exit/Hold Config -----------------------------------------
EXIT_SIGNAL_COOLDOWN = 120          # 2 min between same-type exit alerts per asset
EXIT_SIGNAL_EXPIRY = 1200           # 20 min: active signals expire
EXIT_RSI_NEUTRAL_LOW = 40           # 5m RSI in 40-60 = signal expired
EXIT_RSI_NEUTRAL_HIGH = 60
EXIT_30M_NEUTRAL_LOW = 45           # 30m RSI 45-55 = exhaustion zone
EXIT_30M_NEUTRAL_HIGH = 55
EXIT_15M_TURN_THRESHOLD = 2         # 15m must move 2+ consecutive polls to count as "turning"
TIME_WARNING_1 = 300                # 5 min warning
TIME_WARNING_2 = 900                # 15 min warning

# Repeated signal escalation
REPEAT_SIGNAL_WINDOW = 1800         # 30 min window for counting same-direction signals


# Context alert config
CONTEXT_COOLDOWN_DEFAULT = 3600       # 1 hour
CONTEXT_COOLDOWN_EXHAUSTION = 21600  # 6 hours
CONTEXT_APPROACH_BUFFER = 3         # RSI points from threshold to start warning
CONTEXT_EMA_PROXIMITY_PCT = 0.01     # 1% from EMA50
CONTEXT_BB_SQUEEZE_ENTER = 2.0       # 2% bandwidth = squeeze
CONTEXT_BB_SQUEEZE_EXIT = 3.0        # 3% bandwidth = squeeze over

# --- Logging ------------------------------------------------------------------

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
)
logging.getLogger("httpx").setLevel(logging.WARNING)
logging.getLogger("telegram").setLevel(logging.WARNING)
log = logging.getLogger("LighterRSI")

# --- Candle Fetcher -----------------------------------------------------------

def fetch_candles(asset, resolution, count=500):
    """Fetch closed candles from Lighter REST API."""
    market_id = ASSETS[asset]["market_id"]
    now = int(time.time())
    secs = TF_SECONDS.get(resolution, 3600)
    start = now - (count + 5) * secs

    url = (
        f"{LIGHTER_URL}?market_id={market_id}&resolution={resolution}"
        f"&start_timestamp={start}&end_timestamp={now}&count_back={count + 5}"
    )
    try:
        resp = json.loads(urllib.request.urlopen(url, timeout=15).read().decode())
        if resp.get("code") != 200 or "c" not in resp:
            log.warning(f"Candle API error {asset}/{resolution}: {resp}")
            return None

        raw = resp["c"]
        if not raw:
            return None

        candles = []
        for c in raw:
            candles.append({
                "time": c["t"] / 1000.0,
                "open": float(c["o"]),
                "high": float(c["h"]),
                "low": float(c["l"]),
                "close": float(c["c"]),
                "volume": float(c.get("v", 0)),
                "quote_volume": float(c.get("V", 0)),
            })
        return candles

    except Exception as e:
        log.error(f"fetch_candles({asset}/{resolution}) failed: {e}")
        return None


# ==============================================================================
# INDICATOR FUNCTIONS
# ==============================================================================

def compute_rsi(closes, period=14):
    if len(closes) < period + 1:
        return None
    deltas = [closes[i] - closes[i - 1] for i in range(1, len(closes))]
    gains = [max(0, d) for d in deltas]
    losses = [max(0, -d) for d in deltas]
    avg_gain = sum(gains[:period]) / period
    avg_loss = sum(losses[:period]) / period
    for i in range(period, len(gains)):
        avg_gain = (avg_gain * (period - 1) + gains[i]) / period
        avg_loss = (avg_loss * (period - 1) + losses[i]) / period
    if avg_loss == 0:
        return 100.0
    return 100 - (100 / (1 + avg_gain / avg_loss))


def compute_rsi_series(closes, period=14):
    if len(closes) < period + 1:
        return []
    deltas = [closes[i] - closes[i - 1] for i in range(1, len(closes))]
    gains = [max(0, d) for d in deltas]
    losses = [max(0, -d) for d in deltas]
    avg_gain = sum(gains[:period]) / period
    avg_loss = sum(losses[:period]) / period
    rsi_values = []
    if avg_loss == 0:
        rsi_values.append(100.0)
    else:
        rsi_values.append(100 - (100 / (1 + avg_gain / avg_loss)))
    for i in range(period, len(gains)):
        avg_gain = (avg_gain * (period - 1) + gains[i]) / period
        avg_loss = (avg_loss * (period - 1) + losses[i]) / period
        if avg_loss == 0:
            rsi_values.append(100.0)
        else:
            rsi_values.append(100 - (100 / (1 + avg_gain / avg_loss)))
    return rsi_values


def compute_ema(values, period):
    if len(values) < period:
        return []
    k = 2.0 / (period + 1)
    ema = [sum(values[:period]) / period]
    for v in values[period:]:
        ema.append(v * k + ema[-1] * (1 - k))
    return ema


def compute_macd(closes, fast=12, slow=26, signal_period=9):
    if len(closes) < slow + signal_period:
        return None, None, None
    ema_fast = compute_ema(closes, fast)
    ema_slow = compute_ema(closes, slow)
    offset = len(ema_fast) - len(ema_slow)
    macd_line = [ema_fast[offset + i] - ema_slow[i] for i in range(len(ema_slow))]
    if len(macd_line) < signal_period:
        return None, None, None
    signal_line = compute_ema(macd_line, signal_period)
    offset2 = len(macd_line) - len(signal_line)
    histogram = [macd_line[offset2 + i] - signal_line[i] for i in range(len(signal_line))]
    return macd_line, signal_line, histogram


def compute_bollinger(closes, period=20, num_std=2):
    if len(closes) < period:
        return None, None, None
    window = closes[-period:]
    mid = sum(window) / period
    variance = sum((c - mid) ** 2 for c in window) / period
    std = math.sqrt(variance)
    return mid + num_std * std, mid, mid - num_std * std


def detect_divergence(closes, rsi_values, lookback=20):
    if len(closes) < lookback or len(rsi_values) < lookback:
        return []
    min_len = min(len(closes), len(rsi_values))
    c = closes[-min_len:][-lookback:]
    r = rsi_values[-min_len:][-lookback:]
    divergences = []
    lows_idx = []
    for i in range(2, lookback - 2):
        if c[i] <= min(c[i - 2], c[i - 1]) and c[i] <= min(c[i + 1], c[i + 2]):
            lows_idx.append(i)
    for k in range(1, len(lows_idx)):
        j, i = lows_idx[k - 1], lows_idx[k]
        if c[i] < c[j] and r[i] > r[j]:
            if abs(c[i] - c[j]) / c[j] >= 0.003:
                divergences.append(("bullish", "Price lower low + RSI higher low"))
    highs_idx = []
    for i in range(2, lookback - 2):
        if c[i] >= max(c[i - 2], c[i - 1]) and c[i] >= max(c[i + 1], c[i + 2]):
            highs_idx.append(i)
    for k in range(1, len(highs_idx)):
        j, i = highs_idx[k - 1], highs_idx[k]
        if c[i] > c[j] and r[i] < r[j]:
            if abs(c[i] - c[j]) / c[j] >= 0.003:
                divergences.append(("bearish", "Price higher high + RSI lower high"))
    return divergences


def _get_rsi(asset, tf):
    """Helper: get RSI for an asset/tf from cache."""
    candles = candle_cache.get((asset, tf))
    if not candles or len(candles) < 16:
        return None
    return compute_rsi([c["close"] for c in candles])


def _get_price(asset):
    """Helper: get latest price for an asset."""
    for tf in TF_ORDER:
        candles = candle_cache.get((asset, tf))
        if candles:
            return candles[-1]["close"]
    return None


def _get_4h_ema50(asset):
    """Helper: get 4H EMA(50) value."""
    candles = candle_cache.get((asset, "4h"))
    if not candles or len(candles) < 50:
        return None
    closes = [c["close"] for c in candles]
    ema = compute_ema(closes, 50)
    return ema[-1] if ema else None


# ==============================================================================
# FUNDING RATE FETCHER (Binance perpetual)
# ==============================================================================

def fetch_funding_rates():
    """Fetch latest funding rates from Binance for all assets. Cached for FUNDING_CACHE_TTL."""
    global funding_last_fetch
    now = time.time()
    if now - funding_last_fetch < FUNDING_CACHE_TTL:
        return

    for asset, symbol in BINANCE_SYMBOLS.items():
        try:
            url = f"{BINANCE_FUNDING_URL}?symbol={symbol}&limit=1"
            resp = json.loads(urllib.request.urlopen(url, timeout=10).read().decode())
            if resp and len(resp) > 0:
                rate = float(resp[0]["fundingRate"])
                funding_rates[asset] = {"rate": rate, "time": now}
                log.info(f"Funding rate {asset}: {rate:+.6f} ({rate*100:+.4f}%)")
        except Exception as e:
            log.warning(f"Funding rate fetch failed for {asset}: {e}")

    funding_last_fetch = now


def get_funding_rate(asset):
    """Get cached funding rate for asset. Returns float or None."""
    data = funding_rates.get(asset)
    if data and time.time() - data["time"] < FUNDING_CACHE_TTL * 3:  # stale after 3x TTL
        return data["rate"]
    return None


def get_funding_signal(asset):
    """Interpret funding rate as a directional signal.
    Returns ("long"/"short"/None, description_string).
    High positive funding = longs paying shorts = short confluence.
    High negative funding = shorts paying longs = long confluence.
    """
    rate = get_funding_rate(asset)
    if rate is None:
        return None, ""

    if rate >= FUNDING_EXTREME_THRESHOLD:
        return "short", f"Funding: {rate*100:+.4f}% (longs paying — short bias)"
    elif rate <= -FUNDING_EXTREME_THRESHOLD:
        return "long", f"Funding: {rate*100:+.4f}% (shorts paying — long bias)"
    elif rate >= FUNDING_CONFLUENCE_THRESHOLD:
        return "short", f"Funding: {rate*100:+.4f}% (mild short bias)"
    elif rate <= -FUNDING_CONFLUENCE_THRESHOLD:
        return "long", f"Funding: {rate*100:+.4f}% (mild long bias)"
    return None, ""


# ==============================================================================
# TREND STATE ENGINE (Feature 1)
# ==============================================================================

def get_trend_state(asset):
    """Classify asset into 5 trend states using 4H EMA(50) and 1H RSI.
    Structure (EMA) and momentum (RSI) must agree. If they conflict = NEUTRAL."""
    price = _get_price(asset)
    ema_4h = _get_4h_ema50(asset)
    rsi_1h = _get_rsi(asset, "1h")

    if price is None or ema_4h is None:
        return "NEUTRAL"

    # Check if price is within 0.5% of EMA — neutral zone
    if abs(price - ema_4h) / ema_4h < EMA_NEUTRAL_PCT:
        return "NEUTRAL"

    if price > ema_4h:
        # Structure bullish — check if momentum agrees
        if rsi_1h is not None and rsi_1h > 60:
            return "STRONG_UPTREND"
        elif rsi_1h is not None and 40 <= rsi_1h <= 60:
            return "MILD_UPTREND"
        elif rsi_1h is not None and rsi_1h < 40:
            return "NEUTRAL"  # structure up but momentum bearish = conflicting
        else:
            return "MILD_UPTREND"
    else:
        # Structure bearish — check if momentum agrees
        if rsi_1h is not None and rsi_1h < 40:
            return "STRONG_DOWNTREND"
        elif rsi_1h is not None and 40 <= rsi_1h <= 60:
            return "MILD_DOWNTREND"
        elif rsi_1h is not None and rsi_1h > 60:
            return "NEUTRAL"  # structure down but momentum bullish = conflicting
        else:
            return "MILD_DOWNTREND"


def update_all_trend_states():
    """Update trend state for all assets. Called every cycle. Debounced."""
    for asset in ASSET_NAMES:
        old = trend_state.get(asset)
        new = get_trend_state(asset)

        if old and old != new:
            # Debounce: require new state to persist for N checks
            pending = trend_debounce_pending.get(asset)
            if pending and pending["state"] == new:
                pending["count"] += 1
                if pending["count"] >= TREND_DEBOUNCE_CHECKS:
                    trend_state[asset] = new
                    del trend_debounce_pending[asset]
                    log.info(f"Trend change (confirmed): {asset} {old} -> {new}")
                    pending_trend_changes.append((asset, old, new))
            else:
                trend_debounce_pending[asset] = {"state": new, "count": 1}
        else:
            trend_state[asset] = new
            if asset in trend_debounce_pending:
                del trend_debounce_pending[asset]


def detect_market_regime(asset):
    """Fast regime detection: WATERFALL_DOWN, WATERFALL_UP, or NORMAL.
    Uses 1H RSI + 15M RSI history + 6h price rate of change.
    Much faster than the 4H EMA trend engine — catches waterfalls within 1-2 cycles."""
    rsi_1h = _get_rsi(asset, "1h")
    if rsi_1h is None:
        return "NORMAL"

    # Check 1: 1H RSI at extreme
    is_1h_bearish = rsi_1h < WATERFALL_1H_RSI_DOWN
    is_1h_bullish = rsi_1h > WATERFALL_1H_RSI_UP

    if not is_1h_bearish and not is_1h_bullish:
        return "NORMAL"

    # Check 2: 15M RSI ceiling/floor — confirms sustained trend
    hist_15m = rsi_history_15m.get(asset)
    confirm_15m = False
    if hist_15m and len(hist_15m) >= 4:
        recent_4 = list(hist_15m)[-4:]
        if is_1h_bearish and max(recent_4) < WATERFALL_15M_CEILING:
            confirm_15m = True
        elif is_1h_bullish and min(recent_4) > (100 - WATERFALL_15M_CEILING):
            confirm_15m = True

    # Check 3: Price rate of change over last 6 1H candles
    confirm_roc = False
    candles_1h = candle_cache.get((asset, "1h"))
    if candles_1h and len(candles_1h) >= 7:
        close_now = candles_1h[-1]["close"]
        close_6h = candles_1h[-7]["close"]
        roc_pct = (close_now - close_6h) / close_6h * 100
        if is_1h_bearish and roc_pct < -WATERFALL_ROC_PCT:
            confirm_roc = True
        elif is_1h_bullish and roc_pct > WATERFALL_ROC_PCT:
            confirm_roc = True

    # Need 1H extreme + at least one confirmation
    if is_1h_bearish and (confirm_15m or confirm_roc):
        return "WATERFALL_DOWN"
    if is_1h_bullish and (confirm_15m or confirm_roc):
        return "WATERFALL_UP"

    return "NORMAL"


def update_all_regimes():
    """Update market regime for all assets. Called every cycle. Debounced (2 checks)."""
    for asset in ASSET_NAMES:
        old = market_regime.get(asset, "NORMAL")
        new = detect_market_regime(asset)

        if old != new:
            pending = regime_debounce.get(asset)
            if pending and pending["regime"] == new:
                pending["count"] += 1
                if pending["count"] >= REGIME_DEBOUNCE_CHECKS:
                    market_regime[asset] = new
                    if asset in regime_debounce:
                        del regime_debounce[asset]
                    log.info(f"Regime change (confirmed): {asset} {old} -> {new}")
                    pending_regime_changes.append((asset, old, new))
                    # Reset bounce state on regime change
                    bounce_state[asset] = "idle"
                    bounce_rsi_low[asset] = 100
            else:
                regime_debounce[asset] = {"regime": new, "count": 1}
        else:
            market_regime[asset] = new
            if asset in regime_debounce:
                del regime_debounce[asset]


def get_regime_str(asset):
    """Short regime string for signal messages."""
    regime = market_regime.get(asset, "NORMAL")
    if regime == "WATERFALL_DOWN":
        return "\u26a0\ufe0f WATERFALL"
    elif regime == "WATERFALL_UP":
        return "\u26a0\ufe0f MELT-UP"
    return ""


def get_trend_label(state):
    """Human-readable trend label."""
    labels = {
        "STRONG_UPTREND": "Strong Uptrend",
        "MILD_UPTREND": "Mild Uptrend",
        "NEUTRAL": "Neutral",
        "MILD_DOWNTREND": "Mild Downtrend",
        "STRONG_DOWNTREND": "Strong Downtrend",
    }
    return labels.get(state, state)


# ==============================================================================
# ADAPTIVE RSI THRESHOLDS (Feature 2)
# ==============================================================================

def get_rsi_thresholds(asset):
    """Return (long_entry, short_entry) based on current trend state.
    None = suppressed (don't fire signals for that side).
    Applies per-asset offset (e.g. SOL +5 = wider bands).
    """
    state = trend_state.get(asset, "NEUTRAL")
    cfg = TREND_THRESHOLDS.get(state, TREND_THRESHOLDS["NEUTRAL"])
    offset = ASSET_THRESHOLD_OFFSET.get(asset, 0)
    long_t = cfg["long"]
    short_t = cfg["short"]
    if offset and long_t is not None:
        long_t = long_t - offset  # lower = harder to trigger long
    if offset and short_t is not None:
        short_t = short_t + offset  # higher = harder to trigger short
    return long_t, short_t


def get_15m_thresholds(asset):
    """15M thresholds are 5 points more extreme than 5M ones.
    For longs: 15M threshold = 5M threshold + 5 (higher = more extreme oversold approach)
    For shorts: 15M threshold = 5M threshold - 5 (lower = more extreme overbought approach)
    """
    long_5m, short_5m = get_rsi_thresholds(asset)
    long_15m = (long_5m + 5) if long_5m is not None else None
    short_15m = (short_5m - 5) if short_5m is not None else None
    return long_15m, short_15m


# ==============================================================================
# RSI VELOCITY FILTER (Feature 3)
# ==============================================================================

def update_rsi_history(asset, tf, rsi_val):
    """Store RSI reading in history buffer."""
    if rsi_val is None:
        return
    key = (asset, tf)
    if key not in rsi_history:
        rsi_history[key] = deque(maxlen=5)
    rsi_history[key].append(rsi_val)


def get_rsi_velocity(asset, tf):
    """Calculate RSI movement over last 3 readings.
    Returns (velocity_pts, direction_str) or (0, "").
    """
    key = (asset, tf)
    hist = rsi_history.get(key)
    if not hist or len(hist) < 4:
        return 0, ""
    # Movement from 3 readings ago to current
    oldest = hist[-4]  # 3 candles back
    newest = hist[-1]
    velocity = newest - oldest
    direction = "\u2191" if velocity > 0 else "\u2193"
    return abs(velocity), f"{direction}{abs(velocity):.0f}pts in 3 candles"




# ==============================================================================
# v2.3: RSI DIRECTION TRACKING FOR 15M/30M
# ==============================================================================

def update_rsi_direction_history(asset, tf):
    """Store RSI reading for 15m or 30m direction tracking."""
    rsi_val = _get_rsi(asset, tf)
    if rsi_val is None:
        return
    if tf == "15m":
        if asset not in rsi_history_15m:
            rsi_history_15m[asset] = deque(maxlen=8)
        rsi_history_15m[asset].append(rsi_val)
    elif tf == "30m":
        if asset not in rsi_history_30m:
            rsi_history_30m[asset] = deque(maxlen=8)
        rsi_history_30m[asset].append(rsi_val)


def get_rsi_direction(asset, tf):
    """Return (direction_str, delta_pts) for 15m or 30m RSI.
    direction_str: 'up' / 'down' / 'flat'
    delta_pts: absolute change from previous reading
    """
    hist = rsi_history_15m.get(asset) if tf == "15m" else rsi_history_30m.get(asset)
    if not hist or len(hist) < 2:
        return "flat", 0.0
    delta = hist[-1] - hist[-2]
    if abs(delta) < 1.0:
        return "flat", abs(delta)
    return ("up" if delta > 0 else "down"), abs(delta)


def is_rsi_aligned(direction, rsi_dir):
    """Check if RSI direction supports the trade direction."""
    if direction == "long":
        return rsi_dir == "up"
    elif direction == "short":
        return rsi_dir == "down"
    return False


def _15m_consecutive_against(asset, trade_direction):
    """Count consecutive 15m RSI readings moving against the trade direction."""
    hist = rsi_history_15m.get(asset)
    if not hist or len(hist) < 2:
        return 0
    count = 0
    for i in range(len(hist) - 1, 0, -1):
        delta = hist[i] - hist[i-1]
        if trade_direction == "long" and delta < -0.5:
            count += 1
        elif trade_direction == "short" and delta > 0.5:
            count += 1
        else:
            break
    return count


def _build_tf_context(asset, direction):
    """Build simple confluence summary for entry signals.
    Returns (confluence_str, aligned_count, total_count).
    v2.4: During waterfall, all-oversold = trend strength, labeled accordingly."""
    aligned = 0
    total = 0
    regime = market_regime.get(asset, "NORMAL")

    for tf in ["15m", "30m", "1h"]:
        rsi = _get_rsi(asset, tf)
        if rsi is None:
            continue
        total += 1
        if direction == "long" and rsi < 40:
            aligned += 1
        elif direction == "short" and rsi > 60:
            aligned += 1

    # During waterfall, all-aligned for longs/shorts means trend strength
    tag = ""
    if regime == "WATERFALL_DOWN" and direction == "long" and aligned == total and total > 0:
        tag = " (trend)"
    elif regime == "WATERFALL_UP" and direction == "short" and aligned == total and total > 0:
        tag = " (trend)"
    return f"{aligned}/{total} TFs{tag}", aligned, total


def _get_1d_rsi_str(asset):
    """Get 1D RSI as label + direction arrow for signal context."""
    rsi_1d = _get_rsi(asset, "1d")
    if rsi_1d is None:
        return ""
    # Label
    if rsi_1d > 70:
        label = "Overbought"
    elif rsi_1d >= 60:
        label = "Bullish"
    elif rsi_1d >= 45:
        label = "Neutral"
    elif rsi_1d >= 30:
        label = "Bearish"
    else:
        label = "Oversold"
    # Direction from previous value if available
    hist = rsi_history.get((asset, "1d"))
    if hist and len(hist) >= 2:
        delta = hist[-1] - hist[-2]
        arrow = "\u2191" if delta > 1 else "\u2193" if delta < -1 else ""
    else:
        arrow = ""
    return f"1D: {label}{arrow}"

def fetch_binance_volume():
    """Fetch last 20 5m candles from Binance Futures for volume analysis. Cached for VOLUME_CACHE_TTL."""
    global binance_volume_last_fetch
    now = time.time()
    if now - binance_volume_last_fetch < VOLUME_CACHE_TTL:
        return

    for asset, symbol in BINANCE_SYMBOLS.items():
        try:
            url = f"{BINANCE_KLINES_URL}?symbol={symbol}&interval=5m&limit=20"
            resp = json.loads(urllib.request.urlopen(url, timeout=10).read().decode())
            if resp and len(resp) > 0:
                candles = []
                for c in resp:
                    candles.append({
                        "vol_usd": float(c[7]),  # quote_volume
                        "tbr": float(c[10]) / float(c[7]) if float(c[7]) > 0 else 0.5,  # taker buy ratio
                        "close": float(c[4]),
                        "open": float(c[1]),
                    })
                binance_volume_cache[asset] = {"candles": candles, "time": now}
        except Exception as e:
            log.warning(f"Binance volume fetch failed for {asset}: {e}")

    binance_volume_last_fetch = now


def _get_vol_context(asset):
    """Check recent Binance volume for elevated activity.
    Returns short warning string or empty string. NOT a filter — just context."""
    data = binance_volume_cache.get(asset)
    if not data or time.time() - data["time"] > VOLUME_CACHE_TTL * 3:
        return ""

    candles = data["candles"]
    if len(candles) < 3:
        return ""

    median_vol = VOLUME_MEDIANS.get(asset, 10_000_000)

    # Check last 3 candles for spikes
    recent = candles[-3:]
    max_vol = max(c["vol_usd"] for c in recent)
    max_mult = max_vol / median_vol

    if max_mult < VOLUME_WARNING_MULT:
        return ""

    # Determine direction bias from taker buy ratio
    avg_tbr = sum(c["tbr"] for c in recent) / len(recent)
    if avg_tbr < 0.4:
        bias = "sell-heavy"
    elif avg_tbr > 0.6:
        bias = "buy-heavy"
    else:
        bias = "mixed"

    return f"\u26a1 Vol {max_mult:.0f}x {bias}"


def _get_1h_rsi_trend_str(asset):
    """Get 1H RSI with direction arrow for signal line 3."""
    rsi_1h = _get_rsi(asset, "1h")
    if rsi_1h is None:
        return ""
    hist = rsi_history.get((asset, "1h"))
    if hist and len(hist) >= 2:
        delta = hist[-1] - hist[-2]
        arrow = "\u2191" if delta > 1 else "\u2193" if delta < -1 else ""
    else:
        arrow = ""
    return f"1H RSI {rsi_1h:.0f}{arrow}"


def _register_active_signal(asset, direction, price, rsi_5m, grade):
    """Register an active signal for exit/hold tracking."""
    import time as _time
    active_signals[asset] = {
        "direction": direction,
        "entry_time": _time.time(),
        "entry_price": price,
        "entry_rsi_5m": rsi_5m,
        "entry_rsi_15m": _get_rsi(asset, "15m"),
        "entry_rsi_30m": _get_rsi(asset, "30m"),
        "time_warned_5": False,
        "time_warned_15": False,
    }
    if asset not in signal_history:
        signal_history[asset] = deque(maxlen=10)
    signal_history[asset].append({
        "direction": direction,
        "time": _time.time(),
        "grade": grade,
    })


def check_repeat_signal(asset, direction, grade):
    """Check if this is a repeated signal. Returns (should_fire, count, reason)."""
    import time as _time
    now = _time.time()
    hist = signal_history.get(asset)
    if not hist:
        return True, 1, ""
    recent = [s for s in hist if s["direction"] == direction and now - s["time"] < REPEAT_SIGNAL_WINDOW]
    count = len(recent) + 1
    if count <= 1:
        return True, 1, ""
    elif count == 2:
        if grade not in ("A", "B"):
            return False, count, f"2nd {direction} in {REPEAT_SIGNAL_WINDOW//60}min needs A/B"
        return True, count, ""
    else:
        if grade != "A":
            return False, count, f"{count}th {direction} in {int((now - recent[0]['time'])/60)}min - RSI not holding"
        return True, count, ""

# ==============================================================================
# MOMENTUM PERSISTENCE FILTER (Feature 4)
# ==============================================================================

def update_momentum_persistence(asset):
    """Track consecutive 5M candles with RSI above 60 or below 40."""
    rsi_5m = _get_rsi(asset, "5m")
    if rsi_5m is None:
        return None

    # Reset through 50
    if 45 <= rsi_5m <= 55:
        momentum_above[asset] = 0
        momentum_below[asset] = 0
        momentum_warned[asset] = None
        return None

    if rsi_5m > 60:
        momentum_above[asset] = momentum_above.get(asset, 0) + 1
        momentum_below[asset] = 0
        count = momentum_above[asset]
        if count >= MOMENTUM_PERSISTENCE_THRESHOLD and momentum_warned.get(asset) != "above":
            momentum_warned[asset] = "above"
            log.info(f"Momentum persistence: {asset} RSI>60 for {count} candles (blocking counter-trend shorts)")
            return None  # suppress TG alert — too noisy, momentum info is in /status
    elif rsi_5m < 40:
        momentum_below[asset] = momentum_below.get(asset, 0) + 1
        momentum_above[asset] = 0
        count = momentum_below[asset]
        if count >= MOMENTUM_PERSISTENCE_THRESHOLD and momentum_warned.get(asset) != "below":
            momentum_warned[asset] = "below"
            log.info(f"Momentum persistence: {asset} RSI<40 for {count} candles (blocking counter-trend longs)")
            return None  # suppress TG alert — too noisy, momentum info is in /status
    else:
        # RSI between 40-60 but not in reset zone — don't count
        pass

    return None


def is_momentum_blocked(asset, direction):
    """Momentum persistence — disabled as filter, kept for logging only.
    User wants no suppression; volume context handles warnings instead."""
    return False


# ==============================================================================
# SIGNAL CLASSIFICATION (Feature 5)
# ==============================================================================

def classify_signal(asset, direction):
    """Classify signal as WITH-TREND, COUNTER-TREND, or NEUTRAL.
    v2.4: Regime overrides slow trend engine — waterfall down means longs are always CT."""
    regime = market_regime.get(asset, "NORMAL")

    # Regime overrides: fast detection beats slow EMA trend
    if regime == "WATERFALL_DOWN" and direction == "long":
        return "COUNTER-TREND"
    if regime == "WATERFALL_DOWN" and direction == "short":
        return "WITH-TREND"
    if regime == "WATERFALL_UP" and direction == "short":
        return "COUNTER-TREND"
    if regime == "WATERFALL_UP" and direction == "long":
        return "WITH-TREND"

    # Fall back to slow trend engine
    state = trend_state.get(asset, "NEUTRAL")
    if state == "NEUTRAL":
        return "NEUTRAL"

    is_uptrend = state in ("STRONG_UPTREND", "MILD_UPTREND")
    is_downtrend = state in ("STRONG_DOWNTREND", "MILD_DOWNTREND")

    if direction == "long" and is_uptrend:
        return "WITH-TREND"
    if direction == "short" and is_downtrend:
        return "WITH-TREND"
    if direction == "long" and is_downtrend:
        return "COUNTER-TREND"
    if direction == "short" and is_uptrend:
        return "COUNTER-TREND"
    return "NEUTRAL"


def should_suppress_signal(classification, grade):
    """v2.4: No suppression — all signals pass through with warning tags.
    CT + WATERFALL tags provide context; user decides."""
    return False


# ==============================================================================
# CONFLUENCE BONUS
# ==============================================================================

def get_confluence_bonus(asset, direction):
    """Check supporting indicators for stage 2/3 alerts. Returns list of bonus lines."""
    bonuses = []

    # Volume spike on 5M or 15M
    for tf in ["5m", "15m"]:
        candles = candle_cache.get((asset, tf))
        if candles and len(candles) >= 21:
            volumes = [c["volume"] for c in candles]
            avg = sum(volumes[-21:-1]) / 20
            if avg > 0 and volumes[-1] / avg >= VOLUME_SPIKE_MULT:
                bonuses.append(f"Volume: {volumes[-1]/avg:.1f}x \u2713")
                break

    # MACD crossover on 1H
    candles_1h = candle_cache.get((asset, "1h"))
    if candles_1h and len(candles_1h) >= 36:
        closes = [c["close"] for c in candles_1h]
        _, _, hist = compute_macd(closes)
        if hist and len(hist) >= 2:
            if direction == "long" and hist[-1] > 0 and hist[-2] <= 0:
                bonuses.append("1H MACD bullish cross \u2713")
            elif direction == "short" and hist[-1] < 0 and hist[-2] >= 0:
                bonuses.append("1H MACD bearish cross \u2713")

    # Bollinger band touch on 1H
    if candles_1h and len(candles_1h) >= 20:
        closes = [c["close"] for c in candles_1h]
        upper, mid, lower = compute_bollinger(closes)
        if upper is not None:
            price = closes[-1]
            if direction == "long" and price < lower:
                bonuses.append("1H BB: Lower band \u2713")
            elif direction == "short" and price > upper:
                bonuses.append("1H BB: Upper band \u2713")

    # RSI divergence on 15M
    candles_15m = candle_cache.get((asset, "15m"))
    if candles_15m and len(candles_15m) >= 30:
        closes = [c["close"] for c in candles_15m]
        rsi_series = compute_rsi_series(closes)
        divs = detect_divergence(closes, rsi_series)
        if divs:
            if direction == "long" and divs[-1][0] == "bullish":
                bonuses.append("15M RSI divergence \u2713")
            elif direction == "short" and divs[-1][0] == "bearish":
                bonuses.append("15M RSI divergence \u2713")

    # Funding rate confluence
    funding_dir, funding_desc = get_funding_signal(asset)
    if funding_dir == direction and funding_desc:
        bonuses.append(funding_desc + " \u2713")

    return bonuses


def compute_grade(bonuses):
    """Grade from confluence count."""
    n = len(bonuses)
    if n >= 2:
        return "A"
    if n == 1:
        return "B"
    return "C"


# ==============================================================================
# STAGED RSI ALERTS (core feature — now trend-aware)
# ==============================================================================

def generate_staged_alerts():
    """3-stage RSI alert system based on 15M trigger + 5M confirmation.
    Now uses adaptive thresholds and signal classification."""
    alerts = []

    for asset in ASSET_NAMES:
        cfg = ASSETS[asset]
        emoji = cfg["emoji"]
        priority = cfg["priority"]

        # Get adaptive thresholds
        long_5m, short_5m = get_rsi_thresholds(asset)
        long_15m, short_15m = get_15m_thresholds(asset)

        # Staged thresholds: 15M enters the zone, 5M confirms
        # For 15M approach: use the 15M threshold
        # For 15M trigger (extreme): use the 5M threshold applied to 15M
        rsi_os_15m = long_15m  # approach zone for oversold
        rsi_os_trigger = long_5m  # trigger threshold (more extreme)
        rsi_ob_15m = short_15m  # approach zone for overbought
        rsi_ob_trigger = short_5m  # trigger threshold (more extreme)

        state = staged_state.get(asset, "neutral")
        ts = trend_state.get(asset, "NEUTRAL")
        trend_label = get_trend_label(ts)

        # Get RSI values
        rsi_15m = _get_rsi(asset, "15m")
        rsi_5m = _get_rsi(asset, "5m")
        rsi_1h = _get_rsi(asset, "1h")
        price = _get_price(asset)
        prev_5m = staged_5m_prev.get(asset)

        # Update 5M history
        if rsi_5m is not None:
            staged_5m_prev[asset] = rsi_5m

        if rsi_15m is None or price is None:
            continue

        # --- Reset: 15M RSI back to middle, clear state ---
        if state != "neutral" and 40 < rsi_15m < 60:
            staged_state[asset] = "neutral"
            log.info(f"Staged reset: {asset} -> neutral (15M RSI={rsi_15m:.1f})")
            continue

        new_state = state
        msg = None

        # === LONG SIDE ===
        if long_5m is not None and rsi_os_15m is not None:

            # Stage 1: approaching oversold
            if state == "neutral" and rsi_os_15m >= rsi_15m > (rsi_os_trigger if rsi_os_trigger else 0):
                new_state = "approach_long"

            # Stage 2: 15M crosses below threshold
            elif state in ("neutral", "approach_long") and rsi_os_trigger is not None and rsi_15m <= rsi_os_trigger:
                new_state = "triggered_long"
                rsi_5m_str = f"{rsi_5m:.1f}" if rsi_5m else "N/A"
                rsi_1h_str = f"{rsi_1h:.1f}" if rsi_1h else "N/A"
                bonuses = get_confluence_bonus(asset, "long")
                grade = compute_grade(bonuses)
                if grade == "C" and rsi_5m is not None and rsi_5m <= RSI_DEEP_EXTREME_LOW:
                    grade = "C*"
                classification = classify_signal(asset, "long")
                suppressed = should_suppress_signal(classification, grade)

                if is_momentum_blocked(asset, "long"):
                    log.info(f"Momentum blocked: {asset} LONG (RSI below 40 for {momentum_below.get(asset,0)} candles)")
                elif grade == "C":
                    log.info(f"Suppressed Grade C: {asset} OVERSOLD 15M={rsi_15m:.1f}")
                else:
                    should_fire, rep_count, rep_reason = check_repeat_signal(asset, "long", grade)
                    if not should_fire:
                        log.info(f"Repeat suppressed: {asset} LONG #{rep_count}: {rep_reason}")
                    else:
                        conf_str, _, _ = _build_tf_context(asset, "long")
                        regime_tag = get_regime_str(asset)
                        rep_str = f" ({rep_count}x)" if rep_count >= 2 else ""
                        tag = f" {regime_tag}" if regime_tag else (" \u26a0\ufe0f CT" if classification == "COUNTER-TREND" else "")
                        msg = f"\U0001f7e2 {emoji} {asset} LONG \u2014 Grade {grade}{tag}{rep_str}\n${price:,.2f}\n{_get_1h_rsi_trend_str(asset)} | {conf_str}"
                        vol_ctx = _get_vol_context(asset)
                        if vol_ctx:
                            msg += f"\n{vol_ctx}"
                        _register_active_signal(asset, "long", price, rsi_5m if rsi_5m else 0, grade)

            # Stage 3: 5M confirms (was oversold, now turning up)
            elif state == "triggered_long" and rsi_5m is not None and prev_5m is not None:
                confirm_zone = (long_5m + RSI_APPROACH_BUFFER) if long_5m else 35
                if prev_5m < confirm_zone and rsi_5m > prev_5m + 2:
                    new_state = "neutral"
                    bonuses = get_confluence_bonus(asset, "long")
                    grade = compute_grade(bonuses)
                    if grade == "C" and rsi_5m is not None and rsi_5m <= RSI_DEEP_EXTREME_LOW:
                        grade = "C*"
                    classification = classify_signal(asset, "long")
                    suppressed = should_suppress_signal(classification, grade)

                    vel_pts, vel_str = get_rsi_velocity(asset, "5m")

                    if is_momentum_blocked(asset, "long"):
                        log.info(f"Momentum blocked: {asset} LONG CONFIRMED")
                    elif grade == "C":
                        log.info(f"Suppressed Grade C: {asset} LONG CONFIRMED 5M={rsi_5m:.1f}")
                    else:
                        should_fire, rep_count, rep_reason = check_repeat_signal(asset, "long", grade)
                        if not should_fire:
                            log.info(f"Repeat suppressed: {asset} LONG CONFIRMED #{rep_count}: {rep_reason}")
                        else:
                            conf_str, _, _ = _build_tf_context(asset, "long")
                            regime_tag = get_regime_str(asset)
                            rep_str = f" ({rep_count}x)" if rep_count >= 2 else ""
                            tag = f" {regime_tag}" if regime_tag else (" \u26a0\ufe0f CT" if classification == "COUNTER-TREND" else "")
                            msg = f"\U0001f7e2 {emoji} {asset} LONG \u2014 Grade {grade}{tag}{rep_str}\n${price:,.2f}\n{_get_1h_rsi_trend_str(asset)} | {conf_str}"
                            vol_ctx = _get_vol_context(asset)
                            if vol_ctx:
                                msg += f"\n{vol_ctx}"
                            _register_active_signal(asset, "long", price, rsi_5m if rsi_5m else 0, grade)

        # === SHORT SIDE ===
        if short_5m is not None and rsi_ob_15m is not None and msg is None:

            # Stage 1: approaching overbought
            if state == "neutral" and rsi_ob_15m <= rsi_15m < (rsi_ob_trigger if rsi_ob_trigger else 100):
                new_state = "approach_short"

            # Stage 2: 15M crosses above threshold
            elif state in ("neutral", "approach_short") and rsi_ob_trigger is not None and rsi_15m >= rsi_ob_trigger:
                new_state = "triggered_short"
                rsi_5m_str = f"{rsi_5m:.1f}" if rsi_5m else "N/A"
                rsi_1h_str = f"{rsi_1h:.1f}" if rsi_1h else "N/A"
                bonuses = get_confluence_bonus(asset, "short")
                grade = compute_grade(bonuses)
                if grade == "C" and rsi_5m is not None and rsi_5m >= RSI_DEEP_EXTREME_HIGH:
                    grade = "C*"
                classification = classify_signal(asset, "short")
                suppressed = should_suppress_signal(classification, grade)

                if is_momentum_blocked(asset, "short"):
                    log.info(f"Momentum blocked: {asset} SHORT (RSI above 60 for {momentum_above.get(asset,0)} candles)")
                elif grade == "C":
                    log.info(f"Suppressed Grade C: {asset} OVERBOUGHT 15M={rsi_15m:.1f}")
                else:
                    should_fire, rep_count, rep_reason = check_repeat_signal(asset, "short", grade)
                    if not should_fire:
                        log.info(f"Repeat suppressed: {asset} SHORT #{rep_count}: {rep_reason}")
                    else:
                        conf_str, _, _ = _build_tf_context(asset, "short")
                        regime_tag = get_regime_str(asset)
                        rep_str = f" ({rep_count}x)" if rep_count >= 2 else ""
                        tag = f" {regime_tag}" if regime_tag else (" \u26a0\ufe0f CT" if classification == "COUNTER-TREND" else "")
                        msg = f"\U0001f534 {emoji} {asset} SHORT \u2014 Grade {grade}{tag}{rep_str}\n${price:,.2f}\n{_get_1h_rsi_trend_str(asset)} | {conf_str}"
                        vol_ctx = _get_vol_context(asset)
                        if vol_ctx:
                            msg += f"\n{vol_ctx}"
                        _register_active_signal(asset, "short", price, rsi_5m if rsi_5m else 0, grade)

            # Stage 3: 5M confirms (was overbought, now turning down)
            elif state == "triggered_short" and rsi_5m is not None and prev_5m is not None:
                confirm_zone = (short_5m - RSI_APPROACH_BUFFER) if short_5m else 65
                if prev_5m > confirm_zone and rsi_5m < prev_5m - 2:
                    new_state = "neutral"
                    bonuses = get_confluence_bonus(asset, "short")
                    grade = compute_grade(bonuses)
                    if grade == "C" and rsi_5m is not None and rsi_5m >= RSI_DEEP_EXTREME_HIGH:
                        grade = "C*"
                    classification = classify_signal(asset, "short")
                    suppressed = should_suppress_signal(classification, grade)

                    vel_pts, vel_str = get_rsi_velocity(asset, "5m")

                    if is_momentum_blocked(asset, "short"):
                        log.info(f"Momentum blocked: {asset} SHORT CONFIRMED")
                    elif grade == "C":
                        log.info(f"Suppressed Grade C: {asset} SHORT CONFIRMED 5M={rsi_5m:.1f}")
                    else:
                        should_fire, rep_count, rep_reason = check_repeat_signal(asset, "short", grade)
                        if not should_fire:
                            log.info(f"Repeat suppressed: {asset} SHORT CONFIRMED #{rep_count}: {rep_reason}")
                        else:
                            conf_str, _, _ = _build_tf_context(asset, "short")
                            regime_tag = get_regime_str(asset)
                            rep_str = f" ({rep_count}x)" if rep_count >= 2 else ""
                            tag = f" {regime_tag}" if regime_tag else (" \u26a0\ufe0f CT" if classification == "COUNTER-TREND" else "")
                            msg = f"\U0001f534 {emoji} {asset} SHORT \u2014 Grade {grade}{tag}{rep_str}\n${price:,.2f}\n{_get_1h_rsi_trend_str(asset)} | {conf_str}"
                            vol_ctx = _get_vol_context(asset)
                            if vol_ctx:
                                msg += f"\n{vol_ctx}"
                            _register_active_signal(asset, "short", price, rsi_5m if rsi_5m else 0, grade)

        # === v2.4: BOUNCE-FADE SHORT (only during WATERFALL_DOWN) ===
        regime = market_regime.get(asset, "NORMAL")
        if regime == "WATERFALL_DOWN" and rsi_5m is not None and msg is None:
            bs = bounce_state.get(asset, "idle")
            prev_low = bounce_rsi_low.get(asset, 100)

            # Track lowest RSI seen
            if rsi_5m < prev_low:
                bounce_rsi_low[asset] = rsi_5m

            if bs == "idle" and rsi_5m < 25:
                bounce_state[asset] = "watching"
                bounce_rsi_low[asset] = rsi_5m
                log.info(f"Bounce-fade: {asset} watching (5M RSI {rsi_5m:.1f})")

            elif bs == "watching" and rsi_5m >= BOUNCE_FADE_ENTRY:
                bounce_state[asset] = "ready"
                log.info(f"Bounce-fade: {asset} ready (5M RSI {rsi_5m:.1f}, low was {bounce_rsi_low.get(asset, 0):.1f})")

            elif bs == "ready":
                if prev_5m is not None and rsi_5m < prev_5m - BOUNCE_FADE_TURN:
                    # 5M RSI turning down — fire short signal
                    bounce_state[asset] = "idle"
                    bounce_rsi_low[asset] = 100
                    conf_str, _, _ = _build_tf_context(asset, "short")
                    rsi_1h_val = _get_rsi(asset, "1h")
                    rsi_1h_str = f"{rsi_1h_val:.0f}" if rsi_1h_val else "?"
                    msg = f"\U0001f534 {emoji} {asset} SHORT \u2014 Bounce Fade\n${price:,.2f}\n1H RSI {rsi_1h_str} | {conf_str}"
                    vol_ctx = _get_vol_context(asset)
                    if vol_ctx:
                        msg += f"\n{vol_ctx}"
                    _register_active_signal(asset, "short", price, rsi_5m, "B")
                    log.info(f"Bounce-fade SHORT fired: {asset} 5M RSI {rsi_5m:.1f} (was {bounce_rsi_low.get(asset, 0):.1f})")
                elif rsi_5m > 55:
                    # Bounce is real (RSI reclaiming), cancel fade
                    bounce_state[asset] = "idle"
                    bounce_rsi_low[asset] = 100
                    log.info(f"Bounce-fade: {asset} cancelled — RSI reclaimed 55")

            # Reset if regime clears
        elif regime != "WATERFALL_DOWN":
            if bounce_state.get(asset) != "idle":
                bounce_state[asset] = "idle"
                bounce_rsi_low[asset] = 100

        if new_state != state:
            staged_state[asset] = new_state
            r5 = f"{rsi_5m:.1f}" if rsi_5m else "N/A"
            log.info(f"Staged: {asset} {state} -> {new_state} | 15M={rsi_15m:.1f} 5M={r5} trend={ts}")

        if msg:
            alerts.append(msg)

    return alerts


# ==============================================================================
# STANDALONE 5M RSI ALERTS (all assets, trend-aware + velocity)
# ==============================================================================

def generate_5m_rsi_alerts():
    """Fire alerts when 5m RSI crosses adaptive thresholds.
    Requires RSI velocity >= 15 pts in 3 candles."""
    alerts = []

    for asset in ASSET_NAMES:
        rsi_5m = _get_rsi(asset, "5m")
        price = _get_price(asset)
        if rsi_5m is None or price is None:
            continue

        # Update RSI history for velocity
        update_rsi_history(asset, "5m", rsi_5m)

        emoji = ASSETS[asset]["emoji"]
        now = time.time()
        state = rsi_5m_state.get(asset, "neutral")
        last_alert = rsi_5m_last_alert.get(asset, 0)

        long_thresh, short_thresh = get_rsi_thresholds(asset)
        ts = trend_state.get(asset, "NEUTRAL")
        trend_label = get_trend_label(ts)

        vel_pts, vel_str = get_rsi_velocity(asset, "5m")

        # Oversold: RSI crosses below long threshold
        if long_thresh is not None and rsi_5m <= long_thresh and state != "oversold":
            if now - last_alert >= RSI_5M_COOLDOWN:
                if vel_pts >= RSI_VELOCITY_MIN or rsi_5m <= RSI_DEEP_EXTREME_LOW:
                    classification = classify_signal(asset, "long")
                    rsi_5m_state[asset] = "oversold"
                    rsi_5m_last_alert[asset] = now

                    if is_momentum_blocked(asset, "long"):
                        log.info(f"Momentum blocked: {asset} 5M oversold alert")
                    else:
                        deep_tag = " (DEEP)" if rsi_5m <= RSI_DEEP_EXTREME_LOW else ""
                        should_fire, rep_count, rep_reason = check_repeat_signal(asset, "long", "B")
                        if not should_fire:
                            log.info(f"Repeat suppressed: {asset} 5M oversold #{rep_count}: {rep_reason}")
                        else:
                            conf_str, _, _ = _build_tf_context(asset, "long")
                            regime_tag = get_regime_str(asset)
                            rep_str = f" ({rep_count}x)" if rep_count >= 2 else ""
                            tag = f" {regime_tag}" if regime_tag else (" \u26a0\ufe0f CT" if classification == "COUNTER-TREND" else "")
                            msg = f"\U0001f7e2 {emoji} {asset} LONG \u2014 Grade B{tag}{rep_str}\n${price:,.2f}\n{_get_1h_rsi_trend_str(asset)} | {conf_str}"
                            vol_ctx = _get_vol_context(asset)
                            if vol_ctx:
                                msg += f"\n{vol_ctx}"
                            _register_active_signal(asset, "long", price, rsi_5m if rsi_5m else 0, "B")
                        log.info(f"{asset} 5m RSI oversold: {rsi_5m:.1f} vel={vel_pts:.0f}")
                else:
                    rsi_5m_state[asset] = "oversold"
                    log.info(f"{asset} 5m RSI oversold but slow (vel={vel_pts:.0f} < {RSI_VELOCITY_MIN})")

        # Overbought: RSI crosses above short threshold
        elif short_thresh is not None and rsi_5m >= short_thresh and state != "overbought":
            if now - last_alert >= RSI_5M_COOLDOWN:
                if vel_pts >= RSI_VELOCITY_MIN or rsi_5m >= RSI_DEEP_EXTREME_HIGH:
                    classification = classify_signal(asset, "short")
                    rsi_5m_state[asset] = "overbought"
                    rsi_5m_last_alert[asset] = now

                    if is_momentum_blocked(asset, "short"):
                        log.info(f"Momentum blocked: {asset} 5M overbought alert")
                    else:
                        deep_tag = " (DEEP)" if rsi_5m >= RSI_DEEP_EXTREME_HIGH else ""
                        should_fire, rep_count, rep_reason = check_repeat_signal(asset, "short", "B")
                        if not should_fire:
                            log.info(f"Repeat suppressed: {asset} 5M overbought #{rep_count}: {rep_reason}")
                        else:
                            conf_str, _, _ = _build_tf_context(asset, "short")
                            regime_tag = get_regime_str(asset)
                            rep_str = f" ({rep_count}x)" if rep_count >= 2 else ""
                            tag = f" {regime_tag}" if regime_tag else (" \u26a0\ufe0f CT" if classification == "COUNTER-TREND" else "")
                            msg = f"\U0001f534 {emoji} {asset} SHORT \u2014 Grade B{tag}{rep_str}\n${price:,.2f}\n{_get_1h_rsi_trend_str(asset)} | {conf_str}"
                            vol_ctx = _get_vol_context(asset)
                            if vol_ctx:
                                msg += f"\n{vol_ctx}"
                            _register_active_signal(asset, "short", price, rsi_5m if rsi_5m else 0, "B")
                        log.info(f"{asset} 5m RSI overbought: {rsi_5m:.1f} vel={vel_pts:.0f}")
                else:
                    rsi_5m_state[asset] = "overbought"
                    log.info(f"{asset} 5m RSI overbought but slow (vel={vel_pts:.0f} < {RSI_VELOCITY_MIN})")

        # Reset when RSI returns to neutral zone (40-60)
        elif 40 < rsi_5m < 60:
            rsi_5m_state[asset] = "neutral"

    return alerts


# ==============================================================================
# OTHER ALERTS (EMA, divergence, volume — no per-TF RSI spam)
# ==============================================================================

def check_and_alert(indicator, tf, asset, new_state, message):
    """Return message only on state change."""
    key = (indicator, tf, asset)
    old_state = alert_state.get(key)
    if new_state == old_state:
        return None
    alert_state[key] = new_state
    return message


def generate_other_alerts():
    """EMA crosses, divergence, volume spikes."""
    alerts = []

    for asset in ASSET_NAMES:
        cfg = ASSETS[asset]
        emoji = cfg["emoji"]

        # -- EMA cross ---------------------------------------------------------
        for tf in EMA_TIMEFRAMES:
            candles = candle_cache.get((asset, tf))
            if not candles or len(candles) < 201:
                continue
            closes = [c["close"] for c in candles]
            ema200 = compute_ema(closes, 200)
            ema50 = compute_ema(closes, 50)
            if ema50 and ema200:
                e50 = ema50[-1]
                e200 = ema200[-1]
                new = "golden" if e50 > e200 else "death"
                old = alert_state.get(("ema_cross", tf, asset))
                if old and old != new:
                    if new == "golden":
                        msg = check_and_alert("ema_cross", tf, asset, new,
                            f"{emoji} {asset} {tf} \u2014 Golden Cross\n"
                            f"EMA50 ${e50:,.2f} > EMA200 ${e200:,.2f}")
                    else:
                        msg = check_and_alert("ema_cross", tf, asset, new,
                            f"{emoji} {asset} {tf} \u2014 Death Cross\n"
                            f"EMA50 ${e50:,.2f} < EMA200 ${e200:,.2f}")
                    if msg:
                        alerts.append(msg)
                else:
                    alert_state[("ema_cross", tf, asset)] = new

        # -- Divergence (with Cardwell reclassification) -----------------------
        ts = trend_state.get(asset, "NEUTRAL")
        for tf in DIVERGENCE_TIMEFRAMES:
            candles = candle_cache.get((asset, tf))
            if not candles or len(candles) < 30:
                continue
            closes = [c["close"] for c in candles]
            rsi_series = compute_rsi_series(closes)
            divs = detect_divergence(closes, rsi_series)
            new = divs[-1][0] if divs else "none"
            old = alert_state.get(("divergence", tf, asset))
            if old and old != new and new != "none":
                desc = divs[-1][1]

                # Cardwell reclassification: divergence WITH the trend = continuation
                # Bearish div in strong uptrend = price keeps making highs, RSI fading = normal, not reversal
                # Bullish div in strong downtrend = price keeps making lows, RSI rising = normal, not reversal
                cardwell_continuation = False
                if new == "bearish" and ts in ("STRONG_UPTREND",):
                    cardwell_continuation = True
                    log.info(f"Cardwell: {asset} {tf} bearish div reclassified as continuation (strong uptrend)")
                    msg = check_and_alert("divergence", tf, asset, new,
                        f"{emoji} {asset} {tf} \u2014 RSI Divergence (Continuation)\n"
                        f"{desc}\n"
                        f"Cardwell: bearish div in strong uptrend = trend intact, not reversal")
                elif new == "bullish" and ts in ("STRONG_DOWNTREND",):
                    cardwell_continuation = True
                    log.info(f"Cardwell: {asset} {tf} bullish div reclassified as continuation (strong downtrend)")
                    msg = check_and_alert("divergence", tf, asset, new,
                        f"{emoji} {asset} {tf} \u2014 RSI Divergence (Continuation)\n"
                        f"{desc}\n"
                        f"Cardwell: bullish div in strong downtrend = trend intact, not reversal")
                elif new == "bullish":
                    msg = check_and_alert("divergence", tf, asset, new,
                        f"{emoji} {asset} {tf} \u2014 Bullish RSI Divergence\n"
                        f"{desc}")
                else:
                    msg = check_and_alert("divergence", tf, asset, new,
                        f"{emoji} {asset} {tf} \u2014 Bearish RSI Divergence\n"
                        f"{desc}")

                if msg:
                    alerts.append(msg)
            else:
                alert_state[("divergence", tf, asset)] = new

        # -- Volume Spike -- DISABLED v2.3 (noise — already used as confluence bonus in entry signals)
        pass

    return alerts


# ==============================================================================
# SWING ALERTS (3+ indicator confluence on 1H/4H)
# ==============================================================================

def generate_swing_alerts():
    """Per-asset, check 1H/4H for 3+ aligned indicators."""
    alerts = []
    now = time.time()

    for asset in ASSET_NAMES:
        cfg = ASSETS[asset]
        emoji = cfg["emoji"]
        rsi_os = cfg["rsi_os"]
        rsi_ob = cfg["rsi_ob"]

        if asset in last_swing_alert and now - last_swing_alert[asset] < SWING_COOLDOWN:
            continue

        for tf in ["1h", "4h"]:
            candles = candle_cache.get((asset, tf))
            if not candles or len(candles) < 30:
                continue
            closes = [c["close"] for c in candles]
            price = closes[-1]

            bullish_signals = []
            bearish_signals = []

            rsi = compute_rsi(closes)
            if rsi is not None:
                if rsi < rsi_os:
                    bullish_signals.append(f"RSI oversold ({rsi:.1f})")
                elif rsi > rsi_ob:
                    bearish_signals.append(f"RSI overbought ({rsi:.1f})")

            candles_15m = candle_cache.get((asset, "15m"))
            if candles_15m and len(candles_15m) >= 16:
                rsi_15m = compute_rsi([c["close"] for c in candles_15m])
                if rsi_15m is not None:
                    if rsi_15m < rsi_os:
                        bullish_signals.append(f"15M RSI confirms ({rsi_15m:.1f})")
                    elif rsi_15m > rsi_ob:
                        bearish_signals.append(f"15M RSI confirms ({rsi_15m:.1f})")

            if tf == "1h":
                candles_4h = candle_cache.get((asset, "4h"))
                if candles_4h and len(candles_4h) >= 201:
                    closes_4h = [c["close"] for c in candles_4h]
                    rsi_4h = compute_rsi(closes_4h)
                    ema200_4h = compute_ema(closes_4h, 200)
                    if rsi_4h is not None and ema200_4h:
                        if rsi_4h < 45 and closes_4h[-1] < ema200_4h[-1]:
                            bullish_signals.append("4H bearish trend (contrarian)")
                        elif rsi_4h > 55 and closes_4h[-1] > ema200_4h[-1]:
                            bearish_signals.append("4H bullish trend (contrarian)")

            if len(closes) >= 36:
                _, _, histogram = compute_macd(closes)
                if histogram and len(histogram) >= 2:
                    if histogram[-1] > 0 and histogram[-2] <= 0:
                        bullish_signals.append("MACD bullish cross")
                    elif histogram[-1] < 0 and histogram[-2] >= 0:
                        bearish_signals.append("MACD bearish cross")

            if len(closes) >= 20:
                upper, mid, lower = compute_bollinger(closes)
                if upper is not None:
                    if price < lower:
                        bullish_signals.append("Below lower Bollinger")
                    elif price > upper:
                        bearish_signals.append("Above upper Bollinger")

            rsi_series = compute_rsi_series(closes)
            divs = detect_divergence(closes, rsi_series)
            if divs:
                if divs[-1][0] == "bullish":
                    bullish_signals.append("Bullish RSI divergence")
                else:
                    bearish_signals.append("Bearish RSI divergence")

            if len(bullish_signals) >= 3:
                new = f"bullish_{len(bullish_signals)}"
                signals = "\n".join(f"  \u2022 {s}" for s in bullish_signals)
                msg = check_and_alert("swing", tf, asset, new,
                    f"{emoji} {asset} {tf} \u2014 SWING BULLISH\n"
                    f"{len(bullish_signals)} indicators aligned:\n{signals}\n"
                    f"${price:,.2f}")
                if msg:
                    alerts.append(msg)
                    last_swing_alert[asset] = now
            elif len(bearish_signals) >= 3:
                new = f"bearish_{len(bearish_signals)}"
                signals = "\n".join(f"  \u2022 {s}" for s in bearish_signals)
                msg = check_and_alert("swing", tf, asset, new,
                    f"{emoji} {asset} {tf} \u2014 SWING BEARISH\n"
                    f"{len(bearish_signals)} indicators aligned:\n{signals}\n"
                    f"${price:,.2f}")
                if msg:
                    alerts.append(msg)
                    last_swing_alert[asset] = now
            else:
                alert_state[("swing", tf, asset)] = "neutral"

    return alerts


# ==============================================================================
# CONTEXT ALERTS (proactive market info)
# ==============================================================================

def _ctx_can_fire(alert_type, asset, cooldown=CONTEXT_COOLDOWN_DEFAULT):
    return time.time() - context_cooldowns.get((alert_type, asset), 0) >= cooldown

def _ctx_fire(alert_type, asset):
    context_cooldowns[(alert_type, asset)] = time.time()


def generate_context_alerts():
    """Proactive context alerts — keeps user informed even when trade signals are suppressed."""
    alerts = []

    # --- v2.4: Regime changes (fast waterfall detection) ---
    while pending_regime_changes:
        asset, old_r, new_r = pending_regime_changes.pop(0)
        emoji = ASSETS[asset]["emoji"]
        rsi_1h_val = _get_rsi(asset, "1h")
        rsi_1h_str = f"{rsi_1h_val:.0f}" if rsi_1h_val else "?"
        if new_r == "WATERFALL_DOWN":
            msg = f"\u26a0\ufe0f {emoji} {asset} REGIME: WATERFALL DOWN\n1H RSI: {rsi_1h_str} | Shorts favored, longs risky"
        elif new_r == "WATERFALL_UP":
            msg = f"\u26a0\ufe0f {emoji} {asset} REGIME: MELT-UP\n1H RSI: {rsi_1h_str} | Longs favored, shorts risky"
        else:
            msg = f"\u2139\ufe0f {emoji} {asset} REGIME: Normal\nWaterfall cleared \u2014 standard signals resumed"
        alerts.append(msg)
        log.info(f"Regime alert: {asset} {old_r} -> {new_r}")

    # --- 5a. Trend state changes (drain pending list) ---
    while pending_trend_changes:
        asset, old_ts, new_ts = pending_trend_changes.pop(0)
        emoji = ASSETS[asset]["emoji"]
        old_label = get_trend_label(old_ts)
        new_label = get_trend_label(new_ts)

        # Determine implication
        trend_rank = {"STRONG_DOWNTREND": -2, "MILD_DOWNTREND": -1, "NEUTRAL": 0, "MILD_UPTREND": 1, "STRONG_UPTREND": 2}
        old_r = trend_rank.get(old_ts, 0)
        new_r = trend_rank.get(new_ts, 0)
        if new_r > old_r:
            impl = "Trend strengthening to upside"
        elif new_r < old_r:
            impl = "Trend weakening / shifting to downside"
        else:
            impl = "Trend shift"

        # Show new thresholds
        long_t, short_t = get_rsi_thresholds(asset)
        lt_str = f"L<{long_t}" if long_t is not None else "L:OFF"
        st_str = f"S>{short_t}" if short_t is not None else "S:OFF"

        alerts.append(
            f"\u2139\ufe0f {emoji} {asset} TREND SHIFT: {old_label} \u2192 {new_label}\n"
            f"{impl}\n"
            f"New thresholds: {lt_str} / {st_str}"
        )

    # Sections 1-8 DISABLED v2.3: these are noise.
    # Entry signals already capture confluence (grade + TF count).
    # Only trend shifts (above) are kept.

    return alerts


# ==============================================================================
# TELEGRAM UI
# ==============================================================================


# ==============================================================================
# v2.3: EXIT / HOLD SIGNALS (Multi-TF context while in trade)
# ==============================================================================

def _exit_can_fire(alert_type, asset):
    return time.time() - exit_alert_cooldowns.get((alert_type, asset), 0) >= EXIT_SIGNAL_COOLDOWN

def _exit_fire(alert_type, asset):
    exit_alert_cooldowns[(alert_type, asset)] = time.time()

def generate_exit_signals():
    """Check active signals for exit/hold conditions based on 15M/30M RSI."""
    alerts = []
    now = time.time()
    expired = []

    for asset, sig in list(active_signals.items()):
        emoji = ASSETS[asset]["emoji"]
        direction = sig["direction"]
        entry_time = sig["entry_time"]
        elapsed = now - entry_time

        rsi_5m = _get_rsi(asset, "5m")
        rsi_15m = _get_rsi(asset, "15m")
        rsi_30m = _get_rsi(asset, "30m")

        # --- Expiry check ---
        if elapsed > EXIT_SIGNAL_EXPIRY:
            expired.append(asset)
            continue
        if rsi_5m is not None and EXIT_RSI_NEUTRAL_LOW <= rsi_5m <= EXIT_RSI_NEUTRAL_HIGH:
            if elapsed > 120:  # 2 min grace period
                expired.append(asset)
                continue

        dir_15m, delta_15m = get_rsi_direction(asset, "15m")
        dir_30m, delta_30m = get_rsi_direction(asset, "30m")

        r5 = f"{rsi_5m:.0f}" if rsi_5m else "--"
        r15 = f"{rsi_15m:.1f}" if rsi_15m else "--"
        r30 = f"{rsi_30m:.1f}" if rsi_30m else "--"

        arrow_15 = "\u2191" if dir_15m == "up" else "\u2193" if dir_15m == "down" else "\u2192"
        arrow_30 = "\u2191" if dir_30m == "up" else "\u2193" if dir_30m == "down" else "\u2192"

        # --- (a) 15M RSI turning against ---
        consec_against = _15m_consecutive_against(asset, direction)
        if consec_against >= EXIT_15M_TURN_THRESHOLD and _exit_can_fire("15m_turn", asset):
            _exit_fire("15m_turn", asset)
            alerts.append(
                f"\u26a0\ufe0f {emoji} {asset} \u2014 15M RSI turning against your {direction}\n"
                f"15M RSI: {r15} ({arrow_15}{delta_15m:.0f}pts)\n"
                f"5M: {r5} | 30M: {r30}\n"
                f"Consider tightening stop or taking profit"
            )

        # --- (b) 30M RSI exhaustion (approaching neutral from extreme) ---
        if rsi_30m is not None:
            approaching_neutral = EXIT_30M_NEUTRAL_LOW <= rsi_30m <= EXIT_30M_NEUTRAL_HIGH
            entry_30m = sig.get("entry_rsi_30m")
            was_extreme = (
                (direction == "long" and entry_30m is not None and entry_30m < 40) or
                (direction == "short" and entry_30m is not None and entry_30m > 60)
            )
            if approaching_neutral and was_extreme and _exit_can_fire("30m_exhaust", asset):
                _exit_fire("30m_exhaust", asset)
                alerts.append(
                    f"\U0001f3af {emoji} {asset} \u2014 30M RSI approaching neutral ({rsi_30m:.0f}{arrow_30})\n"
                    f"Move may be exhausting. Lock in profits.\n"
                    f"5M: {r5} | 15M: {r15}"
                )

        # --- (c) 15M supports hold --- DISABLED: bot can't know if user is in a trade

        # --- (d) Time warnings --- DISABLED: bot can't know if user actually entered the trade

    # Clean up expired signals
    for asset in expired:
        del active_signals[asset]
        log.info(f"Active signal expired: {asset}")

    return alerts


def build_menu(selected_asset="ETH"):
    asset_buttons = []
    for name in ASSET_NAMES:
        label = f"[{name}]" if selected_asset == name else name
        asset_buttons.append(InlineKeyboardButton(label, callback_data=f"sel_{name.lower()}"))

    return InlineKeyboardMarkup([
        asset_buttons,
        [InlineKeyboardButton("RSI", callback_data="rsi"),
         InlineKeyboardButton("EMA", callback_data="ema")],
        [InlineKeyboardButton("MACD", callback_data="macd"),
         InlineKeyboardButton("Bollinger", callback_data="bollinger")],
        [InlineKeyboardButton("Divergence", callback_data="divergence"),
         InlineKeyboardButton("Volume", callback_data="volume")],
        [InlineKeyboardButton("Price", callback_data="price"),
         InlineKeyboardButton("Trend", callback_data="trend")],
    ])


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "*LighterRSI Signal Bot v2.4*\n\n"
        "Trend-aware staged RSI alerts for ETH/BTC/SOL on Lighter DEX.\n"
        "Funding rates | SOL-tuned thresholds | Cardwell divergence\n\n"
        "Choose an asset or indicator:",
        parse_mode="Markdown",
        reply_markup=build_menu(),
    )


async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await refresh_candles()
    update_all_trend_states()
    text = format_status()
    await update.message.reply_text(text, parse_mode="Markdown", reply_markup=build_menu())


# -- Formatters ----------------------------------------------------------------

def _get_selected_assets(asset_filter):
    if asset_filter and asset_filter in ASSETS:
        return [asset_filter]
    return ASSET_NAMES


def format_status():
    """Compact 3-asset dashboard with trend info."""
    lines = ["*Dashboard*\n"]
    for asset in ASSET_NAMES:
        cfg = ASSETS[asset]
        emoji = cfg["emoji"]
        price = _get_price(asset)
        price_str = f"${price:,.2f}" if price else "N/A"
        rsi_5m = _get_rsi(asset, "5m")
        rsi_15m = _get_rsi(asset, "15m")
        rsi_1h = _get_rsi(asset, "1h")
        ts = trend_state.get(asset, "NEUTRAL")

        rsi_30m = _get_rsi(asset, "30m")
        r5 = f"{rsi_5m:.0f}" if rsi_5m else "--"
        r15 = f"{rsi_15m:.0f}" if rsi_15m else "--"
        r30 = f"{rsi_30m:.0f}" if rsi_30m else "--"
        r1h = f"{rsi_1h:.0f}" if rsi_1h else "--"

        state = staged_state.get(asset, "neutral")
        state_str = ""
        if state != "neutral":
            state_str = f" | {state.replace('_', ' ').upper()}"

        trend_emoji = {
            "STRONG_UPTREND": "\u2b06\ufe0f\u2b06\ufe0f",
            "MILD_UPTREND": "\u2b06\ufe0f",
            "NEUTRAL": "\u27a1\ufe0f",
            "MILD_DOWNTREND": "\u2b07\ufe0f",
            "STRONG_DOWNTREND": "\u2b07\ufe0f\u2b07\ufe0f",
        }
        te = trend_emoji.get(ts, "")

        lines.append(f"{emoji} {asset}: {price_str} | 5M:{r5} 15M:{r15} 30M:{r30} 1H:{r1h} | {te} {get_trend_label(ts)}{state_str}")

        # Show active signal if any
        if asset in active_signals:
            asig = active_signals[asset]
            el = int(time.time() - asig["entry_time"])
            lines.append(f"  Active: {asig['direction'].upper()} ({el//60}m{el%60:02d}s)")

        # Show adaptive thresholds
        long_t, short_t = get_rsi_thresholds(asset)
        long_str = f"L<{long_t}" if long_t is not None else "L:OFF"
        short_str = f"S>{short_t}" if short_t is not None else "S:OFF"
        mom_a = momentum_above.get(asset, 0)
        mom_b = momentum_below.get(asset, 0)
        mom_str = ""
        if mom_a >= 5:
            mom_str = f" | Mom:{mom_a}\u2191"
        elif mom_b >= 5:
            mom_str = f" | Mom:{mom_b}\u2193"
        lines.append(f"  Thresholds: {long_str} / {short_str}{mom_str}")

    return "\n".join(lines)


def format_trend(asset_filter=None):
    """Detailed trend status for each asset."""
    assets = _get_selected_assets(asset_filter)
    lines = ["*Trend Status*\n"]
    for asset in assets:
        emoji = ASSETS[asset]["emoji"]
        ts = trend_state.get(asset, "NEUTRAL")
        price = _get_price(asset)
        ema_4h = _get_4h_ema50(asset)
        rsi_1h = _get_rsi(asset, "1h")
        rsi_5m = _get_rsi(asset, "5m")

        trend_emoji = {
            "STRONG_UPTREND": "\u2b06\ufe0f\u2b06\ufe0f",
            "MILD_UPTREND": "\u2b06\ufe0f",
            "NEUTRAL": "\u27a1\ufe0f",
            "MILD_DOWNTREND": "\u2b07\ufe0f",
            "STRONG_DOWNTREND": "\u2b07\ufe0f\u2b07\ufe0f",
        }
        te = trend_emoji.get(ts, "")

        lines.append(f"\n{emoji} *{asset}* {te} {get_trend_label(ts)}")

        if price and ema_4h:
            dist = (price - ema_4h) / ema_4h * 100
            lines.append(f"  Price: ${price:,.2f} | 4H EMA50: ${ema_4h:,.2f} ({dist:+.1f}%)")
        if rsi_1h is not None:
            lines.append(f"  1H RSI: {rsi_1h:.1f}")

        long_t, short_t = get_rsi_thresholds(asset)
        long_str = f"RSI < {long_t}" if long_t is not None else "SUPPRESSED"
        short_str = f"RSI > {short_t}" if short_t is not None else "SUPPRESSED"
        lines.append(f"  Long entry: {long_str}")
        lines.append(f"  Short entry: {short_str}")

        # Momentum persistence
        mom_a = momentum_above.get(asset, 0)
        mom_b = momentum_below.get(asset, 0)
        if mom_a > 0:
            lines.append(f"  Momentum: {mom_a} candles RSI>60" + (" \u26a0\ufe0f BLOCKING" if mom_a >= MOMENTUM_PERSISTENCE_THRESHOLD else ""))
        elif mom_b > 0:
            lines.append(f"  Momentum: {mom_b} candles RSI<40" + (" \u26a0\ufe0f BLOCKING" if mom_b >= MOMENTUM_PERSISTENCE_THRESHOLD else ""))
        else:
            lines.append(f"  Momentum: neutral")

        # RSI velocity
        vel_pts, vel_str = get_rsi_velocity(asset, "5m")
        if vel_pts > 0:
            lines.append(f"  5M Velocity: {vel_str}")

        # Funding rate
        rate = get_funding_rate(asset)
        if rate is not None:
            funding_dir, funding_desc = get_funding_signal(asset)
            if funding_dir:
                lines.append(f"  {funding_desc}")
            else:
                lines.append(f"  Funding: {rate*100:+.4f}% (neutral)")

    return "\n".join(lines)


def _rsi_label(rsi, asset="ETH"):
    cfg = ASSETS.get(asset, ASSETS["ETH"])
    if rsi < cfg["rsi_os"]:
        return "OVS"
    if rsi > cfg["rsi_ob"]:
        return "OVB"
    return ""


def format_rsi(asset_filter=None):
    assets = _get_selected_assets(asset_filter)
    lines = ["*RSI Snapshot*\n"]
    for asset in assets:
        emoji = ASSETS[asset]["emoji"]
        lines.append(f"\n{emoji} *{asset}*")
        for tf in RSI_TIMEFRAMES:
            candles = candle_cache.get((asset, tf))
            if not candles or len(candles) < 16:
                lines.append(f"  {tf}: \u2014")
                continue
            rsi = compute_rsi([c["close"] for c in candles])
            if rsi is None:
                lines.append(f"  {tf}: \u2014")
            else:
                lbl = _rsi_label(rsi, asset)
                suffix = f" *{lbl}*" if lbl else ""
                lines.append(f"  {tf}: {rsi:.1f}{suffix}")
    return "\n".join(lines)


def format_ema(asset_filter=None):
    assets = _get_selected_assets(asset_filter)
    lines = ["*EMA Snapshot*\n"]
    for asset in assets:
        emoji = ASSETS[asset]["emoji"]
        lines.append(f"\n{emoji} *{asset}*")
        for tf in EMA_TIMEFRAMES:
            candles = candle_cache.get((asset, tf))
            if not candles or len(candles) < 201:
                n = len(candles) if candles else 0
                lines.append(f"  {tf}: Waiting ({n}/200)")
                continue
            closes = [c["close"] for c in candles]
            price = closes[-1]
            ema50 = compute_ema(closes, 50)
            ema200 = compute_ema(closes, 200)
            if ema50 and ema200:
                e50, e200 = ema50[-1], ema200[-1]
                cross = "Golden" if e50 > e200 else "Death"
                pos = "Above" if price > e200 else "Below"
                lines.append(f"  {tf}: ${price:,.2f} ({pos} EMA200)")
                lines.append(f"    EMA50: ${e50:,.2f} | EMA200: ${e200:,.2f} | {cross}")
    return "\n".join(lines)


def format_macd(asset_filter=None):
    assets = _get_selected_assets(asset_filter)
    lines = ["*MACD Snapshot*\n"]
    for asset in assets:
        emoji = ASSETS[asset]["emoji"]
        lines.append(f"\n{emoji} *{asset}*")
        for tf in MACD_TIMEFRAMES:
            candles = candle_cache.get((asset, tf))
            if not candles or len(candles) < 36:
                lines.append(f"  {tf}: Waiting")
                continue
            closes = [c["close"] for c in candles]
            macd_line, signal_line, histogram = compute_macd(closes)
            if macd_line and signal_line and histogram:
                m, s, h = macd_line[-1], signal_line[-1], histogram[-1]
                trend = "Bullish" if h > 0 else "Bearish"
                lines.append(f"  {tf}: MACD {m:,.2f} | Signal {s:,.2f} | Hist {h:,.2f} ({trend})")
    return "\n".join(lines)


def format_bollinger(asset_filter=None):
    assets = _get_selected_assets(asset_filter)
    lines = ["*Bollinger Bands*\n"]
    for asset in assets:
        emoji = ASSETS[asset]["emoji"]
        lines.append(f"\n{emoji} *{asset}*")
        for tf in BOLLINGER_TIMEFRAMES:
            candles = candle_cache.get((asset, tf))
            if not candles or len(candles) < 21:
                lines.append(f"  {tf}: Waiting")
                continue
            closes = [c["close"] for c in candles]
            upper, mid, lower = compute_bollinger(closes)
            if upper is None:
                continue
            price = closes[-1]
            if price < lower:
                pos = "Below lower (Oversold)"
            elif price > upper:
                pos = "Above upper (Overbought)"
            else:
                pct = (price - lower) / (upper - lower) * 100
                pos = f"Within ({pct:.0f}%)"
            bw = (upper - lower) / mid * 100
            lines.append(f"  {tf}: ${price:,.2f} | {pos} | BW: {bw:.1f}%")
            lines.append(f"    Upper: ${upper:,.2f} | Mid: ${mid:,.2f} | Lower: ${lower:,.2f}")
    return "\n".join(lines)


def format_divergence(asset_filter=None):
    assets = _get_selected_assets(asset_filter)
    lines = ["*RSI Divergence*\n"]
    for asset in assets:
        emoji = ASSETS[asset]["emoji"]
        lines.append(f"\n{emoji} *{asset}*")
        for tf in DIVERGENCE_TIMEFRAMES:
            candles = candle_cache.get((asset, tf))
            if not candles or len(candles) < 30:
                lines.append(f"  {tf}: Waiting")
                continue
            closes = [c["close"] for c in candles]
            rsi_series = compute_rsi_series(closes)
            divs = detect_divergence(closes, rsi_series)
            if divs:
                for dtype, desc in divs[-3:]:
                    lines.append(f"  {tf}: {dtype.title()} \u2014 {desc}")
            else:
                lines.append(f"  {tf}: None")
    return "\n".join(lines)


def format_price(asset_filter=None):
    assets = _get_selected_assets(asset_filter)
    lines = ["*Price*\n"]
    for asset in assets:
        emoji = ASSETS[asset]["emoji"]
        price = _get_price(asset)
        if not price:
            lines.append(f"{emoji} {asset}: N/A")
            continue
        lines.append(f"\n{emoji} *{asset}* ${price:,.2f}")
        for tf in ["5m", "1h", "4h", "1d"]:
            c = candle_cache.get((asset, tf))
            if c and len(c) >= 2:
                chg = c[-1]["close"] - c[-2]["close"]
                pct = (chg / c[-2]["close"]) * 100
                lines.append(f"  {tf}: {pct:+.2f}%")
    return "\n".join(lines)


def format_volume(asset_filter=None):
    assets = _get_selected_assets(asset_filter)
    lines = ["*Volume*\n"]
    for asset in assets:
        emoji = ASSETS[asset]["emoji"]
        lines.append(f"\n{emoji} *{asset}*")
        for tf in VOLUME_TIMEFRAMES:
            candles = candle_cache.get((asset, tf))
            if not candles or len(candles) < 21:
                lines.append(f"  {tf}: Waiting")
                continue
            volumes = [c["volume"] for c in candles]
            cur_vol = volumes[-1]
            avg_vol = sum(volumes[-21:-1]) / 20
            if avg_vol == 0:
                lines.append(f"  {tf}: No data")
                continue
            ratio = cur_vol / avg_vol
            spike_thresh = ASSETS[asset].get("vol_spike", VOLUME_SPIKE_MULT)
            if ratio >= spike_thresh:
                lbl = "SPIKE"
            elif ratio >= 2.0:
                lbl = "Elevated"
            else:
                lbl = "Normal"
            lines.append(f"  {tf}: {cur_vol:,.0f} ({ratio:.1f}x avg) \u2014 {lbl}")
    return "\n".join(lines)


BUTTON_HANDLERS = {
    "rsi": format_rsi,
    "ema": format_ema,
    "macd": format_macd,
    "bollinger": format_bollinger,
    "divergence": format_divergence,
    "volume": format_volume,
    "price": format_price,
    "trend": format_trend,
}


async def button_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()

    data = query.data
    chat_id = str(query.message.chat_id)

    if data.startswith("sel_"):
        sel = data[4:].upper()
        if sel in ASSETS:
            user_selected_asset[chat_id] = sel
        selected = user_selected_asset.get(chat_id, ASSET_NAMES[0])
        await refresh_candles()
        update_all_trend_states()
        text = format_rsi(selected)
        await query.message.reply_text(text, parse_mode="Markdown", reply_markup=build_menu(selected))
        return

    asset_filter = user_selected_asset.get(chat_id, ASSET_NAMES[0])
    handler = BUTTON_HANDLERS.get(data)
    if handler:
        await refresh_candles()
        update_all_trend_states()
        text = handler(asset_filter)
    else:
        text = "Unknown command"

    selected = user_selected_asset.get(chat_id, ASSET_NAMES[0])
    await query.message.reply_text(text, parse_mode="Markdown", reply_markup=build_menu(selected))


# ==============================================================================
# POLLING LOOP
# ==============================================================================

async def refresh_candles():
    now = time.time()
    loop = asyncio.get_event_loop()
    tasks = {}
    for asset in ASSET_NAMES:
        for tf in ALL_TIMEFRAMES:
            key = (asset, tf)
            interval = TF_POLL_INTERVALS.get(tf, 30)
            last = last_fetch.get(key, 0)
            if now - last < interval and key in candle_cache:
                continue
            tasks[key] = loop.run_in_executor(None, partial(fetch_candles, asset, tf, 500))
    if not tasks:
        return
    keys = list(tasks.keys())
    results = await asyncio.gather(*tasks.values(), return_exceptions=True)
    fetched = 0
    for key, result in zip(keys, results):
        if isinstance(result, Exception):
            log.error(f"Fetch {key[0]}/{key[1]}: {result}")
        elif result:
            candle_cache[key] = result
            last_fetch[key] = now
            fetched += 1
    if fetched > 0:
        log.info(f"Refreshed {fetched}/{len(tasks)} candle sets")


async def polling_task(app):
    log.info("Polling loop started")
    while True:
        try:
            await refresh_candles()

            # Fetch funding rates (cached, only hits Binance every 5 min)
            try:
                await asyncio.get_event_loop().run_in_executor(None, fetch_funding_rates)
            except Exception as e:
                log.warning(f"Funding rate update failed: {e}")

            # Fetch Binance volume data (cached, refreshes every 60s)
            try:
                await asyncio.get_event_loop().run_in_executor(None, fetch_binance_volume)
            except Exception as e:
                log.warning(f"Binance volume update failed: {e}")

            # Update trend state every cycle
            update_all_trend_states()

            # Update market regime (fast overlay — detects waterfalls)
            update_all_regimes()

            # Update RSI history for velocity tracking
            for asset in ASSET_NAMES:
                rsi_5m = _get_rsi(asset, "5m")
                update_rsi_history(asset, "5m", rsi_5m)
                # v2.3: track 15m/30m RSI direction + 1D for signal context
                update_rsi_direction_history(asset, "15m")
                update_rsi_direction_history(asset, "30m")
                # Track 1D RSI in main rsi_history for direction arrow
                rsi_1d = _get_rsi(asset, "1d")
                update_rsi_history(asset, "1d", rsi_1d)

            alerts = []

            # Momentum persistence warnings
            for asset in ASSET_NAMES:
                warning = update_momentum_persistence(asset)
                if warning:
                    alerts.append(warning)

            alerts.extend(generate_5m_rsi_alerts())
            alerts.extend(generate_staged_alerts())
            # generate_other_alerts: per-TF RSI/EMA/divergence/volume — DISABLED (noise)
            # generate_swing_alerts: multi-indicator confluence on 1H/4H — DISABLED (noise)
            alerts.extend(generate_context_alerts())  # trend shifts only
            alerts.extend(generate_exit_signals())

            for msg in alerts:
                try:
                    await app.bot.send_message(chat_id=CHAT_ID, text=msg, parse_mode="Markdown")
                    log.info(f"Alert sent: {msg[:80]}...")
                except Exception as e:
                    log.error(f"Alert send failed: {e}")

        except Exception as e:
            log.error(f"Polling loop error: {e}")

        await asyncio.sleep(POLL_INTERVAL)


async def post_init(app):
    log.info("Bootstrapping candle data for all assets...")
    loop = asyncio.get_event_loop()
    tasks = {}
    for asset in ASSET_NAMES:
        for tf in ALL_TIMEFRAMES:
            tasks[(asset, tf)] = loop.run_in_executor(None, partial(fetch_candles, asset, tf, 500))
    keys = list(tasks.keys())
    results = await asyncio.gather(*tasks.values(), return_exceptions=True)
    now = time.time()
    for key, result in zip(keys, results):
        if isinstance(result, Exception):
            log.error(f"Bootstrap {key[0]}/{key[1]}: {result}")
        elif result:
            candle_cache[key] = result
            last_fetch[key] = now
    for asset in ASSET_NAMES:
        counts = []
        for tf in ALL_TIMEFRAMES:
            c = candle_cache.get((asset, tf))
            counts.append(f"{tf}={len(c)}" if c else f"{tf}=0")
        log.info(f"  {asset}: {', '.join(counts)}")

    # v2.3: Initialize direction tracking and exit state
    active_signals.clear()
    signal_history.clear()
    exit_alert_cooldowns.clear()
    for asset in ASSET_NAMES:
        rsi_history_15m[asset] = deque(maxlen=8)
        rsi_history_30m[asset] = deque(maxlen=8)
        rsi_15m_val = _get_rsi(asset, "15m")
        rsi_30m_val = _get_rsi(asset, "30m")
        if rsi_15m_val is not None:
            rsi_history_15m[asset].append(rsi_15m_val)
        if rsi_30m_val is not None:
            rsi_history_30m[asset].append(rsi_30m_val)

    # Initialize staged state and trend
    for asset in ASSET_NAMES:
        staged_state[asset] = "neutral"
        rsi_5m = _get_rsi(asset, "5m")
        if rsi_5m is not None:
            staged_5m_prev[asset] = rsi_5m
            update_rsi_history(asset, "5m", rsi_5m)
        rsi_5m_state[asset] = "neutral"
        rsi_5m_last_alert[asset] = 0
        momentum_above[asset] = 0
        momentum_below[asset] = 0
        momentum_warned[asset] = None
        # Context alert init
        context_flags[("approach_long", asset)] = False
        context_flags[("approach_short", asset)] = False
        context_flags[("exhaustion_ob", asset)] = False
        context_flags[("exhaustion_os", asset)] = False
        context_flags[("ema_pullback", asset)] = False
        context_flags[("bb_squeeze", asset)] = False
        context_flags[("mtf_extreme", asset)] = None
        context_flags[("rsi_1h_prev", asset)] = _get_rsi(asset, "1h")
        for tf in ["1h", "4h"]:
            context_flags[("div_context", asset, tf)] = None

    update_all_trend_states()

    # Bootstrap funding rates
    try:
        fetch_funding_rates()
        fetch_binance_volume()

        # Bootstrap regime detection
        for asset in ASSET_NAMES:
            market_regime[asset] = detect_market_regime(asset)
            bounce_state[asset] = "idle"
            bounce_rsi_low[asset] = 100
            log.info(f"  {asset}: regime={market_regime[asset]}")
        for asset in ASSET_NAMES:
            rate = get_funding_rate(asset)
            rate_str = f"{rate*100:+.4f}%" if rate is not None else "N/A"
            log.info(f"  {asset}: funding={rate_str}")
    except Exception as e:
        log.warning(f"Funding rate bootstrap failed: {e}")

    for asset in ASSET_NAMES:
        ts = trend_state.get(asset, "NEUTRAL")
        long_t, short_t = get_rsi_thresholds(asset)
        log.info(f"  {asset}: trend={ts} long_thresh={long_t} short_thresh={short_t}")

    # Pre-seed alert states to suppress bootstrap alerts
    generate_other_alerts()   # sets divergence/ema/volume states without sending
    generate_swing_alerts()   # sets swing states without sending
    generate_context_alerts() # sets context flags without sending
    log.info("Bootstrap alert states seeded (no alerts sent)")

    asyncio.create_task(polling_task(app))
    log.info("Background polling task launched")


def main():
    log.info("Starting LighterRSI Signal Bot v2.4 (regime+volume+format)...")
    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .post_init(post_init)
        .build()
    )
    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("status", cmd_status))
    app.add_handler(CallbackQueryHandler(button_callback))
    log.info("Bot running -- press Ctrl+C to stop")
    app.run_polling(drop_pending_updates=True)


if __name__ == "__main__":
    main()
