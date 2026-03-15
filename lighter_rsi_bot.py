#!/usr/bin/env python3
"""
LighterRSI Signal Bot — Staged RSI alerts for ETH/BTC/SOL on Lighter DEX.
Read-only (no orders). Pulls candles directly from Lighter's REST API.
"""

import asyncio
import os
import json
import logging
import math
import time
import urllib.request
from datetime import datetime, timezone
from functools import partial

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, ContextTypes

# --- Config -------------------------------------------------------------------

BOT_TOKEN = os.environ.get("TG_TOKEN", "")
CHAT_ID = os.environ.get("TG_CHAT", "")

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

# --- State --------------------------------------------------------------------

candle_cache = {}        # (asset, tf) -> [candle_dicts]
alert_state = {}         # (indicator, tf, asset) -> state_string
last_fetch = {}          # (asset, tf) -> timestamp

# Staged RSI state
staged_state = {}        # asset -> "neutral"/"approach_long"/"approach_short"/"triggered_long"/"triggered_short"
staged_5m_prev = {}      # asset -> previous 5M RSI value

# Standalone 5m RSI alerts (ETH only)
eth_5m_rsi_state = "neutral"     # "neutral" / "oversold" / "overbought"
eth_5m_rsi_last_alert = 0.0      # timestamp of last 5m RSI alert
ETH_5M_RSI_COOLDOWN = 300        # 5 min cooldown between 5m RSI alerts
ETH_5M_RSI_OB = 70               # overbought threshold
ETH_5M_RSI_OS = 30               # oversold threshold

# Swing state
last_swing_alert = {}    # asset -> timestamp

user_selected_asset = {} # chat_id -> "BTC"/"ETH"/"SOL"

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


def _get_4h_trend(asset):
    """Helper: 4H trend label from RSI."""
    rsi = _get_rsi(asset, "4h")
    if rsi is None:
        return "N/A"
    if rsi > 55:
        return "Bullish"
    if rsi < 45:
        return "Bearish"
    return "Neutral"


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
                bonuses.append(f"\U0001f525 Volume spike {tf} ({volumes[-1]/avg:.1f}x)")
                break

    # MACD crossover on 1H
    candles_1h = candle_cache.get((asset, "1h"))
    if candles_1h and len(candles_1h) >= 36:
        closes = [c["close"] for c in candles_1h]
        _, _, hist = compute_macd(closes)
        if hist and len(hist) >= 2:
            if direction == "long" and hist[-1] > 0 and hist[-2] <= 0:
                bonuses.append("\u2705 MACD bullish cross 1H")
            elif direction == "short" and hist[-1] < 0 and hist[-2] >= 0:
                bonuses.append("\u2705 MACD bearish cross 1H")

    # Bollinger band touch on 1H
    if candles_1h and len(candles_1h) >= 20:
        closes = [c["close"] for c in candles_1h]
        upper, mid, lower = compute_bollinger(closes)
        if upper is not None:
            price = closes[-1]
            if direction == "long" and price < lower:
                bonuses.append("\u2705 Below lower Bollinger 1H")
            elif direction == "short" and price > upper:
                bonuses.append("\u2705 Above upper Bollinger 1H")

    # RSI divergence on 15M
    candles_15m = candle_cache.get((asset, "15m"))
    if candles_15m and len(candles_15m) >= 30:
        closes = [c["close"] for c in candles_15m]
        rsi_series = compute_rsi_series(closes)
        divs = detect_divergence(closes, rsi_series)
        if divs:
            if direction == "long" and divs[-1][0] == "bullish":
                bonuses.append("\u2705 Bullish RSI divergence 15M")
            elif direction == "short" and divs[-1][0] == "bearish":
                bonuses.append("\u2705 Bearish RSI divergence 15M")

    return bonuses


# ==============================================================================
# STAGED RSI ALERTS (core feature)
# ==============================================================================

def generate_staged_alerts():
    """3-stage RSI alert system based on 15M trigger + 5M confirmation."""
    alerts = []

    for asset in ASSET_NAMES:
        cfg = ASSETS[asset]
        emoji = cfg["emoji"]
        rsi_os = cfg["rsi_os"]
        rsi_ob = cfg["rsi_ob"]
        approach_os = rsi_os + RSI_APPROACH_BUFFER  # e.g. 35 for ETH
        approach_ob = rsi_ob - RSI_APPROACH_BUFFER  # e.g. 65 for ETH
        priority = cfg["priority"]

        state = staged_state.get(asset, "neutral")

        # Get RSI values
        rsi_15m = _get_rsi(asset, "15m")
        rsi_5m = _get_rsi(asset, "5m")
        rsi_1h = _get_rsi(asset, "1h")
        price = _get_price(asset)
        trend_4h = _get_4h_trend(asset)
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

        # Stage 1: approaching oversold (silent — skip to stage 2)
        if state == "neutral" and approach_os >= rsi_15m > rsi_os:
            new_state = "approach_long"

        # Stage 2: 15M crosses below threshold
        elif state in ("neutral", "approach_long") and rsi_15m <= rsi_os:
            new_state = "triggered_long"
            rsi_5m_str = f"{rsi_5m:.1f}" if rsi_5m else "N/A"
            rsi_1h_str = f"{rsi_1h:.1f}" if rsi_1h else "N/A"
            bonuses = get_confluence_bonus(asset, "long")
            grade = "A" if len(bonuses) >= 2 else "B" if len(bonuses) == 1 else "C"
            lines = [
                f"\U0001f3af {emoji} {asset} OVERSOLD \u2014 Grade {grade}",
                f"15M RSI: {rsi_15m:.1f}",
                f"5M RSI: {rsi_5m_str} | 1H RSI: {rsi_1h_str}",
                f"4H Trend: {trend_4h}",
                f"${price:,.2f}",
            ]
            lines.extend(bonuses)
            if grade != "C":
                msg = "\n".join(lines)
            else:
                log.info(f"Suppressed Grade C: {asset} OVERSOLD 15M={rsi_15m:.1f}")

        # Stage 3: 5M confirms (was oversold, now turning up)
        elif state == "triggered_long" and rsi_5m is not None and prev_5m is not None:
            if prev_5m < (rsi_os + RSI_APPROACH_BUFFER) and rsi_5m > prev_5m + 2:
                new_state = "neutral"
                bonuses = get_confluence_bonus(asset, "long")
                grade = "A" if len(bonuses) >= 2 else "B" if len(bonuses) == 1 else "C"
                lines = [
                    f"\U0001f7e2 {emoji} {asset} LONG CONFIRMED \u2014 Grade {grade}",
                    f"5M RSI turned: {prev_5m:.0f}\u2192{rsi_5m:.0f}",
                    f"15M RSI: {rsi_15m:.1f} | ${price:,.2f}",
                ]
                lines.extend(bonuses)
                if grade != "C":
                    msg = "\n".join(lines)
                else:
                    log.info(f"Suppressed Grade C: {asset} LONG CONFIRMED 5M={rsi_5m:.1f}")

        # === SHORT SIDE ===

        # Stage 1: approaching overbought (silent — skip to stage 2)
        elif state == "neutral" and approach_ob <= rsi_15m < rsi_ob:
            new_state = "approach_short"

        # Stage 2: 15M crosses above threshold
        elif state in ("neutral", "approach_short") and rsi_15m >= rsi_ob:
            new_state = "triggered_short"
            rsi_5m_str = f"{rsi_5m:.1f}" if rsi_5m else "N/A"
            rsi_1h_str = f"{rsi_1h:.1f}" if rsi_1h else "N/A"
            bonuses = get_confluence_bonus(asset, "short")
            grade = "A" if len(bonuses) >= 2 else "B" if len(bonuses) == 1 else "C"
            lines = [
                f"\U0001f3af {emoji} {asset} OVERBOUGHT \u2014 Grade {grade}",
                f"15M RSI: {rsi_15m:.1f}",
                f"5M RSI: {rsi_5m_str} | 1H RSI: {rsi_1h_str}",
                f"4H Trend: {trend_4h}",
                f"${price:,.2f}",
            ]
            lines.extend(bonuses)
            if grade != "C":
                msg = "\n".join(lines)
            else:
                log.info(f"Suppressed Grade C: {asset} OVERBOUGHT 15M={rsi_15m:.1f}")

        # Stage 3: 5M confirms (was overbought, now turning down)
        elif state == "triggered_short" and rsi_5m is not None and prev_5m is not None:
            if prev_5m > (rsi_ob - RSI_APPROACH_BUFFER) and rsi_5m < prev_5m - 2:
                new_state = "neutral"
                bonuses = get_confluence_bonus(asset, "short")
                grade = "A" if len(bonuses) >= 2 else "B" if len(bonuses) == 1 else "C"
                lines = [
                    f"\U0001f534 {emoji} {asset} SHORT CONFIRMED \u2014 Grade {grade}",
                    f"5M RSI turned: {prev_5m:.0f}\u2192{rsi_5m:.0f}",
                    f"15M RSI: {rsi_15m:.1f} | ${price:,.2f}",
                ]
                lines.extend(bonuses)
                if grade != "C":
                    msg = "\n".join(lines)
                else:
                    log.info(f"Suppressed Grade C: {asset} SHORT CONFIRMED 5M={rsi_5m:.1f}")

        if new_state != state:
            staged_state[asset] = new_state
            r5 = f"{rsi_5m:.1f}" if rsi_5m else "N/A"
            log.info(f"Staged: {asset} {state} -> {new_state} | 15M={rsi_15m:.1f} 5M={r5}")

        if msg:
            alerts.append(msg)

    return alerts


# ==============================================================================
# STANDALONE 5M RSI ALERTS (ETH only)
# ==============================================================================

def generate_eth_5m_rsi_alerts():
    """Fire alerts when ETH 5m RSI crosses 30 (oversold) or 70 (overbought)."""
    global eth_5m_rsi_state, eth_5m_rsi_last_alert
    alerts = []

    rsi_5m = _get_rsi("ETH", "5m")
    price = _get_price("ETH")
    if rsi_5m is None or price is None:
        return alerts

    now = time.time()
    emoji = ASSETS["ETH"]["emoji"]

    # Oversold: RSI crosses below 30
    if rsi_5m <= ETH_5M_RSI_OS and eth_5m_rsi_state != "oversold":
        if now - eth_5m_rsi_last_alert >= ETH_5M_RSI_COOLDOWN:
            eth_5m_rsi_state = "oversold"
            eth_5m_rsi_last_alert = now
            alerts.append(
                f"\U0001f7e2 {emoji} ETH 5m RSI OVERSOLD\n"
                f"RSI: {rsi_5m:.1f} | ${price:,.2f}"
            )
            log.info(f"ETH 5m RSI oversold: {rsi_5m:.1f}")

    # Overbought: RSI crosses above 70
    elif rsi_5m >= ETH_5M_RSI_OB and eth_5m_rsi_state != "overbought":
        if now - eth_5m_rsi_last_alert >= ETH_5M_RSI_COOLDOWN:
            eth_5m_rsi_state = "overbought"
            eth_5m_rsi_last_alert = now
            alerts.append(
                f"\U0001f534 {emoji} ETH 5m RSI OVERBOUGHT\n"
                f"RSI: {rsi_5m:.1f} | ${price:,.2f}"
            )
            log.info(f"ETH 5m RSI overbought: {rsi_5m:.1f}")

    # Reset when RSI returns to neutral zone (40-60)
    elif 40 < rsi_5m < 60:
        eth_5m_rsi_state = "neutral"

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

        # -- Divergence --------------------------------------------------------
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
                if new == "bullish":
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

        # -- Volume Spike ------------------------------------------------------
        spike_thresh = ASSETS[asset].get("vol_spike", VOLUME_SPIKE_MULT)
        for tf in VOLUME_TIMEFRAMES:
            candles = candle_cache.get((asset, tf))
            if not candles or len(candles) < 21:
                continue
            volumes = [c["volume"] for c in candles]
            cur_vol = volumes[-1]
            avg_vol = sum(volumes[-21:-1]) / 20
            if avg_vol == 0:
                continue
            ratio = cur_vol / avg_vol
            if ratio >= spike_thresh:
                new = "spike"
                c_last = candles[-1]
                price = c_last["close"]
                qvol = c_last.get("quote_volume", cur_vol * price)
                if qvol >= 1_000_000:
                    vol_str = f"${qvol / 1_000_000:.1f}M"
                elif qvol >= 1_000:
                    vol_str = f"${qvol / 1_000:.0f}K"
                else:
                    vol_str = f"${qvol:,.0f}"
                direction = "Buy" if c_last["close"] >= c_last["open"] else "Sell"
                msg = check_and_alert("volume", tf, asset, new,
                    f"{emoji} {asset} {tf} \u2014 Volume Spike\n"
                    f"{direction} | {vol_str} ({ratio:.1f}x avg)\n"
                    f"${price:,.2f}")
                if msg:
                    alerts.append(msg)
            else:
                alert_state[("volume", tf, asset)] = "normal"

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
# TELEGRAM UI
# ==============================================================================

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
        [InlineKeyboardButton("Price", callback_data="price")],
    ])


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "*LighterRSI Signal Bot*\n\n"
        "Staged RSI alerts for ETH/BTC/SOL on Lighter DEX.\n\n"
        "Choose an asset or indicator:",
        parse_mode="Markdown",
        reply_markup=build_menu(),
    )


async def cmd_status(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await refresh_candles()
    text = format_status()
    await update.message.reply_text(text, parse_mode="Markdown", reply_markup=build_menu())


# -- Formatters ----------------------------------------------------------------

def _get_selected_assets(asset_filter):
    if asset_filter and asset_filter in ASSETS:
        return [asset_filter]
    return ASSET_NAMES


def format_status():
    """Compact 3-asset dashboard."""
    lines = []
    for asset in ASSET_NAMES:
        cfg = ASSETS[asset]
        emoji = cfg["emoji"]
        price = _get_price(asset)
        price_str = f"${price:,.2f}" if price else "N/A"
        rsi_5m = _get_rsi(asset, "5m")
        rsi_15m = _get_rsi(asset, "15m")
        rsi_1h = _get_rsi(asset, "1h")
        trend_4h = _get_4h_trend(asset)

        r5 = f"{rsi_5m:.0f}" if rsi_5m else "--"
        r15 = f"{rsi_15m:.0f}" if rsi_15m else "--"
        r1h = f"{rsi_1h:.0f}" if rsi_1h else "--"

        state = staged_state.get(asset, "neutral")
        state_str = ""
        if state != "neutral":
            state_str = f" | {state.replace('_', ' ').upper()}"

        lines.append(f"{emoji} {asset}: {price_str} | 5M: {r5} | 15M: {r15} | 1H: {r1h} | 4H: {trend_4h}{state_str}")
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
        text = format_rsi(selected)
        await query.message.reply_text(text, parse_mode="Markdown", reply_markup=build_menu(selected))
        return

    asset_filter = user_selected_asset.get(chat_id, ASSET_NAMES[0])
    handler = BUTTON_HANDLERS.get(data)
    if handler:
        await refresh_candles()
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

            alerts = []
            alerts.extend(generate_eth_5m_rsi_alerts())
            alerts.extend(generate_staged_alerts())
            alerts.extend(generate_other_alerts())
            alerts.extend(generate_swing_alerts())

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

    # Initialize staged state
    for asset in ASSET_NAMES:
        staged_state[asset] = "neutral"
        rsi_5m = _get_rsi(asset, "5m")
        if rsi_5m is not None:
            staged_5m_prev[asset] = rsi_5m

    asyncio.create_task(polling_task(app))
    log.info("Background polling task launched")


def main():
    log.info("Starting LighterRSI Signal Bot...")
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
