#!/usr/bin/env python3
"""
LighterRSI Signal Bot — BTC-PERP alerts with confluence grading.

Signal System:
  4H  RSI → trend filter (bullish >55 / bearish <45 / ranging 45-55)
  15m RSI → setup zone (oversold <25 / overbought >75)
  5m/1m RSI → crossback triggers (exit from extreme = signal)
  5m Volume → spike (>2x avg) as confluence condition

Grading: A = 3/3 confluence, B = 2/3, C = 1/3 (suppressed)
Cooldown: 15 min per direction after alert fires.
Target: 3-5 high quality alerts per session.
"""

import asyncio
import json
import logging
import math
import os
import time
import urllib.request
from datetime import datetime, timezone
from functools import partial

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.ext import Application, CommandHandler, CallbackQueryHandler, ContextTypes

# ─── Config ───────────────────────────────────────────────────────────────────

BOT_TOKEN = os.environ.get("TG_TOKEN", "")
CHAT_ID = "5583279698"

LIGHTER_URL = "https://mainnet.zklighter.elliot.ai/api/v1/candles"
MARKET_ID = 1  # BTC-PERP

# Timeframes per indicator (for snapshots)
RSI_TIMEFRAMES = ["1m", "5m", "15m", "1h", "4h", "1d", "1w"]
EMA_TIMEFRAMES = ["4h"]
MACD_TIMEFRAMES = ["1h", "4h"]
BOLLINGER_TIMEFRAMES = ["1h", "4h"]
DIVERGENCE_TIMEFRAMES = ["15m", "1h", "4h"]
VOLUME_TIMEFRAMES = ["5m", "15m", "1h"]
VOLUME_SPIKE_MULT = 2.0   # volume > 2x average = spike

TF_ORDER = ["1m", "5m", "15m", "1h", "4h", "1d", "1w"]
ALL_TIMEFRAMES = sorted(
    set(RSI_TIMEFRAMES + EMA_TIMEFRAMES + MACD_TIMEFRAMES
        + BOLLINGER_TIMEFRAMES + DIVERGENCE_TIMEFRAMES + VOLUME_TIMEFRAMES),
    key=lambda t: TF_ORDER.index(t),
)

# Seconds per candle for each resolution
TF_SECONDS = {
    "1m": 60, "5m": 300, "15m": 900, "1h": 3600,
    "4h": 14400, "1d": 86400, "1w": 604800,
}

RSI_OVERSOLD = 30
RSI_OVERBOUGHT = 70

POLL_INTERVAL = 30        # seconds between polling cycles

RSI_TRIGGER_PERIOD = 7    # scalping period for 5m/1m crossback triggers

# Signal system
SIGNAL_COOLDOWN = 900     # 15 min between alerts in same direction

# ─── State ────────────────────────────────────────────────────────────────────

alert_state = {}       # (indicator, timeframe) → state string (EMA/divergence only)
candle_cache = {}      # timeframe → list of closed candle dicts

# Signal system state
prev_rsi = {}              # tf → previous RSI for crossback detection
signal_cooldown = {}       # "long"|"short" → unix timestamp of last alert
vol_rsi_state = None       # "long"|"short"|None — volume+RSI state machine

# ─── Logging ──────────────────────────────────────────────────────────────────

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[
        logging.FileHandler("rsi_bot.log"),
        logging.StreamHandler(),
    ],
)
log = logging.getLogger("LighterRSI")

# ─── Candle Fetcher ───────────────────────────────────────────────────────────

def fetch_candles(resolution, count=500):
    """Fetch closed candles from Lighter REST API. Returns list of OHLCV dicts or None."""
    now = int(time.time())
    secs = TF_SECONDS.get(resolution, 3600)
    start = now - (count + 5) * secs  # slight over-fetch to guarantee enough closed

    url = (
        f"{LIGHTER_URL}?market_id={MARKET_ID}&resolution={resolution}"
        f"&start_timestamp={start}&end_timestamp={now}&count_back={count + 5}"
    )
    try:
        resp = json.loads(urllib.request.urlopen(url, timeout=15).read().decode())
        if resp.get("code") != 200 or "c" not in resp:
            log.warning(f"Candle API error {resolution}: {resp}")
            return None

        raw = resp["c"]
        if not raw:
            return None

        candles = []
        for c in raw:
            candles.append({
                "time": c["t"] / 1000.0,   # API returns ms → store seconds
                "open": float(c["o"]),
                "high": float(c["h"]),
                "low": float(c["l"]),
                "close": float(c["c"]),
                "volume": float(c.get("v", 0)),
                "quote_volume": float(c.get("V", 0)),
            })

        return candles

    except Exception as e:
        log.error(f"fetch_candles({resolution}) failed: {e}")
        return None


# ═══════════════════════════════════════════════════════════════════════════════
# INDICATOR FUNCTIONS — all operate on plain lists of floats (closes)
# ═══════════════════════════════════════════════════════════════════════════════

def compute_rsi(closes, period=14):
    """RSI with Wilder's smoothing — matches TradingView."""
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
    rs = avg_gain / avg_loss
    return 100 - (100 / (1 + rs))


def compute_rsi_series(closes, period=14):
    """Full RSI series (one value per close after warmup) for divergence detection."""
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
    """Exponential Moving Average. Returns list (shorter than input by period-1)."""
    if len(values) < period:
        return []
    k = 2.0 / (period + 1)
    ema = [sum(values[:period]) / period]          # SMA seed
    for v in values[period:]:
        ema.append(v * k + ema[-1] * (1 - k))
    return ema


def compute_macd(closes, fast=12, slow=26, signal_period=9):
    """Returns (macd_line, signal_line, histogram) or (None, None, None)."""
    if len(closes) < slow + signal_period:
        return None, None, None

    ema_fast = compute_ema(closes, fast)
    ema_slow = compute_ema(closes, slow)

    # Align: ema_fast is longer than ema_slow
    offset = len(ema_fast) - len(ema_slow)
    macd_line = [ema_fast[offset + i] - ema_slow[i] for i in range(len(ema_slow))]

    if len(macd_line) < signal_period:
        return None, None, None

    signal_line = compute_ema(macd_line, signal_period)
    offset2 = len(macd_line) - len(signal_line)
    histogram = [macd_line[offset2 + i] - signal_line[i] for i in range(len(signal_line))]

    return macd_line, signal_line, histogram


def compute_bollinger(closes, period=20, num_std=2):
    """Returns (upper, middle, lower) for the most recent bar, or (None, None, None)."""
    if len(closes) < period:
        return None, None, None
    window = closes[-period:]
    mid = sum(window) / period
    variance = sum((c - mid) ** 2 for c in window) / period
    std = math.sqrt(variance)
    return mid + num_std * std, mid, mid - num_std * std


def detect_divergence(closes, rsi_values, lookback=20):
    """Detect bullish/bearish RSI divergences in the last `lookback` bars."""
    if len(closes) < lookback or len(rsi_values) < lookback:
        return []

    # Align to same length, then take last `lookback`
    min_len = min(len(closes), len(rsi_values))
    c = closes[-min_len:][-lookback:]
    r = rsi_values[-min_len:][-lookback:]
    divergences = []

    # Find swing lows (bullish divergence: price lower low, RSI higher low)
    lows_idx = []
    for i in range(2, lookback - 2):
        if c[i] <= min(c[i - 2], c[i - 1]) and c[i] <= min(c[i + 1], c[i + 2]):
            lows_idx.append(i)
    for k in range(1, len(lows_idx)):
        j, i = lows_idx[k - 1], lows_idx[k]
        if c[i] < c[j] and r[i] > r[j]:
            divergences.append(("bullish", "Price lower low + RSI higher low"))

    # Find swing highs (bearish divergence: price higher high, RSI lower high)
    highs_idx = []
    for i in range(2, lookback - 2):
        if c[i] >= max(c[i - 2], c[i - 1]) and c[i] >= max(c[i + 1], c[i + 2]):
            highs_idx.append(i)
    for k in range(1, len(highs_idx)):
        j, i = highs_idx[k - 1], highs_idx[k]
        if c[i] > c[j] and r[i] < r[j]:
            divergences.append(("bearish", "Price higher high + RSI lower high"))

    return divergences


# ═══════════════════════════════════════════════════════════════════════════════
# ALERT STATE MACHINE (for EMA cross and divergence alerts only)
# ═══════════════════════════════════════════════════════════════════════════════

def check_and_alert(indicator, timeframe, new_state, message):
    """Return message only on state change. Otherwise None."""
    key = (indicator, timeframe)
    old_state = alert_state.get(key)

    if new_state == old_state:
        return None

    alert_state[key] = new_state
    return message


# ═══════════════════════════════════════════════════════════════════════════════
# SIGNAL SYSTEM — confluence-graded crossback alerts
# ═══════════════════════════════════════════════════════════════════════════════

def generate_alerts():
    """Scan all indicators, return list of alert strings."""
    global vol_rsi_state
    alerts = []

    # ── 1. Compute 4H trend bias ───────────────────────────────────────
    trend_bias = None  # "bullish" | "bearish" | "ranging"
    rsi_4h = None
    candles_4h = candle_cache.get("4h")
    if candles_4h and len(candles_4h) >= 16:
        rsi_4h = compute_rsi([c["close"] for c in candles_4h])
        if rsi_4h is not None:
            if rsi_4h > 50:
                trend_bias = "bullish"
            elif rsi_4h < 50:
                trend_bias = "bearish"
            else:
                trend_bias = "ranging"

    # ── 2. Check 15M setup zone ────────────────────────────────────────
    setup_15m = None  # "long" | "short" | None
    rsi_15m = None
    candles_15m = candle_cache.get("15m")
    if candles_15m and len(candles_15m) >= 16:
        rsi_15m = compute_rsi([c["close"] for c in candles_15m])
        if rsi_15m is not None:
            if rsi_15m < RSI_OVERSOLD:
                setup_15m = "long"
            elif rsi_15m > RSI_OVERBOUGHT:
                setup_15m = "short"

    # ── 3. Check 5M volume spike ───────────────────────────────────────
    volume_spike = False
    vol_ratio = 0.0
    candles_5m = candle_cache.get("5m")
    rsi_5m = None
    if candles_5m and len(candles_5m) >= 21:
        volumes = [c["volume"] for c in candles_5m]
        avg_vol = sum(volumes[-21:-1]) / 20
        if avg_vol > 0:
            vol_ratio = volumes[-1] / avg_vol
            volume_spike = vol_ratio >= VOLUME_SPIKE_MULT
    if candles_5m and len(candles_5m) >= 16:
        rsi_5m = compute_rsi([c["close"] for c in candles_5m], RSI_TRIGGER_PERIOD)

    # ── 4. Crossback detection on 5M and 1M ────────────────────────────
    for tf in ["5m", "1m"]:
        candles = candle_cache.get(tf)
        if not candles or len(candles) < 16:
            continue
        closes = [c["close"] for c in candles]
        rsi = compute_rsi(closes, RSI_TRIGGER_PERIOD)
        if rsi is None:
            continue

        price = closes[-1]
        prev = prev_rsi.get(tf)
        prev_rsi[tf] = rsi

        if prev is None:
            continue

        # Crossback: RSI exits extreme zone
        crossback_dir = None
        if prev >= RSI_OVERBOUGHT and rsi < RSI_OVERBOUGHT:
            crossback_dir = "short"
        elif prev <= RSI_OVERSOLD and rsi > RSI_OVERSOLD:
            crossback_dir = "long"

        if not crossback_dir:
            continue

        # Trend filter
        if trend_bias == "bullish" and crossback_dir == "short":
            log.info(f"Crossback {crossback_dir} on {tf} suppressed (bullish trend)")
            continue
        if trend_bias == "bearish" and crossback_dir == "long":
            log.info(f"Crossback {crossback_dir} on {tf} suppressed (bearish trend)")
            continue

        # Cooldown
        now = time.time()
        if now - signal_cooldown.get(crossback_dir, 0) < SIGNAL_COOLDOWN:
            log.info(f"Crossback {crossback_dir} on {tf} suppressed (cooldown)")
            continue

        # Count confluence conditions
        conditions = 0
        details = []

        # C1: 4H RSI confirms direction
        c1 = False
        if crossback_dir == "long" and rsi_4h is not None and rsi_4h > 50:
            c1 = True
        elif crossback_dir == "short" and rsi_4h is not None and rsi_4h < 50:
            c1 = True
        if c1:
            conditions += 1
        if rsi_4h is not None:
            bias_label = "bullish" if rsi_4h > 50 else "bearish" if rsi_4h < 50 else "ranging"
            details.append(f"4H RSI: {rsi_4h:.1f} ({bias_label} {'✓' if c1 else '✗'})")

        # C2: 15M RSI in extreme zone
        c2 = False
        if crossback_dir == "long" and setup_15m == "long":
            c2 = True
        elif crossback_dir == "short" and setup_15m == "short":
            c2 = True
        if c2:
            conditions += 1
        if rsi_15m is not None:
            zone = "oversold" if rsi_15m < RSI_OVERSOLD else "overbought" if rsi_15m > RSI_OVERBOUGHT else "neutral"
            details.append(f"15m RSI: {rsi_15m:.1f} ({zone} {'✓' if c2 else '✗'})")

        # C3: 5M volume spike
        c3 = volume_spike
        if c3:
            conditions += 1
        details.append(f"5m Vol: {vol_ratio:.1f}x avg ({'spike ✓' if c3 else '✗'})")

        # Require minimum 2/3 confluence
        if conditions < 2:
            log.info(f"Crossback {crossback_dir} on {tf} suppressed ({conditions}/3 confluence)")
            continue

        grade = "A" if conditions == 3 else "B"
        signal_cooldown[crossback_dir] = now

        emoji = "🟢" if crossback_dir == "long" else "🔴"
        direction = "LONG" if crossback_dir == "long" else "SHORT"
        range_tag = " (RANGE)" if trend_bias == "ranging" else ""

        lines = [
            f"{emoji} {direction} Signal [Grade {grade}]{range_tag}",
            f"BTC: ${price:,.2f}",
            "",
            f"Trigger: {tf} RSI {prev:.1f} → {rsi:.1f} (crossback ✓)",
        ]
        lines.extend(details)
        if grade == "A":
            lines.append("\nGrade: A — Full confluence")
        else:
            lines.append("\nGrade: B — 2/3 confluence")

        alerts.append("\n".join(lines))
        log.info(f"SIGNAL: Grade {grade} {direction} on {tf} RSI={rsi:.1f}")

    # ── 5. Volume spike + RSI extreme on 5M (A-grade trigger) ──────────
    new_vol_rsi = None
    if volume_spike and rsi_5m is not None:
        if rsi_5m < RSI_OVERSOLD:
            new_vol_rsi = "long"
        elif rsi_5m > RSI_OVERBOUGHT:
            new_vol_rsi = "short"

    if new_vol_rsi and new_vol_rsi != vol_rsi_state:
        suppress = False
        # Trend filter
        if trend_bias == "bullish" and new_vol_rsi == "short":
            suppress = True
        if trend_bias == "bearish" and new_vol_rsi == "long":
            suppress = True
        # Cooldown
        now = time.time()
        if now - signal_cooldown.get(new_vol_rsi, 0) < SIGNAL_COOLDOWN:
            suppress = True

        if not suppress:
            signal_cooldown[new_vol_rsi] = now
            price = candles_5m[-1]["close"]
            emoji = "🟢" if new_vol_rsi == "long" else "🔴"
            direction = "LONG" if new_vol_rsi == "long" else "SHORT"
            rsi_label = "oversold" if new_vol_rsi == "long" else "overbought"
            range_tag = " (RANGE)" if trend_bias == "ranging" else ""

            lines = [
                f"{emoji} {direction} Signal [Grade A]{range_tag}",
                f"BTC: ${price:,.2f}",
                "",
                f"5m RSI: {rsi_5m:.1f} ({rsi_label})",
                f"5m Vol: {vol_ratio:.1f}x avg (spike)",
            ]
            if rsi_4h is not None:
                lines.append(f"4H RSI: {rsi_4h:.1f} ({trend_bias})")
            lines.append("\nGrade: A — Volume spike + RSI extreme")

            alerts.append("\n".join(lines))
            log.info(f"SIGNAL: Grade A Vol+RSI {direction} 5m RSI={rsi_5m:.1f} vol={vol_ratio:.1f}x")

    vol_rsi_state = new_vol_rsi

    # ── EMA Cross (kept — rare, high-value) ────────────────────────────
    for tf in EMA_TIMEFRAMES:
        candles = candle_cache.get(tf)
        if not candles or len(candles) < 201:
            continue
        closes = [c["close"] for c in candles]

        ema200 = compute_ema(closes, 200)
        ema50 = compute_ema(closes, 50)

        if ema50 and ema200:
            e50 = ema50[-1]
            e200 = ema200[-1]
            new = "golden" if e50 > e200 else "death"
            old = alert_state.get(("ema_cross", tf))
            if old and old != new:
                if new == "golden":
                    msg = check_and_alert("ema_cross", tf, new,
                        "🟡 Golden Cross — {}\n"
                        "EMA50 ${:,.2f} > EMA200 ${:,.2f}\n\n"
                        "⚡ Bullish signal".format(tf, e50, e200))
                else:
                    msg = check_and_alert("ema_cross", tf, new,
                        "💀 Death Cross — {}\n"
                        "EMA50 ${:,.2f} < EMA200 ${:,.2f}\n\n"
                        "⚡ Bearish signal".format(tf, e50, e200))
                if msg:
                    alerts.append(msg)
            else:
                alert_state[("ema_cross", tf)] = new

    # ── Divergence (kept — useful context) ─────────────────────────────
    for tf in DIVERGENCE_TIMEFRAMES:
        candles = candle_cache.get(tf)
        if not candles or len(candles) < 30:
            continue
        closes = [c["close"] for c in candles]
        rsi_series = compute_rsi_series(closes)
        divs = detect_divergence(closes, rsi_series)

        new = divs[-1][0] if divs else "none"
        old = alert_state.get(("divergence", tf))
        if old and old != new and new != "none":
            desc = divs[-1][1]
            if new == "bullish":
                msg = check_and_alert("divergence", tf, new,
                    "🟢 Bullish RSI Divergence — {}\n"
                    "{}\n\n⚡ Potential reversal up".format(tf, desc))
            else:
                msg = check_and_alert("divergence", tf, new,
                    "🔴 Bearish RSI Divergence — {}\n"
                    "{}\n\n⚡ Potential reversal down".format(tf, desc))
            if msg:
                alerts.append(msg)
        else:
            alert_state[("divergence", tf)] = new

    return alerts


# ═══════════════════════════════════════════════════════════════════════════════
# TELEGRAM — INLINE KEYBOARD & CALLBACK HANDLERS
# ═══════════════════════════════════════════════════════════════════════════════

def build_menu():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📊 RSI", callback_data="rsi"),
         InlineKeyboardButton("📈 EMA", callback_data="ema")],
        [InlineKeyboardButton("📉 MACD", callback_data="macd"),
         InlineKeyboardButton("🔔 Bollinger", callback_data="bollinger")],
        [InlineKeyboardButton("🔀 Divergence", callback_data="divergence"),
         InlineKeyboardButton("💥 Volume", callback_data="volume")],
        [InlineKeyboardButton("📋 Full Analysis", callback_data="full"),
         InlineKeyboardButton("📅 Daily Report", callback_data="daily")],
        [InlineKeyboardButton("💰 Price", callback_data="price")],
    ])


async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    await update.message.reply_text(
        "🤖 *LighterRSI Signal Bot*\n\n"
        "BTC-PERP confluence-graded alerts on Lighter DEX.\n\n"
        "Signal system: 4H(bias) → 15m(setup) → 5m/1m(trigger)\n"
        "Grades: A (full) | B (2/3) | C (suppressed)\n"
        "Thresholds: RSI <30 oversold | >70 overbought\n\n"
        "Choose an indicator:",
        parse_mode="Markdown",
        reply_markup=build_menu(),
    )


# ── Snapshot Formatters ───────────────────────────────────────────────────────

def _rsi_label(rsi):
    if rsi < RSI_OVERSOLD:
        return "🟢", "OVERSOLD"
    if rsi > RSI_OVERBOUGHT:
        return "🔴", "OVERBOUGHT"
    return "⚪", "Neutral"


def format_rsi():
    lines = ["📊 *RSI Snapshot* — BTC-PERP\n"]
    for tf in RSI_TIMEFRAMES:
        candles = candle_cache.get(tf)
        if not candles or len(candles) < 16:
            lines.append(f"  {tf}: —")
            continue
        closes = [c["close"] for c in candles]
        rsi_period = RSI_TRIGGER_PERIOD if tf in ("5m", "1m") else 14
        rsi = compute_rsi(closes, rsi_period)
        if rsi is None:
            lines.append(f"  {tf}: —")
        else:
            em, lbl = _rsi_label(rsi)
            # Show role context for signal-relevant TFs
            if tf == "4h":
                bias = "bullish" if rsi > 50 else "bearish" if rsi < 50 else "ranging"
                lines.append(f"  {tf}: {em} {rsi:.1f} (Bias: {bias})")
            elif tf == "15m":
                if rsi < RSI_OVERSOLD:
                    lines.append(f"  {tf}: {em} {rsi:.1f} (Setup: oversold)")
                elif rsi > RSI_OVERBOUGHT:
                    lines.append(f"  {tf}: {em} {rsi:.1f} (Setup: overbought)")
                else:
                    lines.append(f"  {tf}: {em} {rsi:.1f} (Setup: watching)")
            elif tf in ("5m", "1m"):
                lines.append(f"  {tf}: {em} {rsi:.1f} (Trigger: {lbl.lower()})")
            else:
                lines.append(f"  {tf}: {em} {rsi:.1f} ({lbl})")
    lines.append(f"\nThresholds: <{RSI_OVERSOLD} oversold | >{RSI_OVERBOUGHT} overbought")
    return "\n".join(lines)


def format_ema():
    lines = ["📈 *EMA Snapshot* — BTC-PERP\n"]
    for tf in EMA_TIMEFRAMES:
        candles = candle_cache.get(tf)
        if not candles or len(candles) < 201:
            lines.append(f"  {tf}: Waiting for data ({len(candles) if candles else 0}/200 candles)")
            continue
        closes = [c["close"] for c in candles]
        price = closes[-1]
        ema50 = compute_ema(closes, 50)
        ema200 = compute_ema(closes, 200)
        if ema50 and ema200:
            e50, e200 = ema50[-1], ema200[-1]
            cross = "🟡 Golden" if e50 > e200 else "💀 Death"
            pos = "🟢 Above" if price > e200 else "🔴 Below"
            lines.append(f"  {tf}:")
            lines.append(f"    Price: ${price:,.2f} ({pos} EMA200)")
            lines.append(f"    EMA50:  ${e50:,.2f}")
            lines.append(f"    EMA200: ${e200:,.2f}")
            lines.append(f"    Cross:  {cross}")
    return "\n".join(lines)


def format_macd():
    lines = ["📉 *MACD Snapshot* — BTC-PERP\n"]
    for tf in MACD_TIMEFRAMES:
        candles = candle_cache.get(tf)
        if not candles or len(candles) < 36:
            lines.append(f"  {tf}: Waiting for data")
            continue
        closes = [c["close"] for c in candles]
        macd_line, signal_line, histogram = compute_macd(closes)
        if macd_line and signal_line and histogram:
            m, s, h = macd_line[-1], signal_line[-1], histogram[-1]
            trend = "🟢 Bullish" if h > 0 else "🔴 Bearish"
            lines.append(f"  {tf}:")
            lines.append(f"    MACD:      {m:,.2f}")
            lines.append(f"    Signal:    {s:,.2f}")
            lines.append(f"    Histogram: {h:,.2f} ({trend})")
    return "\n".join(lines)


def format_bollinger():
    lines = ["🔔 *Bollinger Bands* — BTC-PERP\n"]
    for tf in BOLLINGER_TIMEFRAMES:
        candles = candle_cache.get(tf)
        if not candles or len(candles) < 21:
            lines.append(f"  {tf}: Waiting for data")
            continue
        closes = [c["close"] for c in candles]
        upper, mid, lower = compute_bollinger(closes)
        if upper is None:
            continue
        price = closes[-1]
        if price < lower:
            pos = "🟢 Below lower band (Oversold)"
        elif price > upper:
            pos = "🔴 Above upper band (Overbought)"
        else:
            pct = (price - lower) / (upper - lower) * 100
            pos = f"⚪ Within bands ({pct:.0f}%)"
        bw = (upper - lower) / mid * 100
        lines.append(f"  {tf}:")
        lines.append(f"    Price: ${price:,.2f}")
        lines.append(f"    Upper: ${upper:,.2f}")
        lines.append(f"    Mid:   ${mid:,.2f}")
        lines.append(f"    Lower: ${lower:,.2f}")
        lines.append(f"    {pos}")
        lines.append(f"    Bandwidth: {bw:.1f}%")
    return "\n".join(lines)


def format_divergence():
    lines = ["🔀 *RSI Divergence* — BTC-PERP\n"]
    for tf in DIVERGENCE_TIMEFRAMES:
        candles = candle_cache.get(tf)
        if not candles or len(candles) < 30:
            lines.append(f"  {tf}: Waiting for data")
            continue
        closes = [c["close"] for c in candles]
        rsi_series = compute_rsi_series(closes)
        divs = detect_divergence(closes, rsi_series)
        if divs:
            for dtype, desc in divs[-3:]:
                em = "🟢" if dtype == "bullish" else "🔴"
                lines.append(f"  {tf}: {em} {dtype.title()} — {desc}")
        else:
            lines.append(f"  {tf}: No divergence detected")
    return "\n".join(lines)


def format_price():
    candles = None
    for tf in TF_ORDER:
        if tf in candle_cache and candle_cache[tf]:
            candles = candle_cache[tf]
            break
    if not candles:
        return "💰 Price data unavailable"

    price = candles[-1]["close"]
    lines = [f"💰 *BTC-PERP Price*\n", f"  Current: ${price:,.2f}\n"]
    for tf in ["5m", "1h", "4h", "1d"]:
        c = candle_cache.get(tf)
        if c and len(c) >= 2:
            chg = c[-1]["close"] - c[-2]["close"]
            pct = (chg / c[-2]["close"]) * 100
            em = "🟢" if chg >= 0 else "🔴"
            lines.append(f"  {tf} change: {em} {pct:+.2f}%")
    return "\n".join(lines)


def format_volume():
    lines = ["💥 *Volume Snapshot* — BTC-PERP\n"]
    for tf in VOLUME_TIMEFRAMES:
        candles = candle_cache.get(tf)
        if not candles or len(candles) < 21:
            lines.append(f"  {tf}: Waiting for data")
            continue
        volumes = [c["volume"] for c in candles]
        cur_vol = volumes[-1]
        avg_vol = sum(volumes[-21:-1]) / 20
        if avg_vol == 0:
            lines.append(f"  {tf}: No volume data")
            continue
        ratio = cur_vol / avg_vol
        if ratio >= VOLUME_SPIKE_MULT:
            em = "💥"
            lbl = "SPIKE"
        elif ratio >= 1.5:
            em = "🟡"
            lbl = "Elevated"
        else:
            em = "⚪"
            lbl = "Normal"
        lines.append(f"  {tf}: {em} {cur_vol:,.0f} ({ratio:.1f}x avg) — {lbl}")
    return "\n".join(lines)


def format_full():
    return "\n\n".join([
        format_price(), format_rsi(), format_ema(),
        format_macd(), format_bollinger(), format_divergence(), format_volume(),
    ])


def format_daily():
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
    return f"📅 *Daily Report* — {ts}\n\n{format_full()}"


BUTTON_HANDLERS = {
    "rsi": format_rsi,
    "ema": format_ema,
    "macd": format_macd,
    "bollinger": format_bollinger,
    "divergence": format_divergence,
    "volume": format_volume,
    "full": format_full,
    "daily": format_daily,
    "price": format_price,
}


async def button_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    await query.answer()

    handler = BUTTON_HANDLERS.get(query.data)
    if handler:
        await refresh_candles()
        text = handler()
    else:
        text = "Unknown command"

    await query.message.reply_text(text, parse_mode="Markdown", reply_markup=build_menu())


# ═══════════════════════════════════════════════════════════════════════════════
# POLLING LOOP (async, runs alongside the Telegram bot in the same event loop)
# ═══════════════════════════════════════════════════════════════════════════════

async def refresh_candles():
    """Fetch all timeframes in parallel (IO-bound, run in thread pool)."""
    loop = asyncio.get_event_loop()
    tasks = {
        tf: loop.run_in_executor(None, partial(fetch_candles, tf, 500))
        for tf in ALL_TIMEFRAMES
    }
    results = await asyncio.gather(*tasks.values(), return_exceptions=True)
    for tf, result in zip(tasks.keys(), results):
        if isinstance(result, Exception):
            log.error(f"Fetch {tf}: {result}")
        elif result:
            candle_cache[tf] = result


async def polling_task(app):
    """Background task: poll candles → compute indicators → fire alerts."""
    log.info("Polling loop started")
    while True:
        try:
            await refresh_candles()

            alerts = generate_alerts()
            for msg in alerts:
                try:
                    await app.bot.send_message(
                        chat_id=CHAT_ID, text=msg, parse_mode="Markdown")
                    log.info(f"Alert sent: {msg[:80]}...")
                except Exception as e:
                    log.error(f"Alert send failed: {e}")

        except Exception as e:
            log.error(f"Polling loop error: {e}")

        await asyncio.sleep(POLL_INTERVAL)


async def post_init(app):
    """Called after Application.initialize() — start the background poller."""
    log.info("Bootstrapping candle data...")
    await refresh_candles()
    for tf in ALL_TIMEFRAMES:
        c = candle_cache.get(tf)
        log.info(f"  {tf}: {len(c)} candles" if c else f"  {tf}: no data")

    # Initialize prev_rsi for trigger TFs (no crossback alerts on first poll)
    for tf in ["5m", "1m"]:
        candles = candle_cache.get(tf)
        if candles and len(candles) >= 16:
            rsi = compute_rsi([c["close"] for c in candles], RSI_TRIGGER_PERIOD)
            if rsi is not None:
                prev_rsi[tf] = rsi
                log.info(f"  {tf} RSI({RSI_TRIGGER_PERIOD}) initialized: {rsi:.1f}")

    asyncio.create_task(polling_task(app))
    log.info("Background polling task launched")


# ═══════════════════════════════════════════════════════════════════════════════
# MAIN
# ═══════════════════════════════════════════════════════════════════════════════

def main():
    log.info("Starting LighterRSI Signal Bot — Confluence System")
    log.info(f"  Thresholds: RSI <{RSI_OVERSOLD} oversold | >{RSI_OVERBOUGHT} overbought")
    log.info(f"  RSI periods: {RSI_TRIGGER_PERIOD} (trigger 5m/1m) | 14 (bias/setup)")
    log.info(f"  Trend filter: 4H RSI >50 bullish | <50 bearish")
    log.info(f"  Confluence: 2/3 required (4H bias + 15m setup + 5m volume)")
    log.info(f"  Cooldown: {SIGNAL_COOLDOWN}s per direction")
    log.info(f"  Volume spike: >{VOLUME_SPIKE_MULT}x avg")

    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .post_init(post_init)
        .build()
    )
    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CallbackQueryHandler(button_callback))

    log.info("Bot running — press Ctrl+C to stop")
    app.run_polling(drop_pending_updates=True)


if __name__ == "__main__":
    main()
