#!/usr/bin/env python3
"""
insider_alerts.py - get a phone alert when company insiders buy their own stock,
combined with a quick read of recent news about that company.

How it works
  1. Every minute it checks the SEC's live feed of newly filed Form 4 reports
     (insiders must file these within 2 business days of trading).
  2. It keeps only open-market BUYS (transaction code "P") worth at least
     `min_purchase_usd`.
  3. It looks up recent Google News headlines for the company and scores them
     (crude keyword matching, so treat it as a hint).
  4. It sends you an alert on Telegram (and prints it on screen).
  5. When you buy a stock, log it:  python insider_alerts.py bought ACME 24.10 40
     The app then watches the price and tells you when to SELL: stop-loss, profit
     target, trailing stop, holding-time limit, or insiders selling the stock.
     (Practice mode: set "auto_track": true in config.json and every buy alert
     also opens a simulated trade, so you can watch results without real money.)
  6. When you sell, log it:  python insider_alerts.py sold ACME 27.10
     It then tells you the profit or loss and your running total.

  7. Once a day after the US market closes it also scans about 70 large US stocks for
     "dip-buy" setups: a stock in a long-term uptrend that pulled back, and has just
     started to bounce, while the overall market is healthy. Those alerts come with the
     same sell rules and profit report. Run it by hand any time:  python insider_alerts.py scan
     See how those rules would have done on past prices:  python insider_alerts.py backtest-scan

Honest limits
  * Nothing here is "safe": the dip rules lower the chance of buying a falling stock, they
    do not remove it. They have not been tested on years of real prices.
  * "Instant" means within about a minute of the SEC publishing the filing. The
    insider's trade itself happened up to 2 business days earlier, so the price
    may already have moved.
  * An insider buy is a signal worth checking, not a guarantee. Not financial advice.
  * Sell signals use delayed prices checked every 15 minutes. Simulated profits
    ignore fees and taxes, and real fills will differ.

Setup (about 5 minutes; standard library only, nothing to pip install)
  python insider_alerts.py init            # creates config.json
  Edit config.json: set sec_user_agent to "Your Name your@email.com"
  (the SEC requires this and blocks anonymous programs).

  Telegram: in the Telegram app message @BotFather, send /newbot, follow the
  steps, and paste the token into config.json (telegram_bot_token). Then open
  your new bot, press Start, send it any message, and run:
  python insider_alerts.py find-chat-id    # saves telegram_chat_id for you

Commands
  python insider_alerts.py demo            # show a sample alert, no internet needed
  python insider_alerts.py test-alert      # send a test message to Telegram
  python insider_alerts.py run --once      # check once, then exit
  python insider_alerts.py run             # keep watching until you press Ctrl+C
  python insider_alerts.py bought ACME 24.10 40   # log a real purchase (ticker, price, shares)
  python insider_alerts.py sold ACME 27.10        # log a real sale (price optional) and see the profit
  python insider_alerts.py positions       # open positions and closed-trade profits

Cloud mode (runs without your laptop, for example on GitHub Actions; see insider-alerts.yml)
  python insider_alerts.py cloud           # one check pass; settings come from IA_* environment
                                           # variables; you log trades by messaging the bot:
                                           # "bought ACME 24.10 40", "sold ACME 27.10", "positions"
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import hmac
import json
import math
import os
import re
import sqlite3
import struct
import sys
import time
import zlib
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from email.utils import format_datetime, parsedate_to_datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
CONFIG_PATH = HERE / "config.json"
DB_PATH = Path(os.environ.get("IA_DB_PATH") or HERE / "seen.db")

DEFAULT_CONFIG = {
    "sec_user_agent": "YOUR NAME your-email@example.com",
    "telegram_bot_token": "",
    "telegram_chat_id": "",
    "poll_seconds": 60,
    "min_purchase_usd": 100000,
    "cluster_days": 14,
    "news_hours": 48,
    "watchlist": [],  # e.g. ["AAPL", "NVDA"]; empty = watch every company
    # tracking and sell rules
    "auto_track": False,          # True = practice mode: every buy alert also opens a simulated trade
    "position_usd": 1000,         # size of each simulated trade (practice mode only)
    "stop_loss_pct": 0.08,        # sell if down this much from entry
    "take_profit_pct": 0.20,      # sell if up this much from entry
    "trailing_stop_pct": 0.10,    # after gaining, sell if price falls this far from its peak
    "max_hold_days": 90,          # sell after holding this long
    "min_insider_sale_usd": 250000,  # insiders selling at least this much triggers a sell signal
    "price_check_minutes": 15,    # how often open positions are checked
    # dip-buy scanner (buys in an uptrend after a pullback that has started to bounce)
    "scan_enabled": True,
    "scan_tickers": [],           # empty = a built-in list of about 70 large, liquid US stocks
    "scan_rsi_dip": 35,           # RSI must have dropped to this level or lower in the last 4 days
    "scan_cooldown_days": 10,     # don't alert the same stock again within this many days
    "scan_max_alerts": 15,        # at most this many buy ideas per day from the scanner (best first)
    "scan_markets": ["US", "UK", "Germany", "France", "Netherlands", "Switzerland", "Canada", "Australia", "Japan", "Hong Kong", "Romania"],
    "scan_bots": ["dip", "breakout", "trend", "gap"],  # which scanner bots are on (you can also switch them in the chat)
    "exit_signals": True,         # also send sell signals when a trade looks overbought or its short-term trend breaks
    "scan_min_dollar_volume": 20000000,  # skip stocks trading less than this many dollars per day
    # day trading (15-minute candles, trades opened and closed the same day)
    "day_enabled": True,
    "day_markets": ["US", "Germany", "UK"],     # markets scanned while they are open
    "day_bots": ["orb", "vwap", "gapgo"],       # which day-trading bots are on
    "day_tickers": [],                          # empty = liquid stocks from the built-in lists
    "day_target_r": 1.5,                        # profit target = this many times the risk (distance to the stop)
    "day_max_alerts_per_run": 4,                # at most this many day-trade ideas per 15-minute candle
    "day_max_alerts_per_day": 25,               # and at most this many a day
    "day_close_minutes": 20,                    # close day trades this long before the market closes
    "timezone": "Europe/Bucharest",             # the times shown in day-trade alerts
    # crypto day trading (Binance 15-minute candles, open 24/7)
    "crypto_enabled": True,
    "crypto_coins": [],                         # empty = a built-in list of about 27 large coins, e.g. ["BTC", "ETH"]
    "crypto_bots": ["cbreak", "cvwap", "cdip"],
    "crypto_quote": "USDT",                     # the pair used for prices (the most liquid); you may have to trade USDC or EUR pairs
    "crypto_min_volume_usd": 30000000,          # skip coins that traded less than this over the last 24 hours
    "crypto_max_hold_hours": 3,                 # close a crypto trade after this long if neither the stop nor the target was hit
    "crypto_hours": "7-23",                     # only send new ideas between these local hours (0-24 = all day and night)
    "crypto_max_alerts_per_run": 3,
    "crypto_max_alerts_per_day": 30,
    "crypto_cooldown_min": 120,                 # don't repeat the same bot on the same coin within this many minutes
}

BROWSER_UA = "Mozilla/5.0 (compatible; insider-alerts/1.0)"


def log(msg: str) -> None:
    print(f"[{datetime.now():%H:%M:%S}] {msg}", flush=True)


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


# --------------------------------------------------------------------------- #
# Config
# --------------------------------------------------------------------------- #
def load_config(strict: bool = True) -> dict:
    raw = {}
    if CONFIG_PATH.exists():
        raw = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
    elif strict and not os.environ.get("IA_SEC_USER_AGENT"):
        sys.exit("No config.json yet. Run:  python insider_alerts.py init")
    cfg = {**DEFAULT_CONFIG, **raw}
    for key, default in DEFAULT_CONFIG.items():  # any setting can also come from an IA_<NAME> variable
        val = os.environ.get("IA_" + key.upper())
        if val:
            try:
                if key in ("scan_bots", "scan_markets", "day_markets", "day_bots", "day_tickers", "crypto_bots", "crypto_coins") and not val.lstrip().startswith("["):   # SCAN_BOTS=dip,breakout also works
                    keep = key in ("scan_markets", "day_markets")
                    low = key in ("scan_bots", "day_bots", "crypto_bots")
                    cfg[key] = [x.strip() if keep else x.strip().lower() if low else x.strip().upper() for x in val.split(",") if x.strip()]
                else:
                    cfg[key] = val if isinstance(default, str) else json.loads(val)
            except ValueError:
                sys.exit(f"Bad value for IA_{key.upper()}: {val!r}")
    ua = cfg["sec_user_agent"]
    if strict and ("@" not in ua or "your-email@example.com" in ua):
        sys.exit('Edit config.json and set sec_user_agent to your name and email, e.g. "Ana Pop ana@example.com". '
                 "The SEC requires this and blocks anonymous programs.")
    cfg["watchlist"] = [t.upper() for t in cfg["watchlist"]]
    return cfg


def cmd_init() -> None:
    if CONFIG_PATH.exists():
        sys.exit(f"{CONFIG_PATH} already exists; edit it directly.")
    CONFIG_PATH.write_text(json.dumps(DEFAULT_CONFIG, indent=2), encoding="utf-8")
    print(f"Created {CONFIG_PATH}\nNext: open it and set sec_user_agent (your name + email) and your Telegram token.")


# --------------------------------------------------------------------------- #
# HTTP
# --------------------------------------------------------------------------- #
def http_get(url: str, ua: str, timeout: int = 20, retries: int = 2) -> bytes:
    for attempt in range(retries + 1):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": ua})
            with urllib.request.urlopen(req, timeout=timeout) as resp:
                return resp.read()
        except urllib.error.HTTPError as e:
            if e.code in (429, 500, 502, 503) and attempt < retries:
                time.sleep(2 * (attempt + 1))
                continue
            raise
        except (urllib.error.URLError, TimeoutError, ConnectionError):
            if attempt < retries:
                time.sleep(1.5)
                continue
            raise
    raise RuntimeError("unreachable")


_last_sec_call = 0.0


def sec_get(url: str, ua: str) -> bytes:
    """SEC fair access allows 10 requests/second; stay well under it."""
    global _last_sec_call
    wait = 0.2 - (time.time() - _last_sec_call)
    if wait > 0:
        time.sleep(wait)
    try:
        return http_get(url, ua)
    finally:
        _last_sec_call = time.time()


# --------------------------------------------------------------------------- #
# SEC Form 4 feed and parsing
# --------------------------------------------------------------------------- #
ATOM = "{http://www.w3.org/2005/Atom}"
FEED_URL = ("https://www.sec.gov/cgi-bin/browse-edgar?action=getcurrent&type=4"
            "&company=&dateb=&owner=include&start=0&count=100&output=atom")
ACC_RE = re.compile(r"/data/(\d+)/(\d{18})/")


def fetch_feed(ua: str) -> list[dict]:
    """Newest Form 4 filings, oldest first. Each filing appears twice in the feed
    (issuer and reporting owner), so de-duplicate by accession number."""
    root = ET.fromstring(sec_get(FEED_URL, ua))
    filings, seen = [], set()
    for e in root.findall(ATOM + "entry"):
        link = e.find(ATOM + "link")
        href = link.get("href", "") if link is not None else ""
        m = ACC_RE.search(href)
        if not m or m.group(2) in seen:
            continue
        seen.add(m.group(2))
        filings.append({"cik": m.group(1), "acc": m.group(2),
                        "updated": e.findtext(ATOM + "updated") or "", "index_url": href})
    filings.reverse()
    return filings


def filing_txt_url(cik: str, acc: str) -> str:
    dashed = f"{acc[:10]}-{acc[10:12]}-{acc[12:]}"
    return f"https://www.sec.gov/Archives/edgar/data/{int(cik)}/{acc}/{dashed}.txt"


def _truthy(v) -> bool:
    return (v or "").strip().lower() in ("1", "true")


def _num(v) -> float:
    try:
        return float((v or "0").replace(",", ""))
    except ValueError:
        return 0.0


def parse_form4(text: str) -> dict | None:
    m = re.search(r"<ownershipDocument\b.*?</ownershipDocument>", text, re.S)
    if not m:
        return None
    root = ET.fromstring(m.group(0))
    issuer = root.find("issuer")
    if issuer is None:
        return None
    owners, roles = [], []
    for ro in root.findall("reportingOwner"):
        name = (ro.findtext("reportingOwnerId/rptOwnerName") or "").strip().title()
        if name:
            owners.append(name)
        rel = ro.find("reportingOwnerRelationship")
        if rel is not None:
            if _truthy(rel.findtext("isOfficer")):
                roles.append((rel.findtext("officerTitle") or "Officer").strip())
            if _truthy(rel.findtext("isDirector")):
                roles.append("Director")
            if _truthy(rel.findtext("isTenPercentOwner")):
                roles.append("10% owner")
    buys, sells = [], []
    for t in root.findall("nonDerivativeTable/nonDerivativeTransaction"):
        code = (t.findtext("transactionCoding/transactionCode") or "").strip()
        acquired = (t.findtext("transactionAmounts/transactionAcquiredDisposedCode/value") or "").strip()
        rec = {
            "shares": _num(t.findtext("transactionAmounts/transactionShares/value")),
            "price": _num(t.findtext("transactionAmounts/transactionPricePerShare/value")),
            "date": (t.findtext("transactionDate/value") or "").strip(),
        }
        if code == "P" and acquired == "A":  # open-market purchase
            buys.append(rec)
        elif code == "S" and acquired == "D":  # open-market sale
            sells.append(rec)
    return {
        "ticker": (issuer.findtext("issuerTradingSymbol") or "").strip().upper(),
        "company": (issuer.findtext("issuerName") or "").strip(),
        "owners": owners, "roles": list(dict.fromkeys(roles)), "buys": buys, "sells": sells,
    }


def summarize_buys(p: dict) -> dict:
    shares = sum(b["shares"] for b in p["buys"])
    total = sum(b["shares"] * b["price"] for b in p["buys"])
    dates = sorted(b["date"] for b in p["buys"] if b["date"])
    return {
        "shares": shares, "total": total,
        "avg_price": total / shares if shares else 0.0,
        "date": dates[-1] if dates else "",
        "senior": is_senior(" ".join(p["roles"])),
    }


def is_senior(role_text: str) -> bool:
    t = role_text.lower()
    if re.search(r"\b(ceo|chief executive|cfo|chief financial)\b", t):
        return True
    t2 = re.sub(r"vice[\s-]*(president|chair\w*)", "", t)
    return bool(re.search(r"\b(president|chairman|chair)\b", t2))


# --------------------------------------------------------------------------- #
# News and price context
# --------------------------------------------------------------------------- #
POS = re.compile(r"\b(?:upgrade[sd]?|beats?|tops|surges?|soars?|jumps?|record|raises? (?:guidance|outlook|forecast)|"
                 r"approval|approved|wins?|awarded|contract|partnership|buyback|outperform|strong|rall(?:y|ies))\b", re.I)
NEG = re.compile(r"\b(?:downgrade[sd]?|miss(?:es|ed)?|plunges?|tumbles?|slumps?|sinks?|falls?|drops?|lawsuit|sues?|sued|"
                 r"investigation|probe|recall|fraud|bankruptcy|layoffs?|cuts? (?:guidance|outlook|forecast)|warning|warns?|"
                 r"delay(?:s|ed)?|underperform|short seller|halts?)\b", re.I)


def headline_sentiment(title: str) -> int:
    p, n = bool(POS.search(title)), bool(NEG.search(title))
    return (p and not n) - (n and not p)


def parse_news(raw: bytes, hours: int) -> dict:
    cutoff = datetime.now(timezone.utc) - timedelta(hours=hours)
    items = []
    for it in ET.fromstring(raw).iter("item"):
        title = (it.findtext("title") or "").strip()
        try:
            when = parsedate_to_datetime(it.findtext("pubDate") or "")
            if when.tzinfo is None:
                when = when.replace(tzinfo=timezone.utc)
        except (TypeError, ValueError):
            continue
        if title and when >= cutoff:
            items.append((title, headline_sentiment(title)))
    pos = sum(1 for _, s in items if s > 0)
    neg = sum(1 for _, s in items if s < 0)
    label = "none" if not items else "positive" if pos - neg >= 1 else "negative" if neg - pos >= 1 else "neutral"
    return {"items": items, "pos": pos, "neg": neg, "label": label}


def fetch_news(company: str, ticker: str, hours: int) -> dict:
    name = re.sub(r",?\s+(inc|corp|corporation|co|ltd|plc|holdings|company)\b\.?", "", company, flags=re.I).strip() or ticker
    q = f"{name} {ticker} stock when:{max(1, math.ceil(hours / 24))}d"
    url = "https://news.google.com/rss/search?" + urllib.parse.urlencode(
        {"q": q, "hl": "en-US", "gl": "US", "ceid": "US:en"})
    return parse_news(http_get(url, BROWSER_UA), hours)


def fetch_price(ticker: str) -> float | None:
    """Latest price: Stooq for US stocks (free, no key), Yahoo for the rest. None if unavailable."""
    if market_suffix(ticker):
        return yahoo_price(ticker)
    sym = ticker.lower().replace(".", "-")
    try:
        raw = http_get(f"https://stooq.com/q/l/?s={sym}.us&f=sd2t2c&h&e=csv", BROWSER_UA, timeout=10, retries=0)
        lines = raw.decode("utf-8", "replace").strip().splitlines()
        return float(lines[1].split(",")[-1])
    except Exception:
        return None


# --------------------------------------------------------------------------- #
# Scoring and alert text
# --------------------------------------------------------------------------- #
def evaluate(buy: dict, cluster_n: int, news: dict, cfg: dict) -> tuple[str, list[str]]:
    score, why = 0, [f"large purchase (${buy['total']:,.0f})"]
    if buy["total"] >= 5 * cfg["min_purchase_usd"]:
        score += 1
        why[0] = f"very large purchase (${buy['total']:,.0f})"
    if buy["senior"]:
        score += 1
        why.append("senior insider (CEO/CFO/President/Chair)")
    if cluster_n >= 2:
        score += 1
        why.append(f"{cluster_n} different insiders bought within {cfg['cluster_days']} days")
    if news["label"] == "positive":
        score += 1
        why.append("recent news looks positive")
    elif news["label"] == "negative":
        score -= 1
        why.append("WARNING: recent news looks negative")
    level = "STRONG" if score >= 3 else "MODERATE" if score >= 1 else "WEAK"
    return level, why


def format_alert(p: dict, buy: dict, level: str, why: list[str], news: dict,
                 price: float | None, filing: dict, demo: bool = False) -> str:
    icon = {"STRONG": "🟢", "MODERATE": "🟡", "WEAK": "⚪"}[level]
    who = ", ".join(p["owners"]) or "An insider"
    role = f" ({'; '.join(p['roles'])})" if p["roles"] else ""
    lines = [
        f"{'[DEMO] ' if demo else ''}{icon} {level} insider buy: {p['ticker']} ({p['company']})",
        f"{who}{role} bought {buy['shares']:,.0f} shares at ~${buy['avg_price']:,.2f} "
        f"= ${buy['total']:,.0f} on {buy['date'] or 'unknown date'}",
    ]
    ctx = f"Filed with the SEC: {filing['updated'][:16].replace('T', ' ')}"
    if price:
        ctx += f" | last close ${price:,.2f}"
        if buy["avg_price"]:
            ctx += f" ({price / buy['avg_price'] - 1:+.1%} vs insider's price)"
    lines += [ctx, "Why: " + "; ".join(why)]
    if news["items"]:
        lines.append(f"News (last {news.get('hours', 48)}h): {news['pos']} positive, {news['neg']} negative, "
                     f"{len(news['items']) - news['pos'] - news['neg']} neutral")
        for title, s in news["items"][:3]:
            lines.append(f"  {'+' if s > 0 else '-' if s < 0 else '.'} {title[:110]}")
    else:
        lines.append("News: nothing found in the time window")
    lines += [filing["index_url"], "Not financial advice. Read the filing and decide for yourself."]
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# Notifications
# --------------------------------------------------------------------------- #
def send_telegram(token: str, chat_id: str, text: str) -> None:
    req = urllib.request.Request(
        f"https://api.telegram.org/bot{token}/sendMessage",
        data=json.dumps({"chat_id": chat_id, "text": text, "disable_web_page_preview": True}).encode(),
        headers={"Content-Type": "application/json"})
    urllib.request.urlopen(req, timeout=15).read()


def make_notifier(cfg: dict):
    token, chat = cfg["telegram_bot_token"], str(cfg["telegram_chat_id"])

    def notify(msg: str) -> None:
        print("\n" + "=" * 64 + "\n" + msg + "\n" + "=" * 64, flush=True)
        log_alert(msg)
        if token and chat:
            try:
                send_telegram(token, chat, msg)
            except Exception as e:  # keep running even if Telegram hiccups
                log(f"Telegram send failed: {e}")
    return notify


def cmd_find_chat_id(cfg: dict) -> None:
    token = cfg["telegram_bot_token"]
    if not token:
        sys.exit("Put your bot token in config.json first (telegram_bot_token).")
    data = json.loads(urllib.request.urlopen(f"https://api.telegram.org/bot{token}/getUpdates", timeout=15).read())
    chats = {}
    for u in data.get("result", []):
        c = (u.get("message") or u.get("channel_post") or {}).get("chat")
        if c:
            chats[c["id"]] = c.get("first_name") or c.get("title") or c.get("username") or ""
    if not chats:
        sys.exit("No messages found. Open your bot in Telegram, press Start, send it any message, then run this again.")
    if len(chats) > 1:
        sys.exit("Several chats found; set telegram_chat_id in config.json to one of: "
                 + ", ".join(f"{i} ({n})" for i, n in chats.items()))
    chat_id, name = next(iter(chats.items()))
    raw = json.loads(CONFIG_PATH.read_text(encoding="utf-8"))
    raw["telegram_chat_id"] = str(chat_id)
    CONFIG_PATH.write_text(json.dumps(raw, indent=2), encoding="utf-8")
    print(f"Saved telegram_chat_id {chat_id} ({name}). Try:  python insider_alerts.py test-alert")


# --------------------------------------------------------------------------- #
# Positions, sell signals and profit reports
# --------------------------------------------------------------------------- #
def init_db() -> sqlite3.Connection:
    DB_PATH.parent.mkdir(parents=True, exist_ok=True)
    db = sqlite3.connect(DB_PATH)
    db.row_factory = sqlite3.Row
    db.execute("CREATE TABLE IF NOT EXISTS seen (acc TEXT PRIMARY KEY, at TEXT)")
    db.execute("CREATE TABLE IF NOT EXISTS buys (acc TEXT, ticker TEXT, owner TEXT, total REAL, at TEXT)")
    db.execute("CREATE TABLE IF NOT EXISTS meta (k TEXT PRIMARY KEY, v TEXT)")
    db.execute("CREATE TABLE IF NOT EXISTS alerts_log (id INTEGER PRIMARY KEY AUTOINCREMENT, at TEXT, text TEXT)")
    db.execute("""CREATE TABLE IF NOT EXISTS positions (
        id INTEGER PRIMARY KEY AUTOINCREMENT, ticker TEXT, company TEXT, shares REAL,
        entry_price REAL, entry_at TEXT, peak REAL, last_price REAL,
        manual INTEGER DEFAULT 0, status TEXT DEFAULT 'open',
        sell_alerted INTEGER DEFAULT 0, news_warned INTEGER DEFAULT 0,
        exit_price REAL, exit_at TEXT, exit_reason TEXT, pnl REAL, ret REAL)""")
    have = [r[1] for r in db.execute("PRAGMA table_info(positions)")]
    for col, decl in (("bot", "TEXT DEFAULT ''"), ("kind", "TEXT DEFAULT 'swing'"), ("stop", "REAL"),
                      ("target", "REAL"), ("exit_by", "TEXT"), ("mgmt_t", "INTEGER DEFAULT 0")):
        if col not in have:
            db.execute(f"ALTER TABLE positions ADD COLUMN {col} {decl}")
    db.commit()
    return db


def money(x: float) -> str:
    return f"{'+' if x >= 0 else '-'}${abs(x):,.2f}"


def open_positions(db: sqlite3.Connection, ticker: str | None = None) -> list[dict]:
    sql, args = "SELECT * FROM positions WHERE status='open'", ()
    if ticker:
        sql, args = sql + " AND ticker=?", (ticker,)
    return [dict(r) for r in db.execute(sql + " ORDER BY id", args)]


def is_swing(pos: dict) -> bool:
    return (pos.get("kind") or "swing") == "swing"


def held_days(pos: dict) -> int:
    return (utc_now() - datetime.fromisoformat(pos["entry_at"])).days


def open_tracked_position(db: sqlite3.Connection, parsed: dict, entry: float, cfg: dict, bot: str = "insider") -> int:
    """Simulated trade opened when a buy alert fires. Returns the share count.
    `bot` says which bot(s) found it, e.g. "insider" or "dip+breakout"."""
    shares = max(1, int(cfg["position_usd"] * usd_rate(parsed["ticker"]) // entry))
    db.execute("INSERT INTO positions (ticker, company, shares, entry_price, entry_at, peak, last_price, manual, bot) "
               "VALUES (?, ?, ?, ?, ?, ?, ?, 0, ?)",
               (parsed["ticker"], parsed["company"], shares, entry, now_iso(), entry, entry, bot))
    db.commit()
    return shares


def sell_reason(pos: dict, price: float, cfg: dict, days: int) -> str | None:
    entry = pos["entry_price"]
    peak = pos["peak"] or entry
    chg = price / entry - 1
    if chg <= -cfg["stop_loss_pct"]:
        return f"stop-loss hit ({chg:+.1%} from entry)"
    if chg >= cfg["take_profit_pct"]:
        return f"profit target reached ({chg:+.1%} from entry)"
    if peak > entry and price <= peak * (1 - cfg["trailing_stop_pct"]):
        return f"trailing stop: price fell {1 - price / peak:.1%} from its peak of {fp(pos['ticker'], peak)}"
    if days >= cfg["max_hold_days"]:
        return f"held {days} days (limit {cfg['max_hold_days']}); time to free up the money"
    return None


def totals(db: sqlite3.Connection) -> dict:
    r = db.execute("SELECT COUNT(*), COALESCE(SUM(pnl > 0), 0), COALESCE(SUM(pnl), 0) "
                   "FROM positions WHERE status='closed'").fetchone()
    return {"n": r[0], "wins": int(r[1]), "pnl": float(r[2])}


def close_position(db: sqlite3.Connection, pos: dict, price: float, reason: str) -> tuple[float, float]:
    pnl = (price - pos["entry_price"]) * pos["shares"] / usd_rate(pos["ticker"])      # profit in US dollars
    ret = price / pos["entry_price"] - 1
    db.execute("UPDATE positions SET status='closed', exit_price=?, exit_at=?, exit_reason=?, pnl=?, ret=?, "
               "last_price=? WHERE id=?", (price, now_iso(), reason, pnl, ret, price, pos["id"]))
    db.commit()
    return pnl, ret


def format_closed(pos: dict, price: float, reason: str, pnl: float, ret: float, tot: dict, via_signal: bool) -> str:
    kind = "your trade" if pos["manual"] else "simulated trade"
    icon = "✅" if pnl > 0 else "❌" if pnl < 0 else "➖"
    head = (f"🔴 SELL signal: {pos['ticker']} - {kind} closed" if via_signal
            else f"{icon} Trade closed ({kind}): {pos['ticker']}")
    days = held_days(pos)
    lines = [head]
    if reason:
        lines.append(f"Reason: {reason}")
    lines += [
        f"Bought {pos['shares']:g} shares at {fp(pos['ticker'], pos['entry_price'])} on {pos['entry_at'][:10]}, "
        f"sold at {fp(pos['ticker'], price)} ({days} day{'s' if days != 1 else ''})",
        f"{icon} {'PROFIT' if pnl >= 0 else 'LOSS'}: {money(pnl)} ({ret:+.1%})",
        f"All closed trades so far: {tot['n']}, {tot['wins']} winner{'s' if tot['wins'] != 1 else ''}, "
        f"net {money(tot['pnl'])}",
    ]
    if via_signal:
        lines.append("Not financial advice. Simulated: ignores fees, taxes and real-world fills.")
    return "\n".join(lines)


def format_sell_signal(pos: dict, price: float, reason: str) -> str:
    pnl, ret = (price - pos["entry_price"]) * pos["shares"] / usd_rate(pos["ticker"]), price / pos["entry_price"] - 1
    sold_cmd = how_to("sold %s %.2f" % (pos["ticker"], price))
    return "\n".join([
        f"🔴 SELL signal: {pos['ticker']}",
        f"Reason: {reason}",
        f"You hold {pos['shares']:g} shares bought at {fp(pos['ticker'], pos['entry_price'])}; "
        f"now ~{fp(pos['ticker'], price)}: {money(pnl)} ({ret:+.1%}) unrealised",
        f"After you sell, tell me the price so I can report your profit:\n  {sold_cmd}",
        "Not financial advice.",
    ])


def trigger_sell(db: sqlite3.Connection, pos: dict, price: float, reason: str, notify) -> None:
    """Simulated positions close and report the profit. Your own (logged) positions only get an
    alert; the profit is reported when you run `sold`."""
    if pos["manual"]:
        db.execute("UPDATE positions SET sell_alerted=1 WHERE id=?", (pos["id"],))
        db.commit()
        notify(format_sell_signal(pos, price, reason))
    else:
        pnl, ret = close_position(db, pos, price, reason)
        notify(format_closed(pos, price, reason, pnl, ret, totals(db), via_signal=True))


def check_positions(cfg: dict, db: sqlite3.Connection, notify) -> int:
    """Look up the latest price of each open position and apply the sell rules."""
    acted = 0
    for pos in open_positions(db):
        if pos["sell_alerted"] or not is_swing(pos):
            continue
        price = fetch_price(pos["ticker"])
        if price is None:
            continue
        pos["peak"] = max(pos["peak"] or pos["entry_price"], price)
        pos["last_price"] = price
        db.execute("UPDATE positions SET peak=?, last_price=? WHERE id=?", (pos["peak"], price, pos["id"]))
        db.commit()
        reason = sell_reason(pos, price, cfg, held_days(pos))
        if reason:
            trigger_sell(db, pos, price, reason, notify)
            acted += 1
        elif not pos["news_warned"]:
            try:
                news = fetch_news(pos["company"] or pos["ticker"], pos["ticker"], cfg["news_hours"])
            except Exception:
                continue
            if news["label"] == "negative" and news["neg"] - news["pos"] >= 2:
                db.execute("UPDATE positions SET news_warned=1 WHERE id=?", (pos["id"],))
                db.commit()
                bad = [t for t, s in news["items"] if s < 0][:3]
                notify("\n".join([f"⚠️ Heads-up: news about {pos['ticker']} (you hold it) looks negative"]
                                 + [f"  - {t[:110]}" for t in bad]
                                 + ["Not a sell signal by itself. Check it before deciding."]))
    return acted


def handle_insider_sales(cfg: dict, db: sqlite3.Connection, parsed: dict, notify) -> None:
    sale = sum(s["shares"] * s["price"] for s in parsed["sells"])
    if sale < cfg["min_insider_sale_usd"]:
        return
    held = [p for p in open_positions(db, parsed["ticker"]) if not p["sell_alerted"] and is_swing(p)]
    if not held:
        return
    price = fetch_price(parsed["ticker"])
    who = ", ".join(parsed["owners"]) or "an insider"
    reason = (f"insiders are selling: {who} sold ${sale:,.0f} of {parsed['ticker']} "
              f"(sales are often pre-planned, but it weakens the reason you bought)")
    for pos in held:
        trigger_sell(db, pos, price or pos["last_price"] or pos["entry_price"], reason, notify)


CHAT_MODE = False  # True in the cloud job, where you give commands by messaging the bot


def how_to(cmd: str) -> str:
    """How you give a command: a plain chat message in the cloud, Command Prompt otherwise."""
    return cmd if CHAT_MODE else f"python insider_alerts.py {cmd}"


def meta_get(db: sqlite3.Connection, key: str, default: str = "") -> str:
    r = db.execute("SELECT v FROM meta WHERE k=?", (key,)).fetchone()
    return r[0] if r else default


def meta_set(db: sqlite3.Connection, key: str, val) -> None:
    db.execute("INSERT OR REPLACE INTO meta (k, v) VALUES (?, ?)", (key, str(val)))
    db.commit()


def log_bought(db: sqlite3.Connection, ticker: str, price: float, shares: float, cfg: dict) -> str:
    t = ticker.upper()
    if not re.fullmatch(r"[A-Z][A-Z.\-]{0,5}", t):
        raise ValueError(f"'{ticker}' doesn't look like a stock ticker")
    if price <= 0 or shares <= 0:
        raise ValueError("price and shares must be positive numbers")
    held = open_positions(db, t)
    if held:  # replace the simulated position with your real purchase
        db.execute("UPDATE positions SET shares=?, entry_price=?, entry_at=?, peak=?, last_price=?, manual=1, "
                   "sell_alerted=0, news_warned=0 WHERE id=?", (shares, price, now_iso(), price, price, held[0]["id"]))
    else:
        db.execute("INSERT INTO positions (ticker, company, shares, entry_price, entry_at, peak, last_price, manual) "
                   "VALUES (?, '', ?, ?, ?, ?, ?, 1)", (t, shares, price, now_iso(), price, price))
    db.commit()
    verb = "send" if CHAT_MODE else "run"
    note = market_price_note(t, price)
    return (f"Logged: {shares:g} {t} at {fp(t, price)}. I'll alert you to sell at {fp(t, price * (1 - cfg['stop_loss_pct']))} "
            f"(stop-loss) or {fp(t, price * (1 + cfg['take_profit_pct']))} (profit target), if it falls "
            f"{cfg['trailing_stop_pct']:.0%} from its peak after gaining, after {cfg['max_hold_days']} days, "
            f"or if insiders start selling.\nWhen you sell, {verb}:  {how_to('sold ' + t + ' <price>')}" + note)


def cmd_bought(db: sqlite3.Connection, ticker: str, price: float, shares: float, cfg: dict) -> None:
    try:
        print(log_bought(db, ticker, price, shares, cfg))
    except ValueError as e:
        sys.exit(str(e))


def log_sold(db: sqlite3.Connection, cfg: dict, ticker: str, price: float | None) -> list[str]:
    t = ticker.upper()
    held = open_positions(db, t)
    if not held:
        raise ValueError(f"No open {t} position. See:  {how_to('positions')}")
    typed = price is not None
    if price is None:
        price = fetch_price(t)
        if price is None:
            raise ValueError(f"Couldn't fetch a price. Send it yourself:  {how_to('sold ' + t + ' <price>')}")
    texts = []
    for pos in held:
        pnl, ret = close_position(db, pos, price, "sold by you")
        texts.append(format_closed(pos, price, "", pnl, ret, totals(db), via_signal=False))
    if typed and texts:
        texts[-1] += market_price_note(t, price)
    return texts


def cmd_sold(db: sqlite3.Connection, cfg: dict, ticker: str, price: float | None) -> None:
    try:
        texts = log_sold(db, cfg, ticker, price)
    except ValueError as e:
        sys.exit(str(e))
    notify = make_notifier(cfg)
    for text in texts:
        notify(text)


def positions_text(db: sqlite3.Connection) -> str:
    opens = open_positions(db)
    lines = ["OPEN POSITIONS (last price = most recent check)" if opens else "No open positions."]
    for p in opens:
        px = p["last_price"] or p["entry_price"]
        lines.append(f"  {p['ticker']:6} {p['shares']:g} sh  in {fp(p['ticker'], p['entry_price'])} ({p['entry_at'][:10]})  "
                     f"last {fp(p['ticker'], px)}  {money((px - p['entry_price']) * p['shares'] / usd_rate(p['ticker']))} ({px / p['entry_price'] - 1:+.1%})  "
                     f"{'yours' if p['manual'] else 'simulated day trade' if p.get('kind') == 'day' else 'simulated crypto trade' if p.get('kind') == 'crypto' else 'simulated'}")
    closed = [dict(r) for r in db.execute("SELECT * FROM positions WHERE status='closed' ORDER BY exit_at")]
    if closed:
        lines += ["", "CLOSED TRADES"]
        for p in closed:
            lines.append(f"  {p['ticker']:6} {p['entry_at'][:10]} -> {p['exit_at'][:10]}  "
                         f"${p['entry_price']:,.2f} -> ${p['exit_price']:,.2f}  {money(p['pnl'])} ({p['ret']:+.1%})  {p['exit_reason']}")
        t = totals(db)
        lines += ["", f"Total: {t['n']} closed trades, {t['wins']} winners, net {money(t['pnl'])}"]
    return "\n".join(lines)


def cmd_positions(db: sqlite3.Connection) -> None:
    print(positions_text(db))


# --------------------------------------------------------------------------- #
# Dip scanner: "pullback in an uptrend, now bouncing" alerts from price history
# --------------------------------------------------------------------------- #
DEFAULT_SCAN = ("AAPL MSFT NVDA AMZN GOOGL META AVGO TSLA LLY JPM V UNH XOM MA COST HD PG JNJ ABBV NFLX "
                "BAC CRM ORCL WMT KO MRK CVX AMD PEP ADBE TMO LIN CSCO ACN MCD ABT DIS WFC GE IBM QCOM "
                "TXN INTU CAT AMGN VZ NOW AMAT PFE ISRG GS UBER BKNG SPGI LOW HON UNP T RTX NEE PGR DE "
                "LRCX ADP BLK ETN SBUX MU "
                "PANW CMG KLAC SNPS CDNS MDLZ MMC CB SO DUK ICE CME MCO AON CI ELV REGN VRTX GILD BSX SYK "
                "MDT ZTS BDX HCA CVS MO PM TJX NKE ORLY AZO ROST MAR HLT YUM DG DLTR LULU EL CL KMB GIS "
                "HSY STZ KR SYY ADM TGT BMY SCHW MS C USB PNC TFC COF AXP MET PRU AIG TRV ALL AFL CINF "
                "FI FIS PYPL ANET FTNT MSI APH TEL GLW HPQ DELL STX WDC NXPI ON MCHP ADI MPWR SWKS TER "
                "ZS CRWD DDOG NET SNOW TEAM WDAY ADSK ROP CTSH EPAM GDDY PLTR SHOP SQ ABNB DASH LYFT EXPE "
                "COP EOG SLB OXY PSX MPC VLO HAL BKR KMI WMB OKE FANG DVN HES CTRA APA "
                "LMT NOC GD LHX TDG BA HII TXT CARR OTIS MMM EMR ITW PH ROK CMI PCAR FDX UPS CSX NSC DAL UAL LUV "
                "WM RSG ECL SHW APD DD DOW NUE STLD FCX NEM MLM VMC "
                "AMT PLD CCI EQIX PSA O SPG WELL DLR AVB EQR "
                "D AEP EXC SRE XEL ED PEG WEC EIX PCG "
                "F GM TM HMC APTV BWA LKQ "
                "DHR A IQV IDXX MTD WAT EW ALGN RMD DXCM PODD HOLX "
                "CHTR CMCSA TMUS WBD PARA FOXA EA TTWO MTCH "
                "ADBE PAYX ZBRA TRMB KEYS "
                "AMP BK STT NTRS RJF FITB HBAN RF KEY CFG MTB "
                "GPC POOL TSCO ULTA BBY KMX DRI DPZ").split()
DEFAULT_SCAN = list(dict.fromkeys(DEFAULT_SCAN))

# --------------------------------------------------------------------------- #
# Stocks outside the US. They carry the Yahoo exchange ending (SAP.DE, 7203.T).
# suffix -> (market, index used as that market's health check, price prefix, price ending, decimals,
#            local currency per 1 US dollar, rough, only used for position sizes and $ profit)
# --------------------------------------------------------------------------- #
MARKETS = {
    "": ("US", "SPY", "$", "", 2, 1.0),
    "L": ("UK", "^FTSE", "", "p", 1, 79.0),            # London prices are in pence
    "DE": ("Germany", "^GDAXI", "€", "", 2, 0.92),
    "PA": ("France", "^FCHI", "€", "", 2, 0.92),
    "AS": ("Netherlands", "^AEX", "€", "", 2, 0.92),
    "SW": ("Switzerland", "^SSMI", "CHF ", "", 2, 0.88),
    "TO": ("Canada", "^GSPTSE", "C$", "", 2, 1.38),
    "AX": ("Australia", "^AXJO", "A$", "", 2, 1.52),
    "T": ("Japan", "^N225", "¥", "", 0, 150.0),
    "HK": ("Hong Kong", "^HSI", "HK$", "", 2, 7.8),
    "RO": ("Romania", None, "", " RON", 2, 4.6),       # no index available: only the stock's own trend is checked
}
GLOBAL_SCAN = {
    "L": "SHEL AZN HSBA ULVR BP GSK RIO BATS DGE REL LSEG NG CPG BA LLOY BARC VOD GLEN AAL PRU TSCO RKT NWG STAN EXPN SSE FLTR WPP",
    "DE": "SAP SIE ALV DTE AIR MBG BMW VOW3 BAS BAYN ADS IFX MUV2 DB1 RWE EOAN HEN3 DHL MRK SY1 CON FRE HNR1",
    "PA": "MC OR TTE SAN RMS SU AI BNP CS EL KER DG SAF CAP ORA VIE ENGI",
    "AS": "ASML INGA PHIA HEIA AD WKL PRX ADYEN NN",
    "SW": "NESN ROG NOVN UBSG ZURN ABBN CFR LONN SIKA GIVN HOLN",
    "TO": "RY TD ENB CNQ SHOP CP CNR BMO BNS SU TRP ATD CM MFC NTR WCN FNV AEM",
    "AX": "BHP CBA CSL NAB WBC ANZ WES MQG FMG WOW TLS GMG COL",
    "T": "7203 6758 9984 8306 6861 9432 6098 8035 4063 7974 6501 8058 9983 4519 6902",
    "HK": "0700 9988 0939 1299 0005 3690 1810 2318 0941 1211 9618 1398",
    "RO": "TLV SNP H2O SNG SNN BRD TGN EL M",
}
GLOBAL_TICKERS = [f"{t}.{suf}" for suf, names in GLOBAL_SCAN.items() for t in names.split()]


def market_suffix(ticker: str) -> str:
    """'' for US tickers (BRK.B counts as US), otherwise the exchange ending such as 'DE'."""
    if "." in ticker:
        end = ticker.rsplit(".", 1)[1].upper()
        if end in MARKETS and end:
            return end
    return ""


def market_name(ticker: str) -> str:
    return MARKETS[market_suffix(ticker)][0]


def usd_rate(ticker: str) -> float:
    return MARKETS[market_suffix(ticker)][5]


def is_crypto(ticker: str) -> bool:
    return ticker.endswith(("USDT", "USDC")) and ticker.isalpha() and ticker.isupper() and len(ticker) > 5


def fp(ticker: str, x: float) -> str:
    """A price in the right currency for that stock: $12.30, €45.10, 7,350p, ¥2,950. Crypto gets more decimals for cheap coins."""
    if is_crypto(ticker):
        return f"${x:,.2f}" if x >= 100 else f"${x:,.4f}" if x >= 1 else f"${x:,.5f}" if x >= 0.01 else f"${x:.7f}"
    _, _, pre, end, dec, _ = MARKETS[market_suffix(ticker)]
    return f"{pre}{x:,.{dec}f}{end}"


def min_turnover(cfg: dict, ticker: str) -> float:
    """Daily trading volume (in the stock's own currency) a stock needs to count as easy to trade.
    Small markets like Romania are far thinner, so their limit is a tenth of the usual one."""
    return cfg["scan_min_dollar_volume"] * usd_rate(ticker) * (0.1 if market_suffix(ticker) == "RO" else 1.0)


def cur_of(ticker: str) -> list:
    """[prefix, ending, decimals] so the app can show a stock's price in its own currency."""
    _, _, pre, end, dec, _ = MARKETS[market_suffix(ticker)]
    return [pre, end, dec]


def scan_universe(cfg: dict) -> list[str]:
    if cfg["scan_tickers"]:
        return [t.upper() for t in cfg["scan_tickers"]]
    on = {m.lower() for m in cfg["scan_markets"]}
    return [t for t in DEFAULT_SCAN + GLOBAL_TICKERS if market_name(t).lower() in on]


def utc_now() -> datetime:
    return datetime.now(timezone.utc)


def parse_stooq_csv(raw: bytes) -> list[dict]:
    lines = raw.decode("utf-8", "replace").strip().splitlines()
    if not lines or not lines[0].lower().startswith("date"):
        raise ValueError("no price table (got: " + (lines[0][:50] if lines else "nothing") + ")")
    bars = []
    for ln in lines[1:]:
        p = ln.split(",")
        try:
            bars.append({"date": p[0], "open": float(p[1]), "high": float(p[2]), "low": float(p[3]),
                         "close": float(p[4]), "volume": float(p[5]) if len(p) > 5 and p[5] else 0.0})
        except (ValueError, IndexError):
            continue
    bars.sort(key=lambda b: b["date"])
    return bars


def parse_yahoo_json(raw: bytes) -> list[dict]:
    res = json.loads(raw)["chart"]["result"][0]
    q = res["indicators"]["quote"][0]
    vols = q.get("volume") or []
    bars = []
    for i, ts in enumerate(res.get("timestamp") or []):
        try:
            o, h, l, c = q["open"][i], q["high"][i], q["low"][i], q["close"][i]
        except (KeyError, IndexError):
            continue
        if None in (o, h, l, c):
            continue
        bars.append({"date": datetime.fromtimestamp(ts, timezone.utc).strftime("%Y-%m-%d"),
                     "open": float(o), "high": float(h), "low": float(l), "close": float(c),
                     "volume": float(vols[i]) if i < len(vols) and vols[i] else 0.0})
    bars.sort(key=lambda b: b["date"])
    return bars


def yahoo_symbol(ticker: str) -> str:
    """Yahoo's spelling: BRK.B -> BRK-B, but SAP.DE and ^FTSE stay as they are."""
    t = ticker.upper()
    return urllib.parse.quote(t if t.startswith("^") or market_suffix(t) else t.replace(".", "-"))


def fetch_history(ticker: str, days: int = 420, min_bars: int = 210) -> list[dict]:
    """Daily prices for the last `days` calendar days. US stocks: Stooq first, then Yahoo. Others: Yahoo."""
    sym = ticker.lower().replace(".", "-")
    us = not ticker.startswith("^") and not market_suffix(ticker)
    now = utc_now()
    start = now - timedelta(days=days)
    d1, d2, first = start.strftime("%Y%m%d"), now.strftime("%Y%m%d"), start.strftime("%Y-%m-%d")
    yrange = "2y" if days <= 730 else "5y" if days <= 1825 else "10y"
    errors = []
    if us:
        try:
            bars = parse_stooq_csv(http_get(f"https://stooq.com/q/d/l/?s={sym}.us&i=d&d1={d1}&d2={d2}",
                                            BROWSER_UA, timeout=20, retries=1))
            bars = [b for b in bars if b["date"] >= first]
            if len(bars) >= min_bars:
                return bars
            errors.append("Stooq: too little data")
        except Exception as e:
            errors.append(f"Stooq: {e}")
    try:
        bars = parse_yahoo_json(http_get(
            f"https://query1.finance.yahoo.com/v8/finance/chart/{yahoo_symbol(ticker)}?range={yrange}&interval=1d",
            BROWSER_UA, timeout=20, retries=1))
        bars = [b for b in bars if b["date"] >= first]
        if len(bars) >= min_bars:
            return bars
        errors.append("Yahoo: too little data")
    except Exception as e:
        errors.append(f"Yahoo: {e}")
    raise RuntimeError("; ".join(errors))


def rsi_series(closes: list[float], n: int = 14) -> list:
    """Wilder's RSI. Entries before the first full window are None."""
    out = [None] * len(closes)
    if len(closes) <= n:
        return out
    ch = [closes[i] - closes[i - 1] for i in range(1, len(closes))]
    ag = sum(max(c, 0) for c in ch[:n]) / n
    al = sum(max(-c, 0) for c in ch[:n]) / n

    def val(g: float, l: float) -> float:
        return 100.0 if l == 0 else 100 - 100 / (1 + g / l)
    out[n] = val(ag, al)
    for i in range(n, len(ch)):
        ag = (ag * (n - 1) + max(ch[i], 0)) / n
        al = (al * (n - 1) + max(-ch[i], 0)) / n
        out[i + 1] = val(ag, al)
    return out


def atr_pct(bars: list[dict], n: int = 14) -> float | None:
    """Typical daily move as a fraction of the price (average true range)."""
    trs = [max(bars[i]["high"] - bars[i]["low"], abs(bars[i]["high"] - bars[i - 1]["close"]),
               abs(bars[i]["low"] - bars[i - 1]["close"])) for i in range(1, len(bars))]
    if len(trs) < n:
        return None
    atr = sum(trs[:n]) / n
    for t in trs[n:]:
        atr = (atr * (n - 1) + t) / n
    return atr / bars[-1]["close"]


def market_is_healthy(spy: list[dict]) -> bool:
    closes = [b["close"] for b in spy]
    return len(closes) >= 200 and closes[-1] > sum(closes[-200:]) / 200


def evaluate_dip(bars: list[dict], cfg: dict) -> dict | None:
    """Returns a setup description if the latest bar is a bounce after a pullback in an uptrend."""
    if len(bars) < 221:
        return None
    closes, vols = [b["close"] for b in bars], [b["volume"] for b in bars]
    c = closes[-1]
    s50, s200 = sum(closes[-50:]) / 50, sum(closes[-200:]) / 200
    s200_old = sum(closes[-220:-20]) / 200
    if not (c > s200 and s50 > s200 and s200 > s200_old):          # 1) long-term uptrend
        return None
    if sum(closes[i] * vols[i] for i in range(-20, 0)) / 20 < cfg["scan_min_dollar_volume"]:
        return None                                                  # 2) easy to trade
    rsi = rsi_series(closes)
    r_now, r_prev = rsi[-1], rsi[-2]
    recent = [x for x in rsi[-5:-1] if x is not None]
    if r_now is None or r_prev is None or not recent:
        return None
    low_rsi = min(recent)
    if low_rsi > cfg["scan_rsi_dip"]:                                # 3) it really dipped
        return None
    if not (c > closes[-2] and r_now > r_prev):                      # 4) and has started to bounce
        return None
    if c > 0.97 * max(closes[-10:]):                                 # 5) a real pullback (3%+)
        return None
    if c < 0.85 * max(closes[-20:]):                                 # 6) not a falling knife (15%+)
        return None
    avg_vol = sum(vols[-21:-1]) / 20
    deep, support = low_rsi <= 30, c >= 0.97 * s50
    vol_up = avg_vol > 0 and vols[-1] > avg_vol
    score = deep + support + vol_up
    why = ["long-term uptrend (above rising 200-day average)",
           f"pulled back {1 - c / max(closes[-10:]):.1%} from its 10-day high and has started to bounce"]
    if deep:
        why.append(f"oversold dip (RSI fell to {low_rsi:.0f})")
    if support:
        why.append("holding near its 50-day average")
    if vol_up:
        why.append(f"bounce on higher volume ({vols[-1] / avg_vol:.1f}x the 20-day average)")
    return {"bot": "dip", "date": bars[-1]["date"], "close": c, "rsi_low": low_rsi, "rsi_now": r_now,
            "vs50": c / s50 - 1, "vs200": c / s200 - 1, "pullback": c / max(closes[-10:]) - 1,
            "atr": atr_pct(bars), "score": score, "why": why,
            "level": "STRONG" if score >= 3 else "MODERATE" if score == 2 else "WEAK"}


# --------------------------------------------------------------------------- #
# More scanner bots. Every buy bot needs the same safety checks first:
# a long-term uptrend and a stock that is easy to trade. The scan also pauses
# all of them when the overall market is weak.
# --------------------------------------------------------------------------- #
def uptrend_ok(bars: list[dict], cfg: dict) -> bool:
    if len(bars) < 221:
        return False
    closes, vols = [b["close"] for b in bars], [b["volume"] for b in bars]
    s50, s200 = sum(closes[-50:]) / 50, sum(closes[-200:]) / 200
    s200_old = sum(closes[-220:-20]) / 200
    if not (closes[-1] > s200 and s50 > s200 and s200 > s200_old):
        return False
    return sum(closes[i] * vols[i] for i in range(-20, 0)) / 20 >= cfg["scan_min_dollar_volume"]


def _level(score: int) -> str:
    return "STRONG" if score >= 3 else "MODERATE" if score == 2 else "WEAK"


def evaluate_breakout(bars: list[dict], cfg: dict) -> dict | None:
    """A new 3-month closing high on heavy volume, in an uptrend, not already stretched."""
    if not uptrend_ok(bars, cfg):
        return None
    closes, vols = [b["close"] for b in bars], [b["volume"] for b in bars]
    b, c = bars[-1], closes[-1]
    avg_vol = sum(vols[-21:-1]) / 20
    if c <= max(closes[-64:-1]):                                    # 1) a new 3-month closing high
        return None
    if not (avg_vol > 0 and vols[-1] >= 1.5 * avg_vol):             # 2) real buying interest
        return None
    s50 = sum(closes[-50:]) / 50
    if c > 1.15 * s50:                                              # 3) not already stretched far above its trend
        return None
    r = rsi_series(closes)[-1]
    if r is None or r >= 80:                                        # 4) not overheated
        return None
    if b["high"] > b["low"] and c < b["low"] + 0.5 * (b["high"] - b["low"]):
        return None                                                  # 5) closed in the top half of the day
    year_high = c >= max(closes[-252:])
    heavy = vols[-1] >= 2 * avg_vol
    base = (max(closes[-21:-1]) - min(closes[-21:-1])) / c < 0.08
    score = year_high + heavy + base
    why = ["long-term uptrend (above rising 200-day average)",
           f"closed at a new 3-month high on {vols[-1] / avg_vol:.1f}x its usual volume"]
    if year_high:
        why.append("also a new 1-year high")
    if base:
        why.append("it moved sideways for a month first, then broke out")
    return {"bot": "breakout", "date": b["date"], "close": c, "rsi_now": r, "vs50": c / s50 - 1,
            "atr": atr_pct(bars), "score": score, "why": why, "level": _level(score)}


def evaluate_trend(bars: list[dict], cfg: dict) -> dict | None:
    """The 20-day average crossed above the 50-day within the last 3 days, in a long-term uptrend."""
    if not uptrend_ok(bars, cfg):
        return None
    closes, vols = [b["close"] for b in bars], [b["volume"] for b in bars]
    c = closes[-1]
    def avg(n: int, back: int) -> float:
        end = len(closes) - back
        return sum(closes[end - n:end]) / n
    crossed = any(avg(20, k) > avg(50, k) and avg(20, k + 1) <= avg(50, k + 1) for k in range(3))
    if not crossed or avg(20, 0) <= avg(50, 0) or c <= avg(20, 0):
        return None
    r = rsi_series(closes)[-1]
    if r is None or not (50 <= r <= 70):                            # momentum is up, but not overheated
        return None
    avg_vol = sum(vols[-21:-1]) / 20
    near_high = c >= 0.95 * max(closes[-63:])
    vol_up = avg_vol > 0 and vols[-1] > avg_vol
    mid = 55 <= r <= 68
    score = near_high + vol_up + mid
    why = ["long-term uptrend (above rising 200-day average)",
           "its 20-day average just moved above its 50-day average, a sign the short-term trend turned up"]
    if near_high:
        why.append("price is within 5% of its 3-month high")
    if vol_up:
        why.append("on above-average volume")
    return {"bot": "trend", "date": bars[-1]["date"], "close": c, "rsi_now": r,
            "vs50": c / avg(50, 0) - 1, "atr": atr_pct(bars), "score": score, "why": why, "level": _level(score)}


def evaluate_gap(bars: list[dict], cfg: dict) -> dict | None:
    """Jumped 4%+ at the open on heavy volume (often earnings or big news) and held the gain all day."""
    if len(bars) < 221:
        return None
    closes, vols = [b["close"] for b in bars], [b["volume"] for b in bars]
    b, c, prev = bars[-1], closes[-1], closes[-2]
    s200 = sum(closes[-200:]) / 200
    if c <= s200 or sum(closes[i] * vols[i] for i in range(-20, 0)) / 20 < cfg["scan_min_dollar_volume"]:
        return None
    gap = b["open"] / prev - 1
    if gap < 0.04 or c < b["open"] or c < prev * 1.03:               # a real gap that did not fade
        return None
    avg_vol = sum(vols[-21:-1]) / 20
    if not (avg_vol > 0 and vols[-1] >= 2 * avg_vol):
        return None
    s50 = sum(closes[-50:]) / 50
    if c > 1.25 * s50:                                               # already far above its trend
        return None
    big = gap >= 0.06
    huge_vol = vols[-1] >= 3 * avg_vol
    strong_close = b["high"] > b["low"] and c >= b["low"] + 0.75 * (b["high"] - b["low"])
    score = big + huge_vol + strong_close
    why = [f"gapped up {gap:.1%} at the open and closed {c / prev - 1:+.1%} on the day, holding the gain",
           f"on {vols[-1] / avg_vol:.1f}x its usual volume (often earnings or big news)",
           "still above its 200-day average"]
    return {"bot": "gap", "date": b["date"], "close": c, "gap": gap, "vs50": c / s50 - 1,
            "atr": atr_pct(bars), "score": score, "why": why, "level": _level(score)}


# id -> (evaluate function, name shown in the app, word used in the alert title, one-line description)
BOTS = {
    "dip": (evaluate_dip, "Dip Bot", "dip-buy", "Strong stocks that pulled back and have started to bounce."),
    "breakout": (evaluate_breakout, "Breakout Bot", "breakout", "Stocks closing at a new 3-month high on heavy volume."),
    "trend": (evaluate_trend, "Trend Bot", "trend", "Stocks whose 20-day average just crossed above the 50-day."),
    "gap": (evaluate_gap, "Gap Bot", "gap-up", "Stocks that jump 4% or more on heavy volume and hold it, often after earnings."),
}


def enabled_bots(cfg: dict, db: sqlite3.Connection | None = None) -> list[str]:
    off = set()
    if db is not None:
        try:
            off = set(json.loads(meta_get(db, "bots_off", "[]")))
        except ValueError:
            pass
    return [b for b in BOTS if b in [x.lower() for x in cfg["scan_bots"]] and b not in off]


def trade_line(cfg: dict) -> str:
    return (f"Sell rules: stop-loss -{cfg['stop_loss_pct']:.0%}, profit target +{cfg['take_profit_pct']:.0%}, "
            f"trailing stop {cfg['trailing_stop_pct']:.0%} from the peak, max {cfg['max_hold_days']} days"
            + (", or earlier if it looks overbought or its short-term trend breaks." if cfg.get("exit_signals") else "."))


def format_bot_alert(ticker: str, hits: list, cfg: dict) -> str:
    """hits: [(bot_id, setup)]. One hit gets its own wording; two or more become one stronger alert."""
    icon = {"STRONG": "🟢", "MODERATE": "🟡", "WEAK": "⚪"}
    if len(hits) == 1:
        bot, e = hits[0]
        if bot == "dip":
            return format_dip_alert(ticker, e, cfg)
        head = f"{icon[e['level']]} {e['level']} {BOTS[bot][2]} idea: {ticker}"
        why = e["why"]
    else:
        names = " and ".join(BOTS[b][1] for b, _ in hits)
        e = hits[0][1]
        head = f"🟢 STRONG idea confirmed by {len(hits)} bots: {ticker}"
        why = [f"{BOTS[b][1]}: {'; '.join(x['why'][1:] or x['why'])}" for b, x in hits]
        head_note = f"Found by {names}. When more than one bot agrees, I treat it as stronger."
    lines = [head, f"Price {fp(ticker, e['close'])} (close of {e['date']})"
             + (f" | typical daily move ±{e['atr']:.1%}" if e.get("atr") else "")]
    if len(hits) > 1:
        lines.append(head_note)
    lines += [("Why: " + "; ".join(why)) if len(hits) == 1 else ("Why:\n  " + "\n  ".join(why)),
              trade_line(cfg),
              "Check the company's next earnings date first: a report can move the price sharply either way. "
              "Not financial advice."]
    return "\n".join(lines)


def format_dip_alert(ticker: str, e: dict, cfg: dict) -> str:
    icon = {"STRONG": "🟢", "MODERATE": "🟡", "WEAK": "⚪"}[e["level"]]
    lines = [f"{icon} {e['level']} dip-buy idea: {ticker}",
             f"Price {fp(ticker, e['close'])} (close of {e['date']}) | RSI dipped to {e['rsi_low']:.0f}, now {e['rsi_now']:.0f} | "
             f"pullback {e['pullback']:.1%} from the 10-day high",
             f"Trend: {e['vs50']:+.1%} vs 50-day average, {e['vs200']:+.1%} vs 200-day average"
             + (f" | typical daily move ±{e['atr']:.1%}" if e["atr"] else ""),
             "Why: " + "; ".join(e["why"]),
             trade_line(cfg),
             "Check the company's next earnings date first: a report can move the price sharply either way. "
             "A dip can keep falling. Not financial advice."]
    return "\n".join(lines)


def market_info(spy: list[dict]) -> dict:
    closes = [b["close"] for b in spy]
    s200 = sum(closes[-200:]) / 200
    return {"state": "up" if closes[-1] > s200 else "down", "spy": round(closes[-1], 2), "vs200": round(closes[-1] / s200 - 1, 4),
            "chg20": round(closes[-1] / closes[-21] - 1, 4) if len(closes) > 21 else 0.0,
            "swing": round(atr_pct(spy) or 0.0, 4), "bar": spy[-1]["date"]}


def run_scan(cfg: dict, db: sqlite3.Connection, notify, force: bool = False) -> int | None:
    """Scan once with every bot that is on. Returns the number of alerts, or None if today's prices are not published yet."""
    spy = fetch_history("SPY")  # raises if no price data is reachable
    bar_date = spy[-1]["date"]
    if not force:
        if bar_date == meta_get(db, "scan_bar"):
            log("scan: today's prices are not published yet")
            return None
        if (utc_now().date() - datetime.fromisoformat(bar_date).date()).days > 5:
            raise RuntimeError(f"price data looks stale (latest bar {bar_date})")
    info = market_info(spy)
    healthy = info["state"] == "up"
    meta_set(db, "market_info", json.dumps(info))
    state, prev = info["state"], meta_get(db, "market_state")
    if state != prev:
        meta_set(db, "market_state", state)
        if not healthy:
            notify("📉 The US market (S&P 500) is below its 200-day average, a weak phase. "
                   "I'm pausing all buy ideas for US stocks until it recovers (other countries are checked against their own market). "
                   "Insider alerts and sell signals keep running.")
        elif prev == "down":
            notify("📈 The US market is back above its 200-day average. Buy ideas for US stocks are on again.")
    meta_set(db, "scan_bar", bar_date)

    bots = enabled_bots(cfg, db)
    held = {p["ticker"] for p in open_positions(db)}
    hits, failed = [], 0
    tickers = scan_universe(cfg)
    health = {"": info}                              # market ending -> that market's health (None: no index, no filter)
    regions = {"US": info}
    paused = set()
    for t in tickers:
        if t in held:
            continue
        suf = market_suffix(t)
        if suf not in health:
            index = MARKETS[suf][1]
            try:
                health[suf] = market_info(fetch_history(index)) if index else None
            except Exception as e:
                log(f"scan: no {MARKETS[suf][0]} market data ({str(e)[:60]}), checking its stocks without a market filter")
                health[suf] = None
            if health[suf]:
                regions[MARKETS[suf][0]] = health[suf]
        if health[suf] and health[suf]["state"] == "down":
            paused.add(MARKETS[suf][0])
            continue
        last = meta_get(db, "scan_last_" + t)
        if last and (datetime.fromisoformat(bar_date) - datetime.fromisoformat(last)).days < cfg["scan_cooldown_days"]:
            continue
        try:
            time.sleep(0.15)
            bars = fetch_history(t)
        except Exception:
            failed += 1
            continue
        if (datetime.fromisoformat(bar_date) - datetime.fromisoformat(bars[-1]["date"])).days > 4:
            failed += 1                                   # no recent prices (delisted or a long holiday)
            continue
        cfg_t = {**cfg, "scan_min_dollar_volume": min_turnover(cfg, t)}   # money in the stock's own currency
        found = [(b, e) for b in bots if (e := BOTS[b][0](bars, cfg_t))]
        if found:
            hits.append((t, found))
    meta_set(db, "regions_info", json.dumps(regions))
    log(f"scan: {len(tickers)} stocks, {failed} unavailable, {len(hits)} setup(s) found ({', '.join(bots)})"
        + (f"; paused, weak market: {', '.join(sorted(paused))}" if paused else ""))
    # best first: more bots agreeing, then the higher score, then (for dips) the deeper dip
    hits.sort(key=lambda h: (-len(h[1]), -max(e["score"] for _, e in h[1]),
                             min((e.get("rsi_low", 50) for _, e in h[1]), default=50)))

    sent = 0
    for t, found in hits[: cfg["scan_max_alerts"]]:
        msg = format_bot_alert(t, found, cfg)
        close = found[0][1]["close"]
        bought_cmd = how_to(f"bought {t} <price you paid> <shares>")
        checks, ok = verify_idea(t, close, cfg)
        bump(db, "check_ideas")
        if not ok:
            bump(db, "check_flagged")
        msg += "\nCheck Bot (second look):\n  " + "\n  ".join(checks)
        if not ok:
            head, _, rest = msg.partition("\n")
            msg = re.sub(r"^\S+ (STRONG|MODERATE|WEAK)", "⚠️ CAUTION", head) + "\n" + rest
            msg += "\nI'd skip this one, so I'm not tracking a trade for it."
        elif cfg["auto_track"]:
            shares = open_tracked_position(db, {"ticker": t, "company": t}, close, cfg, bot="+".join(b for b, _ in found))
            msg += (f"\nTracking a ${cfg['position_usd']:,} trade ({shares} shares at ~{fp(t, close)}, the close). "
                    f"I'll send the sell alert and the % result. Your real price will differ a little.\n"
                    f"Bought it for real? {bought_cmd}")
        if ok and not cfg["auto_track"]:
            msg += f"\nIf you buy it, log it so I can tell you when to sell:\n  {bought_cmd}"
        notify(msg)
        meta_set(db, "scan_last_" + t, bar_date)
        sent += 1
    return sent


def run_exit_signals(cfg: dict, db: sqlite3.Connection, notify) -> int:
    """Daily check of open trades for two extra sell signals (on top of the stop-loss, target, trailing stop
    and time limit): overbought after a gain, and the short-term trend breaking."""
    if not cfg["exit_signals"]:
        return 0
    acted = 0
    for pos in open_positions(db):
        if pos["sell_alerted"] or not is_swing(pos):
            continue
        try:
            time.sleep(0.3)
            bars = fetch_history(pos["ticker"])
        except Exception:
            continue
        reason = exit_signal(bars, pos)
        if reason:
            price = bars[-1]["close"]
            trigger_sell(db, pos, price, reason, notify)
            acted += 1
    return acted


def exit_signal(bars: list[dict], pos: dict) -> str | None:
    """Reason to sell from the daily chart, or None. Used live and in the backtest."""
    closes = [b["close"] for b in bars]
    if len(closes) < 60:
        return None
    entry_day = pos["entry_at"][:10]
    ret = closes[-1] / pos["entry_price"] - 1
    r = rsi_series(closes)[-1]
    if r is not None and r >= 75 and ret >= 0.03:
        return f"overbought (RSI {r:.0f}) after a {ret:+.1%} gain; the price rose fast, a common time to take profit"
    if held_days(pos) >= 2:
        sma20 = lambda i: sum(closes[i - 19:i + 1]) / 20
        n = len(closes)
        was_above = any(closes[i] >= sma20(i) for i in range(n - 1) if bars[i]["date"] > entry_day and i >= 19)
        if was_above and closes[-1] < sma20(n - 1):
            return "it closed below its 20-day average after being above it, so the short-term trend broke"
    return None


# --------------------------------------------------------------------------- #
# Check Bot: a second look at every buy idea and at the prices in your trades
# --------------------------------------------------------------------------- #
def bump(db: sqlite3.Connection, key: str, n: int = 1) -> None:
    meta_set(db, key, int(meta_get(db, key, "0") or 0) + n)


def yahoo_price(ticker: str) -> float | None:
    """A second, independent live price (Yahoo), so one bad data source can't fool us."""
    try:
        raw = http_get(f"https://query1.finance.yahoo.com/v8/finance/chart/{yahoo_symbol(ticker)}"
                       "?range=1d&interval=1d", BROWSER_UA, timeout=10, retries=0)
        px = json.loads(raw)["chart"]["result"][0]["meta"]["regularMarketPrice"]
        return float(px) if px else None
    except Exception:
        return None


def verify_idea(ticker: str, close: float, cfg: dict) -> tuple[list[str], bool]:
    """Second look at a buy idea before it is sent. Returns (lines for the alert, okay_to_track).
    Checks the live price against the close the idea was based on (two sources) and the latest news."""
    lines, ok = [], True
    quotes = [q for q in ((fetch_price(ticker), yahoo_price(ticker)) if not market_suffix(ticker) else (yahoo_price(ticker),)) if q]
    if not quotes:
        lines.append("Couldn't double-check the live price right now (no price source answered).")
    else:
        if len(quotes) == 2 and abs(quotes[0] / quotes[1] - 1) > 0.03:
            lines.append(f"⚠️ My two price sources disagree ({fp(ticker, quotes[0])} vs {fp(ticker, quotes[1])}). "
                         "Look the price up yourself before buying.")
            ok = False
        else:
            q = quotes[-1]
            diff = q / close - 1
            if abs(diff) > 0.05:
                lines.append(f"⚠️ The live price ({fp(ticker, q)}) is {diff:+.1%} from the close this idea was based on "
                             f"({fp(ticker, close)}). It has already moved, so don't chase it.")
                ok = False
            else:
                lines.append(f"✔ Live price {fp(ticker, q)} matches the close ({fp(ticker, close)}), {diff:+.1%}.")
    try:
        news = fetch_news(ticker, ticker, cfg["news_hours"])
        if news["label"] == "negative" and news["neg"] - news["pos"] >= 2:
            bad = [t for t, sc in news["items"] if sc < 0][:2]
            lines.append("⚠️ Recent news looks negative: " + "; ".join(t[:90] for t in bad))
            ok = False
        else:
            lines.append("✔ No clearly negative news in the last %d hours." % cfg["news_hours"])
    except Exception:
        lines.append("Couldn't check the news right now.")
    return lines, ok


def market_price_note(ticker: str, price: float) -> str:
    """For a trade you log by hand: warn if the price you typed is far from the market price (a typo?)."""
    try:
        q = fetch_price(ticker) or yahoo_price(ticker)
    except Exception:
        q = None
    if q and abs(price / q - 1) > 0.10:
        return (f"\n⚠️ Check Bot: {fp(ticker, price)} is {price / q - 1:+.0%} from the latest price ({fp(ticker, q)}). "
                f"Typo? If so, send  sold {ticker.upper()} {price:g}  and then log it again with the right price.")
    return ""


def run_trade_audit(cfg: dict, db: sqlite3.Connection, notify) -> int:
    """Re-checks recently closed trades against the daily prices: was the entry and exit price really
    traded that day, and does the profit add up? Each trade is audited once. Returns the number flagged."""
    done = set(json.loads(meta_get(db, "audited_ids", "[]")))
    since = (utc_now() - timedelta(days=14)).isoformat(timespec="seconds")
    flagged = 0
    rows = [dict(r) for r in db.execute("SELECT * FROM positions WHERE status='closed' AND exit_at>=? AND COALESCE(kind, 'swing') <> 'crypto' ORDER BY id", (since,))]
    for pos in [r for r in rows if r["id"] not in done][:15]:
        try:
            time.sleep(0.3)
            bars = {b["date"]: b for b in fetch_history(pos["ticker"], 60, min_bars=20)}
        except Exception:
            continue                                   # try again on the next daily run
        problems = []
        for label, px, at in (("bought", pos["entry_price"], pos["entry_at"]), ("sold", pos["exit_price"], pos["exit_at"])):
            b = bars.get(at[:10])
            if b and not (b["low"] * 0.98 <= px <= b["high"] * 1.02):
                problems.append(f"you {label} at {fp(pos['ticker'], px)} on {at[:10]}, but that day's range was {fp(pos['ticker'], b['low'])} to {fp(pos['ticker'], b['high'])}")
        if abs((pos["exit_price"] - pos["entry_price"]) * pos["shares"] / usd_rate(pos["ticker"]) - pos["pnl"]) > 0.02:
            problems.append("the profit doesn't match the prices")
        done.add(pos["id"])
        bump(db, "audit_checked")
        if problems:
            flagged += 1
            bump(db, "audit_flagged")
            notify(f"⚠️ Check Bot: please double-check your {pos['ticker']} trade: " + "; ".join(problems)
                   + ". If a price was a typo, the reported % may be wrong.")
    meta_set(db, "audited_ids", json.dumps(sorted(done)[-200:]))
    return flagged


def maybe_scan(cfg: dict, db: sqlite3.Connection, notify) -> None:
    """Run the daily scan after the US market has closed (weekdays, 21:45 UTC or later), once per day."""
    if not cfg["scan_enabled"]:
        return
    now = utc_now()
    if now.weekday() >= 5 or (now.hour, now.minute) < (21, 45):
        return
    today = now.strftime("%Y-%m-%d")
    if meta_get(db, "scan_done") == today:
        return
    try:
        n = run_scan(cfg, db, notify)
    except Exception as e:
        day, _, count = meta_get(db, "scan_fail").partition(":")
        count = int(count or 0) + 1 if day == today else 1
        meta_set(db, "scan_fail", f"{today}:{count}")
        log(f"scan failed ({count} today): {e}")
        if count == 6:
            notify("⚠️ I couldn't download price data for today's scan. I'll keep trying until midnight (UTC).")
        return
    if n is not None:
        meta_set(db, "scan_done", today)
        log(f"scan done, {n} buy idea(s) sent")
        try:
            log(f"exit check done, {run_exit_signals(cfg, db, notify)} sell signal(s)")
        except Exception as e:
            log(f"exit check failed: {e}")
        try:
            log(f"trade audit done, {run_trade_audit(cfg, db, notify)} trade(s) flagged")
        except Exception as e:
            log(f"trade audit failed: {e}")


def cmd_scan(cfg: dict) -> None:
    n = run_scan(cfg, init_db(), make_notifier(cfg), force=True)
    print(f"Scan finished: {n} buy idea(s).")


# --------------------------------------------------------------------------- #
# Day trading: 15-minute candles, trades opened and closed the same day
# --------------------------------------------------------------------------- #
DAY_BOTS = {
    "orb": ("Opening Range Bot", "Stocks that break above the high of their first 30 minutes on heavy volume."),
    "vwap": ("VWAP Bot", "Stocks that are up on the day, dipped under the day's average price (VWAP) and just climbed back above it."),
    "gapgo": ("Gap-and-Go Bot", "Stocks that gapped up at the open, held the gap and are now breaking to a new high of the day."),
}
DAY_EXTRA_US = ("AMD PLTR COIN MSTR SMCI UBER SHOP PYPL SNOW CRWD PANW MU INTC BAC WFC C F GM RIVN SOFI HOOD RBLX DKNG "
                "ROKU ABNB DIS NKE BA CAT GE QCOM TXN AMAT LRCX ARM MRVL SNAP PINS ENPH FSLR MARA RIOT")
# UTC minutes after midnight between which a market is worth checking. Summer time moves the real hours by
# an hour, so the windows are wide; the candles themselves tell whether the market is really open.
DAY_WINDOWS = {"US": (13 * 60 + 30, 21 * 60 + 5), "Canada": (13 * 60 + 30, 21 * 60 + 5),
               "UK": (7 * 60, 16 * 60 + 35), "Germany": (7 * 60, 16 * 60 + 35), "France": (7 * 60, 16 * 60 + 35),
               "Netherlands": (7 * 60, 16 * 60 + 35), "Switzerland": (7 * 60, 16 * 60 + 35)}
SUFFIX_OF = {v[0]: k for k, v in MARKETS.items()}
CANDLE = 900  # seconds in one 15-minute candle


def tz_of(cfg: dict):
    try:
        from zoneinfo import ZoneInfo
        return ZoneInfo(cfg.get("timezone") or "UTC")
    except Exception:
        return timezone.utc


def hm(cfg: dict, ts: float) -> str:
    """A clock time in your time zone, e.g. 16:45 (marked UTC if the time zone database is missing)."""
    tz = tz_of(cfg)
    return datetime.fromtimestamp(ts, tz).strftime("%H:%M") + (" UTC" if tz is timezone.utc else "")


def parse_yahoo_intraday(raw: bytes) -> dict:
    """15-minute candles grouped into trading days, plus the live price and the session hours."""
    res = json.loads(raw)["chart"]["result"][0]
    meta = res.get("meta") or {}
    q = res["indicators"]["quote"][0]
    vols = q.get("volume") or []
    bars = []
    for i, ts in enumerate(res.get("timestamp") or []):
        try:
            o, h, l, c = q["open"][i], q["high"][i], q["low"][i], q["close"][i]
        except (KeyError, IndexError):
            continue
        if None in (o, h, l, c):
            continue
        bars.append({"t": int(ts), "open": float(o), "high": float(h), "low": float(l), "close": float(c),
                     "volume": float(vols[i]) if i < len(vols) and vols[i] else 0.0})
    bars.sort(key=lambda b: b["t"])
    off = int(meta.get("gmtoffset") or 0)
    sessions, days = [], []
    for b in bars:
        d = (b["t"] + off) // 86400
        if days and days[-1] == d:
            sessions[-1].append(b)
        else:
            days.append(d)
            sessions.append([b])
    reg = (meta.get("currentTradingPeriod") or {}).get("regular") or {}
    live = meta.get("regularMarketPrice")
    return {"sessions": sessions, "days": days, "off": off, "live": float(live) if live else None,
            "start": reg.get("start"), "end": reg.get("end")}


def fetch_intraday(ticker: str, rng: str = "10d") -> dict:
    return parse_yahoo_intraday(http_get(
        f"https://query1.finance.yahoo.com/v8/finance/chart/{yahoo_symbol(ticker)}?range={rng}&interval=15m",
        BROWSER_UA, timeout=15, retries=1))


def session_len(data: dict) -> int:
    """How many 15-minute candles a full trading day has on this exchange."""
    if data.get("start") and data.get("end") and data["days"] and data["end"] > data["start"] \
            and (data["end"] + data["off"]) // 86400 == data["days"][-1]:
        return max(8, round((data["end"] - data["start"]) / CANDLE))
    prior = [len(s) for s in data["sessions"][:-1]]
    return max(prior) if prior else 26


def session_end(data: dict, first_t: int) -> float:
    if data.get("end") and data["days"] and (data["end"] + data["off"]) // 86400 == data["days"][-1]:
        return float(data["end"])
    return first_t + session_len(data) * CANDLE


def idx_state(prev_close: float, S: list[dict]) -> dict:
    """Is the market itself holding up today? Not more than 0.25% under its open and 1% under yesterday's close."""
    c = S[-1]["close"]
    return {"ok": c / S[0]["open"] - 1 > -0.0025 and c / prev_close - 1 > -0.01,
            "chg_open": c / S[0]["open"] - 1, "chg_prev": c / prev_close - 1}


def day_ctx(prior: list[list[dict]], S: list[dict], n_total: int, ticker: str = "") -> dict | None:
    """The numbers the day bots look at, using only candles up to the last one in S (today's finished candles)."""
    prior = [p for p in prior if p][-8:]
    if len(S) < 2 or len(prior) < 3:
        return None
    i = len(S) - 1
    cumv = cumpv = 0.0
    vwap = []
    for b in S:
        cumv += b["volume"]
        cumpv += (b["high"] + b["low"] + b["close"]) / 3 * b["volume"]
        vwap.append(cumpv / cumv if cumv > 0 else b["close"])
    if cumv <= 0:
        return None
    mean = lambda xs: sum(xs) / len(xs)
    cum_ref = [sum(b["volume"] for b in ps[:i + 1]) for ps in prior if len(ps) > i]
    bar_ref = [ps[i]["volume"] for ps in prior if len(ps) > i]
    first_ref = [ps[0]["volume"] for ps in prior]
    ratio = lambda x, ref: x / mean(ref) if len(ref) >= 3 and mean(ref) > 0 else None
    trs = []
    for seq in (prior[-1], S):
        for k in range(1, len(seq)):
            trs.append(max(seq[k]["high"] - seq[k]["low"], abs(seq[k]["high"] - seq[k - 1]["close"]),
                           abs(seq[k]["low"] - seq[k - 1]["close"])))
    if len(trs) < 8:
        return None
    atr = mean(trs[-14:])
    prev_close = prior[-1][-1]["close"]
    c = S[-1]["close"]
    if atr <= 0 or prev_close <= 0 or c <= 0:
        return None
    return {"ticker": ticker, "S": S, "i": i, "vwap": vwap, "prev_close": prev_close, "gap": S[0]["open"] / prev_close - 1,
            "atr": atr, "atr_pct": atr / c, "left": n_total - 1 - i,
            "rvol_cum": ratio(cumv, cum_ref), "rvol_bar": ratio(S[-1]["volume"], bar_ref), "rvol_first": ratio(S[0]["volume"], first_ref),
            "turnover": mean([sum(b["close"] * b["volume"] for b in ps) for ps in prior]), "mkt_chg": 0.0}


def day_gate(ctx: dict, cfg: dict) -> bool:
    """Only liquid stocks with a sensible price and a daily swing big enough to trade, but not wild."""
    t = ctx["ticker"]
    need = min_turnover(cfg, t) * (1.0 if not market_suffix(t) else 0.4)     # Yahoo reports thinner volume outside the US
    return (ctx["turnover"] >= need and ctx["S"][-1]["close"] / usd_rate(t) >= 5
            and 0.0015 <= ctx["atr_pct"] <= 0.03)


def _day_level(score: int) -> str:
    return "STRONG" if score >= 80 else "MODERATE"


def day_setup(ctx: dict, cfg: dict, stop: float, why: list[str], score: int) -> dict | None:
    c = ctx["S"][-1]["close"]
    if stop >= c:
        return None
    risk = c - stop
    if not 0.0025 <= risk / c <= 0.025:          # too tight to survive normal noise, or too wide to be worth it
        return None
    target = c + cfg["day_target_r"] * risk
    return {"entry": c, "stop": stop, "target": target, "risk_pct": risk / c, "reward_pct": target / c - 1, "why": why,
            "score": score, "level": _day_level(score), "t": ctx["S"][-1]["t"]}


def evaluate_orb(ctx: dict, cfg: dict) -> dict | None:
    S, i, t = ctx["S"], ctx["i"], ctx["ticker"]
    if i < 3 or i > 10 or ctx["left"] < 5:
        return None
    orh, orl = max(b["high"] for b in S[:2]), min(b["low"] for b in S[:2])
    b = S[i]
    c = b["close"]
    if c <= orh or any(x["close"] > orh for x in S[2:i]) or c - orh > ctx["atr"]:   # must be the first close above, not chased
        return None
    if not 0.003 <= (orh - orl) / c <= 0.03 or c <= ctx["vwap"][i]:
        return None
    rng = b["high"] - b["low"]
    avg_v = sum(x["volume"] for x in S[:i]) / i
    if rng <= 0 or (c - b["low"]) / rng < 0.6 or avg_v <= 0 or b["volume"] < 1.3 * avg_v:
        return None
    if (ctx["rvol_cum"] is not None and ctx["rvol_cum"] < 1.0) or not -0.05 <= ctx["gap"] <= 0.08:
        return None
    stop = max(orl, c - 2 * ctx["atr"])
    score = (60 + (10 if b["volume"] >= 2 * avg_v else 0) + (10 if (ctx["rvol_cum"] or 0) >= 1.5 else 0)
             + (5 if (c - b["low"]) / rng >= 0.8 else 0) + (5 if ctx["mkt_chg"] > 0.003 else 0))
    why = [f"closed above the high of the first 30 minutes ({fp(t, orh)})",
           f"above the day's average price (VWAP {fp(t, ctx['vwap'][i])})",
           f"this candle's volume is {b['volume'] / avg_v:.1f}x the day's average candle"
           + (f", the day's volume so far is {ctx['rvol_cum']:.1f}x normal" if ctx["rvol_cum"] else "")]
    return day_setup(ctx, cfg, stop, why, score)


def evaluate_vwap(ctx: dict, cfg: dict) -> dict | None:
    S, i, v, t = ctx["S"], ctx["i"], ctx["vwap"], ctx["ticker"]
    if i < 4 or ctx["left"] < 5:
        return None
    b = S[i]
    c = b["close"]
    if not (c > v[i] and S[i - 1]["close"] <= v[i - 1]):                     # a fresh cross back above VWAP
        return None
    up = c / ctx["prev_close"] - 1
    if up < 0.003 or max(S[j]["high"] / v[j] - 1 for j in range(i)) < 0.006:  # up on the day, and clearly strong earlier
        return None
    rng = b["high"] - b["low"]
    avg_v = sum(x["volume"] for x in S[max(0, i - 5):i]) / len(S[max(0, i - 5):i])
    if rng <= 0 or (c - b["low"]) / rng < 0.5 or avg_v <= 0 or b["volume"] < 1.1 * avg_v:
        return None
    stop = min(x["low"] for x in S[max(0, i - 3):i + 1]) * 0.9995
    score = (60 + (10 if b["volume"] >= 1.8 * avg_v else 0) + (10 if (ctx["rvol_cum"] or 0) >= 1.3 else 0)
             + (5 if up >= 0.015 else 0) + (5 if ctx["mkt_chg"] > 0.003 else 0))
    why = [f"up {up:.1%} on the day, was trading well above its average price earlier",
           f"dipped under the day's average price (VWAP {fp(t, v[i])}) and has just closed back above it",
           f"this candle's volume is {b['volume'] / avg_v:.1f}x the last few candles"]
    return day_setup(ctx, cfg, stop, why, score)


def evaluate_gapgo(ctx: dict, cfg: dict) -> dict | None:
    S, i, v, t = ctx["S"], ctx["i"], ctx["vwap"], ctx["ticker"]
    gap = ctx["gap"]
    if not 2 <= i <= 8 or ctx["left"] < 5 or not 0.02 <= gap <= 0.12:
        return None
    if ctx["rvol_first"] is None or ctx["rvol_first"] < 2.0:                    # the open must have been busy
        return None
    pc = ctx["prev_close"]
    if any(x["close"] < pc * (1 + gap * 0.5) for x in S):                       # the gap must be holding
        return None
    b = S[i]
    c = b["close"]
    rng = b["high"] - b["low"]
    if c <= max(x["high"] for x in S[:i]) or c <= v[i] or rng <= 0 or (c - b["low"]) / rng < 0.5:
        return None
    stop = min(x["low"] for x in S[max(0, i - 2):i + 1]) * 0.9995
    score = (60 + (10 if ctx["rvol_first"] >= 3 else 0) + (10 if gap >= 0.04 else 0)
             + (5 if (c - b["low"]) / rng >= 0.8 else 0) + (5 if ctx["mkt_chg"] > 0.003 else 0))
    why = [f"gapped up {gap:.1%} at the open and has held the gap",
           f"the first candle's volume was {ctx['rvol_first']:.1f}x normal",
           f"now closing at a new high of the day, above VWAP ({fp(t, v[i])})"]
    return day_setup(ctx, cfg, stop, why, score)


DAY_EVAL = {"orb": evaluate_orb, "vwap": evaluate_vwap, "gapgo": evaluate_gapgo}


def enabled_day_bots(cfg: dict, db: sqlite3.Connection | None = None) -> list[str]:
    if not cfg["day_enabled"]:
        return []
    off = set()
    if db is not None:
        try:
            off = set(json.loads(meta_get(db, "bots_off", "[]")))
        except ValueError:
            pass
    return [b for b in DAY_BOTS if b in [x.lower() for x in cfg["day_bots"]] and b not in off]


def day_universe(cfg: dict, suf: str) -> list[str]:
    if cfg["day_tickers"]:
        return [t.upper() for t in cfg["day_tickers"] if market_suffix(t.upper()) == suf]
    if suf == "":
        return list(dict.fromkeys(DEFAULT_SCAN + DAY_EXTRA_US.split()))
    return [f"{t}.{suf}" for t in GLOBAL_SCAN.get(suf, "").split()]


def day_markets_open(cfg: dict, now: datetime) -> list[str]:
    """The enabled day-trading markets that are inside their trading window right now."""
    if now.weekday() >= 5:
        return []
    mins = now.hour * 60 + now.minute
    want = {m.lower() for m in cfg["day_markets"]}
    return [m for m, (a, b) in DAY_WINDOWS.items() if m.lower() in want and a <= mins <= b]


def bot_names(bots: list[str]) -> str:
    return " + ".join((DAY_BOTS.get(b) or CRYPTO_BOTS[b])[0] for b in bots if b in DAY_BOTS or b in CRYPTO_BOTS)


def format_day_alert(cfg: dict, ticker: str, found: list, e: dict, live: float | None, now_ts: float,
                     end_ts: float, mkt_line: str) -> str:
    icon = {"STRONG": "🟢", "MODERATE": "🟡"}
    names = bot_names([b for b, _ in found])
    if len(found) == 1:
        head = f"⚡ {e['level']} day-trade idea: {ticker} ({names})"
    else:
        head = f"⚡ STRONG day-trade idea confirmed by {len(found)} bots: {ticker}"
    age = max(0, round((now_ts - (e["t"] + CANDLE)) / 60))
    lines = [head]
    if len(found) > 1:
        lines.append(f"Buy around {fp(ticker, live or e['entry'])} | candle closed {hm(cfg, e['t'] + CANDLE)} (data about {age} min old)")
        lines.append(f"Found by {' and '.join(DAY_BOTS[b][0] for b, _ in found)}. When more than one bot agrees, I treat it as stronger.")
    else:
        lines.append(f"Buy around {fp(ticker, live or e['entry'])} | candle closed {hm(cfg, e['t'] + CANDLE)} (data about {age} min old)")
    lines.append(f"Stop-loss {fp(ticker, e['stop'])} ({-e['risk_pct']:.1%}) | Target {fp(ticker, e['target'])} ({e['reward_pct']:+.1%}) "
                 f"| the target is {cfg['day_target_r']:g}x the risk")
    lines.append(f"Close it by {hm(cfg, end_ts - cfg['day_close_minutes'] * 60)} even if neither level is hit "
                 f"(the market closes {hm(cfg, end_ts)}).")
    why = [f"{DAY_BOTS[b][0]}: {'; '.join(x['why'])}" for b, x in found] if len(found) > 1 else e["why"]
    lines.append(("Why:\n  " + "\n  ".join(why)) if len(found) > 1 else "Why: " + "; ".join(why))
    if mkt_line:
        lines.append(mkt_line)
    lines.append("Put the stop and the target in as orders with your broker right away. My alerts can arrive minutes late, "
                 "and day trades move fast.")
    return "\n".join(lines)


def day_verify(ticker: str, e: dict, live: float | None, cfg: dict) -> tuple[list[str], bool]:
    """Check Bot for day trades: has the price already run, and is there negative news?"""
    lines, ok = [], True
    if live:
        if live <= e["stop"] or live >= e["entry"] + 0.5 * (e["target"] - e["entry"]):
            lines.append(f"⚠️ The live price ({fp(ticker, live)}) has already moved a long way from the signal "
                         f"({fp(ticker, e['entry'])}). Don't chase it.")
            ok = False
        else:
            lines.append(f"✔ Live price {fp(ticker, live)} is still close to the signal ({fp(ticker, e['entry'])}).")
    else:
        lines.append("Couldn't double-check the live price right now.")
    try:
        news = fetch_news(ticker, ticker, cfg["news_hours"])
        if news["label"] == "negative" and news["neg"] - news["pos"] >= 2:
            bad = [t for t, sc in news["items"] if sc < 0][:2]
            lines.append("⚠️ Recent news looks negative: " + "; ".join(t[:90] for t in bad))
            ok = False
        else:
            lines.append("✔ No clearly negative news in the last %d hours." % cfg["news_hours"])
    except Exception:
        lines.append("Couldn't check the news right now.")
    return lines, ok


def open_day_trade(db: sqlite3.Connection, cfg: dict, ticker: str, entry: float, e: dict, bots: list[str],
                   exit_by_ts: float, now_ts: float) -> float:
    shares = round(cfg["position_usd"] * usd_rate(ticker) / entry, 4)
    db.execute("INSERT INTO positions (ticker, company, shares, entry_price, entry_at, peak, last_price, manual, bot, kind, stop, "
               "target, exit_by, mgmt_t) VALUES (?, ?, ?, ?, ?, ?, ?, 0, ?, 'day', ?, ?, ?, ?)",
               (ticker, ticker, shares, entry, datetime.fromtimestamp(now_ts, timezone.utc).isoformat(timespec="seconds"), entry, entry,
                "+".join(bots), e["stop"], e["target"],
                datetime.fromtimestamp(exit_by_ts, timezone.utc).isoformat(timespec="seconds"), int(now_ts // CANDLE * CANDLE)))
    db.commit()
    return shares


def day_totals(db: sqlite3.Connection, since: str = "", kind: str = "day") -> dict:
    r = db.execute("SELECT COUNT(*), COALESCE(SUM(pnl > 0), 0), COALESCE(SUM(pnl), 0) FROM positions "
                   "WHERE status='closed' AND kind=? AND exit_at>=?", (kind, since)).fetchone()
    return {"n": r[0], "wins": int(r[1]), "pnl": float(r[2])}


def format_day_closed(cfg: dict, db: sqlite3.Connection, pos: dict, price: float, reason: str, pnl: float, ret: float,
                      exit_ts: float) -> str:
    icon = "✅" if pnl > 0 else "❌" if pnl < 0 else "➖"
    t = pos["ticker"]
    entry_ts = datetime.fromisoformat(pos["entry_at"]).timestamp()
    mins = max(0, round((exit_ts - entry_ts) / 60))
    today = datetime.fromtimestamp(exit_ts, timezone.utc).strftime("%Y-%m-%d")
    kind = pos.get("kind") or "day"
    label = "Crypto trade" if kind == "crypto" else "Day trade"
    td, al = day_totals(db, today, kind), day_totals(db, "", kind)
    return "\n".join([
        f"{icon} {label} closed: {t} ({bot_names(pos['bot'].split('+'))}) {ret:+.1%}",
        f"Reason: {reason}",
        f"Bought ~{fp(t, pos['entry_price'])} at {hm(cfg, entry_ts)}, sold ~{fp(t, price)} at {hm(cfg, exit_ts)} ({mins} min)",
        f"{icon} {'PROFIT' if pnl >= 0 else 'LOSS'}: {money(pnl)} ({ret:+.2%}) on a simulated ${cfg['position_usd']:,} trade",
        f"{label}s today: {td['n']} closed, {td['wins']} winner{'s' if td['wins'] != 1 else ''}, net {money(td['pnl'])}",
        f"All {label.lower()}s so far: {al['n']} closed, {al['wins']} winner{'s' if al['wins'] != 1 else ''}, net {money(al['pnl'])}",
        "Bought it for real and it's still open? Sell it now.",
        "Simulated: ignores fees, spreads and real-world fills. Not financial advice.",
    ])


def manage_day_trades(cfg: dict, db: sqlite3.Connection, notify, fetch=None, ts: float | None = None) -> int:
    """Follow every open day trade: stop, target, and closing before the market closes. Candles are checked in order
    (the stop first if one candle touched both), and the live price catches moves between candles."""
    fetch = fetch or fetch_intraday
    ts = utc_now().timestamp() if ts is None else ts
    closed = 0
    for pos in open_positions(db):
        if pos.get("kind") != "day" or pos["manual"]:
            continue
        try:
            data = fetch(pos["ticker"], "5d")
        except Exception:
            continue
        stop, target = pos["stop"], pos["target"]
        exit_by = datetime.fromisoformat(pos["exit_by"]).timestamp()
        bars = [b for ss in data["sessions"] for b in ss if b["t"] > (pos["mgmt_t"] or 0) and b["t"] + CANDLE <= ts]
        done = None
        for b in bars:
            if b["low"] <= stop:
                done = (min(b["open"], stop), "stop-loss hit", b["t"] + CANDLE)
            elif b["high"] >= target:
                done = (max(b["open"], target), "profit target reached", b["t"] + CANDLE)
            elif b["t"] + CANDLE >= exit_by:
                done = (b["close"], "closing before the market closes (day trades are not held overnight)", b["t"] + CANDLE)
            if done:
                break
        live = data.get("live")
        if not done:
            now_px = live or (bars[-1]["close"] if bars else None)
            if now_px:
                if ts >= exit_by:
                    done = (now_px, "closing before the market closes (day trades are not held overnight)", ts)
                elif live and live <= stop:
                    done = (live, "stop-loss hit (live price)", ts)
                elif live and live >= target:
                    done = (live, "profit target reached (live price)", ts)
        if done:
            price, reason, exit_ts = done
            pnl, ret = close_position(db, pos, price, reason)
            db.execute("UPDATE positions SET exit_at=? WHERE id=?",
                       (datetime.fromtimestamp(min(exit_ts, ts), timezone.utc).isoformat(timespec="seconds"), pos["id"]))
            db.commit()
            notify(format_day_closed(cfg, db, pos, price, reason, pnl, ret, min(exit_ts, ts)))
            closed += 1
        else:
            last = live or (bars[-1]["close"] if bars else pos["last_price"])
            db.execute("UPDATE positions SET last_price=?, peak=?, mgmt_t=? WHERE id=?",
                       (last, max(pos["peak"] or 0, last or 0), max([pos["mgmt_t"] or 0] + [b["t"] for b in bars]), pos["id"]))
            db.commit()
    return closed


def scan_day_market(cfg: dict, db: sqlite3.Connection, notify, market: str, expected: int, ts: float, fetch=None) -> int | None:
    """Look at one market's stocks after a new 15-minute candle closed. Returns the number of alerts, or None
    if the market isn't trading right now (or its data is late), so the next run should try again."""
    fetch = fetch or fetch_intraday
    suf = SUFFIX_OF[market]
    index = MARKETS[suf][1]
    info = json.loads(meta_get(db, "day_info", "{}") or "{}")
    state = None
    if index:                                            # the market's own index first: one request tells if it is open
        try:
            idata = fetch(index)
            today = int(ts + idata["off"]) // 86400
            if not idata["days"] or idata["days"][-1] != today or len(idata["sessions"]) < 2:
                return None
            IS = [b for b in idata["sessions"][-1] if b["t"] + CANDLE <= ts]
            if not IS or IS[-1]["t"] < expected - CANDLE:
                return None
            state = idx_state(idata["sessions"][-2][-1]["close"], IS)
        except Exception as ex:
            log(f"day: no {market} index data ({str(ex)[:60]}), checking its stocks without a market filter")
    bots = enabled_day_bots(cfg, db)
    info[market] = {"state": "unknown" if state is None else "up" if state["ok"] else "down", "at": int(ts),
                    "chg_open": round(state["chg_open"], 4) if state else 0.0}
    meta_set(db, "day_info", json.dumps(info))
    if not bots:
        return 0
    if state is not None and not state["ok"]:
        log(f"day: {market} is weak today ({state['chg_open']:+.2%} from its open), day-trade ideas paused")
        return 0
    from concurrent.futures import ThreadPoolExecutor
    tickers = day_universe(cfg, suf)

    def grab(t):
        try:
            return t, fetch(t)
        except Exception:
            return t, None
    with ThreadPoolExecutor(max_workers=6) as ex:
        got = dict(ex.map(grab, tickers))
    day_key = datetime.fromtimestamp(ts, timezone.utc).strftime("%Y-%m-%d")
    evaluated = {k: v for k, v in json.loads(meta_get(db, "day_evaluated", "{}") or "{}").items() if v > ts - 2 * 86400}
    sent_map = {k: v for k, v in json.loads(meta_get(db, "day_sent", "{}") or "{}").items() if k.startswith(day_key)}
    held = {p["ticker"] for p in open_positions(db)}
    hits, failed, stale, fresh = [], 0, 0, 0
    for t in tickers:
        data = got.get(t)
        if not data or not data["sessions"]:
            failed += 1
            continue
        if data["days"][-1] != int(ts + data["off"]) // 86400:
            stale += 1
            continue
        S = [b for b in data["sessions"][-1] if b["t"] + CANDLE <= ts]
        if not S or S[-1]["t"] < expected - CANDLE:
            stale += 1
            continue
        fresh += 1
        if evaluated.get(t, 0) >= S[-1]["t"]:
            continue
        evaluated[t] = S[-1]["t"]
        if t in held:
            continue
        ctx = day_ctx(data["sessions"][:-1], S, session_len(data), t)
        if not ctx or not day_gate(ctx, cfg):
            continue
        if state is not None:
            ctx["mkt_chg"] = state["chg_open"]
        done = sent_map.get(f"{day_key}:{t}", [])
        found = [(b, e) for b in bots if b not in done and (e := DAY_EVAL[b](ctx, cfg))]
        if found:
            found.sort(key=lambda x: -x[1]["score"])
            hits.append((t, found, data, S))
    log(f"day: {market}: {len(tickers)} stocks, {failed} unavailable, {stale} not trading or late, {len(hits)} setup(s) found")
    if len(tickers) >= 3 and failed >= max(3, int(0.8 * len(tickers))) and meta_get(db, "day_fail_" + market) != day_key:
        meta_set(db, "day_fail_" + market, day_key)
        notify(f"⚠️ I couldn't get 15-minute prices for {market} stocks just now ({failed} of {len(tickers)} failed). "
               "The price source (Yahoo) may be blocking GitHub's servers or having a bad moment. "
               "Day-trade alerts for this market won't work until that clears. I'll keep trying and won't repeat this today.")
    hits.sort(key=lambda h: (-len(h[1]), -h[1][0][1]["score"]))
    count_key = "day_count_" + day_key
    sent = 0
    for t, found, data, S in hits:
        if sent >= cfg["day_max_alerts_per_run"] or int(meta_get(db, count_key, "0") or 0) >= cfg["day_max_alerts_per_day"]:
            break
        e = found[0][1]
        live = data.get("live")
        end_ts = session_end(data, data["sessions"][-1][0]["t"])
        exit_by = end_ts - cfg["day_close_minutes"] * 60
        if ts >= exit_by - 600:
            continue
        done = sent_map.get(f"{day_key}:{t}", [])
        if live and (live <= e["stop"] or live >= e["entry"] + 0.5 * (e["target"] - e["entry"])):
            log(f"day: skipped {t}, the price already moved")           # too late to buy it at a sensible price
            sent_map[f"{day_key}:{t}"] = done + [b for b, _ in found]
            continue
        mkt_line = (f"Market: the {market} index is {state['chg_open']:+.1%} since the open." if state else "")
        msg = format_day_alert(cfg, t, found, e, live, ts, end_ts, mkt_line)
        checks, ok = day_verify(t, e, live, cfg)
        bump(db, "check_ideas")
        if not ok:
            bump(db, "check_flagged")
        msg += "\nCheck Bot (second look):\n  " + "\n  ".join(checks)
        if not ok:
            head, _, rest = msg.partition("\n")
            msg = re.sub(r"^\S+ (STRONG|MODERATE|WEAK)", "⚠️ CAUTION", head) + "\n" + rest
            msg += "\nI'd skip this one, so I'm not tracking a trade for it."
        elif cfg["auto_track"]:
            entry = live or e["entry"]
            shares = open_day_trade(db, cfg, t, entry, e, [b for b, _ in found], exit_by, ts)
            msg += (f"\nTracking a ${cfg['position_usd']:,} simulated day trade ({shares:g} shares at ~{fp(t, entry)}). "
                    f"I'll send a message when it hits the stop or the target, or when it's time to close it, with the % result.")
        else:
            msg += "\nI only track day trades when AUTO_TRACK is on, so there will be no result message for this one."
        msg += "\nNot financial advice. Day trading is risky: fees and delays can wipe out small gains."
        notify(msg)
        sent_map[f"{day_key}:{t}"] = done + [b for b, _ in found]
        bump(db, count_key)
        sent += 1
    meta_set(db, "day_evaluated", json.dumps(evaluated))
    meta_set(db, "day_sent", json.dumps(sent_map))
    db.execute("DELETE FROM meta WHERE k LIKE 'day_count_%' AND k<>?", (count_key,))
    db.commit()
    return sent if fresh >= max(1, (len(tickers) - failed) // 2) else None


def maybe_day(cfg: dict, db: sqlite3.Connection, notify, fetch=None, now: datetime | None = None) -> int:
    """Called on every cloud run (about every 5 minutes): follow open day trades, then, whenever a new 15-minute
    candle has closed, look at the markets that are open."""
    if not cfg["day_enabled"]:
        return 0
    now = now or utc_now()
    ts = now.timestamp()
    sent = 0
    try:
        log(f"day trades checked, {manage_day_trades(cfg, db, notify, fetch, ts)} closed")
    except Exception as e:
        log(f"day trade check failed: {type(e).__name__}: {e}")
    expected = int(ts - CANDLE) // CANDLE * CANDLE          # start of the newest finished candle
    for market in day_markets_open(cfg, now):
        key = "day_bar_" + market
        if int(meta_get(db, key, "0") or 0) >= expected:
            continue
        try:
            n = scan_day_market(cfg, db, notify, market, expected, ts, fetch)
        except Exception as e:
            log(f"day: {market} scan failed: {type(e).__name__}: {e}")
            continue
        if n is not None:
            meta_set(db, key, expected)
            sent += n
    return sent


def day_text(cfg: dict, db: sqlite3.Connection) -> str:
    opens = [p for p in open_positions(db) if p.get("kind") == "day"]
    today = utc_now().strftime("%Y-%m-%d")
    td, al = day_totals(db, today), day_totals(db)
    lines = [f"Day trading is {'on' if cfg['day_enabled'] else 'off'} for: {', '.join(cfg['day_markets'])}.",
             "Bots: " + ", ".join(f"{DAY_BOTS[b][0]} ({'on' if b in enabled_day_bots(cfg, db) else 'off'})" for b in DAY_BOTS)]
    if opens:
        lines.append("Open day trades:")
        for p in opens:
            px = p["last_price"] or p["entry_price"]
            lines.append(f"  {p['ticker']:8} in {fp(p['ticker'], p['entry_price'])}, now {fp(p['ticker'], px)} ({px / p['entry_price'] - 1:+.1%}), "
                         f"stop {fp(p['ticker'], p['stop'])}, target {fp(p['ticker'], p['target'])}, "
                         f"close by {hm(cfg, datetime.fromisoformat(p['exit_by']).timestamp())}")
    else:
        lines.append("No open day trades.")
    lines.append(f"Today: {td['n']} closed, {td['wins']} winners, net {money(td['pnl'])}")
    lines.append(f"All day trades: {al['n']} closed, {al['wins']} winners, net {money(al['pnl'])}")
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# Day-trading backtest: replay the three day bots on the last ~2 months of 15-minute candles
# --------------------------------------------------------------------------- #
def sim_day_trade(S: list[dict], i: int, delay: int, stop: float, target: float):
    """Enter at the open of the candle `delay` candles after the signal candle i, then follow the stop/target.
    The last exit is the close of the second-to-last candle (about 15-30 minutes before the market closes).
    Returns (return, reason, exit candle index) or None if the trade could not be taken."""
    j0, last = i + delay, len(S) - 2
    if j0 > last:
        return None
    entry = S[j0]["open"]
    if entry <= stop or entry >= target:
        return None                                           # the price had already run or broken the stop
    for j in range(j0, last + 1):
        b = S[j]
        if b["low"] <= stop:
            return min(b["open"], stop) / entry - 1, "stop-loss", j
        if b["high"] >= target:
            return max(b["open"], target) / entry - 1, "profit target", j
    return S[last]["close"] / entry - 1, "end of day", last


def cmd_backtest_day(cfg: dict, stocks: int = 60, market: str = "US", cost_pct: float = 0.10, delays: list[int] | None = None) -> None:
    import random
    delays = delays or [1, 2]
    cost = cost_pct / 100
    wanted = [m for m in DAY_WINDOWS if market.lower() in ("all", m.lower())]
    if not wanted:
        sys.exit("Day-trading backtests support: " + ", ".join(DAY_WINDOWS) + ", or all.")
    bots = list(DAY_BOTS)
    R = cfg["day_target_r"]
    all_stats = {d: {b: [] for b in bots} for d in delays}
    base_stats = {d: {b: [] for b in bots} for d in delays}
    ends = {d: {b: {"stop-loss": 0, "profit target": 0, "end of day": 0} for b in bots} for d in delays}
    n_stocks, days_seen, failed = 0, set(), []
    for m in wanted:
        suf = SUFFIX_OF[m]
        index = MARKETS[suf][1]
        idx_by_day = {}
        if index:
            try:
                idata = fetch_intraday(index, "59d")
                for k, ss in enumerate(idata["sessions"][1:], 1):
                    idx_by_day[idata["days"][k]] = (idata["sessions"][k - 1][-1]["close"], {b["t"]: b for b in ss}, ss[0]["open"])
            except Exception:
                print(f"  (no {m} index data: tested without a market filter)", flush=True)
        universe = day_universe(cfg, suf)[:max(5, stocks)]
        for n, t in enumerate(universe, 1):
            try:
                time.sleep(0.3)
                data = fetch_intraday(t, "59d")
            except Exception as e:
                failed.append(t)
                print(f"  [{m} {n}/{len(universe)}] {t}: skipped ({str(e)[:50]})", flush=True)
                continue
            ss, ds = data["sessions"], data["days"]
            n_total = max(len(s) for s in ss)
            n_stocks += 1
            print(f"  [{m} {n}/{len(universe)}] {t}: {len(ss)} days", flush=True)
            for s in range(3, len(ss)):
                S, prior = ss[s], ss[max(0, s - 8):s]
                if len(S) < n_total - 3:
                    continue                                   # a half day (holiday); skip
                days_seen.add(ds[s])
                taken = {}
                free_at = -1
                for i in range(len(S)):
                    if i <= free_at:
                        continue
                    ctx = day_ctx(prior, S[:i + 1], n_total, t)
                    if not ctx or not day_gate(ctx, cfg):
                        continue
                    ix = idx_by_day.get(ds[s])
                    if ix and S[i]["t"] in ix[1]:
                        c = ix[1][S[i]["t"]]["close"]
                        if not (c / ix[2] - 1 > -0.0025 and c / ix[0] - 1 > -0.01):
                            continue
                        ctx["mkt_chg"] = c / ix[2] - 1
                    for bot in bots:
                        if bot in taken:
                            continue
                        e = DAY_EVAL[bot](ctx, cfg)
                        if not e:
                            continue
                        taken[bot] = True
                        rng = random.Random(f"{t}{ds[s]}{bot}")
                        first = None
                        for d in delays:
                            r = sim_day_trade(S, i, d, e["stop"], e["target"])
                            if r is None:
                                continue
                            first = first or r
                            all_stats[d][bot].append(r[0] - cost)
                            ends[d][bot][r[1]] += 1
                            lo, hi = 3, len(S) - 7              # random-time entry with the same stop and target distances
                            if hi > lo:
                                k = rng.randint(lo, hi)
                                ent = S[k + d]["open"]
                                rb = sim_day_trade(S, k, d, ent * (1 - e["risk_pct"]), ent * (1 + e["risk_pct"] * R))
                                if rb:
                                    base_stats[d][bot].append(rb[0] - cost)
                        if first:
                            free_at = max(free_at, first[2])      # one trade at a time per stock
    if n_stocks < 5:
        sys.exit("Could not download enough 15-minute data to run the backtest. Yahoo only keeps about 2 months of it; try again later.")
    pc = lambda x: f"{x:+.2%}"
    print(f"\nDAY-TRADING SUMMARY: {', '.join(wanted)}, {n_stocks} stocks, {len(days_seen)} trading days, costs {cost:.2%} per trade")
    print(f"Rules: signal on a finished 15-minute candle; you buy {delays[0]} candle(s) later at that candle's open"
          f" (second table: {delays[-1]}); stop at the bot's stop, target {R:g}x the risk; closed ~15-30 min before the close.\n")
    for d in delays:
        label = f"If you act {d} candle(s) after the signal (about {d * 15 - 10}-{d * 15 + 5} min of delay)"
        print(label)
        print(f"{'Bot':18} {'Trades':>7} {'Win rate':>9} {'Avg trade':>10} {'Random time':>12}   Verdict")
        for b in bots:
            st, bs = trade_stats(all_stats[d][b]), trade_stats(base_stats[d][b])
            if not st["n"]:
                print(f"{DAY_BOTS[b][0]:18} {0:>7} {'':>9} {'':>10} {'':>12}   no trades (rules never matched)")
                continue
            base = bs["avg"] if bs.get("n") else 0.0
            verdict = ("too few trades to judge" if st["n"] < 30 else
                       "beat random timing: worth keeping on" if st["avg"] > 0.0005 and st["avg"] > base + 0.001 else
                       "profitable, but no better than random timing" if st["avg"] > 0 else
                       "lost money: turn it off")
            print(f"{DAY_BOTS[b][0]:18} {st['n']:>7} {st['win']:>9.0%} {pc(st['avg']):>10} {pc(base):>12}   {verdict}")
        print()
    d0 = delays[0]
    print(f"How the trades ended (delay {d0}): " + "; ".join(
        f"{DAY_BOTS[b][0]}: " + ", ".join(f"{k} {v / max(1, sum(ends[d0][b].values())):.0%}" for k, v in ends[d0][b].items()) for b in bots))
    print("\nHOW TO READ THIS")
    print(" * 'Random time' = the same stop and target distances, but entering at a random time that day. A bot only helps if its")
    print("   average trade is clearly above that.")
    print(" * Yahoo keeps only about 2 months of 15-minute candles, and that is one market mood. Few trades means luck can decide;")
    print("   wait for 30+ trades per bot, and judge again as time passes. Today's biggest stocks make old results look better (survivorship bias).")
    print(" * Compare the two tables: the more your delay costs, the less this works for you. Fees, spreads and slippage are only")
    print("   roughly covered by the cost setting; small accounts feel them most.")
    if failed:
        print(f"\n(Skipped, no data: {', '.join(failed)})")


# --------------------------------------------------------------------------- #
# Crypto day trading: Binance 15-minute candles (public price data, no key needed). Crypto never closes,
# so there is no opening range; trades get a stop, a target and a time limit instead.
# --------------------------------------------------------------------------- #
CRYPTO_BOTS = {
    "cbreak": ("Crypto Breakout Bot", "Coins that close above their 24-hour high on heavy volume while Bitcoin is calm or rising."),
    "cvwap": ("Crypto VWAP Bot", "Coins in a short-term uptrend that dipped under their 24-hour average price (VWAP) and climbed back above it."),
    "cdip": ("Crypto Dip Bot", "Coins in an uptrend that were sold off hard (very low RSI) and have just started to bounce."),
}
CRYPTO_COINS = ("BTC ETH BNB SOL XRP DOGE ADA AVAX LINK DOT TRX LTC BCH ATOM NEAR APT ARB OP INJ SUI TON UNI AAVE FIL ETC HBAR XLM")
BINANCE_HOSTS = ["https://data-api.binance.vision", "https://api.binance.com", "https://api1.binance.com"]
_BINANCE_HOST = [None]


def parse_klines(rows: list) -> list[dict]:
    out = []
    for r in rows:
        try:
            out.append({"t": int(r[0]) // 1000, "open": float(r[1]), "high": float(r[2]), "low": float(r[3]), "close": float(r[4]),
                        "volume": float(r[5]), "qvol": float(r[7])})
        except (ValueError, IndexError, TypeError):
            continue
    out.sort(key=lambda b: b["t"])
    return out


def fetch_klines(symbol: str, limit: int = 300, end_ms: int | None = None, interval: str = "15m") -> list[dict]:
    """Candles (oldest first) from Binance's public market-data servers. The last one may still be running."""
    qs = f"symbol={symbol}&interval={interval}&limit={limit}" + (f"&endTime={end_ms}" if end_ms else "")
    hosts = ([_BINANCE_HOST[0]] if _BINANCE_HOST[0] else []) + [h for h in BINANCE_HOSTS if h != _BINANCE_HOST[0]]
    last = None
    for host in hosts:
        try:
            rows = json.loads(http_get(f"{host}/api/v3/klines?{qs}", BROWSER_UA, timeout=15, retries=1))
            if isinstance(rows, dict):
                raise RuntimeError(str(rows.get("msg", "error"))[:60])
            _BINANCE_HOST[0] = host
            return parse_klines(rows)
        except Exception as e:
            last = e
    raise RuntimeError(f"Binance prices not reachable ({str(last)[:60]})")


def crypto_symbols(cfg: dict) -> list[str]:
    coins = cfg["crypto_coins"] or CRYPTO_COINS.split()
    return [f"{c.upper()}{cfg['crypto_quote']}" for c in coins]


def coin_of(symbol: str, cfg: dict | None = None) -> str:
    for q in ((cfg or {}).get("crypto_quote"), "USDT", "USDC"):
        if q and symbol.endswith(q):
            return symbol[:-len(q)]
    return symbol


def ema_list(vals: list[float], n: int) -> list[float]:
    k, out, e = 2 / (n + 1), [], vals[0]
    for v in vals:
        e = v * k + e * (1 - k)
        out.append(e)
    return out


def crypto_ctx(bars: list[dict], symbol: str = "") -> dict | None:
    """Numbers the crypto bots look at, from finished candles (oldest first, the last is the one being judged)."""
    if len(bars) < 200:
        return None
    c = bars[-1]["close"]
    closes = [b["close"] for b in bars]
    win = bars[-96:]
    vol24 = sum(b["volume"] for b in win)
    if vol24 <= 0 or c <= 0:
        return None
    vwap_at = lambda k: (lambda w: sum((b["high"] + b["low"] + b["close"]) / 3 * b["volume"] for b in w) / max(1e-12, sum(b["volume"] for b in w)))(bars[k - 95:k + 1])
    trs = [max(bars[k]["high"] - bars[k]["low"], abs(bars[k]["high"] - bars[k - 1]["close"]), abs(bars[k]["low"] - bars[k - 1]["close"]))
           for k in range(len(bars) - 14, len(bars))]
    atr = sum(trs) / 14
    if atr <= 0:
        return None
    r = rsi_series(closes[-80:])
    e20, e50, e192 = ema_list(closes, 20), ema_list(closes, 50), ema_list(closes, 192)
    n = len(bars)
    return {"symbol": symbol, "S": bars, "c": c, "atr": atr, "atr_pct": atr / c,
            "vwap": vwap_at(n - 1), "vwap_prev": vwap_at(n - 2),
            "high24": max(b["high"] for b in bars[-97:-1]), "high24_prev": max(b["high"] for b in bars[-98:-2]),
            "vol_ratio": bars[-1]["volume"] / max(1e-12, sum(b["volume"] for b in bars[-21:-1]) / 20),
            "vol5": sum(b["volume"] for b in bars[-6:-1]) / 5,
            "ema20": e20[-1], "ema50": e50[-1], "ema192": e192[-1], "ema192_prev": e192[-25],
            "rsi": r[-1], "rsi_min6": min(x for x in r[-7:-1] if x is not None) if any(x is not None for x in r[-7:-1]) else None,
            "chg24": c / bars[-97]["close"] - 1, "qvol24": sum(b["qvol"] for b in win), "mkt_chg": 0.0}


def crypto_gate(ctx: dict, cfg: dict) -> bool:
    return ctx["qvol24"] >= cfg["crypto_min_volume_usd"] and 0.001 <= ctx["atr_pct"] <= 0.02


def crypto_setup(ctx: dict, cfg: dict, stop: float, why: list[str], score: int) -> dict | None:
    c = ctx["c"]
    if stop >= c:
        return None
    risk = c - stop
    if not 0.004 <= risk / c <= 0.03:
        return None
    target = c + cfg["day_target_r"] * risk
    return {"entry": c, "stop": stop, "target": target, "risk_pct": risk / c, "reward_pct": target / c - 1, "why": why,
            "score": score, "level": _day_level(score), "t": ctx["S"][-1]["t"]}


def evaluate_cbreak(ctx: dict, cfg: dict) -> dict | None:
    S, c, sym = ctx["S"], ctx["c"], ctx["symbol"]
    b = S[-1]
    rng = b["high"] - b["low"]
    if c <= ctx["high24"] or S[-2]["close"] > ctx["high24_prev"] or c - ctx["high24"] > ctx["atr"]:     # a fresh break, not chased
        return None
    if ctx["vol_ratio"] < 2.0 or rng <= 0 or (c - b["low"]) / rng < 0.6 or c <= ctx["vwap"] or c <= ctx["ema50"]:
        return None
    stop = min(x["low"] for x in S[-2:]) - 0.1 * ctx["atr"]
    score = (60 + (10 if ctx["vol_ratio"] >= 3 else 0) + (10 if c > ctx["ema192"] else 0) + (5 if (c - b["low"]) / rng >= 0.8 else 0)
             + (5 if ctx["mkt_chg"] > 0.003 else 0))
    why = [f"closed above its highest price of the last 24 hours ({fp(sym, ctx['high24'])})",
           f"this candle's volume is {ctx['vol_ratio']:.1f}x the recent average", f"above its 24-hour average price (VWAP {fp(sym, ctx['vwap'])})"]
    return crypto_setup(ctx, cfg, stop, why, score)


def evaluate_cvwap(ctx: dict, cfg: dict) -> dict | None:
    S, c, sym = ctx["S"], ctx["c"], ctx["symbol"]
    b = S[-1]
    rng = b["high"] - b["low"]
    if not (c > ctx["vwap"] and S[-2]["close"] <= ctx["vwap_prev"]):
        return None
    if not (ctx["ema20"] > ctx["ema50"] and c > ctx["ema50"] and ctx["chg24"] > 0):
        return None
    if rng <= 0 or (c - b["low"]) / rng < 0.5 or b["volume"] < 1.2 * ctx["vol5"]:
        return None
    stop = min(x["low"] for x in S[-4:]) * 0.9995
    score = (60 + (10 if b["volume"] >= 2 * ctx["vol5"] else 0) + (10 if ctx["chg24"] >= 0.03 else 0)
             + (5 if (c - b["low"]) / rng >= 0.8 else 0) + (5 if ctx["mkt_chg"] > 0.003 else 0))
    why = [f"in an uptrend (up {ctx['chg24']:.1%} in 24 hours, 20-period average above the 50)",
           f"dipped under its 24-hour average price (VWAP {fp(sym, ctx['vwap'])}) and has just closed back above it",
           f"this candle's volume is {b['volume'] / ctx['vol5']:.1f}x the last few candles"]
    return crypto_setup(ctx, cfg, stop, why, score)


def evaluate_cdip(ctx: dict, cfg: dict) -> dict | None:
    S, c, sym = ctx["S"], ctx["c"], ctx["symbol"]
    b = S[-1]
    if ctx["rsi"] is None or ctx["rsi_min6"] is None:
        return None
    if not (ctx["rsi_min6"] <= 28 and ctx["rsi"] >= ctx["rsi_min6"] + 6 and ctx["rsi"] < 50):
        return None
    if not (c > ctx["ema192"] * 0.985 and ctx["ema192"] > ctx["ema192_prev"]):                           # the bigger trend is still up
        return None
    if not (c > b["open"] and c > S[-2]["close"] and b["volume"] >= ctx["vol5"]):
        return None
    stop = min(x["low"] for x in S[-6:]) * 0.9995
    score = 60 + (10 if ctx["rsi_min6"] <= 22 else 0) + (10 if b["volume"] >= 1.5 * ctx["vol5"] else 0) + (5 if c > ctx["ema20"] else 0) + (5 if ctx["mkt_chg"] > 0 else 0)
    why = [f"sold off hard (RSI fell to {ctx['rsi_min6']:.0f}) inside a rising 2-day trend", f"now bouncing (RSI {ctx['rsi']:.0f}) on a green candle with more volume"]
    return crypto_setup(ctx, cfg, stop, why, score)


CRYPTO_EVAL = {"cbreak": evaluate_cbreak, "cvwap": evaluate_cvwap, "cdip": evaluate_cdip}


def btc_state(bars: list[dict]) -> dict:
    """Bitcoin sets the mood for every coin: no new ideas if it fell more than 1.5% in 4 hours or 1% in 1 hour."""
    c = bars[-1]["close"]
    c4, c1 = c / bars[-17]["close"] - 1, c / bars[-5]["close"] - 1
    return {"ok": c4 > -0.015 and c1 > -0.01, "chg4h": c4, "chg1h": c1}


def enabled_crypto_bots(cfg: dict, db: sqlite3.Connection | None = None) -> list[str]:
    if not cfg["crypto_enabled"]:
        return []
    off = set()
    if db is not None:
        try:
            off = set(json.loads(meta_get(db, "bots_off", "[]")))
        except ValueError:
            pass
    return [b for b in CRYPTO_BOTS if b in [x.lower() for x in cfg["crypto_bots"]] and b not in off]


def crypto_hours_open(cfg: dict, ts: float) -> bool:
    """New ideas only between your chosen local hours (default 7-23), so they don't wake you up."""
    try:
        a, b = [int(x) for x in str(cfg["crypto_hours"]).split("-")]
    except ValueError:
        return True
    h = datetime.fromtimestamp(ts, tz_of(cfg)).hour + datetime.fromtimestamp(ts, tz_of(cfg)).minute / 60
    return a <= h < b


def format_crypto_alert(cfg: dict, symbol: str, found: list, e: dict, live: float | None, now_ts: float, hold_ts: float, mkt_line: str) -> str:
    coin = coin_of(symbol, cfg)
    names = bot_names([b for b, _ in found])
    head = (f"⚡ {e['level']} crypto day-trade idea: {coin} ({names})" if len(found) == 1
            else f"⚡ STRONG crypto day-trade idea confirmed by {len(found)} bots: {coin}")
    age = max(0, round((now_ts - (e["t"] + CANDLE)) / 60))
    lines = [head, f"Buy around {fp(symbol, live or e['entry'])} ({symbol}) | candle closed {hm(cfg, e['t'] + CANDLE)} (data about {age} min old)"]
    if len(found) > 1:
        lines.append(f"Found by {' and '.join(CRYPTO_BOTS[b][0] for b, _ in found)}. When more than one bot agrees, I treat it as stronger.")
    lines.append(f"Stop-loss {fp(symbol, e['stop'])} ({-e['risk_pct']:.1%}) | Target {fp(symbol, e['target'])} ({e['reward_pct']:+.1%}) "
                 f"| the target is {cfg['day_target_r']:g}x the risk")
    lines.append(f"Close it by {hm(cfg, hold_ts)} even if neither level is hit (crypto never closes, so trades get a "
                 f"{cfg['crypto_max_hold_hours']:g}-hour limit).")
    why = [f"{CRYPTO_BOTS[b][0]}: {'; '.join(x['why'])}" for b, x in found] if len(found) > 1 else e["why"]
    lines.append(("Why:\n  " + "\n  ".join(why)) if len(found) > 1 else "Why: " + "; ".join(why))
    if mkt_line:
        lines.append(mkt_line)
    lines.append(f"On Binance in the EU, USDT pairs aren't available to you: trade {coin}/USDC or {coin}/EUR instead (the price is almost the same).")
    lines.append("Put the stop and the target in as orders (an OCO order) right away. My alerts can arrive minutes late, and crypto moves fast.")
    return "\n".join(lines)


def open_crypto_trade(db: sqlite3.Connection, cfg: dict, symbol: str, entry: float, e: dict, bots: list[str],
                      exit_by_ts: float, now_ts: float) -> float:
    shares = round(cfg["position_usd"] / entry, 8)
    db.execute("INSERT INTO positions (ticker, company, shares, entry_price, entry_at, peak, last_price, manual, bot, kind, stop, "
               "target, exit_by, mgmt_t) VALUES (?, ?, ?, ?, ?, ?, ?, 0, ?, 'crypto', ?, ?, ?, ?)",
               (symbol, symbol, shares, entry, datetime.fromtimestamp(now_ts, timezone.utc).isoformat(timespec="seconds"), entry, entry,
                "+".join(bots), e["stop"], e["target"],
                datetime.fromtimestamp(exit_by_ts, timezone.utc).isoformat(timespec="seconds"), int(now_ts // CANDLE * CANDLE)))
    db.commit()
    return shares


def manage_crypto_trades(cfg: dict, db: sqlite3.Connection, notify, fetch=None, ts: float | None = None) -> int:
    """Follow every open crypto trade: stop, target and the time limit (the same candle-by-candle rules as day trades)."""
    fetch = fetch or fetch_klines
    ts = utc_now().timestamp() if ts is None else ts
    closed = 0
    for pos in open_positions(db):
        if pos.get("kind") != "crypto":
            continue
        try:
            allb = fetch(pos["ticker"], 60)
        except Exception:
            continue
        stop, target = pos["stop"], pos["target"]
        exit_by = datetime.fromisoformat(pos["exit_by"]).timestamp()
        bars = [b for b in allb if b["t"] > (pos["mgmt_t"] or 0) and b["t"] + CANDLE <= ts]
        live = allb[-1]["close"] if allb else None
        done = None
        for b in bars:
            if b["low"] <= stop:
                done = (min(b["open"], stop), "stop-loss hit", b["t"] + CANDLE)
            elif b["high"] >= target:
                done = (max(b["open"], target), "profit target reached", b["t"] + CANDLE)
            elif b["t"] + CANDLE >= exit_by:
                done = (b["close"], f"time limit ({cfg['crypto_max_hold_hours']:g} hours): time to close it", b["t"] + CANDLE)
            if done:
                break
        if not done and live:
            if ts >= exit_by:
                done = (live, f"time limit ({cfg['crypto_max_hold_hours']:g} hours): time to close it", ts)
            elif live <= stop:
                done = (live, "stop-loss hit (live price)", ts)
            elif live >= target:
                done = (live, "profit target reached (live price)", ts)
        if done:
            price, reason, exit_ts = done
            pnl, ret = close_position(db, pos, price, reason)
            db.execute("UPDATE positions SET exit_at=? WHERE id=?",
                       (datetime.fromtimestamp(min(exit_ts, ts), timezone.utc).isoformat(timespec="seconds"), pos["id"]))
            db.commit()
            notify(format_day_closed(cfg, db, pos, price, reason, pnl, ret, min(exit_ts, ts)))
            closed += 1
        else:
            last = live or pos["last_price"]
            db.execute("UPDATE positions SET last_price=?, peak=?, mgmt_t=? WHERE id=?",
                       (last, max(pos["peak"] or 0, last or 0), max([pos["mgmt_t"] or 0] + [b["t"] for b in bars]), pos["id"]))
            db.commit()
    return closed


def scan_crypto(cfg: dict, db: sqlite3.Connection, notify, expected: int, ts: float, fetch=None) -> int | None:
    """Look at every coin after a new 15-minute candle closed. Returns the number of alerts, or None to try again next run."""
    fetch = fetch or fetch_klines
    day_key = datetime.fromtimestamp(ts, timezone.utc).strftime("%Y-%m-%d")
    try:
        btc = [b for b in fetch(f"BTC{cfg['crypto_quote']}", 300) if b["t"] + CANDLE <= ts]
        if len(btc) < 200 or btc[-1]["t"] < expected - CANDLE:
            return None
        state = btc_state(btc)
    except Exception as ex:
        log(f"crypto: no Bitcoin data ({str(ex)[:70]})")
        if meta_get(db, "crypto_fail") != day_key:
            meta_set(db, "crypto_fail", day_key)
            notify("⚠️ I couldn't get Binance prices just now, so crypto ideas are paused. Binance may be blocking GitHub's servers "
                   "or having a bad moment. I'll keep trying and won't repeat this today.")
        return None
    meta_set(db, "crypto_info", json.dumps({"state": "up" if state["ok"] else "down", "at": int(ts), "chg4h": round(state["chg4h"], 4),
                                            "chg1h": round(state["chg1h"], 4)}))
    bots = enabled_crypto_bots(cfg, db)
    if not bots:
        return 0
    if not state["ok"]:
        log(f"crypto: Bitcoin is falling ({state['chg4h']:+.1%} in 4 hours), crypto ideas paused")
        return 0
    if not crypto_hours_open(cfg, ts):
        return 0
    from concurrent.futures import ThreadPoolExecutor
    symbols = crypto_symbols(cfg)

    def grab(s):
        try:
            return s, fetch(s, 300)
        except Exception:
            return s, None
    with ThreadPoolExecutor(max_workers=6) as ex:
        got = dict(ex.map(grab, symbols))
    evaluated = {k: v for k, v in json.loads(meta_get(db, "crypto_evaluated", "{}") or "{}").items() if v > ts - 2 * 86400}
    last_sent = {k: v for k, v in json.loads(meta_get(db, "crypto_sent", "{}") or "{}").items() if v > ts - 86400}
    held = {p["ticker"] for p in open_positions(db)}
    hits, failed, stale = [], 0, 0
    for sym in symbols:
        rows = got.get(sym)
        if not rows:
            failed += 1
            continue
        bars = [b for b in rows if b["t"] + CANDLE <= ts]
        if len(bars) < 200 or bars[-1]["t"] < expected - CANDLE:
            stale += 1
            continue
        if evaluated.get(sym, 0) >= bars[-1]["t"] or sym in held:
            continue
        evaluated[sym] = bars[-1]["t"]
        ctx = crypto_ctx(bars, sym)
        if not ctx or not crypto_gate(ctx, cfg):
            continue
        ctx["mkt_chg"] = state["chg4h"]
        found = [(b, e) for b in bots if ts - last_sent.get(f"{sym}:{b}", 0) >= cfg["crypto_cooldown_min"] * 60 and (e := CRYPTO_EVAL[b](ctx, cfg))]
        if found:
            found.sort(key=lambda x: -x[1]["score"])
            hits.append((sym, found, rows))
    log(f"crypto: {len(symbols)} coins, {failed} unavailable, {stale} late, {len(hits)} setup(s) found")
    hits.sort(key=lambda h: (-len(h[1]), -h[1][0][1]["score"]))
    count_key, sent = "crypto_count_" + day_key, 0
    for sym, found, rows in hits:
        if sent >= cfg["crypto_max_alerts_per_run"] or int(meta_get(db, count_key, "0") or 0) >= cfg["crypto_max_alerts_per_day"]:
            break
        e = found[0][1]
        live = rows[-1]["close"]
        for b, _ in found:
            last_sent[f"{sym}:{b}"] = ts
        if live <= e["stop"] or live >= e["entry"] + 0.5 * (e["target"] - e["entry"]):
            log(f"crypto: skipped {sym}, the price already moved")
            continue
        hold_ts = ts + cfg["crypto_max_hold_hours"] * 3600
        mkt_line = f"Market: Bitcoin is {state['chg4h']:+.1%} over the last 4 hours."
        msg = format_crypto_alert(cfg, sym, found, e, live, ts, hold_ts, mkt_line)
        checks, ok = [], True
        if live:
            checks.append(f"✔ Live price {fp(sym, live)} is still close to the signal ({fp(sym, e['entry'])}).")
        try:
            news = fetch_news(f"{coin_of(sym, cfg)} crypto", coin_of(sym, cfg), cfg["news_hours"])
            if news["label"] == "negative" and news["neg"] - news["pos"] >= 2:
                bad = [t for t, sc in news["items"] if sc < 0][:2]
                checks.append("⚠️ Recent news looks negative: " + "; ".join(t[:90] for t in bad))
                ok = False
            else:
                checks.append("✔ No clearly negative news in the last %d hours." % cfg["news_hours"])
        except Exception:
            checks.append("Couldn't check the news right now.")
        bump(db, "check_ideas")
        if not ok:
            bump(db, "check_flagged")
        msg += "\nCheck Bot (second look):\n  " + "\n  ".join(checks)
        if not ok:
            head, _, rest = msg.partition("\n")
            msg = re.sub(r"^\S+ (STRONG|MODERATE|WEAK)", "⚠️ CAUTION", head) + "\n" + rest
            msg += "\nI'd skip this one, so I'm not tracking a trade for it."
        elif cfg["auto_track"]:
            shares = open_crypto_trade(db, cfg, sym, live, e, [b for b, _ in found], hold_ts, ts)
            msg += (f"\nTracking a ${cfg['position_usd']:,} simulated crypto trade ({shares:g} {coin_of(sym, cfg)} at ~{fp(sym, live)}). "
                    f"I'll send a message when it hits the stop or the target, or when the time limit is up, with the % result.")
        else:
            msg += "\nI only track trades when AUTO_TRACK is on, so there will be no result message for this one."
        msg += "\nNot financial advice. Crypto is very risky: prices can move fast, and fees and delays can wipe out small gains."
        notify(msg)
        bump(db, count_key)
        sent += 1
    meta_set(db, "crypto_evaluated", json.dumps(evaluated))
    meta_set(db, "crypto_sent", json.dumps(last_sent))
    db.execute("DELETE FROM meta WHERE k LIKE 'crypto_count_%' AND k<>?", (count_key,))
    db.commit()
    return sent if stale + failed <= len(symbols) // 2 else None


def maybe_crypto(cfg: dict, db: sqlite3.Connection, notify, fetch=None, now: datetime | None = None) -> int:
    """Called on every cloud run: follow open crypto trades, then look at the coins whenever a new 15-minute candle has closed."""
    if not cfg["crypto_enabled"]:
        return 0
    now = now or utc_now()
    ts = now.timestamp()
    try:
        log(f"crypto trades checked, {manage_crypto_trades(cfg, db, notify, fetch, ts)} closed")
    except Exception as e:
        log(f"crypto trade check failed: {type(e).__name__}: {e}")
    expected = int(ts - CANDLE) // CANDLE * CANDLE
    if int(meta_get(db, "crypto_bar", "0") or 0) >= expected:
        return 0
    try:
        n = scan_crypto(cfg, db, notify, expected, ts, fetch)
    except Exception as e:
        log(f"crypto scan failed: {type(e).__name__}: {e}")
        return 0
    if n is None:
        return 0
    meta_set(db, "crypto_bar", expected)
    return n


def crypto_text(cfg: dict, db: sqlite3.Connection) -> str:
    opens = [p for p in open_positions(db) if p.get("kind") == "crypto"]
    today = utc_now().strftime("%Y-%m-%d")
    td, al = day_totals(db, today, "crypto"), day_totals(db, "", "crypto")
    info = json.loads(meta_get(db, "crypto_info", "{}") or "{}")
    lines = [f"Crypto day trading is {'on' if cfg['crypto_enabled'] else 'off'} (new ideas between {cfg['crypto_hours']} o'clock your time).",
             "Bots: " + ", ".join(f"{CRYPTO_BOTS[b][0]} ({'on' if b in enabled_crypto_bots(cfg, db) else 'off'})" for b in CRYPTO_BOTS)]
    if info:
        lines.append(f"Bitcoin: {'calm or rising' if info['state'] == 'up' else 'falling, ideas paused'} ({info['chg4h']:+.1%} in 4 hours)")
    if opens:
        lines.append("Open crypto trades:")
        for p in opens:
            px = p["last_price"] or p["entry_price"]
            lines.append(f"  {coin_of(p['ticker'], cfg):6} in {fp(p['ticker'], p['entry_price'])}, now {fp(p['ticker'], px)} ({px / p['entry_price'] - 1:+.1%}), "
                         f"stop {fp(p['ticker'], p['stop'])}, target {fp(p['ticker'], p['target'])}, "
                         f"close by {hm(cfg, datetime.fromisoformat(p['exit_by']).timestamp())}")
    else:
        lines.append("No open crypto trades.")
    lines.append(f"Today: {td['n']} closed, {td['wins']} winners, net {money(td['pnl'])}")
    lines.append(f"All crypto trades: {al['n']} closed, {al['wins']} winners, net {money(al['pnl'])}")
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# Crypto backtest: replay the three crypto bots on the last weeks of 15-minute candles
# --------------------------------------------------------------------------- #
def fetch_klines_history(symbol: str, days: int, fetch=None) -> list[dict]:
    """About `days` days of 15-minute candles, fetched in pages of 1000."""
    fetch = fetch or fetch_klines
    need, out, end_ms = days * 96, [], None
    while len(out) < need:
        page = fetch(symbol, 1000, end_ms)
        if not page:
            break
        out = page + out
        end_ms = page[0]["t"] * 1000 - 1
        if len(page) < 1000:
            break
        time.sleep(0.2)
    return out[-need:]


def sim_crypto_trade(S: list[dict], i: int, delay: int, stop: float, target: float, hold: int):
    """Enter at the open of the candle `delay` candles after the signal; stop first if one candle hits both;
    otherwise leave at the close of the `hold`-th candle. Returns (return, reason, exit index) or None."""
    j0 = i + delay
    last = min(len(S) - 1, j0 + hold - 1)
    if j0 >= len(S) - 1:
        return None
    entry = S[j0]["open"]
    if entry <= stop or entry >= target:
        return None
    for j in range(j0, last + 1):
        b = S[j]
        if b["low"] <= stop:
            return min(b["open"], stop) / entry - 1, "stop-loss", j
        if b["high"] >= target:
            return max(b["open"], target) / entry - 1, "profit target", j
    return S[last]["close"] / entry - 1, "time limit", last


def cmd_backtest_crypto(cfg: dict, days: int = 45, coins: int = 27, cost_pct: float = 0.20, delays: list[int] | None = None, fetch=None) -> None:
    import random
    delays, fetch = delays or [1, 2], fetch or fetch_klines
    cost, R = cost_pct / 100, cfg["day_target_r"]
    hold = max(1, int(cfg["crypto_max_hold_hours"] * 4))
    quote = cfg["crypto_quote"]
    try:
        btc = fetch_klines_history(f"BTC{quote}", days, fetch)
    except Exception as e:
        sys.exit(f"Couldn't download Binance prices, so I can't run the backtest.\nCheck your internet connection and try again. Details: {e}")
    if len(btc) < 400:
        sys.exit("Not enough Bitcoin price history came back to run the backtest.")
    btc_ok = {}
    for k in range(16, len(btc)):
        btc_ok[btc[k]["t"]] = (btc[k]["close"] / btc[k - 16]["close"] - 1 > -0.015, btc[k]["close"] / btc[k - 4]["close"] - 1 > -0.01,
                               btc[k]["close"] / btc[k - 16]["close"] - 1)
    bots = list(CRYPTO_BOTS)
    res = {d: {b: [] for b in bots} for d in delays}
    base = {d: {b: [] for b in bots} for d in delays}
    ends = {d: {b: {"stop-loss": 0, "profit target": 0, "time limit": 0} for b in bots} for d in delays}
    signals = {b: 0 for b in bots}
    failed, n_coins, span_days = [], 0, 0.0
    symbols = crypto_symbols({**cfg, "crypto_coins": cfg["crypto_coins"][:coins] if cfg["crypto_coins"] else CRYPTO_COINS.split()[:coins]})
    for n, sym in enumerate(symbols, 1):
        try:
            S = btc if sym == f"BTC{quote}" else fetch_klines_history(sym, days, fetch)
        except Exception as e:
            failed.append(sym)
            print(f"  [{n}/{len(symbols)}] {sym}: skipped ({str(e)[:50]})", flush=True)
            continue
        if len(S) < 400:
            failed.append(sym)
            continue
        n_coins += 1
        span_days = max(span_days, (S[-1]["t"] - S[0]["t"]) / 86400)
        print(f"  [{n}/{len(symbols)}] {sym}: {len(S)} candles", flush=True)
        free_at, cool = -1, {b: -10**9 for b in bots}
        for i in range(260, len(S) - hold - 3):
            if i <= free_at:
                continue
            ok = btc_ok.get(S[i]["t"])
            if not ok or not (ok[0] and ok[1]):
                continue
            ctx = crypto_ctx(S[i - 299:i + 1] if i >= 299 else S[:i + 1], sym)
            if not ctx or not crypto_gate(ctx, cfg):
                continue
            ctx["mkt_chg"] = ok[2]
            for bot in bots:
                if i - cool[bot] < cfg["crypto_cooldown_min"] // 15:
                    continue
                e = CRYPTO_EVAL[bot](ctx, cfg)
                if not e:
                    continue
                cool[bot] = i
                signals[bot] += 1
                rng = random.Random(f"{sym}{i}{bot}")
                first = None
                for d in delays:
                    r = sim_crypto_trade(S, i, d, e["stop"], e["target"], hold)
                    if r is None:
                        continue
                    first = first or r
                    res[d][bot].append(r[0] - cost)
                    ends[d][bot][r[1]] += 1
                    k = rng.randint(260, len(S) - hold - 5)                # random-time entry, same stop and target distances
                    ent = S[k + d]["open"]
                    rb = sim_crypto_trade(S, k, d, ent * (1 - e["risk_pct"]), ent * (1 + e["risk_pct"] * R), hold)
                    if rb:
                        base[d][bot].append(rb[0] - cost)
                if first:
                    free_at = max(free_at, first[2])
    if n_coins < 5:
        sys.exit("Could not download enough coins to run the backtest.")
    pc = lambda x: f"{x:+.2%}"
    print(f"\nCRYPTO SUMMARY: {n_coins} coins, about {span_days:.0f} days of 15-minute candles, costs {cost:.2%} per round trip "
          f"(Binance charges about 0.1% per side)")
    print(f"Rules: signal on a finished 15-minute candle; you buy {delays[0]} candle(s) later at its open (second table: {delays[-1]}); "
          f"stop at the bot's stop, target {R:g}x the risk, closed after {cfg['crypto_max_hold_hours']:g} hours at the latest; "
          f"no ideas while Bitcoin is falling.\n")
    for d in delays:
        print(f"If you act {d} candle(s) after the signal (about {d * 15 - 10}-{d * 15 + 5} min of delay)")
        print(f"{'Bot':22} {'Trades':>7} {'Per day':>8} {'Win rate':>9} {'Avg trade':>10} {'Random time':>12}   Verdict")
        for b in bots:
            st, bs = trade_stats(res[d][b]), trade_stats(base[d][b])
            if not st["n"]:
                print(f"{CRYPTO_BOTS[b][0]:22} {0:>7} {'':>8} {'':>9} {'':>10} {'':>12}   no trades (rules never matched)")
                continue
            b0 = bs["avg"] if bs.get("n") else 0.0
            verdict = ("too few trades to judge" if st["n"] < 30 else
                       "beat random timing: worth keeping on" if st["avg"] > 0.0005 and st["avg"] > b0 + 0.001 else
                       "profitable, but no better than random timing" if st["avg"] > 0 else
                       "lost money: turn it off")
            print(f"{CRYPTO_BOTS[b][0]:22} {st['n']:>7} {st['n'] / max(1, span_days):>8.1f} {st['win']:>9.0%} {pc(st['avg']):>10} {pc(b0):>12}   {verdict}")
        print()
    d0 = delays[0]
    print(f"How the trades ended (delay {d0}): " + "; ".join(
        f"{CRYPTO_BOTS[b][0]}: " + ", ".join(f"{k} {v / max(1, sum(ends[d0][b].values())):.0%}" for k, v in ends[d0][b].items()) for b in bots))
    tot = sum(len(res[d0][b]) for b in bots)
    print(f"\nAll three bots together: about {tot / max(1, span_days):.1f} trades a day across {n_coins} coins "
          f"(so roughly one every {24 * 60 * max(1, span_days) / max(1, tot):.0f} minutes, day and night).")
    print("\nHOW TO READ THIS")
    print(" * 'Random time' = the same stop and target distances, entering at a random time. A bot only helps if its average trade is clearly above that.")
    print(" * Only a few weeks of data, one market mood. Wait for 30+ trades per bot; today's biggest coins make old results look better.")
    print(" * Compare the two tables: the more your delay costs, the less this works for you. Fees matter a lot: a small gain per trade can vanish.")
    if failed:
        print(f"\n(Skipped, no data: {', '.join(failed)})")


# --------------------------------------------------------------------------- #
# Backtest: replay the dip rules on past prices
# --------------------------------------------------------------------------- #
def indicators(bars: list[dict]) -> dict:
    """RSI and 20-day average for every bar, so the backtest can test the extra sell signals quickly."""
    closes = [b["close"] for b in bars]
    sma20, run = [None] * len(closes), 0.0
    for k, c in enumerate(closes):
        run += c
        if k >= 20:
            run -= closes[k - 20]
        if k >= 19:
            sma20[k] = run / 20
    return {"rsi": rsi_series(closes), "sma20": sma20}


def simulate_trade(bars: list[dict], i: int, cfg: dict, hold_days: int, ind: dict | None = None):
    """Buy at the NEXT day's open after the signal on bar i, then apply the sell rules.
    With `ind` (from indicators()) the extra sell signals are applied too: overbought after a gain, and the
    short-term trend breaking. Returns (exit_index, return, reason) or None if the trade is still open."""
    j = i + 1
    if j >= len(bars) or bars[j]["open"] <= 0:
        return None
    entry = bars[j]["open"]
    stop, target = entry * (1 - cfg["stop_loss_pct"]), entry * (1 + cfg["take_profit_pct"])
    peak, d0, above = entry, datetime.fromisoformat(bars[j]["date"]), False
    for k in range(j, len(bars)):
        b = bars[k]
        if b["open"] <= stop:
            return k, b["open"] / entry - 1, "stop-loss"        # gapped below the stop: filled at the open
        if b["low"] <= stop:
            return k, stop / entry - 1, "stop-loss"             # checked before the target (the pessimistic order)
        if b["high"] >= target:
            return k, target / entry - 1, "profit target"
        peak = max(peak, b["close"])
        if peak > entry and b["close"] <= peak * (1 - cfg["trailing_stop_pct"]):
            return k, b["close"] / entry - 1, "trailing stop"
        if ind is not None:
            r, m = ind["rsi"][k], ind["sma20"][k]
            if r is not None and r >= 75 and b["close"] / entry - 1 >= 0.03:
                return k, b["close"] / entry - 1, "overbought"
            if m is not None:
                if k > j and b["close"] >= m:
                    above = True
                if above and k - j >= 2 and b["close"] < m:
                    return k, b["close"] / entry - 1, "trend break"
        if (datetime.fromisoformat(b["date"]) - d0).days >= hold_days:
            return k, b["close"] / entry - 1, "time limit"
    return None


def spy_health_by_date(spy: list[dict]) -> dict:
    closes, ok = [b["close"] for b in spy], {}
    for i in range(199, len(spy)):
        ok[spy[i]["date"]] = closes[i] > sum(closes[i - 199:i + 1]) / 200
    return ok


def scan_signals(bars: list[dict], spy_ok: dict, cfg: dict, bot: str = "dip") -> list:
    """Every day the bot would have alerted, using only data up to that day."""
    out, evaluate = [], BOTS[bot][0]
    for i in range(220, len(bars) - 1):
        if not spy_ok.get(bars[i]["date"]):
            continue
        e = evaluate(bars[max(0, i - 259): i + 1], cfg)
        if e:
            out.append((i, e))
    return out


def trade_stats(rets: list[float]) -> dict:
    import statistics
    if not rets:
        return {"n": 0}
    wins, losses = [r for r in rets if r > 0], [r for r in rets if r <= 0]
    return {"n": len(rets), "win": len(wins) / len(rets), "avg": sum(rets) / len(rets),
            "median": statistics.median(rets),
            "avg_win": sum(wins) / len(wins) if wins else 0.0,
            "avg_loss": sum(losses) / len(losses) if losses else 0.0,
            "pf": (sum(wins) / -sum(losses)) if losses and sum(losses) < 0 else float("inf"),
            "best": max(rets), "worst": min(rets)}


def scaled_cfg(cfg: dict, ticker: str) -> dict:
    """The liquidity limit is in US dollars; for a stock priced in another currency it is converted."""
    return {**cfg, "scan_min_dollar_volume": min_turnover(cfg, ticker)}


class AlwaysHealthy(dict):
    def get(self, key, default=None):
        return True


def run_backtest(cfg: dict, data: dict, spy: list[dict], holds: list[int], cost: float,
                 bot: str = "dip", exits: bool = False, sigs: dict | None = None, ok_by: dict | None = None) -> dict:
    """data: ticker -> bars. Applies the same cooldown, one-trade-per-stock and daily alert cap as the live scanner.
    `exits` adds the overbought and trend-break sell signals."""
    from collections import defaultdict
    spy_ok = spy_health_by_date(spy)
    ok_by = ok_by or {}                              # ticker -> {date: is that stock's market healthy}
    ok_of = lambda t: ok_by.get(t, spy_ok)
    if sigs is None:
        sigs = {t: scan_signals(b, ok_of(t), scaled_cfg(cfg, t), bot) for t, b in data.items()}
    inds = {t: indicators(b) for t, b in data.items()} if exits else {}
    by_date = defaultdict(list)
    for t, lst in sigs.items():
        for i, e in lst:
            by_date[data[t][i]["date"]].append((t, i, e))
    results = {}
    for hold in holds:
        trades, free_at, last_alert = [], {}, {}
        for d in sorted(by_date):
            day = datetime.fromisoformat(d)
            cands = [c for c in by_date[d] if d > free_at.get(c[0], "")
                     and (c[0] not in last_alert or (day - datetime.fromisoformat(last_alert[c[0]])).days >= cfg["scan_cooldown_days"])]
            cands.sort(key=lambda c: (-c[2]["score"], c[2].get("rsi_low", 50)))
            for t, i, e in cands[: cfg["scan_max_alerts"]]:
                r = simulate_trade(data[t], i, cfg, hold, inds.get(t))
                if r is None:
                    continue
                k, ret, reason = r
                trades.append({"ticker": t, "date": d, "level": e["level"], "ret": ret - cost, "reason": reason,
                               "exit_date": data[t][k]["date"], "year": d[:4]})
                free_at[t], last_alert[t] = data[t][k]["date"], d
        base = []                                  # benchmark: buy any of these stocks on any day the market is healthy
        for t, bars in data.items():
            for i in range(220, len(bars) - 1, 3):
                if not ok_of(t).get(bars[i]["date"]):
                    continue
                entry, d0 = bars[i + 1]["open"], datetime.fromisoformat(bars[i + 1]["date"])
                for k in range(i + 1, min(len(bars), i + 1 + hold + 8)):
                    if (datetime.fromisoformat(bars[k]["date"]) - d0).days >= hold:
                        base.append(bars[k]["close"] / entry - 1 - cost)
                        break
        results[hold] = {"trades": trades, "stats": trade_stats([t["ret"] for t in trades]),
                         "baseline": trade_stats(base)}
    return results


def print_backtest(res: dict, cfg: dict, first: str, last: str, n_stocks: int, years: float, cost: float,
                   name: str = "DIP BOT", exits: bool = False) -> None:
    pc = lambda x: f"{x:+.2%}"
    print(f"\n{name.upper()} BACKTEST{' (with the overbought and trend-break sell signals)' if exits else ''}: {n_stocks} stocks, {first} -> {last} ({years:g} years requested), "
          f"costs {cost:.2%} per trade")
    print(f"Rules: buy at the next day's open after the alert; stop-loss -{cfg['stop_loss_pct']:.0%}, profit target "
          f"+{cfg['take_profit_pct']:.0%}, trailing stop {cfg['trailing_stop_pct']:.0%}; at most {cfg['scan_max_alerts']} "
          f"alerts a day, {cfg['scan_cooldown_days']}-day cooldown per stock\n")
    print(f"{'Max hold':>9} {'Trades':>7} {'Win rate':>9} {'Avg trade':>10} {'Median':>8} {'Avg win':>8} "
          f"{'Avg loss':>9} {'Profit factor':>14} {'Worst':>8}   Baseline avg / win rate")
    for hold, r in res.items():
        st, bs = r["stats"], r["baseline"]
        if not st["n"]:
            print(f"{hold:>6} d   no trades")
            continue
        base = f"{pc(bs['avg'])} / {bs['win']:.0%}" if bs.get("n") else "n/a"
        pf = "inf" if st["pf"] == float("inf") else f"{st['pf']:.2f}"
        print(f"{hold:>6} d {st['n']:>7} {st['win']:>9.0%} {pc(st['avg']):>10} {pc(st['median']):>8} "
              f"{pc(st['avg_win']):>8} {pc(st['avg_loss']):>9} {pf:>14} {pc(st['worst']):>8}   {base}")
    h0 = next(iter(res))
    trades = res[h0]["trades"]
    if trades:
        print(f"\nHow the {h0}-day trades ended: " + ", ".join(
            f"{k} {sum(1 for t in trades if t['reason'] == k) / len(trades):.0%}"
            for k in ("stop-loss", "profit target", "trailing stop", "time limit")))
        print(f"By year ({h0}-day hold):")
        for y in sorted({t["year"] for t in trades}):
            st = trade_stats([t["ret"] for t in trades if t["year"] == y])
            print(f"  {y}: {st['n']:>3} trades, {st['win']:.0%} winners, average {pc(st['avg'])}")
        for lvl in ("STRONG", "MODERATE", "WEAK"):
            st = trade_stats([t["ret"] for t in trades if t["level"] == lvl])
            if st["n"]:
                print(f"  {lvl:8}: {st['n']:>3} trades, {st['win']:.0%} winners, average {pc(st['avg'])}")
    print("\nHOW TO READ THIS")
    print(" * 'Baseline' = buying any of these stocks on any day the market was healthy and holding the same time.")
    print("   A bot only helps if 'Avg trade' is clearly above the baseline.")
    print(" * The stock list is today's big winners, so old results look better than they would have at the time")
    print("   (survivorship bias). Real results are likely worse. Past results do not predict future ones.")
    print(" * Prices are daily, so stop-loss fills are optimistic in fast markets. Taxes and spreads are not included.")


def cmd_backtest_scan(cfg: dict, years: float, holds: list[int], cost_pct: float, stocks: int = 100, market: str = "US") -> None:
    days = int(years * 365) + 330                     # plus a year of warm-up for the 200-day average
    cost = cost_pct / 100
    try:
        spy = fetch_history("SPY", days)
    except Exception as e:
        sys.exit(f"Couldn't download price data, so I can't run the backtest.\nCheck your internet connection and try again. Details: {e}")
    wanted = None if market.lower() == "all" else market.lower()
    universe, per = [], {}
    for t in ([x.upper() for x in cfg["scan_tickers"]] if cfg["scan_tickers"] else DEFAULT_SCAN + GLOBAL_TICKERS):
        m = market_name(t)
        if wanted and m.lower() != wanted:
            continue
        per[m] = per.get(m, 0) + 1
        if per[m] <= max(5, stocks):                  # the biggest companies of each market first
            universe.append(t)
    if not universe:
        sys.exit(f"No stocks for market '{market}'. Try: US, UK, Germany, France, Netherlands, Switzerland, Canada, Australia, Japan, Hong Kong, Romania or all.")
    ok_by, index_ok = {}, {}
    data, failed = {}, []
    for n, t in enumerate(universe, 1):
        try:
            time.sleep(0.3)
            data[t] = fetch_history(t, days)
            suf = market_suffix(t)
            if suf not in index_ok:
                idx = MARKETS[suf][1]
                try:
                    index_ok[suf] = spy_health_by_date(spy if suf == "" else fetch_history(idx, days)) if idx else AlwaysHealthy()
                except Exception:
                    index_ok[suf] = AlwaysHealthy()
                    print(f"  (no {MARKETS[suf][0]} index data: that market is tested without a market filter)", flush=True)
            ok_by[t] = index_ok[suf]
            print(f"  [{n}/{len(universe)}] {t}: {len(data[t])} days", flush=True)
        except Exception as e:
            failed.append(t)
            print(f"  [{n}/{len(universe)}] {t}: skipped ({str(e)[:60]})", flush=True)
    if len(data) < 5:
        sys.exit("Could not download enough price data to run the backtest.")
    print(f"\nTesting {len(BOTS)} bots on {len(data)} stocks (this takes a few minutes)...", flush=True)
    results, alt = {}, {}
    for bot in BOTS:
        sigs = {t: scan_signals(b, ok_by[t], scaled_cfg(cfg, t), bot) for t, b in data.items()}
        results[bot] = run_backtest(cfg, data, spy, holds, cost, bot, cfg["exit_signals"], sigs, ok_by)
        alt[bot] = run_backtest(cfg, data, spy, holds[:1], cost, bot, not cfg["exit_signals"], sigs, ok_by)
        print(f"  {BOTS[bot][1]} done", flush=True)
    first, last = spy[220]["date"], spy[-1]["date"]
    h0 = holds[0]
    pc = lambda x: f"{x:+.2%}"
    print(f"\nSUMMARY: what each bot would have done ({n_years(first, last)}, {len(data)} stocks, max hold {h0} days, "
          f"costs {cost:.2%} per trade)")
    print(f"{'Bot':14} {'Trades':>7} {'Win rate':>9} {'Avg trade':>10} {'Baseline':>9}   Verdict")
    for bot in BOTS:
        st, bs = results[bot][h0]["stats"], results[bot][h0]["baseline"]
        if not st["n"]:
            print(f"{BOTS[bot][1]:14} {0:>7} {'':>9} {'':>10} {'':>9}   no trades (rules never matched)")
            continue
        base = bs["avg"] if bs.get("n") else 0.0
        verdict = ("too few trades to judge" if st["n"] < 30 else
                   "beat the baseline: keep it on" if st["avg"] > 0 and st["avg"] > base + 0.002 else
                   "profitable, but no better than buying at random" if st["avg"] > 0 else
                   "lost money: turn it off")
        print(f"{BOTS[bot][1]:14} {st['n']:>7} {st['win']:>9.0%} {pc(st['avg']):>10} {pc(base):>9}   {verdict}")
    print(f"\nExtra sell signals (overbought, trend break), average trade at a {h0}-day max hold:")
    for bot in BOTS:
        on, off = (results[bot][h0], alt[bot][h0]) if cfg["exit_signals"] else (alt[bot][h0], results[bot][h0])
        if on["stats"]["n"] and off["stats"]["n"]:
            print(f"  {BOTS[bot][1]:14} with {pc(on['stats']['avg'])}, without {pc(off['stats']['avg'])}")
    for bot in BOTS:
        print_backtest(results[bot], cfg, first, last, len(data), years, cost, BOTS[bot][1], cfg["exit_signals"])
    if failed:
        print(f"\n(Skipped, no data: {', '.join(failed)})")


def n_years(first: str, last: str) -> str:
    return f"{first} to {last}"


# --------------------------------------------------------------------------- #
# iPhone app: alert history, encrypted data file, and Web Push notifications
# --------------------------------------------------------------------------- #
ALERT_DB = None  # set by the runners so every alert is also kept in the app's history


def log_alert(text: str) -> None:
    if ALERT_DB is None:
        return
    try:
        ALERT_DB.execute("INSERT INTO alerts_log (at, text) VALUES (?, ?)", (now_iso(), text))
        ALERT_DB.execute("DELETE FROM alerts_log WHERE id NOT IN (SELECT id FROM alerts_log ORDER BY id DESC LIMIT 300)")
        ALERT_DB.commit()
    except sqlite3.Error:
        pass


def have_crypto() -> bool:
    try:
        import cryptography  # noqa: F401
        return True
    except ImportError:
        return False


def b64u(b: bytes) -> str:
    return base64.urlsafe_b64encode(b).rstrip(b"=").decode()


def b64u_dec(s: str) -> bytes:
    return base64.urlsafe_b64decode(s + "=" * (-len(s) % 4))


# ---- Web Push (RFC 8291 message encryption + RFC 8292 VAPID), using only `cryptography` ----
PUSH_HOSTS = ("apple.com", "googleapis.com", "mozilla.com", "windows.com")


def _hmac(key: bytes, data: bytes) -> bytes:
    return hmac.new(key, data, hashlib.sha256).digest()


def encrypt_push(payload: bytes, ua_public: bytes, auth: bytes, as_key=None, salt: bytes | None = None) -> bytes:
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric import ec
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    as_key = as_key or ec.generate_private_key(ec.SECP256R1())
    salt = salt or os.urandom(16)
    as_pub = as_key.public_key().public_bytes(serialization.Encoding.X962, serialization.PublicFormat.UncompressedPoint)
    secret = as_key.exchange(ec.ECDH(), ec.EllipticCurvePublicKey.from_encoded_point(ec.SECP256R1(), ua_public))
    ikm = _hmac(_hmac(auth, secret), b"WebPush: info\x00" + ua_public + as_pub + b"\x01")
    prk = _hmac(salt, ikm)
    cek = _hmac(prk, b"Content-Encoding: aes128gcm\x00\x01")[:16]
    nonce = _hmac(prk, b"Content-Encoding: nonce\x00\x01")[:12]
    ciphertext = AESGCM(cek).encrypt(nonce, payload + b"\x02", None)      # 0x02 marks the last (only) record
    return salt + struct.pack(">IB", 4096, len(as_pub)) + as_pub + ciphertext


def vapid_keys(db: sqlite3.Connection):
    """(private key object, public key as base64url). Created on first use and kept in the database."""
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric import ec
    pem = meta_get(db, "vapid_priv")
    if pem:
        key = serialization.load_pem_private_key(pem.encode(), None)
    else:
        key = ec.generate_private_key(ec.SECP256R1())
        meta_set(db, "vapid_priv", key.private_bytes(serialization.Encoding.PEM, serialization.PrivateFormat.PKCS8,
                                                     serialization.NoEncryption()).decode())
    pub = key.public_key().public_bytes(serialization.Encoding.X962, serialization.PublicFormat.UncompressedPoint)
    return key, b64u(pub)


def vapid_auth(endpoint: str, key, pub_b64: str, subject: str) -> str:
    from cryptography.hazmat.primitives import hashes
    from cryptography.hazmat.primitives.asymmetric import ec
    from cryptography.hazmat.primitives.asymmetric.utils import decode_dss_signature
    u = urllib.parse.urlparse(endpoint)
    claims = {"aud": f"{u.scheme}://{u.netloc}", "exp": int(time.time()) + 12 * 3600, "sub": subject}
    seg = lambda o: b64u(json.dumps(o, separators=(",", ":")).encode())
    signing = f"{seg({'typ': 'JWT', 'alg': 'ES256'})}.{seg(claims)}"
    r, s_ = decode_dss_signature(key.sign(signing.encode(), ec.ECDSA(hashes.SHA256())))
    return f"vapid t={signing}.{b64u(r.to_bytes(32, 'big') + s_.to_bytes(32, 'big'))}, k={pub_b64}"


def send_push(sub: dict, payload: bytes, key, pub_b64: str, subject: str) -> int:
    body = encrypt_push(payload, b64u_dec(sub["keys"]["p256dh"]), b64u_dec(sub["keys"]["auth"]))
    req = urllib.request.Request(sub["endpoint"], data=body, method="POST", headers={
        "Content-Encoding": "aes128gcm", "Content-Type": "application/octet-stream", "TTL": "86400",
        "Urgency": "high", "Authorization": vapid_auth(sub["endpoint"], key, pub_b64, subject)})
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            return resp.status
    except urllib.error.HTTPError as e:
        return e.code


def add_push_sub(db: sqlite3.Connection, raw: str) -> None:
    bad = ValueError("That code isn't valid. In the app open Settings, tap 'Copy connection code', and paste it again.")
    try:
        sub = json.loads(raw)
        ep, keys = sub["endpoint"], sub["keys"]
        host = urllib.parse.urlparse(ep).hostname or ""
        ok = (ep.startswith("https://") and any(host == h or host.endswith("." + h) for h in PUSH_HOSTS)
              and len(b64u_dec(keys["p256dh"])) == 65 and len(b64u_dec(keys["auth"])) == 16)
    except (ValueError, KeyError, TypeError, AttributeError):
        raise bad from None
    if not ok:
        raise bad
    subs = [x for x in json.loads(meta_get(db, "push_subs", "[]")) if x["endpoint"] != ep]
    subs.append({"endpoint": ep, "keys": {"p256dh": keys["p256dh"], "auth": keys["auth"]}})
    meta_set(db, "push_subs", json.dumps(subs[-5:]))


def push_all(db: sqlite3.Connection, text: str) -> int:
    """Send an alert as a notification to every connected phone. Returns how many were delivered."""
    subs = json.loads(meta_get(db, "push_subs", "[]"))
    if not subs or not have_crypto():
        return 0
    key, pub = vapid_keys(db)
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    payload = json.dumps({"title": (lines[0] if lines else "Stock alert")[:120],
                          "body": " · ".join(lines[1:3])[:220]}, ensure_ascii=False).encode()
    repo = os.environ.get("GITHUB_REPOSITORY", "")
    subject = f"https://{repo.split('/')[0]}.github.io/{repo.split('/')[1]}" if "/" in repo else "https://example.com"
    keep, delivered = [], 0
    for sub in subs:
        try:
            code = send_push(sub, payload, key, pub, subject)
        except Exception as e:
            log(f"push: could not reach the push service ({type(e).__name__})")
            keep.append(sub)
            continue
        if code in (404, 410):
            log("push: a phone unsubscribed, removing it")
            continue
        keep.append(sub)
        if 200 <= code < 300:
            delivered += 1
        else:
            log(f"push: the push service answered {code}")
    if len(keep) != len(subs):
        meta_set(db, "push_subs", json.dumps(keep))
    return delivered


# ---- the data file the app reads (encrypted, so the public website shows nothing) ----
PBKDF2_ITERATIONS = 600_000


def encrypt_json(obj, password: str) -> dict:
    from cryptography.hazmat.primitives.ciphers.aead import AESGCM
    salt, iv = os.urandom(16), os.urandom(12)
    key = hashlib.pbkdf2_hmac("sha256", password.encode(), salt, PBKDF2_ITERATIONS, dklen=32)
    ct = AESGCM(key).encrypt(iv, json.dumps(obj, separators=(",", ":")).encode(), None)
    enc = lambda b: base64.b64encode(b).decode()
    return {"v": 1, "kdf": "PBKDF2-SHA256", "iter": PBKDF2_ITERATIONS, "salt": enc(salt), "iv": enc(iv), "ct": enc(ct)}


BOT_INFO = {
    "market": ("Market Watcher", "Checks whether the overall market is healthy. The buy bots pause when it is not."),
    "insider": ("Insider Bot", "Follows company insiders buying their own stock, checked against the news."),
    "dip": (BOTS["dip"][1], BOTS["dip"][3]),
    "breakout": (BOTS["breakout"][1], BOTS["breakout"][3]),
    "trend": (BOTS["trend"][1], BOTS["trend"][3]),
    "gap": (BOTS["gap"][1], BOTS["gap"][3]),
    "orb": DAY_BOTS["orb"],
    "vwap": DAY_BOTS["vwap"],
    "gapgo": DAY_BOTS["gapgo"],
    "cbreak": CRYPTO_BOTS["cbreak"],
    "cvwap": CRYPTO_BOTS["cvwap"],
    "cdip": CRYPTO_BOTS["cdip"],
    "exit": ("Exit Bot", "Watches your open trades and tells you when to sell, then reports the profit or loss."),
    "check": ("Check Bot", "Double-checks every buy idea (live price from two sources, latest news) and the prices in your closed trades."),
}


def classify_alert(text: str) -> str:
    """Which bot sent an alert, judged from its first line. '' if it is none of them."""
    first = text.split("\n", 1)[0]
    if "Check Bot" in first or "CAUTION" in first:
        return "check"
    if "confirmed by" in first:
        return "multi"
    if "crypto day-trade idea" in first:
        for key, (name, _) in CRYPTO_BOTS.items():
            if name in first:
                return key
    if "day-trade idea" in first:
        for key, (name, _) in DAY_BOTS.items():
            if name in first:
                return key
    for key, word in (("dip", "dip-buy idea"), ("breakout", "breakout idea"), ("trend", "trend idea"),
                      ("gap", "gap-up idea"), ("insider", "insider buy")):
        if word in first:
            return key
    if "SELL signal" in first or "Trade closed" in first or "Day trade closed" in first or "Crypto trade closed" in first or "Heads-up" in first:
        return "exit"
    if "overall market" in first or "\U0001F4C9" in first or "\U0001F4C8" in first:
        return "market"
    return ""


def bot_rows(cfg: dict, db: sqlite3.Connection, alerts: list[dict]) -> list[dict]:
    """One row per bot for the app's Bots tab: is it on, when it last spoke, and how its tracked trades did."""
    on_scan, on_day, on_cr = set(enabled_bots(cfg, db)), set(enabled_day_bots(cfg, db)), set(enabled_crypto_bots(cfg, db))
    names = {v[0]: k for k, v in BOT_INFO.items()}
    closed = [dict(r) for r in db.execute("SELECT bot, pnl, ret FROM positions WHERE status='closed'")]
    cutoff = (utc_now() - timedelta(days=30)).isoformat(timespec="seconds")
    rows = []
    for key in ("market", "insider", "dip", "breakout", "trend", "gap", "orb", "vwap", "gapgo", "cbreak", "cvwap", "cdip", "exit", "check"):
        mine, last, n30 = [], "", 0
        for a in alerts:
            kind = a["bot"]
            hit = kind == key
            if kind == "multi":
                m = re.search(r"Found by (.+?)\.", a["text"].split("\n", 3)[2] if a["text"].count("\n") >= 2 else "")
                hit = bool(m) and any(names.get(x.strip()) == key for x in m.group(1).split(" and "))
            if hit:
                last = last or a["at"]
                n30 += a["at"] >= cutoff
        for c in closed:
            if key in (c["bot"] or "").split("+"):
                mine.append(c)
        wins = sum(1 for c in mine if c["pnl"] > 0)
        rows.append({"id": key, "name": BOT_INFO[key][0], "what": BOT_INFO[key][1],
                     "on": key in on_scan if key in BOTS else key in on_day if key in DAY_BOTS else key in on_cr if key in CRYPTO_BOTS else True,
                     "group": "day" if key in DAY_BOTS else "crypto" if key in CRYPTO_BOTS else "", "last_at": last, "alerts30": n30,
                     "n": len(mine), "wins": wins,
                     "avg_ret": round(sum(c["ret"] for c in mine) / len(mine), 4) if mine else 0.0})
    mi = lambda k: int(meta_get(db, k, "0") or 0)
    rows[-1].update({"on": True, "ideas": mi("check_ideas"), "ideas_flagged": mi("check_flagged"),
                     "audited": mi("audit_checked"), "audit_flagged": mi("audit_flagged")})
    for a in alerts:                                   # last time it raised a warning
        if "Check Bot" in a["text"].split("\n", 1)[0] or a["text"].startswith("⚠️ CAUTION"):
            rows[-1]["last_at"] = a["at"]
            break
    return rows


def day_block(cfg: dict, db: sqlite3.Connection, now: datetime) -> dict:
    today = now.strftime("%Y-%m-%d")
    return {"enabled": bool(cfg["day_enabled"]), "markets": cfg["day_markets"],
            "info": json.loads(meta_get(db, "day_info", "{}") or "{}"), "now": int(now.timestamp()),
            "alerts_today": int(meta_get(db, "day_count_" + today, "0") or 0),
            "today": day_totals(db, today), "all": day_totals(db), "target_r": cfg["day_target_r"],
            "close_min": cfg["day_close_minutes"]}


def cur_for(ticker: str, price: float):
    """How the app writes prices for this ticker: stocks use their market's currency, coins get more decimals when cheap."""
    if is_crypto(ticker):
        return ["$", "", 2 if price >= 100 else 4 if price >= 1 else 5 if price >= 0.01 else 7]
    return cur_of(ticker)


def crypto_block(cfg: dict, db: sqlite3.Connection, now: datetime) -> dict:
    today = now.strftime("%Y-%m-%d")
    return {"enabled": bool(cfg["crypto_enabled"]), "hours": cfg["crypto_hours"], "hold_hours": cfg["crypto_max_hold_hours"],
            "info": json.loads(meta_get(db, "crypto_info", "{}") or "{}"), "now": int(now.timestamp()),
            "alerts_today": int(meta_get(db, "crypto_count_" + today, "0") or 0),
            "today": day_totals(db, today, "crypto"), "all": day_totals(db, "", "crypto"), "target_r": cfg["day_target_r"]}


def build_app_data(cfg: dict, db: sqlite3.Connection, now: datetime, history_fn=None, day_history_fn=None, crypto_history_fn=None) -> dict:
    history_fn = history_fn or (lambda t, n: fetch_history(t, n, min_bars=20))
    day_history_fn = day_history_fn or (lambda t: fetch_intraday(t, "2d"))
    crypto_history_fn = crypto_history_fn or (lambda t: fetch_klines(t, 100))
    closed = [dict(r) for r in db.execute("SELECT * FROM positions WHERE status='closed' ORDER BY exit_at, id")]
    cum, equity = 0.0, []
    for p in closed:
        cum += p["pnl"]
        equity.append({"t": p["exit_at"], "cum": round(cum, 2), "ticker": p["ticker"],
                       "pnl": round(p["pnl"], 2), "ret": round(p["ret"], 4)})
    opens = []
    for p in open_positions(db):
        last = p["last_price"] or p["entry_price"]
        isday = p.get("kind") in ("day", "crypto")
        sell_by = datetime.fromisoformat(p["exit_by"]) if isday else datetime.fromisoformat(p["entry_at"]) + timedelta(days=cfg["max_hold_days"])
        opens.append({"day": isday, "crypto": p.get("kind") == "crypto", "exit_by": p["exit_by"] if isday else "", "ticker": p["ticker"], "shares": p["shares"], "entry_price": p["entry_price"],
                      "entry_at": p["entry_at"], "last_price": last, "mine": bool(p["manual"]), "bot": p["bot"] or "", "cur": cur_for(p["ticker"], p["entry_price"]),
                      "coin": coin_of(p["ticker"], cfg), "pnl": round((last - p["entry_price"]) * p["shares"] / usd_rate(p["ticker"]), 2), "ret": round(last / p["entry_price"] - 1, 4),
                      "days": held_days(p), "stop": round(p["stop"], 4) if isday else round(p["entry_price"] * (1 - cfg["stop_loss_pct"]), 2),
                      "target": round(p["target"], 4) if isday else round(p["entry_price"] * (1 + cfg["take_profit_pct"]), 2),
                      "sell_by": sell_by.strftime("%Y-%m-%d")})
    recent = [
        {"ticker": p["ticker"], "shares": p["shares"], "entry_price": p["entry_price"], "exit_price": p["exit_price"],
         "entry_at": p["entry_at"], "exit_at": p["exit_at"], "pnl": round(p["pnl"], 2), "ret": round(p["ret"], 4),
         "reason": p["exit_reason"], "mine": bool(p["manual"]), "bot": p["bot"] or "", "cur": cur_for(p["ticker"], p["entry_price"]),
         "coin": coin_of(p["ticker"], cfg),
         "day": p.get("kind") in ("day", "crypto"), "crypto": p.get("kind") == "crypto"} for p in reversed(closed[-30:])]
    wins = sum(1 for p in closed if p["pnl"] > 0)
    alerts = []
    for r in db.execute("SELECT at, text FROM alerts_log ORDER BY id DESC LIMIT 300"):
        alerts.append({"at": r["at"], "text": r["text"], "bot": classify_alert(r["text"])})
    bots = bot_rows(cfg, db, alerts)
    alerts = alerts[:60]
    charts, tickers = {}, []
    for t in [p["ticker"] for p in opens] + [p["ticker"] for p in recent[:10]]:
        if t not in tickers:
            tickers.append(t)
    day_open = {p["ticker"] for p in opens if p["day"]}
    for t in tickers[:20]:
        if t in day_open:
            continue
        try:
            charts[t] = [[b["date"], round(b["close"], 2)] for b in history_fn(t, 220)[-120:]]
        except Exception as e:
            log(f"app: no price history for {t} ({type(e).__name__})")
    charts_day = {}
    for t in sorted(day_open)[:10]:                                   # today's 15-minute prices for the open day trades
        try:
            if is_crypto(t):
                charts_day[t] = [[b["t"], round(b["close"], 6)] for b in crypto_history_fn(t)[-96:]]
            else:
                d = day_history_fn(t)
                charts_day[t] = [[b["t"], round(b["close"], 4)] for b in d["sessions"][-1]]
        except Exception as e:
            log(f"app: no intraday prices for {t} ({type(e).__name__})")
    key_pub = ""
    if have_crypto():
        try:
            key_pub = vapid_keys(db)[1]
        except Exception:
            pass
    return {"v": 1, "generated_at": now.isoformat(timespec="seconds"),
            "market": meta_get(db, "market_state"), "market_info": json.loads(meta_get(db, "market_info", "{}") or "{}"),
            "regions": json.loads(meta_get(db, "regions_info", "{}") or "{}"),
            "bots": bots, "day": day_block(cfg, db, now), "crypto": crypto_block(cfg, db, now), "charts_day": charts_day,
            "rules": {k: cfg[k] for k in ("stop_loss_pct", "take_profit_pct", "trailing_stop_pct", "max_hold_days",
                                          "position_usd", "auto_track", "exit_signals")},
            "push": {"available": bool(key_pub), "key": key_pub, "devices": len(json.loads(meta_get(db, "push_subs", "[]")))},
            "stats": {"n": len(closed), "wins": wins, "net": round(sum(p["pnl"] for p in closed), 2),
                      "avg_ret": round(sum(p["ret"] for p in closed) / len(closed), 4) if closed else 0.0},
            "equity": equity, "open": opens, "closed": recent, "alerts": alerts, "charts": charts}


# <<APP_FILES_BEGIN>>
APP_FILES_B64 = {
    "index.html": (
        "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"
    ),
    "sw.js": (
        "eNqNVVFvGzcMfvev4O6h0BWJvO6ps+ENQRG0A4KhaBvkYSgKRcfzqZalm6Sza7j+76V4d4ntJtj8chJJkR/Jj/T0Jfzloqkw"
        "wJXFkCJEDBujEbY+rDDMYIXYRkgNgmpbiA1aC2qjjFX3FsHXtTWOdK4ind9GaLvYgPPJ1EarZLyLEl5OJ5oOCd5cvXl3DQso"
        "jLpkV5ebV8V8UH58d31zQ8p/CjktLsjGVfhNNmlt822tnKkxJrnF+/HMVvT48tXrX2Xrlo/333/j++f5ZBLR1lJV1fUGXbox"
        "MaHDIMh7TMpm1wJLWPwB+wkAyq0y6dYlY4VWusEofYtOMO5SUhWcEJrNdfZ5Za1g2OWoZB2HjCvT3pE345aiLMv55FA+j0bp"
        "ZDYq4fNw6AowYFrhLoqSJQBD4Czjh++DX5uIkpJjoayNTRRDrFi9gl8WCxgSWqt2lA+uK7SYkGT0Ow3wmJm2hsBH+iqzFmw3"
        "pjedwnu1xMiEyISh4BhnkMKOOeQwZWKROFDHo4eurShtsg/BbPACaoIN90qvIHl+EdUGK9C+3Y1kkznKJ1LRS8UBwETyvCES"
        "cxYVNBgQxEjansKGyO23DtDpsGvT4LSUz7WkxqSb0370PA34L7EUJX07IuH8QdEFSwqHW7j9cCNILUlSZr2pge9rTI2vuAPF"
        "2+tPBXz/nl9JH8zSOJZb34/NKBssWpUap9Yo0VXxzqRGFDl9umr5NXpXlCUBS11wcyZOwNh6V7El95HTySDO2kqGD/n1vz4Z"
        "rviCfOY+e4eCExks/ms02i7lUBd9iUtJKVHwnkL7w5GnHnKOMsoOD/iOHw0R12pMYgjYmMR6+uZKnZjlNVKesPOZTueVddpo"
        "moGeXQuCm5Fl/u5HEUo+/DkcuP4Ec5Zt4QCMG8SX8vHFHpJJFmdQfEyeuK3yrqWQ977azX7yl/BbYn9FAdnjU5uAUwm4pCRC"
        "z5e8fv8+2rui95Xj5tKcRR7b3SNg03xky+JiUOZdOjtbqaMuP6GMMznJhEoNh151+B8VP/5/oG2iV+d779gg8y8O/Hu6DuNC"
        "4r7nnUz13rW53Fv6E/Fb8m4oTlfhraNcUvDWYpW3UoeEd+CSJXgno1D7AGKYBlo+0BvseZqL2usuFuQX9Dh5RHyWElRu2hHB"
        "T2DmubljYEKcpcpEePECnhDzMuH+ZF7Pf6r1D009bOk="
    ),
    "manifest.webmanifest": (
        "eNqNjsFKxDAQhu99iiFea5cVFfXmpeAjiMgSk7Ebtp0Jk1S2LvvuTrYVFlTwMId8/zf/5FABGLIDmgcwT5SCR4HHHiUnU5cs"
        "bVny5ts4TzwmJyHmwFSiZx4FUma3A3uyauCIBFmsmmDJQxR+DxncKB/YLPXZav0ofaloVgt0unkOfEixt1NBukDe9kw4R2/W"
        "7TrhkfzGcc9SnIv2ur1t72Yhb3HAP7LgmJLSF30AHEwSV5yCL9f3V02kztR6M3xi0YyyvU5heZq/GAbb4WoR4yiR04lbmsyx"
        "/qX3Zv2zV9le59+9WvtaHasvs32BJQ=="
    ),
    "icon-180.png": (
        "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"
    ),
    "icon-192.png": (
        "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"
        "mLMtzeVcuK4pt26o19BPCo80uGbLNMZ37flYErFiYXTeRVqd83LQRKKBiquMddgzCwUcppQUuDZFubv9VI0/TWylAzH4xbB3"
        "S3VV1Stbfcuvg1yuXij0PnYqRTxfPgPnPRoXsUh3RfI8ZcxPm1b0qnFSm+Mk2mJRV8QeeLBfrraELAUnKXp15gjVwBD9+hJP"
        "oDofMyJ8aoIc4i7hoySpATesYWbe1h/MIRLbfCdnO6T3Rn6asno9EY38c4qVWFM9CSLxKSv/pt5KX7M33H334R1XGbWwXaPs"
        "KHatjvbtLx2wwL5RfM7njMwHz/6mnhddeCOlwrJ2gNzuQJTSvsgQEarovlAvXVwcvtjFqZfhdufD8tjcXxbPbBQuMW+MuSnK"
        "CmjYAGYoa0G5H6etTUArmHbHsX5V0sl5UfKRz9aHKYHMhZ/26dTyvkfX97HN/YGvydTbAJv834rkFDA3o0FKGsXNttZu9/jd"
        "hrp/+x2XsLmPnRFJlIp2tNMn19s38wpahOl3D6yU10eDFqCZ5z7jcxj7Yjw616JvUnyKZckayh05NOH1pdX3OxITdtr668kS"
        "aT7TfHByh04/ZV4tyc1565Q8IXH3FVvXN5/cCxYKS2eE54n1mtPkZrc9av36wYSU6jSB35ryQph1b/AqBdTdSzPITqyoXDVL"
        "FWrfwdiW/hRfQgkYLE7GiDzaG2vS8CLZqniSFFyn31bG95IyfqhRagiDObWEgjT/o4IWUQYqCXBWIFf7D+Gl+ft7ZhMtjoQQ"
        "SZHIPxfOoFWayM/TeGqXCfgEymKj5prx1y8D2xgQMDOv/G0qd2q+4C3hVApIvMfrYFk6lNe6unqxbX/8YQjrWrae83iH48sh"
        "k3kK307gbEmm7TsVlTy1OoQYt511oIuKZEnoVKZBiVfb/mbZB+T1F0WPmenHiVersa7dUAsbldPDnu5CE1DesCDygrnC0uZf"
        "t3DxqFvPGufzAnigUOhZeZM4525VPL9xMcnmz1lWlVdo8IztTRCV7ZbBdVU7JE+N3L3jrS9zpTsWzzIcWo87iPib2dq0Dhs9"
        "57zBU7XEN3VNKFRb0TM+rxvkpjzSl9d/Lw9Rvx62HQv5fFQCOOtMkR7E0ilPKCI2Ewu1V1PcuOwNDzqY6HwIbSlBf4/m+G+8"
        "iNWBJM35r2+qJL53e5bhCYw01/2tBAXQ39gL+2IXz55r6Cx+dqCqHfPr+yvcZfASpKCA7O75kqgkzc/qj9bAR7VVgpCLe6GW"
        "0zxX/KM5AA4eE/6envtIJ6Yrus4e52sXbNznzJY9uQTfzFZUYAozu1jRRhfdunNu4BMPhwu1IbTd/pOn1NK6NU0065svH5qT"
        "MELuTlW/tTNeMbLPgod6E2UggMaOkT4/S8kCLzRZ4fX6I1wGGo2uWN92Y5KMfagijSM4LTIy/H0DRzyZTakfchUdvWCWRTT0"
        "sTTNqH66IHc/tpEtuM19FOE/0uuocIX54ldBdlcKwah70KLmyLvbZR9Tuumz0+kzWWDbsfWe/I4PkYPujUfdQ9PRnT5489xy"
        "BN+BeQgodKucU5u0CuMOl3eeMFJzHcg7HwlhM2S+eCGFnoUnvCRRSMbw6M0q9l2O5rHLqZQECyg5UszgSwI9y6Pfb/rXLcjN"
        "KyOt7NgUsU4DMUCjS4zSI6svi0VRW9IqeA9hduGs4scrugjbs+VzjdOv3anWmVLxdA5s4cI+mrLihCzn22Y2ple3j68tTQSs"
        "+wqo8rPaJ9qt04a9Uj/Upf6ASGN3LDPksSYKor1hJgScfi7cuGjx9w0a+hc++vS28o07/173+UcPemsnf2VjA8MQKfdmbCOW"
        "EvW5+/kBLY8egJBNE3JbR4QqfxQ3f4ZLVpZW3h0lht2ehdFkpH+q9iBReKk9y+uAndSzhG5oxWBqQgoQ3G+FmE/SQBPtY20b"
        "ObKS6WyTbHKeMTkyvHsqTV2l3w649ezWG7vvm4yzyqoUfJz9Qnvpg3swow71qZzwZnomDNEDXZs42Hce5Xp3exaJNlcYOaKE"
        "+W4zLakthSvSdxs/SIRk6V16JjwuSPwu8CeMe7lcm6URfuJFU5dG+/+Tw/5n+v+3otZ4+Zxu84hcm+a72ktVAWn0dY10aiB2"
        "4f8C1TLVOQ=="
    ),
    "icon-512.png": (
        "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"
    ),
}
# <<APP_FILES_END>>


def app_files() -> dict:
    return {name: zlib.decompress(base64.b64decode(blob)) for name, blob in APP_FILES_B64.items()}


def export_app(cfg: dict, db: sqlite3.Connection, out_dir: str, password: str, force: bool = False,
               history_fn=None, now: datetime | None = None, day_history_fn=None, crypto_history_fn=None) -> bool:
    """Write the website (app + encrypted data) into out_dir if something worth publishing changed."""
    now = now or utc_now()
    opens = open_positions(db)
    sig = "|".join([str(db.execute("SELECT COALESCE(MAX(id), 0) FROM alerts_log").fetchone()[0]),
                    str(db.execute("SELECT COUNT(*) FROM positions WHERE status='closed'").fetchone()[0]),
                    ",".join(f"{p['id']}:{p['manual']}" for p in opens), meta_get(db, "market_state"),
                    meta_get(db, "push_subs", "[]"),
                    hashlib.sha1(b"".join(v for _, v in sorted(app_files().items()))).hexdigest()[:12]])   # a new app version publishes by itself
    last = meta_get(db, "app_published_at")
    age = (now - datetime.fromisoformat(last)).total_seconds() if last else None
    day_trading = any(p.get("kind") in ("day", "crypto") for p in opens)
    if not (force or sig != meta_get(db, "app_sig") or age is None or (day_trading and age >= 600) or (opens and age >= 1800)
            or age >= 43200):
        return False
    data = build_app_data(cfg, db, now, history_fn, day_history_fn, crypto_history_fn)
    out = Path(out_dir)
    out.mkdir(parents=True, exist_ok=True)
    (out / "data.enc.json").write_text(json.dumps(encrypt_json(data, password)))
    for name, blob in app_files().items():
        (out / name).write_bytes(blob)
    meta_set(db, "app_sig", sig)
    meta_set(db, "app_published_at", now.isoformat(timespec="seconds"))
    return True


def tell_telegram(cfg: dict, text: str) -> None:
    if cfg["telegram_bot_token"] and cfg["telegram_chat_id"]:
        try:
            send_telegram(cfg["telegram_bot_token"], str(cfg["telegram_chat_id"]), text)
        except Exception as e:
            log(f"Telegram send failed: {e}")


def cmd_export_app(cfg: dict, out_dir: str, force: bool = False) -> None:
    db, changed = init_db(), False
    pw = os.environ.get("IA_APP_PASSWORD", "")
    try:
        if not pw:
            log("app: APP_PASSWORD is not set, so the phone app is not published")
        elif len(pw) < 12:
            log("app: APP_PASSWORD is shorter than 12 characters, so the phone app is not published")
            if not meta_get(db, "weak_pw_told"):
                meta_set(db, "weak_pw_told", "1")
                tell_telegram(cfg, "⚠️ Your APP_PASSWORD secret is too short, so I haven't published your phone app. "
                                   "Anyone could guess a short password. Change the secret on GitHub to 12 or more "
                                   "characters, for example four random words.")
        elif not have_crypto():
            log("app: the 'cryptography' library is missing")
        else:
            changed = export_app(cfg, db, out_dir, pw, force)
            log("app: published new data" if changed else "app: nothing new to publish")
            repo = os.environ.get("GITHUB_REPOSITORY", "")
            if changed and "/" in repo and not meta_get(db, "app_url_sent"):
                meta_set(db, "app_url_sent", "1")
                owner, name = repo.split("/", 1)
                tell_telegram(cfg, f"📱 Your phone app is being published. It will be ready in about a minute at:\n"
                                   f"https://{owner}.github.io/{name}/\n"
                                   "On your iPhone open it in Safari, tap Share, then Add to Home Screen.")
    finally:
        gh_out = os.environ.get("GITHUB_OUTPUT")
        if gh_out:
            with open(gh_out, "a", encoding="utf-8") as fh:
                fh.write(f"changed={'true' if changed else 'false'}\n")


# --------------------------------------------------------------------------- #
# Cloud mode: one check pass per run; you give commands by messaging the bot
# --------------------------------------------------------------------------- #
HELP = ("Send me:\n"
        "  bought ACME 24.10 40   (log a buy: ticker, price you paid, shares)\n"
        "  sold ACME 27.10        (log a sale; the price is optional)\n"
        "  positions              (open positions and profits)\n"
        "  bots                   (which scanner bots are on)\n"
        "  bot breakout off       (switch a bot off or on: dip, breakout, trend, gap, orb, vwap, gapgo, cbreak, cvwap, cdip)\n"
        "  day                    (day trading: open day trades and today's results)\n"
        "  crypto                 (crypto day trading: open crypto trades and today's results)\n"
        "  push <code>            (connect the iPhone app; the app shows you the code)\n"
        "  help                   (show this)")


def _number(s: str) -> float:
    try:
        return float(s.replace(",", "."))
    except ValueError:
        raise ValueError(f"'{s}' is not a number") from None


def bots_command(db: sqlite3.Connection, cfg: dict, args: list[str]) -> str:
    off = set(json.loads(meta_get(db, "bots_off", "[]")))
    if len(args) == 2 and args[1].lower() in ("on", "off"):
        bot = args[0].lower().replace("-bot", "").replace("bot", "").strip() or args[0].lower()
        if bot not in BOTS and bot not in DAY_BOTS and bot not in CRYPTO_BOTS:
            raise ValueError("Bots you can switch: " + ", ".join(list(BOTS) + list(DAY_BOTS) + list(CRYPTO_BOTS)) + ".   Example:  bot breakout off")
        if args[1].lower() == "off":
            off.add(bot)
        else:
            off.discard(bot)
        meta_set(db, "bots_off", json.dumps(sorted(off)))
        name = BOTS[bot][1] if bot in BOTS else DAY_BOTS[bot][0] if bot in DAY_BOTS else CRYPTO_BOTS[bot][0]
        setting = ("scan_bots", "SCAN_BOTS") if bot in BOTS else ("day_bots", "DAY_BOTS") if bot in DAY_BOTS else ("crypto_bots", "CRYPTO_BOTS")
        if args[1].lower() == "on" and bot not in [x.lower() for x in cfg[setting[0]]]:
            return (f"{name} is allowed again, but your {setting[1]} setting on GitHub doesn't include it, "
                    f"so it stays off until you add it there.")
        return (f"{name} is now {'off' if args[1].lower() == 'off' else 'on'}. "
                + ("It takes effect at the next daily scan." if bot in BOTS else "It takes effect at the next 15-minute candle."))
    on = enabled_bots(cfg, db)
    lines = ["Scanner bots (they run once a day after the US market closes):"]
    for b in BOTS:
        lines.append(f"  {BOTS[b][1]:14} {'on' if b in on else 'off'}")
    on_day = enabled_day_bots(cfg, db)
    lines.append("")
    lines.append(f"Day-trading bots (15-minute candles while the market is open; {'on' if cfg['day_enabled'] else 'OFF'} for {', '.join(cfg['day_markets'])}):")
    for b in DAY_BOTS:
        lines.append(f"  {DAY_BOTS[b][0]:18} {'on' if b in on_day else 'off'}")
    on_cr = enabled_crypto_bots(cfg, db)
    lines.append("")
    lines.append(f"Crypto bots (Binance 15-minute candles, day and night; {'on' if cfg['crypto_enabled'] else 'OFF'}):")
    for b in CRYPTO_BOTS:
        lines.append(f"  {CRYPTO_BOTS[b][0]:20} {'on' if b in on_cr else 'off'}")
    lines.append("Switch one:  bot breakout off   or   bot orb on   or   bot cdip off")
    return "\n".join(lines)


def handle_command(text: str, db: sqlite3.Connection, cfg: dict) -> str:
    parts = text.split()
    cmd = parts[0].lstrip("/").split("@")[0].lower() if parts else ""
    args = parts[1:]
    try:
        if cmd in ("bought", "buy"):
            if len(args) != 3:
                raise ValueError("Format:  bought ACME 24.10 40   (ticker, price you paid, shares)")
            return log_bought(db, args[0], _number(args[1]), _number(args[2]), cfg)
        if cmd in ("sold", "sell"):
            if len(args) not in (1, 2):
                raise ValueError("Format:  sold ACME 27.10   (the price is optional)")
            return "\n\n".join(log_sold(db, cfg, args[0], _number(args[1]) if len(args) == 2 else None))
        if cmd in ("positions", "position", "pos"):
            return positions_text(db)
        if cmd in ("bots", "bot"):
            return bots_command(db, cfg, args)
        if cmd in ("day", "daytrades", "daytrading"):
            return day_text(cfg, db)
        if cmd in ("crypto", "coins"):
            return crypto_text(cfg, db)
        if cmd == "push":
            add_push_sub(db, text.partition(" ")[2].strip())
            sent = push_all(db, "✅ Notifications are on\nYou'll get your alerts on this phone too.")
            return ("✅ Notifications connected. I just sent a test notification to your phone."
                    if sent else "✅ Code saved, but I couldn't send a test notification yet. "
                                 "I'll keep trying with your next alert.")
        if cmd in ("start", "help"):
            return HELP
    except ValueError as e:
        return str(e)
    return "I didn't understand that.\n" + HELP


def process_telegram(cfg: dict, db: sqlite3.Connection) -> int:
    """Read messages you sent to the bot since the last pass and answer them. Only your own chat is obeyed."""
    token, chat = cfg["telegram_bot_token"], str(cfg["telegram_chat_id"])
    if not (token and chat):
        return 0
    offset = int(meta_get(db, "tg_offset", "0"))
    data = json.loads(http_get(f"https://api.telegram.org/bot{token}/getUpdates?offset={offset}&timeout=0",
                               BROWSER_UA, timeout=15))
    handled = 0
    for u in data.get("result", []):
        offset = max(offset, u["update_id"] + 1)
        msg = u.get("message") or {}
        text = (msg.get("text") or "").strip()
        if str((msg.get("chat") or {}).get("id")) != chat or not text:
            continue
        try:
            reply = handle_command(text, db, cfg)
        except Exception as e:
            log(f"chat command failed: {type(e).__name__}")
            reply = "Sorry, that command failed. Check the format with:  help"
        try:
            send_telegram(token, chat, reply)
        except Exception as e:
            log(f"Telegram reply failed: {e}")
        handled += 1
    meta_set(db, "tg_offset", offset)
    return handled


def make_quiet_notifier(cfg: dict, db: sqlite3.Connection | None = None):
    """Telegram and phone-app push. Nothing about your trades is printed, because cloud logs may be public."""
    token, chat = cfg["telegram_bot_token"], str(cfg["telegram_chat_id"])

    def notify(msg: str) -> None:
        log_alert(msg)
        if token and chat:
            try:
                send_telegram(token, chat, msg)
                log("alert sent")
            except Exception as e:
                log(f"Telegram send failed: {e}")
        else:
            log("an alert was generated but Telegram is not configured")
        if db is not None:
            try:
                push_all(db, msg)
            except Exception as e:
                log(f"push failed: {type(e).__name__}")
    return notify


def cmd_cloud(cfg: dict) -> None:
    """One check pass, meant to be started every few minutes by a scheduler such as GitHub Actions."""
    global CHAT_MODE, ALERT_DB
    CHAT_MODE = True
    db = init_db()
    ALERT_DB = db
    notify = make_quiet_notifier(cfg, db)

    def ago(days: int) -> str:
        return (datetime.now(timezone.utc) - timedelta(days=days)).isoformat(timespec="seconds")
    db.execute("DELETE FROM seen WHERE at < ?", (ago(7),))
    db.execute("DELETE FROM buys WHERE at < ?", (ago(30),))
    db.commit()

    if not meta_get(db, "welcomed"):
        notify("✅ Cloud alerts are running. I check for insider buys every few minutes, "
               "so replies to your messages can take a few minutes too.\n\n" + HELP)
        meta_set(db, "welcomed", "1")
    try:  # your messages first, so a buy you just logged is watched in this same pass
        log(f"{process_telegram(cfg, db)} chat command(s) handled")
    except Exception as e:
        log(f"chat commands failed: {e}")
    try:
        log(f"checked the SEC feed, {poll(cfg, db, notify)} buy alert(s) sent")
        if int(meta_get(db, "fails", "0")) >= 6:
            notify("✅ SEC checks are working again.")
        meta_set(db, "fails", 0)
    except Exception as e:
        fails = int(meta_get(db, "fails", "0")) + 1
        meta_set(db, "fails", fails)
        log(f"SEC check failed ({fails} in a row): {e}")
        if fails == 6:
            notify("⚠️ I haven't been able to reach the SEC feed for about 30 minutes, so I may be missing "
                   "insider buys. I'll keep trying and tell you when it works again.")
    try:
        maybe_scan(cfg, db, notify)
    except Exception as e:
        log(f"scan failed: {e}")
    try:
        maybe_day(cfg, db, notify)
    except Exception as e:
        log(f"day trading failed: {type(e).__name__}: {e}")
    try:
        maybe_crypto(cfg, db, notify)
    except Exception as e:
        log(f"crypto trading failed: {type(e).__name__}: {e}")
    try:
        if open_positions(db):
            log(f"checked open positions, {check_positions(cfg, db, notify)} sell signal(s)")
    except Exception as e:
        log(f"position check failed: {e}")


# --------------------------------------------------------------------------- #
# Main loop
# --------------------------------------------------------------------------- #


def poll(cfg: dict, db: sqlite3.Connection, notify) -> int:
    ua, sent = cfg["sec_user_agent"], 0
    for f in fetch_feed(ua):
        if db.execute("SELECT 1 FROM seen WHERE acc=?", (f["acc"],)).fetchone():
            continue
        try:
            text = sec_get(filing_txt_url(f["cik"], f["acc"]), ua).decode("utf-8", "replace")
            parsed = parse_form4(text)
        except Exception as e:
            log(f"could not read filing {f['acc']} (will retry): {e}")
            continue
        db.execute("INSERT OR IGNORE INTO seen VALUES (?, ?)", (f["acc"], now_iso()))
        db.commit()
        if not parsed or not re.fullmatch(r"[A-Z][A-Z.\-]{0,5}", parsed["ticker"]):
            continue
        handle_insider_sales(cfg, db, parsed, notify)
        if not parsed["buys"]:
            continue
        buy = summarize_buys(parsed)
        owner = parsed["owners"][0] if parsed["owners"] else f["acc"]
        db.execute("INSERT INTO buys VALUES (?, ?, ?, ?, ?)", (f["acc"], parsed["ticker"], owner, buy["total"], now_iso()))
        db.commit()
        if cfg["watchlist"] and parsed["ticker"] not in cfg["watchlist"]:
            continue
        if buy["total"] < cfg["min_purchase_usd"]:
            continue
        since = (datetime.now(timezone.utc) - timedelta(days=cfg["cluster_days"])).isoformat(timespec="seconds")
        cluster_n = db.execute("SELECT COUNT(DISTINCT owner) FROM buys WHERE ticker=? AND at>=?",
                               (parsed["ticker"], since)).fetchone()[0]
        try:
            news = fetch_news(parsed["company"], parsed["ticker"], cfg["news_hours"])
        except Exception as e:
            log(f"news lookup failed for {parsed['ticker']}: {e}")
            news = {"items": [], "pos": 0, "neg": 0, "label": "none"}
        news["hours"] = cfg["news_hours"]
        level, why = evaluate(buy, cluster_n, news, cfg)
        price = fetch_price(parsed["ticker"])
        msg = format_alert(parsed, buy, level, why, news, price, f)
        entry = price or buy["avg_price"]
        t = parsed["ticker"]
        bought_cmd = how_to(f"bought {t} <price you paid> <shares>")
        if open_positions(db, t):
            msg += f"\nYou already have a tracked {t} position, so I won't open another."
        elif cfg["auto_track"]:
            if entry > 0:
                shares = open_tracked_position(db, parsed, entry, cfg)
                msg += (f"\nPractice mode: tracking a simulated ${cfg['position_usd']:,} trade "
                        f"({shares} shares at ~${entry:,.2f}). I'll tell you when to sell and what the profit was.\n"
                        f"Bought it for real? {bought_cmd}")
        else:
            msg += (f"\nIf you buy it, log it so I can tell you when to sell and report your profit:\n"
                    f"  {bought_cmd}")
        notify(msg)
        sent += 1
    return sent


def cmd_run(cfg: dict, once: bool) -> None:
    global ALERT_DB
    db, notify = init_db(), make_notifier(cfg)
    ALERT_DB = db
    scope = ", ".join(cfg["watchlist"]) if cfg["watchlist"] else "all companies"
    log(f"Watching SEC insider filings ({scope}); alerting on buys >= ${cfg['min_purchase_usd']:,}. Ctrl+C to stop.")
    if not (cfg["telegram_bot_token"] and cfg["telegram_chat_id"]):
        log("Telegram is not set up, so alerts will only appear on this screen.")
    last_pos_check = 0.0
    try:
        while True:
            try:
                n = poll(cfg, db, notify)
                log(f"checked, {n} buy alert(s) sent")
            except Exception as e:
                log(f"check failed, will retry: {e}")
            try:
                maybe_scan(cfg, db, notify)
            except Exception as e:
                log(f"scan failed, will retry: {e}")
            if once or time.time() - last_pos_check >= cfg["price_check_minutes"] * 60:
                try:
                    if open_positions(db):
                        log(f"checked open positions, {check_positions(cfg, db, notify)} sell signal(s)")
                except Exception as e:
                    log(f"position check failed, will retry: {e}")
                last_pos_check = time.time()
            if once:
                break
            time.sleep(max(30, int(cfg["poll_seconds"])))
    except KeyboardInterrupt:
        print("\nStopped.")


# --------------------------------------------------------------------------- #
# Demo (no internet)
# --------------------------------------------------------------------------- #
SAMPLE_FORM4 = """<?xml version="1.0"?>
<ownershipDocument>
  <documentType>4</documentType>
  <issuer><issuerCik>0000000000</issuerCik><issuerName>Acme Robotics, Inc.</issuerName>
    <issuerTradingSymbol>ACME</issuerTradingSymbol></issuer>
  <reportingOwner>
    <reportingOwnerId><rptOwnerName>DOE JANE</rptOwnerName></reportingOwnerId>
    <reportingOwnerRelationship><isDirector>1</isDirector><isOfficer>1</isOfficer>
      <officerTitle>Chief Executive Officer</officerTitle></reportingOwnerRelationship>
  </reportingOwner>
  <nonDerivativeTable><nonDerivativeTransaction>
    <transactionDate><value>2026-11-05</value></transactionDate>
    <transactionCoding><transactionCode>P</transactionCode></transactionCoding>
    <transactionAmounts><transactionShares><value>12000</value></transactionShares>
      <transactionPricePerShare><value>24.10</value></transactionPricePerShare>
      <transactionAcquiredDisposedCode><value>A</value></transactionAcquiredDisposedCode></transactionAmounts>
  </nonDerivativeTransaction></nonDerivativeTable>
</ownershipDocument>"""


def cmd_demo(cfg: dict) -> None:
    now = format_datetime(datetime.now(timezone.utc))
    heads = ["Acme Robotics beats estimates and raises outlook", "Analyst upgrades Acme Robotics to buy",
             "Acme Robotics faces delay in new factory"]
    rss = "<rss><channel>" + "".join(f"<item><title>{h}</title><pubDate>{now}</pubDate></item>" for h in heads) \
          + "</channel></rss>"
    p = parse_form4(SAMPLE_FORM4)
    buy, news = summarize_buys(p), parse_news(rss.encode(), 48)
    news["hours"] = 48
    level, why = evaluate(buy, 2, news, DEFAULT_CONFIG)
    filing = {"updated": datetime.now().strftime("%Y-%m-%dT%H:%M"), "index_url": "https://www.sec.gov/ (sample, not a real filing)"}
    notify = make_notifier(cfg)
    notify(format_alert(p, buy, level, why, news, 25.40, filing, demo=True))
    pos = {"ticker": "ACME", "shares": 41, "entry_price": 24.40, "manual": 0,
           "entry_at": (datetime.now(timezone.utc) - timedelta(days=15)).isoformat(timespec="seconds")}
    notify("[DEMO] " + format_closed(pos, 27.10, "trailing stop: price fell 10.3% from its peak of $30.20",
                                     (27.10 - 24.40) * 41, 27.10 / 24.40 - 1,
                                     {"n": 3, "wins": 2, "pnl": 256.10}, via_signal=True))


def main(argv=None) -> None:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser(description="Alerts when company insiders buy their own stock (SEC Form 4) plus news.")
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("init", help="create config.json")
    sub.add_parser("find-chat-id", help="find and save your Telegram chat id")
    sub.add_parser("test-alert", help="send a test message")
    sub.add_parser("demo", help="show a sample alert (no internet needed)")
    r = sub.add_parser("run", help="watch for insider buys")
    r.add_argument("--once", action="store_true", help="check once and exit")
    b = sub.add_parser("bought", help="log a real purchase so I can tell you when to sell")
    b.add_argument("ticker")
    b.add_argument("price", type=float)
    b.add_argument("shares", type=float)
    s = sub.add_parser("sold", help="log a real sale and get the profit report")
    s.add_argument("ticker")
    s.add_argument("price", type=float, nargs="?", help="sale price (default: latest price)")
    sub.add_parser("positions", help="open positions and closed-trade profits")
    sub.add_parser("cloud", help="one check pass for a scheduler such as GitHub Actions (IA_* settings)")
    sub.add_parser("scan", help="scan about 70 large US stocks for dip-buy setups right now")
    ea = sub.add_parser("export-app", help="build the encrypted data file and iPhone web app (used by the cloud job)")
    ea.add_argument("--out", default="site", help="folder to write the website into")
    ea.add_argument("--force", action="store_true", help="publish even if nothing changed")
    bt = sub.add_parser("backtest-scan", help="replay every buy bot on past prices and show how each would have done")
    bt.add_argument("--years", type=float, default=5, help="years of history to test (default 5)")
    bt.add_argument("--hold-days", type=int, nargs="+", default=[5, 10, 20, 90], help="max holding times to compare")
    bt.add_argument("--cost", type=float, default=0.10, help="trading cost per trade in percent (default 0.10)")
    bt.add_argument("--stocks", type=int, default=100, help="how many stocks to test per market, biggest first (default 100)")
    bt.add_argument("--market", default="US", help="US (default), UK, Germany, France, Netherlands, Switzerland, Canada, Australia, Japan, \"Hong Kong\", Romania, or all")
    bt.add_argument("--stop", type=float, help="stop-loss in percent (default: from config)")
    bt.add_argument("--target", type=float, help="profit target in percent (default: from config)")
    bt.add_argument("--trail", type=float, help="trailing stop in percent (default: from config)")
    bd = sub.add_parser("backtest-day", help="replay the day-trading bots on the last ~2 months of 15-minute candles")
    bd.add_argument("--stocks", type=int, default=60, help="how many stocks to test per market (default 60)")
    bd.add_argument("--market", default="US", help="US (default), UK, Germany, France, Netherlands, Switzerland, Canada, or all")
    bd.add_argument("--cost", type=float, default=0.10, help="trading cost per trade in percent (default 0.10)")
    bd.add_argument("--delay", type=int, nargs="+", default=[1, 2], help="candles between the signal and your purchase (default 1 2)")
    bc = sub.add_parser("backtest-crypto", help="replay the crypto bots on the last weeks of Binance 15-minute candles")
    bc.add_argument("--coins", type=int, default=27, help="how many coins to test (default 27)")
    bc.add_argument("--days", type=int, default=45, help="how many days of history (default 45)")
    bc.add_argument("--cost", type=float, default=0.20, help="trading cost per round trip in percent (default 0.20)")
    bc.add_argument("--delay", type=int, nargs="+", default=[1, 2], help="candles between the signal and your purchase (default 1 2)")
    args = ap.parse_args(argv)

    if args.cmd == "init":
        cmd_init()
    elif args.cmd == "find-chat-id":
        cmd_find_chat_id(load_config(strict=False))
    elif args.cmd == "test-alert":
        cfg = load_config(strict=False)
        if not (cfg["telegram_bot_token"] and cfg["telegram_chat_id"]):
            sys.exit("Set telegram_bot_token and telegram_chat_id in config.json first (see the top of this file).")
        make_notifier(cfg)("Test alert from insider_alerts.py. If you can read this, Telegram is set up.")
    elif args.cmd == "demo":
        cmd_demo(load_config(strict=False))
    elif args.cmd == "bought":
        cmd_bought(init_db(), args.ticker, args.price, args.shares, load_config(strict=False))
    elif args.cmd == "sold":
        cmd_sold(init_db(), load_config(strict=False), args.ticker, args.price)
    elif args.cmd == "positions":
        cmd_positions(init_db())
    elif args.cmd == "cloud":
        cmd_cloud(load_config(strict=True))
    elif args.cmd == "scan":
        cmd_scan(load_config(strict=False))
    elif args.cmd == "export-app":
        cmd_export_app(load_config(strict=False), args.out, args.force)
    elif args.cmd == "backtest-scan":
        cfg = load_config(strict=False)
        for key, val in (("stop_loss_pct", args.stop), ("take_profit_pct", args.target), ("trailing_stop_pct", args.trail)):
            if val is not None:
                cfg[key] = val / 100
        cmd_backtest_scan(cfg, args.years, args.hold_days, args.cost, args.stocks, args.market)
    elif args.cmd == "backtest-crypto":
        cmd_backtest_crypto(load_config(strict=False), args.days, args.coins, args.cost, args.delay)
    elif args.cmd == "backtest-day":
        cmd_backtest_day(load_config(strict=False), args.stocks, args.market, args.cost, args.delay)
    else:
        cmd_run(load_config(strict=True), args.once)


if __name__ == "__main__":
    main()
