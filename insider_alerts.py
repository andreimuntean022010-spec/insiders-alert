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
    "scan_max_alerts": 5,         # at most this many dip alerts per day (best first)
    "scan_min_dollar_volume": 20000000,  # skip stocks trading less than this many dollars per day
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
    """Last close from Stooq (free, no key). Returns None if unavailable."""
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
    db.commit()
    return db


def money(x: float) -> str:
    return f"{'+' if x >= 0 else '-'}${abs(x):,.2f}"


def open_positions(db: sqlite3.Connection, ticker: str | None = None) -> list[dict]:
    sql, args = "SELECT * FROM positions WHERE status='open'", ()
    if ticker:
        sql, args = sql + " AND ticker=?", (ticker,)
    return [dict(r) for r in db.execute(sql + " ORDER BY id", args)]


def held_days(pos: dict) -> int:
    return (utc_now() - datetime.fromisoformat(pos["entry_at"])).days


def open_tracked_position(db: sqlite3.Connection, parsed: dict, entry: float, cfg: dict) -> int:
    """Simulated trade opened when a buy alert fires. Returns the share count."""
    shares = max(1, int(cfg["position_usd"] // entry))
    db.execute("INSERT INTO positions (ticker, company, shares, entry_price, entry_at, peak, last_price, manual) "
               "VALUES (?, ?, ?, ?, ?, ?, ?, 0)",
               (parsed["ticker"], parsed["company"], shares, entry, now_iso(), entry, entry))
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
        return f"trailing stop: price fell {1 - price / peak:.1%} from its peak of ${peak:,.2f}"
    if days >= cfg["max_hold_days"]:
        return f"held {days} days (limit {cfg['max_hold_days']}); time to free up the money"
    return None


def totals(db: sqlite3.Connection) -> dict:
    r = db.execute("SELECT COUNT(*), COALESCE(SUM(pnl > 0), 0), COALESCE(SUM(pnl), 0) "
                   "FROM positions WHERE status='closed'").fetchone()
    return {"n": r[0], "wins": int(r[1]), "pnl": float(r[2])}


def close_position(db: sqlite3.Connection, pos: dict, price: float, reason: str) -> tuple[float, float]:
    pnl = (price - pos["entry_price"]) * pos["shares"]
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
        f"Bought {pos['shares']:g} shares at ${pos['entry_price']:,.2f} on {pos['entry_at'][:10]}, "
        f"sold at ${price:,.2f} ({days} day{'s' if days != 1 else ''})",
        f"{icon} {'PROFIT' if pnl >= 0 else 'LOSS'}: {money(pnl)} ({ret:+.1%})",
        f"All closed trades so far: {tot['n']}, {tot['wins']} winner{'s' if tot['wins'] != 1 else ''}, "
        f"net {money(tot['pnl'])}",
    ]
    if via_signal:
        lines.append("Not financial advice. Simulated: ignores fees, taxes and real-world fills.")
    return "\n".join(lines)


def format_sell_signal(pos: dict, price: float, reason: str) -> str:
    pnl, ret = (price - pos["entry_price"]) * pos["shares"], price / pos["entry_price"] - 1
    sold_cmd = how_to("sold %s %.2f" % (pos["ticker"], price))
    return "\n".join([
        f"🔴 SELL signal: {pos['ticker']}",
        f"Reason: {reason}",
        f"You hold {pos['shares']:g} shares bought at ${pos['entry_price']:,.2f}; "
        f"now ~${price:,.2f}: {money(pnl)} ({ret:+.1%}) unrealised",
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
        if pos["sell_alerted"]:
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
    held = [p for p in open_positions(db, parsed["ticker"]) if not p["sell_alerted"]]
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
    return (f"Logged: {shares:g} {t} at ${price:,.2f}. I'll alert you to sell at ${price * (1 - cfg['stop_loss_pct']):,.2f} "
            f"(stop-loss) or ${price * (1 + cfg['take_profit_pct']):,.2f} (profit target), if it falls "
            f"{cfg['trailing_stop_pct']:.0%} from its peak after gaining, after {cfg['max_hold_days']} days, "
            f"or if insiders start selling.\nWhen you sell, {verb}:  {how_to('sold ' + t + ' <price>')}")


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
    if price is None:
        price = fetch_price(t)
        if price is None:
            raise ValueError(f"Couldn't fetch a price. Send it yourself:  {how_to('sold ' + t + ' <price>')}")
    texts = []
    for pos in held:
        pnl, ret = close_position(db, pos, price, "sold by you")
        texts.append(format_closed(pos, price, "", pnl, ret, totals(db), via_signal=False))
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
        lines.append(f"  {p['ticker']:6} {p['shares']:g} sh  in ${p['entry_price']:,.2f} ({p['entry_at'][:10]})  "
                     f"last ${px:,.2f}  {money((px - p['entry_price']) * p['shares'])} ({px / p['entry_price'] - 1:+.1%})  "
                     f"{'yours' if p['manual'] else 'simulated'}")
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
                "LRCX ADP BLK ETN SBUX MU").split()


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


def fetch_history(ticker: str, days: int = 420) -> list[dict]:
    """Daily prices for the last `days` calendar days. Tries Stooq first, then Yahoo."""
    sym = ticker.lower().replace(".", "-")
    now = utc_now()
    start = now - timedelta(days=days)
    d1, d2, first = start.strftime("%Y%m%d"), now.strftime("%Y%m%d"), start.strftime("%Y-%m-%d")
    yrange = "2y" if days <= 730 else "5y" if days <= 1825 else "10y"
    errors = []
    try:
        bars = parse_stooq_csv(http_get(f"https://stooq.com/q/d/l/?s={sym}.us&i=d&d1={d1}&d2={d2}",
                                        BROWSER_UA, timeout=20, retries=1))
        bars = [b for b in bars if b["date"] >= first]
        if len(bars) >= 210:
            return bars
        errors.append("Stooq: too little data")
    except Exception as e:
        errors.append(f"Stooq: {e}")
    try:
        bars = parse_yahoo_json(http_get(
            f"https://query1.finance.yahoo.com/v8/finance/chart/{ticker.upper().replace('.', '-')}?range={yrange}&interval=1d",
            BROWSER_UA, timeout=20, retries=1))
        bars = [b for b in bars if b["date"] >= first]
        if len(bars) >= 210:
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
    return {"date": bars[-1]["date"], "close": c, "rsi_low": low_rsi, "rsi_now": r_now,
            "vs50": c / s50 - 1, "vs200": c / s200 - 1, "pullback": c / max(closes[-10:]) - 1,
            "atr": atr_pct(bars), "score": score, "why": why,
            "level": "STRONG" if score >= 3 else "MODERATE" if score == 2 else "WEAK"}


def format_dip_alert(ticker: str, e: dict, cfg: dict) -> str:
    icon = {"STRONG": "🟢", "MODERATE": "🟡", "WEAK": "⚪"}[e["level"]]
    lines = [f"{icon} {e['level']} dip-buy idea: {ticker}",
             f"Price ${e['close']:,.2f} (close of {e['date']}) | RSI dipped to {e['rsi_low']:.0f}, now {e['rsi_now']:.0f} | "
             f"pullback {e['pullback']:.1%} from the 10-day high",
             f"Trend: {e['vs50']:+.1%} vs 50-day average, {e['vs200']:+.1%} vs 200-day average"
             + (f" | typical daily move ±{e['atr']:.1%}" if e["atr"] else ""),
             "Why: " + "; ".join(e["why"]),
             f"Sell rules: stop-loss -{cfg['stop_loss_pct']:.0%}, profit target +{cfg['take_profit_pct']:.0%}, "
             f"trailing stop {cfg['trailing_stop_pct']:.0%} from the peak, max {cfg['max_hold_days']} days.",
             "Check the company's next earnings date first: a report can move the price sharply either way. "
             "A dip can keep falling. Not financial advice."]
    return "\n".join(lines)


def run_scan(cfg: dict, db: sqlite3.Connection, notify, force: bool = False) -> int | None:
    """Scan once. Returns the number of alerts, or None if today's prices are not published yet."""
    spy = fetch_history("SPY")  # raises if no price data is reachable
    bar_date = spy[-1]["date"]
    if not force:
        if bar_date == meta_get(db, "scan_bar"):
            log("scan: today's prices are not published yet")
            return None
        if (utc_now().date() - datetime.fromisoformat(bar_date).date()).days > 5:
            raise RuntimeError(f"price data looks stale (latest bar {bar_date})")
    healthy = market_is_healthy(spy)
    state, prev = ("up" if healthy else "down"), meta_get(db, "market_state")
    if state != prev:
        meta_set(db, "market_state", state)
        if not healthy:
            notify("📉 The overall market (S&P 500) is below its 200-day average, a weak phase. "
                   "I'm pausing dip-buy alerts until it recovers. Insider alerts keep running.")
        elif prev == "down":
            notify("📈 The overall market is back above its 200-day average. Dip-buy alerts are on again.")
    meta_set(db, "scan_bar", bar_date)
    if not healthy:
        log("scan: market below its 200-day average, no dip alerts")
        return 0

    held = {p["ticker"] for p in open_positions(db)}
    hits, failed = [], 0
    tickers = [t.upper() for t in (cfg["scan_tickers"] or DEFAULT_SCAN)]
    for t in tickers:
        if t in held:
            continue
        last = meta_get(db, "scan_last_" + t)
        if last and (datetime.fromisoformat(bar_date) - datetime.fromisoformat(last)).days < cfg["scan_cooldown_days"]:
            continue
        try:
            time.sleep(0.3)
            e = evaluate_dip(fetch_history(t), cfg)
        except Exception:
            failed += 1
            continue
        if e:
            hits.append((t, e))
    log(f"scan: {len(tickers)} stocks checked, {failed} unavailable, {len(hits)} setup(s) found")
    hits.sort(key=lambda h: (-h[1]["score"], h[1]["rsi_low"]))

    sent = 0
    for t, e in hits[: cfg["scan_max_alerts"]]:
        msg = format_dip_alert(t, e, cfg)
        bought_cmd = how_to(f"bought {t} <price you paid> <shares>")
        if cfg["auto_track"]:
            shares = open_tracked_position(db, {"ticker": t, "company": t}, e["close"], cfg)
            msg += (f"\nTracking a ${cfg['position_usd']:,} trade ({shares} shares at ~${e['close']:,.2f}, the close). "
                    f"I'll send the sell alert and the % result. Your real price will differ a little.\n"
                    f"Bought it for real? {bought_cmd}")
        else:
            msg += f"\nIf you buy it, log it so I can tell you when to sell:\n  {bought_cmd}"
        notify(msg)
        meta_set(db, "scan_last_" + t, bar_date)
        sent += 1
    return sent


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
            notify("⚠️ I couldn't download price data for today's dip scan. I'll keep trying until midnight (UTC).")
        return
    if n is not None:
        meta_set(db, "scan_done", today)
        log(f"scan done, {n} dip alert(s) sent")


def cmd_scan(cfg: dict) -> None:
    n = run_scan(cfg, init_db(), make_notifier(cfg), force=True)
    print(f"Scan finished: {n} dip alert(s).")


# --------------------------------------------------------------------------- #
# Backtest: replay the dip rules on past prices
# --------------------------------------------------------------------------- #
def simulate_trade(bars: list[dict], i: int, cfg: dict, hold_days: int):
    """Buy at the NEXT day's open after the signal on bar i, then apply the sell rules.
    Returns (exit_index, return, reason) or None if the trade is still open at the end of the data."""
    j = i + 1
    if j >= len(bars) or bars[j]["open"] <= 0:
        return None
    entry = bars[j]["open"]
    stop, target = entry * (1 - cfg["stop_loss_pct"]), entry * (1 + cfg["take_profit_pct"])
    peak, d0 = entry, datetime.fromisoformat(bars[j]["date"])
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
        if (datetime.fromisoformat(b["date"]) - d0).days >= hold_days:
            return k, b["close"] / entry - 1, "time limit"
    return None


def spy_health_by_date(spy: list[dict]) -> dict:
    closes, ok = [b["close"] for b in spy], {}
    for i in range(199, len(spy)):
        ok[spy[i]["date"]] = closes[i] > sum(closes[i - 199:i + 1]) / 200
    return ok


def scan_signals(bars: list[dict], spy_ok: dict, cfg: dict) -> list:
    """Every day the scanner would have alerted, using only data up to that day."""
    out = []
    for i in range(220, len(bars) - 1):
        if not spy_ok.get(bars[i]["date"]):
            continue
        e = evaluate_dip(bars[max(0, i - 259): i + 1], cfg)
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


def run_backtest(cfg: dict, data: dict, spy: list[dict], holds: list[int], cost: float) -> dict:
    """data: ticker -> bars. Applies the same cooldown, one-trade-per-stock and daily alert cap as the live scanner."""
    from collections import defaultdict
    spy_ok = spy_health_by_date(spy)
    sigs = {t: scan_signals(b, spy_ok, cfg) for t, b in data.items()}
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
            cands.sort(key=lambda c: (-c[2]["score"], c[2]["rsi_low"]))
            for t, i, e in cands[: cfg["scan_max_alerts"]]:
                r = simulate_trade(data[t], i, cfg, hold)
                if r is None:
                    continue
                k, ret, reason = r
                trades.append({"ticker": t, "date": d, "level": e["level"], "ret": ret - cost, "reason": reason,
                               "exit_date": data[t][k]["date"], "year": d[:4]})
                free_at[t], last_alert[t] = data[t][k]["date"], d
        base = []                                  # benchmark: buy any of these stocks on any day the market is healthy
        for t, bars in data.items():
            for i in range(220, len(bars) - 1, 3):
                if not spy_ok.get(bars[i]["date"]):
                    continue
                entry, d0 = bars[i + 1]["open"], datetime.fromisoformat(bars[i + 1]["date"])
                for k in range(i + 1, min(len(bars), i + 1 + hold + 8)):
                    if (datetime.fromisoformat(bars[k]["date"]) - d0).days >= hold:
                        base.append(bars[k]["close"] / entry - 1 - cost)
                        break
        results[hold] = {"trades": trades, "stats": trade_stats([t["ret"] for t in trades]),
                         "baseline": trade_stats(base)}
    return results


def print_backtest(res: dict, cfg: dict, first: str, last: str, n_stocks: int, years: float, cost: float) -> None:
    pc = lambda x: f"{x:+.2%}"
    print(f"\nDIP-SCANNER BACKTEST: {n_stocks} stocks, {first} -> {last} ({years:g} years requested), "
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
    print("   The dip rules only help if 'Avg trade' is clearly above the baseline.")
    print(" * The stock list is today's big winners, so old results look better than they would have at the time")
    print("   (survivorship bias). Real results are likely worse. Past results do not predict future ones.")
    print(" * Prices are daily, so stop-loss fills are optimistic in fast markets. Taxes and spreads are not included.")


def cmd_backtest_scan(cfg: dict, years: float, holds: list[int], cost_pct: float) -> None:
    days = int(years * 365) + 330                     # plus a year of warm-up for the 200-day average
    cost = cost_pct / 100
    try:
        spy = fetch_history("SPY", days)
    except Exception as e:
        sys.exit(f"Couldn't download price data, so I can't run the backtest.\nCheck your internet connection and try again. Details: {e}")
    tickers = [t.upper() for t in (cfg["scan_tickers"] or DEFAULT_SCAN)]
    data, failed = {}, []
    for n, t in enumerate(tickers, 1):
        try:
            time.sleep(0.3)
            data[t] = fetch_history(t, days)
            print(f"  [{n}/{len(tickers)}] {t}: {len(data[t])} days", flush=True)
        except Exception as e:
            failed.append(t)
            print(f"  [{n}/{len(tickers)}] {t}: skipped ({str(e)[:60]})", flush=True)
    if len(data) < 5:
        sys.exit("Could not download enough price data to run the backtest.")
    print(f"\nTesting the rules on {len(data)} stocks (this takes a minute)...", flush=True)
    res = run_backtest(cfg, data, spy, holds, cost)
    print_backtest(res, cfg, spy[220]["date"], spy[-1]["date"], len(data), years, cost)
    if failed:
        print(f"\n(Skipped, no data: {', '.join(failed)})")


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


def build_app_data(cfg: dict, db: sqlite3.Connection, now: datetime, history_fn=None) -> dict:
    history_fn = history_fn or fetch_history
    closed = [dict(r) for r in db.execute("SELECT * FROM positions WHERE status='closed' ORDER BY exit_at, id")]
    cum, equity = 0.0, []
    for p in closed:
        cum += p["pnl"]
        equity.append({"t": p["exit_at"], "cum": round(cum, 2), "ticker": p["ticker"],
                       "pnl": round(p["pnl"], 2), "ret": round(p["ret"], 4)})
    opens = []
    for p in open_positions(db):
        last = p["last_price"] or p["entry_price"]
        sell_by = datetime.fromisoformat(p["entry_at"]) + timedelta(days=cfg["max_hold_days"])
        opens.append({"ticker": p["ticker"], "shares": p["shares"], "entry_price": p["entry_price"],
                      "entry_at": p["entry_at"], "last_price": last, "mine": bool(p["manual"]),
                      "pnl": round((last - p["entry_price"]) * p["shares"], 2), "ret": round(last / p["entry_price"] - 1, 4),
                      "days": held_days(p), "stop": round(p["entry_price"] * (1 - cfg["stop_loss_pct"]), 2),
                      "target": round(p["entry_price"] * (1 + cfg["take_profit_pct"]), 2),
                      "sell_by": sell_by.strftime("%Y-%m-%d")})
    recent = [
        {"ticker": p["ticker"], "shares": p["shares"], "entry_price": p["entry_price"], "exit_price": p["exit_price"],
         "entry_at": p["entry_at"], "exit_at": p["exit_at"], "pnl": round(p["pnl"], 2), "ret": round(p["ret"], 4),
         "reason": p["exit_reason"], "mine": bool(p["manual"])} for p in reversed(closed[-30:])]
    wins = sum(1 for p in closed if p["pnl"] > 0)
    alerts = []
    for r in db.execute("SELECT at, text FROM alerts_log ORDER BY id DESC LIMIT 60"):
        alerts.append({"at": r["at"], "text": r["text"]})
    charts, tickers = {}, []
    for t in [p["ticker"] for p in opens] + [p["ticker"] for p in recent[:10]]:
        if t not in tickers:
            tickers.append(t)
    for t in tickers[:20]:
        try:
            charts[t] = [[b["date"], round(b["close"], 2)] for b in history_fn(t, 220)[-120:]]
        except Exception as e:
            log(f"app: no price history for {t} ({type(e).__name__})")
    key_pub = ""
    if have_crypto():
        try:
            key_pub = vapid_keys(db)[1]
        except Exception:
            pass
    return {"v": 1, "generated_at": now.isoformat(timespec="seconds"),
            "market": meta_get(db, "market_state"),
            "rules": {k: cfg[k] for k in ("stop_loss_pct", "take_profit_pct", "trailing_stop_pct", "max_hold_days",
                                          "position_usd", "auto_track")},
            "push": {"available": bool(key_pub), "key": key_pub, "devices": len(json.loads(meta_get(db, "push_subs", "[]")))},
            "stats": {"n": len(closed), "wins": wins, "net": round(sum(p["pnl"] for p in closed), 2),
                      "avg_ret": round(sum(p["ret"] for p in closed) / len(closed), 4) if closed else 0.0},
            "equity": equity, "open": opens, "closed": recent, "alerts": alerts, "charts": charts}


# <<APP_FILES_BEGIN>>
APP_FILES_B64 = {
    "index.html": (
        "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"
        "5Wz65Z3/C/uEE0s="
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
               history_fn=None, now: datetime | None = None) -> bool:
    """Write the website (app + encrypted data) into out_dir if something worth publishing changed."""
    now = now or utc_now()
    opens = open_positions(db)
    sig = "|".join([str(db.execute("SELECT COALESCE(MAX(id), 0) FROM alerts_log").fetchone()[0]),
                    str(db.execute("SELECT COUNT(*) FROM positions WHERE status='closed'").fetchone()[0]),
                    ",".join(f"{p['id']}:{p['manual']}" for p in opens), meta_get(db, "market_state"),
                    meta_get(db, "push_subs", "[]")])
    last = meta_get(db, "app_published_at")
    age = (now - datetime.fromisoformat(last)).total_seconds() if last else None
    if not (force or sig != meta_get(db, "app_sig") or age is None or (opens and age >= 1800) or age >= 43200):
        return False
    data = build_app_data(cfg, db, now, history_fn)
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
        "  push <code>            (connect the iPhone app; the app shows you the code)\n"
        "  help                   (show this)")


def _number(s: str) -> float:
    try:
        return float(s.replace(",", "."))
    except ValueError:
        raise ValueError(f"'{s}' is not a number") from None


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
    bt = sub.add_parser("backtest-scan", help="replay the dip-buy rules on past prices and show how they would have done")
    bt.add_argument("--years", type=float, default=5, help="years of history to test (default 5)")
    bt.add_argument("--hold-days", type=int, nargs="+", default=[5, 10, 20, 90], help="max holding times to compare")
    bt.add_argument("--cost", type=float, default=0.10, help="trading cost per trade in percent (default 0.10)")
    bt.add_argument("--stop", type=float, help="stop-loss in percent (default: from config)")
    bt.add_argument("--target", type=float, help="profit target in percent (default: from config)")
    bt.add_argument("--trail", type=float, help="trailing stop in percent (default: from config)")
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
        cmd_backtest_scan(cfg, args.years, args.hold_days, args.cost)
    else:
        cmd_run(load_config(strict=True), args.once)


if __name__ == "__main__":
    main()
