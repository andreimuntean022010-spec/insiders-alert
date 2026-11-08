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

Honest limits
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
import json
import math
import os
import re
import sqlite3
import sys
import time
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
    return (datetime.now(timezone.utc) - datetime.fromisoformat(pos["entry_at"])).days


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
# Cloud mode: one check pass per run; you give commands by messaging the bot
# --------------------------------------------------------------------------- #
HELP = ("Send me:\n"
        "  bought ACME 24.10 40   (log a buy: ticker, price you paid, shares)\n"
        "  sold ACME 27.10        (log a sale; the price is optional)\n"
        "  positions              (open positions and profits)\n"
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


def make_quiet_notifier(cfg: dict):
    """Telegram only. Nothing about your trades is printed, because cloud logs may be public."""
    token, chat = cfg["telegram_bot_token"], str(cfg["telegram_chat_id"])

    def notify(msg: str) -> None:
        if not (token and chat):
            log("an alert was generated but Telegram is not configured")
            return
        try:
            send_telegram(token, chat, msg)
            log("alert sent")
        except Exception as e:
            log(f"Telegram send failed: {e}")
    return notify


def cmd_cloud(cfg: dict) -> None:
    """One check pass, meant to be started every few minutes by a scheduler such as GitHub Actions."""
    global CHAT_MODE
    CHAT_MODE = True
    db, notify = init_db(), make_quiet_notifier(cfg)

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
    db, notify = init_db(), make_notifier(cfg)
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
    else:
        cmd_run(load_config(strict=True), args.once)


if __name__ == "__main__":
    main()
