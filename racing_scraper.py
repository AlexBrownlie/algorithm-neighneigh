#!/usr/bin/env python3
"""
racing_scraper.py - collect Australian horse-racing data into SQLite and export
a leakage-safe, model-ready CSV.

Commands
  init                          create the database
  ingest-punters --file saved.html | --url URL   (punters.com.au track results page)
  crawl-track  --track tracks/flemington_45 [--years 2] [--page-template URL]
                                walk a Punters track's results history back N years\n  ingest-html  --profile P.json --date YYYY-MM-DD [--end YYYY-MM-DD]
                                scrape meetings via a site profile (CSS selectors)
  load-bsp     --url URL | --file F.csv
                                load Betfair BSP historical price CSV (optional)
  import-csv   --kind runs|races|horses|odds --file F.csv
                                load data you already have (any source)
  export       --out features.csv [--from D] [--to D]
                                one row per runner, features use ONLY earlier races
  stats                         row counts

Notes
  * Respects robots.txt, rate limits, caches raw pages with timestamps.
  * You must check each site's terms of use yourself. If robots.txt or the terms
    forbid automated access, use import-csv with data you are licensed to use.
  * Site profiles contain CSS selectors. The example profile uses PLACEHOLDER
    selectors; inspect the real page (browser dev tools) and edit them.
"""
import argparse, csv, datetime as dt, hashlib, io, json, os, re, sqlite3, sys, time
import urllib.robotparser
from urllib.parse import urljoin, urlparse

import requests
from bs4 import BeautifulSoup

DB_DEFAULT = "racing.db"
CACHE_DIR = "raw_cache"
USER_AGENT = "personal-racing-research/1.0 (contact: set-your-email)"

SCHEMA = """
CREATE TABLE IF NOT EXISTS meetings(
  meeting_id TEXT PRIMARY KEY, race_date TEXT, track TEXT, state TEXT,
  rail TEXT, weather TEXT, source TEXT, scraped_at TEXT);
CREATE TABLE IF NOT EXISTS races(
  race_id TEXT PRIMARY KEY, meeting_id TEXT, race_date TEXT, track TEXT, race_no INTEGER,
  name TEXT, start_time TEXT, distance_m INTEGER, class TEXT, prize_money REAL,
  field_size INTEGER, track_rating_label TEXT, track_rating_num INTEGER, rail TEXT,
  winning_time_s REAL, source TEXT, scraped_at TEXT);
CREATE TABLE IF NOT EXISTS horses(
  horse_key TEXT PRIMARY KEY, name TEXT, sire TEXT, dam TEXT, dam_sire TEXT,
  sex TEXT, colour TEXT, foaled TEXT, country TEXT);
CREATE TABLE IF NOT EXISTS runs(
  run_id TEXT PRIMARY KEY, race_id TEXT, horse_key TEXT, saddle_cloth INTEGER, barrier INTEGER,
  jockey TEXT, trainer TEXT, weight_kg REAL, claim_kg REAL, gear TEXT, age INTEGER,
  finish_pos INTEGER, margin_l REAL, scratched INTEGER DEFAULT 0, source TEXT, scraped_at TEXT);
CREATE TABLE IF NOT EXISTS odds_snapshots(
  run_id TEXT, captured_at TEXT, source TEXT, price_type TEXT, price REAL,
  PRIMARY KEY(run_id, captured_at, source, price_type));
CREATE TABLE IF NOT EXISTS betfair_bsp(
  event_date TEXT, menu_hint TEXT, event_name TEXT, event_dt TEXT, selection_name TEXT,
  horse_key TEXT, track_norm TEXT, race_no INTEGER, win_lose INTEGER, bsp REAL, ppwap REAL,
  morningwap REAL, ppmax REAL, ppmin REAL, ipmax REAL, ipmin REAL,
  morningtradedvol REAL, pptradedvol REAL, iptradedvol REAL, fetched_at TEXT);
CREATE TABLE IF NOT EXISTS meeting_index(
  meeting_date TEXT, track_slug TEXT, feature_race_url TEXT PRIMARY KEY, feature_title TEXT,
  distance_m INTEGER, prize_money REAL, track_rating_label TEXT, track_rating_num INTEGER,
  scraped_at TEXT, done INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS eq_tracks(
  code TEXT PRIMARY KEY, name TEXT, country TEXT, added_at TEXT);
CREATE TABLE IF NOT EXISTS chart_text(
  pdf_url TEXT PRIMARY KEY, track_code TEXT, race_date TEXT, pdf_path TEXT, text TEXT,
  fetched_at TEXT, parsed INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS raw_pages(
  url TEXT, fetched_at TEXT, status INTEGER, sha256 TEXT, path TEXT);
CREATE INDEX IF NOT EXISTS ix_runs_horse ON runs(horse_key);
CREATE INDEX IF NOT EXISTS ix_runs_race ON runs(race_id);
CREATE INDEX IF NOT EXISTS ix_races_date ON races(race_date);
CREATE INDEX IF NOT EXISTS ix_bsp ON betfair_bsp(event_date, track_norm, race_no, horse_key);
"""

# ------------------------------------------------------------------ helpers
def now_iso():
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")

def norm(s):
    """Normalise names for keys: lowercase, strip punctuation/country tags/spaces."""
    if s is None:
        return ""
    s = re.sub(r"\(.*?\)", "", str(s).lower())
    return re.sub(r"[^a-z0-9]", "", s)

def to_float(s):
    if s is None: return None
    if isinstance(s, (int, float)): return float(s)
    m = re.search(r"-?\d+(?:[.,]\d+)?", str(s).replace(",", "") if re.search(r"\d,\d{3}", str(s)) else str(s))
    return float(m.group(0).replace(",", ".")) if m else None

def to_int(s):
    f = to_float(s)
    return int(f) if f is not None else None

def parse_track_rating(s):
    """'Heavy 8' -> ('Heavy', 8); 'Good 4' -> ('Good', 4); 'Soft' -> ('Soft', 5)."""
    if not s: return None, None
    s = str(s).strip()
    m = re.match(r"(?i)(firm|good|soft|heavy|synthetic|dead)\s*\(?(\d{1,2})?\)?", s)
    if not m: return s, None
    label = m.group(1).capitalize()
    num = int(m.group(2)) if m.group(2) else {"Firm": 1, "Good": 3, "Dead": 4, "Soft": 6,
                                              "Heavy": 9, "Synthetic": None}.get(label)
    return label, num

MARGIN_WORDS = {"nose": .05, "short head": .1, "sh": .1, "head": .2, "hd": .2, "short neck": .25,
                "neck": .3, "nk": .3, "dead heat": 0.0, "dh": 0.0}
def parse_margin(s):
    """'1.25L', '0.5', 'Head', 'Nose' -> lengths (float)."""
    if s is None: return None
    t = str(s).strip().lower().replace("lengths", "").replace("length", "").rstrip("l").strip()
    if t in MARGIN_WORDS: return MARGIN_WORDS[t]
    return to_float(t)

def parse_time_s(s):
    """'1:10.52' -> 70.52"""
    if not s: return None
    m = re.match(r"\s*(?:(\d+):)?(\d+(?:\.\d+)?)", str(s))
    return (int(m.group(1) or 0) * 60 + float(m.group(2))) if m else None

def parse_distance(s):
    m = re.search(r"(\d{3,4})\s*m?", str(s or ""))
    return int(m.group(1)) if m else None

def parse_money(s):
    if not s: return None
    t = str(s).lower().replace(",", "").replace("$", "")
    m = re.search(r"(\d+(?:\.\d+)?)\s*(k|m)?", t)
    if not m: return None
    v = float(m.group(1))
    return v * {"k": 1e3, "m": 1e6}.get(m.group(2), 1)

def parse_price(s):
    """'$3.40', '3.4', '5/2' -> decimal odds."""
    if not s: return None
    t = str(s).strip().replace("$", "")
    m = re.match(r"(\d+)\s*/\s*(\d+)", t)
    if m: return 1 + int(m.group(1)) / int(m.group(2))
    f = to_float(t)
    return f if f and f > 1 else None

def connect(path):
    con = sqlite3.connect(path)
    con.row_factory = sqlite3.Row
    con.create_function("norm", 1, norm)
    con.executescript(SCHEMA)
    con.executescript(EXTRA_SCHEMA)
    _migrate(con)
    return con

# ------------------------------------------------------------------ fetcher
class Fetcher:
    def __init__(self, con, delay=3.0, cache_dir=CACHE_DIR, ua=USER_AGENT, respect_robots=True):
        self.con, self.delay, self.cache_dir, self.ua = con, delay, cache_dir, ua
        self.respect_robots = respect_robots
        self._last = 0.0
        self._robots = {}
        self.sess = requests.Session()
        self.sess.headers["User-Agent"] = ua
        os.makedirs(cache_dir, exist_ok=True)

    def _load_robots(self, base):
        """Fetch + parse robots.txt once per site. Returns (parser_or_None, status, detail)."""
        if base in self._robots: return self._robots[base]
        rp = urllib.robotparser.RobotFileParser()
        status, detail = None, ""
        try:
            r = self.sess.get(base + "/robots.txt", timeout=20)
            status = r.status_code
            if status == 200:
                rp.parse(r.text.splitlines()); detail = "ok"
            elif status in (401, 403):
                rp = None; detail = f"robots.txt itself returned HTTP {status} (site is refusing this client)"
            elif 400 <= status < 500:
                rp.parse([]); detail = f"no robots.txt (HTTP {status}); treated as allow-all"
            else:
                rp = None; detail = f"robots.txt returned HTTP {status} (server error)"
        except requests.RequestException as e:
            rp = None; detail = f"could not fetch robots.txt: {type(e).__name__}: {e}"
        self._robots[base] = (rp, status, detail)
        return self._robots[base]

    def allowed(self, url):
        self.deny_reason = ""
        if not self.respect_robots: return True
        p = urlparse(url)
        if p.scheme == "file": return True
        rp, status, detail = self._load_robots(f"{p.scheme}://{p.netloc}")
        if rp is None:
            self.deny_reason = f"cannot confirm {url} is allowed - {detail}. Not crawling."
            return False
        if not rp.can_fetch(self.ua, url):
            self.deny_reason = f"robots.txt disallows {url}"
            return False
        return True

    def crawl_delay(self, url):
        p = urlparse(url)
        rp = (self._robots.get(f"{p.scheme}://{p.netloc}") or (None,))[0]
        try:
            return float(rp.crawl_delay(self.ua) or 0) if rp else 0.0
        except Exception:
            return 0.0

    def get_bytes(self, url, dest):
        """Download a binary file to dest (skips if already there). Honors robots.txt + delay."""
        p = urlparse(url)
        if os.path.exists(dest) and os.path.getsize(dest) > 0:
            return dest
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        if p.scheme == "file":
            import shutil; shutil.copyfile(p.path, dest); return dest
        if not self.allowed(url):
            raise PermissionError(self.deny_reason or f"robots.txt disallows {url}")
        wait = max(self.delay, self.crawl_delay(url)) - (time.time() - self._last)
        if wait > 0: time.sleep(wait)
        r = self.sess.get(url, timeout=60)
        self._last = time.time()
        self.con.execute("INSERT INTO raw_pages VALUES(?,?,?,?,?)",
                         (url, now_iso(), r.status_code, hashlib.sha256(r.content).hexdigest(), dest))
        self.con.commit()
        if r.status_code != 200 or not r.content.startswith(b"%PDF"):
            raise RuntimeError(f"HTTP {r.status_code} / not a PDF: {url}")
        with open(dest, "wb") as f: f.write(r.content)
        return dest

    def get(self, url, use_cache=True):
        """Return page text. Raises PermissionError if robots.txt disallows."""
        p = urlparse(url)
        if p.scheme == "file":
            with open(p.path, encoding="utf-8") as f:
                return f.read()
        key = hashlib.sha256(url.encode()).hexdigest()[:24]
        path = os.path.join(self.cache_dir, key + ".html")
        if use_cache and os.path.exists(path):
            with open(path, encoding="utf-8") as f:
                return f.read()
        if not self.allowed(url):
            raise PermissionError(self.deny_reason or f"robots.txt disallows {url}")
        wait = self.delay - (time.time() - self._last)
        if wait > 0: time.sleep(wait)
        r = self.sess.get(url, timeout=30)
        self._last = time.time()
        text = r.text
        sha = hashlib.sha256(text.encode()).hexdigest()
        snap = os.path.join(self.cache_dir, f"{key}_{int(time.time())}.html")
        with open(snap, "w", encoding="utf-8") as f: f.write(text)
        if r.status_code == 200:
            with open(path, "w", encoding="utf-8") as f: f.write(text)
        self.con.execute("INSERT INTO raw_pages VALUES(?,?,?,?,?)",
                         (url, now_iso(), r.status_code, sha, snap))
        self.con.commit()
        if r.status_code != 200:
            raise RuntimeError(f"HTTP {r.status_code} for {url}")
        return text

# ------------------------------------------------------------------ upserts
def upsert(con, table, key_cols, row):
    cols = list(row)
    upd = ", ".join(f"{c}=COALESCE(excluded.{c}, {table}.{c})" for c in cols if c not in key_cols)
    sql = (f"INSERT INTO {table}({','.join(cols)}) VALUES({','.join('?'*len(cols))}) "
           f"ON CONFLICT({','.join(key_cols)}) DO UPDATE SET {upd}" if upd else
           f"INSERT OR IGNORE INTO {table}({','.join(cols)}) VALUES({','.join('?'*len(cols))})")
    con.execute(sql, [row[c] for c in cols])

def store_race(con, meeting, race, runners, source):
    ts = now_iso()
    track, date = meeting["track"], meeting["race_date"]
    mid = f"{date}_{norm(track)}"
    upsert(con, "meetings", ["meeting_id"], dict(
        meeting_id=mid, race_date=date, track=track, state=meeting.get("state"),
        rail=meeting.get("rail"), weather=meeting.get("weather"), source=source, scraped_at=ts))
    rid = f"{mid}_R{race['race_no']}"
    label, num = parse_track_rating(race.get("track_rating") or meeting.get("track_rating"))
    upsert(con, "races", ["race_id"], dict(
        race_id=rid, meeting_id=mid, race_date=date, track=track, race_no=race["race_no"],
        name=race.get("name"), start_time=race.get("start_time"),
        distance_m=parse_distance(race.get("distance")), **{"class": race.get("class")},
        prize_money=parse_money(race.get("prize")), field_size=len([r for r in runners if not r.get('scratched')]) or None,
        track_rating_label=label, track_rating_num=num, rail=meeting.get("rail"),
        winning_time_s=parse_time_s(race.get("winning_time")), source=source, scraped_at=ts))
    for r in runners:
        hk = norm(r["name"])
        if not hk: continue
        upsert(con, "horses", ["horse_key"], dict(
            horse_key=hk, name=r["name"].strip(), sire=r.get("sire"), dam=r.get("dam"),
            dam_sire=r.get("dam_sire"), sex=r.get("sex"), colour=r.get("colour"),
            foaled=r.get("foaled"), country=r.get("country")))
        run_id = f"{rid}_{hk}"
        fin = to_int(r.get("finish"))
        upsert(con, "runs", ["run_id"], dict(
            run_id=run_id, race_id=rid, horse_key=hk, saddle_cloth=to_int(r.get("cloth")),
            barrier=to_int(r.get("barrier")), jockey=(r.get("jockey") or None),
            trainer=(r.get("trainer") or None), weight_kg=to_float(r.get("weight")),
            claim_kg=to_float(r.get("claim")), gear=r.get("gear"), age=to_int(r.get("age")),
            finish_pos=fin, margin_l=parse_margin(r.get("margin")),
            scratched=1 if r.get("scratched") else 0, source=source, scraped_at=ts))
        prices = dict(r.get("prices") or {})
        if r.get("price"):
            prices[r.get("price_type") or "fixed_win"] = r["price"]
        for ptype, raw in prices.items():
            p = parse_price(raw)
            if p:
                upsert(con, "odds_snapshots", ["run_id", "captured_at", "source", "price_type"], dict(
                    run_id=run_id, captured_at=ts, source=source, price_type=ptype, price=p))
    con.commit()
    return rid

# ------------------------------------------------------------------ HTML profile adapter
def _txt(node, sel):
    """Select text by CSS selector (supports 'sel@attr' for attributes)."""
    if not sel or node is None: return None
    attr = None
    if "@" in sel: sel, attr = sel.rsplit("@", 1)
    el = node.select_one(sel) if sel else node
    if el is None: return None
    return (el.get(attr) if attr else el.get_text(" ", strip=True)) or None

def parse_meeting_page(html, profile, date_str, url=""):
    soup = BeautifulSoup(html, "html.parser")
    m = profile.get("meeting", {})
    meeting = {"race_date": date_str, "track": _txt(soup, m.get("track")) or profile.get("default_track"),
               "rail": _txt(soup, m.get("rail")), "weather": _txt(soup, m.get("weather")),
               "track_rating": _txt(soup, m.get("track_rating")), "state": _txt(soup, m.get("state"))}
    out = []
    for i, rn in enumerate(soup.select(profile["race_selector"]), 1):
        rs = profile.get("race", {})
        race = {k: _txt(rn, rs.get(k)) for k in
                ("name", "distance", "class", "prize", "track_rating", "start_time", "winning_time")}
        race["race_no"] = to_int(_txt(rn, rs.get("number"))) or i
        runners = []
        for ru in rn.select(profile["runner_selector"]):
            rsel = profile.get("runner", {})
            r = {k: _txt(ru, v) for k, v in rsel.items() if k != "scratched"}
            sc = rsel.get("scratched")
            r["scratched"] = bool(sc and (ru.select_one(sc) is not None or
                                          "scr" in " ".join(ru.get("class") or []).lower()))
            if r.get("name"): runners.append(r)
        out.append((race, runners))
    return meeting, out

def ingest_html(con, fetcher, profile, d0, d1):
    d = d0
    n = 0
    while d <= d1:
        ds = d.isoformat()
        idx_url = profile["meeting_index_url"].format(date=d)
        try:
            idx = BeautifulSoup(fetcher.get(idx_url), "html.parser")
        except (PermissionError, RuntimeError) as e:
            print(f"[skip {ds}] {e}", file=sys.stderr); d += dt.timedelta(days=1); continue
        links = [urljoin(idx_url, a["href"]) for a in idx.select(profile["meeting_link_selector"]) if a.get("href")]
        for url in dict.fromkeys(links):
            try:
                meeting, races = parse_meeting_page(fetcher.get(url), profile, ds, url)
            except (PermissionError, RuntimeError) as e:
                print(f"[skip {url}] {e}", file=sys.stderr); continue
            if not meeting["track"]:
                print(f"[skip {url}] no track name parsed - check selectors", file=sys.stderr); continue
            for race, runners in races:
                store_race(con, meeting, race, runners, profile.get("name", "html"))
                n += 1
        d += dt.timedelta(days=1)
    print(f"stored {n} races")


# ------------------------------------------------------------------ Punters.com.au results adapter
def _own_text(el):
    """Text directly inside el (not inside child tags)."""
    return " ".join(t.strip() for t in el.find_all(string=True, recursive=False) if t.strip())

def parse_punters_results(html):
    """Parse a punters.com.au track results page (one table per race).
    Returns list of (meeting, race, runners). Gives results + SP/tote prices only;
    trainer, barrier, weight, pedigree are on the per-race Form Guide pages."""
    soup = BeautifulSoup(html, "html.parser")
    title = (soup.title.get_text() if soup.title else "")
    track = re.sub(r"(?i)\s*race results.*$", "", title).strip() or None
    out = []
    for tb in soup.select("table.results-table"):
        h = tb.find_previous("h4", class_="results-date-heading")
        try:
            date = dt.datetime.strptime(h.get_text(strip=True), "%A %d %B %Y").date().isoformat()
        except (AttributeError, ValueError):
            date = None
        th = tb.select_one("thead th")
        if th is None or date is None or track is None: continue
        strong = th.find("strong")
        race_no = to_int(strong.get_text()) if strong else None
        name = _own_text(th) or None
        spans = [x.get_text(" ", strip=True) for x in th.select(".details-line span.capitalize")]
        dist = th.select_one("abbr.conversion")
        start = th.select_one("abbr.timestamp")
        local_start = None
        if start and start.get("datetime"):
            try:  # UTC -> Melbourne local; fixed offset is fine for stored ordering within a day
                u = dt.datetime.fromisoformat(start["datetime"].replace("Z", "+00:00"))
                from zoneinfo import ZoneInfo
                local_start = u.astimezone(ZoneInfo("Australia/Melbourne")).strftime("%H:%M")
            except Exception:
                pass
        race = {"race_no": race_no, "name": name, "distance": dist.get("data-value") if dist else None,
                "prize": next((x for x in spans if "$" in x), None),
                "track_rating": next((x for x in spans if re.match(r"(?i)(firm|good|soft|heavy|synthetic|dead)", x)), None),
                "start_time": local_start}
        runners = []
        for i, tr in enumerate(tb.select("tbody tr")):
            tds = tr.find_all("td", recursive=False)
            if len(tds) < 5: continue
            a = tds[0].find("a")
            if a is None: continue
            icon = tds[0].select_one(".result-icon")
            jk = tds[1].select_one(".jockey-name")
            jtxt = re.sub(r"^\s*J:\s*", "", jk.get_text(" ", strip=True)) if jk else None
            tote = [x.strip() for x in tds[2].get_text(" ", strip=True).split("/")]
            prices = {"sp": tds[3].get_text(strip=True)}
            if tote and tote[0]: prices["tote_win"] = tote[0]
            if len(tote) > 1 and tote[1]: prices["tote_place"] = tote[1]
            mg = tds[4].get_text(strip=True)
            if i == 0 and ":" in mg:          # winner's row holds the race time
                race["winning_time"] = mg; mg = None
            runners.append({"name": a.get_text(strip=True), "cloth": _own_text(tds[0]),
                            "finish": icon.get_text(strip=True) if icon else None,
                            "jockey": jtxt, "margin": mg, "prices": prices})
        meeting = {"race_date": date, "track": track}
        out.append((meeting, race, runners))
    return out

def ingest_punters(con, html, source="punters"):
    n = 0
    for meeting, race, runners in parse_punters_results(html):
        if race["race_no"] and runners:
            store_race(con, meeting, race, runners, source); n += 1
    print(f"stored {n} races")

# ------------------------------------------------------------------ Punters track-history crawler
PUNTERS_BASE = "https://www.punters.com.au/"
NEXT_TEXT = re.compile(r"(?i)^\s*(next|older|previous|prev|more|load more|show more|earlier|[<>\u2039\u203a\u00ab\u00bb]+)\b")

def _track_url(track):
    t = track.strip()
    if t.startswith("file:"): return t
    if t.startswith("http"): return t if t.endswith("/") or "?" in t else t + "/"
    t = t.strip("/")
    if not t.startswith("tracks/"): t = "tracks/" + t
    if not t.endswith("results"): t += "/results"
    return PUNTERS_BASE + t + "/"

def discover_links(html, page_url, results_url):
    """Candidate 'older results' links on a page: rel=next, next/older-style anchors,
    or any link back into this track's results path carrying a query/extra path segment."""
    soup = BeautifulSoup(html, "html.parser")
    base_path = urlparse(results_url).path
    found = []
    for a in soup.find_all("a", href=True):
        h = a["href"].strip()
        if h.startswith(("javascript:", "#", "mailto:")): continue
        u = urljoin(page_url, h).split("#")[0]
        pu = urlparse(u)
        if pu.netloc != urlparse(results_url).netloc: continue
        rel = " ".join(a.get("rel") or [])
        text = a.get_text(" ", strip=True)
        same_track = pu.path.startswith(base_path) and u.rstrip("/") != results_url.rstrip("/")
        if "next" in rel or NEXT_TEXT.match(text) and pu.path.startswith(base_path) or same_track:
            found.append(u)
    for l in soup.find_all("link", rel=True):
        if "next" in (l.get("rel") or []) and l.get("href"):
            found.append(urljoin(page_url, l["href"]))
    return list(dict.fromkeys(found))

def page_dates(html):
    return [x.get_text(strip=True) for x in BeautifulSoup(html, "html.parser").select("h4.results-date-heading")]

def crawl_track(con, fetcher, track, since, max_pages=500, template=None, verbose=True):
    """Walk a track's results history back to `since`, storing every race found.
    Strategy 1 (default): follow pagination/older links found on each page.
    Strategy 2: --page-template 'https://.../results/?page={n}' (n = 1, 2, 3, ...)."""
    results_url = _track_url(track)
    seen, queue, pages, races_total, oldest_seen = set(), [], 0, 0, None
    def handle(url, fresh):
        nonlocal pages, races_total, oldest_seen
        html = fetcher.get(url, use_cache=not fresh)
        pages += 1
        parsed = parse_punters_results(html)
        dates = sorted({m["race_date"] for m, _, _ in parsed})
        kept = 0
        for meeting, race, runners in parsed:
            if meeting["race_date"] < since.isoformat(): continue
            if race["race_no"] and runners:
                store_race(con, meeting, race, runners, "punters"); kept += 1
        races_total += kept
        if dates:
            oldest_seen = min(dates[0], oldest_seen or dates[0])
        if verbose:
            print(f"[{pages}] {url}  meetings={dates or '-'} stored_races={kept}", flush=True)
        return html, dates, parsed
    try:
        if template:
            n = 1
            while pages < max_pages:
                url = template.format(n=n, base=results_url)
                html, dates, parsed = handle(url, fresh=(n == 1))
                if not parsed or (dates and dates[0] < since.isoformat()): break
                n += 1
            return races_total, pages, oldest_seen
        html, dates, parsed = handle(results_url, fresh=True)
        seen.add(results_url)
        links = discover_links(html, results_url, results_url)
        if not links and parsed:
            print("\nNo pagination / older-results links found in the page HTML. The history is\n"
                  "probably loaded by JavaScript. Open the live page, scroll/click to load older\n"
                  "results, then in browser dev tools > Network copy the request URL that appears\n"
                  "and rerun with --page-template (use {n} for the page number, e.g.\n"
                  "  --page-template 'https://www.punters.com.au/tracks/flemington_45/results/?page={n}').\n")
        queue = links
        stop = bool(dates and dates[0] < since.isoformat())
        while queue and pages < max_pages and not stop:
            url = queue.pop(0)
            if url in seen: continue
            seen.add(url)
            html, dates, parsed = handle(url, fresh=False)
            if dates and dates[0] < since.isoformat():
                continue      # past the cutoff: don't follow this branch further
            for l in discover_links(html, url, results_url):
                if l not in seen: queue.append(l)
    except PermissionError as e:
        print(f"[stopped] {e}", file=sys.stderr)
    return races_total, pages, oldest_seen

# ------------------------------------------------------------------ Punters meeting index ("Latest Results at <track>")
def parse_meeting_index(html):
    """One entry per meeting from the 'Latest Results' list at the bottom of a track results page:
    date, the meeting's headline race, and a link to that race's form-guide page."""
    soup = BeautifulSoup(html, "html.parser")
    out = []
    for li in soup.select("ul.latest-track-results li.latest-result"):
        a = li.find("a", href=True)
        t = li.select_one(".latest-result__track-title")
        if not a or not t: continue
        m = re.search(r"/form-guide/horses/([a-z0-9-]+)-(\d{8})/", a["href"])
        if not m: continue
        title = t.get_text(" ", strip=True)
        rating = li.select_one(".latest-result__track-conditions")
        label, num = parse_track_rating(rating.get_text(strip=True) if rating else None)
        rest = re.sub(r"^.*?\d{4}\s*", "", title, count=1)          # strip 'Saturday 12th September, 2026'
        out.append(dict(meeting_date=dt.datetime.strptime(m.group(2), "%Y%m%d").date().isoformat(),
                        track_slug=m.group(1), feature_race_url=a["href"], feature_title=rest,
                        distance_m=parse_distance(rest), prize_money=parse_money(re.search(r"\$[\d.,]+[km]?", rest).group(0)) if re.search(r"\$[\d.,]+[km]?", rest) else None,
                        track_rating_label=label, track_rating_num=num))
    return out

def sibling_race_links(html, page_url):
    """All race pages of the same meeting that are linked from a form-guide race page."""
    m = re.search(r"/form-guide/horses/([a-z0-9-]+-\d{8})/", page_url)
    if not m: return []
    soup = BeautifulSoup(html, "html.parser")
    links = {urljoin(page_url, a["href"]).split("#")[0].split("?")[0] for a in soup.find_all("a", href=True)}
    return sorted(u for u in links if f"/form-guide/horses/{m.group(1)}/" in u and re.search(r"-race-\d+/?$", u))

def list_meetings(con, html, since=None):
    n = 0
    rows = parse_meeting_index(html)
    for r in rows:
        if since and r["meeting_date"] < since.isoformat(): continue
        r["scraped_at"] = now_iso()
        upsert(con, "meeting_index", ["feature_race_url"], r); n += 1
    con.commit()
    if rows:
        print(f"{len(rows)} meetings listed ({min(r['meeting_date'] for r in rows)} .. {max(r['meeting_date'] for r in rows)}); {n} stored")
    else:
        print("no 'Latest Results' list found in the page")
    return n

# ------------------------------------------------------------------ Equibase chart PDFs (North America)
EQ_CAL = "https://www.equibase.com/static/chart/pdf/{track}-calendar.html"
EQ_PDF = "https://www.equibase.com/static/chart/pdf/{name}"
EQ_NAME = re.compile(r"([A-Z0-9]{2,4})(\d{2})(\d{2})(\d{2})([A-Z]{3})?\.pdf", re.I)   # e.g. ALB091326USA.pdf = MMDDYY (assumed)

def parse_equibase_calendar(html, track, base_url):
    """Find chart-PDF links for one track on its calendar page. Date taken from MMDDYY in the file name
    (assumption - verify against the text of a downloaded chart)."""
    soup = BeautifulSoup(html, "html.parser")
    hrefs = [a["href"] for a in soup.find_all("a", href=True)] + re.findall(r"[\w/.:-]*%s\d{6}[A-Z]{0,3}\.pdf" % re.escape(track), html, re.I)
    out = {}
    for h in hrefs:
        fn = h.split("/")[-1].split("?")[0]
        m = EQ_NAME.fullmatch(fn)
        if not m or m.group(1).upper() != track.upper(): continue
        mm, dd, yy = int(m.group(2)), int(m.group(3)), int(m.group(4))
        try: d = dt.date(2000 + yy, mm, dd)
        except ValueError: continue
        url = urljoin(base_url, h)
        out[url] = d
    return sorted(((d, u) for u, d in out.items()), reverse=True)

def pdf_to_text(path):
    """Layout-preserving text (pdftotext -layout), falling back to pdfplumber."""
    import subprocess, shutil
    if shutil.which("pdftotext"):
        r = subprocess.run(["pdftotext", "-layout", path, "-"], capture_output=True, text=True)
        if r.returncode == 0 and r.stdout.strip(): return r.stdout
    import pdfplumber
    with pdfplumber.open(path) as pdf:
        return "\n\f".join((pg.extract_text(layout=True) or "") for pg in pdf.pages)

_TID = re.compile(r"[?&]tid=([A-Za-z0-9]+)(?:&ctry=([A-Za-z]+))?")

def parse_equibase_tracks(path):
    """Extract (code, name, country) from a saved Equibase 'Full Charts' page (.html) or a
    'print to PDF' of it. Codes come from the links (tid=XXX&ctry=YYY); nothing is requested from the site."""
    found = []                                   # (code, country, name_or_None) in page order
    if path.lower().endswith(".pdf"):
        import subprocess
        try:
            import pypdf
        except ImportError:
            sys.exit("PDF input needs pypdf:  pip install pypdf   (or save the page as .html instead)")
        links = []
        for pg in pypdf.PdfReader(path).pages:
            for a in pg.get("/Annots") or []:
                uri = (a.get_object().get("/A") or {}).get("/URI") or ""
                m = _TID.search(uri)
                if m: links.append((m.group(1).upper(), (m.group(2) or "").upper()))
        txt = subprocess.run(["pdftotext", "-layout", path, "-"], capture_output=True, text=True).stdout
        names = [re.split(r"\s{2,}", l.strip())[0] for l in txt.splitlines()
                 if re.search(r"No Racing|\d(?:st|nd|rd|th) Post|Racing Today|Post\s+\d", l)]
        if len(names) == len(links):
            found = [(c, k, n) for (c, k), n in zip(links, names)]
        else:                                    # can't pair safely: keep codes, skip names
            print(f"note: {len(links)} links but {len(names)} track names; storing codes without names", file=sys.stderr)
            found = [(c, k, None) for c, k in links]
    else:
        html = open(path, encoding="utf-8", errors="ignore").read()
        for a in BeautifulSoup(html, "html.parser").find_all("a", href=True):
            m = _TID.search(a["href"])
            if m:
                found.append((m.group(1).upper(), (m.group(2) or "").upper(), a.get_text(" ", strip=True) or None))
        if not found:                            # JS-built pages: fall back to raw regex over the source
            found = [(m.group(1).upper(), (m.group(2) or "").upper(), None) for m in _TID.finditer(html)]
    out = {}
    for c, k, n in found:                        # dedupe (featured list repeats tracks); prefer a real name
        if c not in out or (n and not out[c][1]): out[c] = (k, n)
    return [(c, n, k) for c, (k, n) in out.items()]

def import_tracks(con, path):
    rows = parse_equibase_tracks(path)
    ts = now_iso()
    for c, n, k in rows:
        con.execute("INSERT INTO eq_tracks(code,name,country,added_at) VALUES(?,?,?,?) "
                    "ON CONFLICT(code) DO UPDATE SET name=COALESCE(excluded.name,name), country=COALESCE(NULLIF(excluded.country,''),country)",
                    (c, n, k, ts))
    con.commit()
    print(f"{len(rows)} tracks stored in eq_tracks:")
    for c, n, k in rows: print(f"  {c:5} {k:4} {n or ''}")

def stored_track_codes(con, countries=None, exclude=None):
    rows = con.execute("SELECT code, country FROM eq_tracks ORDER BY code").fetchall()
    cs = {x.strip().upper() for x in countries.split(",")} if countries else None
    ex = {x.strip().upper() for x in exclude.split(",")} if exclude else set()
    return [r["code"] for r in rows if (not cs or (r["country"] or "").upper() in cs) and r["code"] not in ex]

class RateLimiter:
    """Global politeness limit shared by all worker threads: request *starts* are at least
    `interval` seconds apart no matter how many threads are running."""
    def __init__(self, interval):
        import threading
        self.interval, self._lock, self._next = interval, threading.Lock(), 0.0
    def wait(self):
        with self._lock:
            now = time.monotonic()
            slot = max(now, self._next)
            self._next = slot + self.interval
        if slot > now: time.sleep(slot - now)

def _download_chart(url, dest, ua, limiter, local):
    """Runs in a worker thread. Touches NO sqlite. Returns (status, sha, text)."""
    p = urlparse(url)
    if os.path.exists(dest) and os.path.getsize(dest) > 0:
        return 200, None, pdf_to_text(dest)
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    if p.scheme == "file":
        import shutil; shutil.copyfile(p.path, dest)
        return 200, None, pdf_to_text(dest)
    sess = getattr(local, "sess", None)
    if sess is None:
        sess = local.sess = requests.Session(); sess.headers["User-Agent"] = ua
    limiter.wait()
    r = sess.get(url, timeout=60)
    sha = hashlib.sha256(r.content).hexdigest()
    if r.status_code != 200 or not r.content.startswith(b"%PDF"):
        return r.status_code, sha, None
    with open(dest, "wb") as f: f.write(r.content)
    return 200, sha, pdf_to_text(dest)

def crawl_equibase(con, fetcher, tracks, since, pdf_dir="equibase_pdfs", calendar_url=EQ_CAL, workers=1):
    import threading
    from concurrent.futures import ThreadPoolExecutor, as_completed
    workers = max(1, int(workers))
    jobs = []                      # (track, date, url, dest)
    for track in tracks:
        track = track.strip().upper()
        cal = calendar_url.format(track=track)
        try:
            html = fetcher.get(cal, use_cache=False)
        except (PermissionError, RuntimeError, OSError, requests.RequestException) as e:
            print(f"[{track}] calendar unavailable: {e}", file=sys.stderr); continue
        days = [(d, u) for d, u in parse_equibase_calendar(html, track, cal) if d >= since]
        print(f"[{track}] {len(days)} race days since {since}")
        if not days:
            print(f"[{track}] no chart-PDF links found in the calendar HTML - it may be built with JavaScript; "
                  "save the page and send it so the link extraction can be adjusted", file=sys.stderr)
        for d, url in days:
            if con.execute("SELECT 1 FROM chart_text WHERE pdf_url=?", (url,)).fetchone(): continue
            if not fetcher.allowed(url):          # robots checked here, on the main thread
                print(f"  [skip {d}] {fetcher.deny_reason}", file=sys.stderr); continue
            jobs.append((track, d, url, os.path.join(pdf_dir, track, url.split("/")[-1])))
    if not jobs:
        print("nothing to download"); return
    first = jobs[0][2]
    interval = max(fetcher.delay, fetcher.crawl_delay(first)) if urlparse(first).scheme != "file" else 0.0
    print(f"{len(jobs)} charts to fetch, {workers} worker(s), one request every {interval:g}s overall "
          f"(~{len(jobs) * interval / 60:.0f} min minimum)")
    limiter, local = RateLimiter(interval), threading.local()
    done = failed = 0
    ex = ThreadPoolExecutor(max_workers=workers)
    try:
        futs = {ex.submit(_download_chart, u, dest, fetcher.ua, limiter, local): (t, d, u, dest)
                for t, d, u, dest in jobs}
        for fu in as_completed(futs):
            t, d, u, dest = futs[fu]
            try:
                status, sha, txt = fu.result()
            except Exception as e:
                failed += 1; print(f"  [skip {t} {d}] {type(e).__name__}: {e}", file=sys.stderr); continue
            if sha:
                con.execute("INSERT INTO raw_pages VALUES(?,?,?,?,?)", (u, now_iso(), status, sha, dest))
            if txt is None:
                failed += 1; print(f"  [skip {t} {d}] HTTP {status} / not a PDF: {u}", file=sys.stderr)
                con.commit(); continue
            con.execute("INSERT OR REPLACE INTO chart_text(pdf_url,track_code,race_date,pdf_path,text,fetched_at) VALUES(?,?,?,?,?,?)",
                        (u, t, d.isoformat(), dest, txt, now_iso()))
            con.commit(); done += 1
            print(f"  [{done + failed}/{len(jobs)}] {t} {d} {len(txt)} chars", flush=True)
    except KeyboardInterrupt:
        print("\ninterrupted - cancelling pending downloads (finished ones are saved; re-run to resume)", file=sys.stderr)
        ex.shutdown(wait=False, cancel_futures=True); con.commit(); raise SystemExit(130)
    ex.shutdown(wait=True)
    print(f"done: {done} stored, {failed} failed")

# ------------------------------------------------------------------ Betfair BSP
# URL pattern is from memory and UNVERIFIED - check Betfair's data page and pass --url / --file.
BSP_URL_TEMPLATE = "https://promo.betfair.com/betfairsp/prices/dwbfpricesaus{date:%d%m%Y}win.csv"

def _num(x):
    try: return float(x)
    except (TypeError, ValueError): return None

def load_bsp_text(con, text):
    rd = csv.DictReader(io.StringIO(text))
    ts, n = now_iso(), 0
    for r in rd:
        r = {k.strip().upper(): (v or "").strip() for k, v in r.items() if k}
        ev = r.get("EVENT_NAME", "")
        # e.g. "R4 1200m Mdn" ; MENU_HINT e.g. "Aus / Flemington (AUS) 4th Oct"
        m = re.search(r"R(\d+)", ev)
        race_no = int(m.group(1)) if m else None
        hint = r.get("MENU_HINT", "")
        track = re.sub(r"(?i)^.*?/\s*", "", hint)
        track = re.split(r"\(|\d", track)[0].strip()
        edt = r.get("EVENT_DT", "")
        try:
            ed = dt.datetime.strptime(edt[:10], "%d-%m-%Y").date().isoformat()
        except ValueError:
            ed = edt[:10]
        con.execute("INSERT INTO betfair_bsp VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)", (
            ed, hint, ev, edt, r.get("SELECTION_NAME"),
            norm(re.sub(r"^\d+\.\s*", "", r.get("SELECTION_NAME", ""))), norm(track), race_no,
            to_int(r.get("WIN_LOSE")), _num(r.get("BSP")), _num(r.get("PPWAP")),
            _num(r.get("MORNINGWAP")), _num(r.get("PPMAX")), _num(r.get("PPMIN")),
            _num(r.get("IPMAX")), _num(r.get("IPMIN")), _num(r.get("MORNINGTRADEDVOL")),
            _num(r.get("PPTRADEDVOL")), _num(r.get("IPTRADEDVOL")), ts))
        n += 1
    con.commit()
    print(f"loaded {n} BSP rows")

# ------------------------------------------------------------------ generic CSV import
CSV_KINDS = {
    "horses": ("horses", ["horse_key"]),
    "races": ("races", ["race_id"]),
    "runs": ("runs", ["run_id"]),
    "odds": ("odds_snapshots", ["run_id", "captured_at", "source", "price_type"]),
}
def import_csv(con, kind, path):
    table, keys = CSV_KINDS[kind]
    cols = {r[1] for r in con.execute(f"PRAGMA table_info({table})")}
    n = 0
    with open(path, newline="", encoding="utf-8") as f:
        for row in csv.DictReader(f):
            row = {k: (v if v != "" else None) for k, v in row.items() if k in cols}
            if kind == "horses" and "horse_key" not in row and row.get("name"):
                row["horse_key"] = norm(row["name"])
            if not all(row.get(k) for k in keys): continue
            upsert(con, table, keys, row); n += 1
    con.commit()
    print(f"imported {n} {kind} rows")

# ------------------------------------------------------------------ export
# Every feature for a run uses only races with a strictly earlier race_dt
# (GROUPS frame ends at 1 PRECEDING peer group, so same-time races are excluded).
EXPORT_SQL = """
WITH v AS (
  SELECT r.run_id, r.race_id, r.horse_key, r.barrier, r.jockey, r.trainer, r.weight_kg, r.age,
         r.finish_pos, r.margin_l,
         ra.race_date, COALESCE(ra.start_time,'00:00') AS st,
         ra.race_date || ' ' || COALESCE(ra.start_time,'00:00') AS race_dt,
         ra.track, ra.race_no, ra.distance_m, ra.class, ra.prize_money, ra.field_size,
         ra.track_rating_label, ra.track_rating_num,
         CASE WHEN ra.track_rating_num >= 5 THEN 1 ELSE 0 END AS is_wet,
         CASE WHEN r.finish_pos = 1 THEN 1 ELSE 0 END AS won,
         CASE WHEN r.finish_pos BETWEEN 1 AND 3 THEN 1 ELSE 0 END AS placed,
         CASE WHEN r.finish_pos IS NOT NULL THEN 1 ELSE 0 END AS ran,
         h.sire, h.dam_sire, h.sex,
         COALESCE(NULLIF(norm(h.sire),''),'unknown') AS sire_key,
         COALESCE(NULLIF(norm(r.trainer),''),'unknown') AS trainer_key,
         julianday(ra.race_date) AS jd
  FROM runs r JOIN races ra ON ra.race_id = r.race_id
  JOIN horses h ON h.horse_key = r.horse_key
  WHERE r.scratched = 0
),
f AS (
  SELECT v.*,
    COALESCE(SUM(ran)    OVER hw,0) AS prior_starts,
    COALESCE(SUM(won)    OVER hw,0) AS prior_wins,
    COALESCE(SUM(placed) OVER hw,0) AS prior_places,
    COALESCE(SUM(CASE WHEN is_wet=1 THEN ran END) OVER hw,0) AS prior_wet_starts,
    COALESCE(SUM(CASE WHEN is_wet=1 THEN won END) OVER hw,0) AS prior_wet_wins,
    COALESCE(SUM(CASE WHEN is_wet=1 THEN placed END) OVER hw,0) AS prior_wet_places,
    jd - MAX(CASE WHEN ran=1 THEN jd END) OVER hw AS days_since_last,
    COALESCE(SUM(ran)    OVER sw,0) AS sire_prior_starts,
    COALESCE(SUM(won)    OVER sw,0) AS sire_prior_wins,
    COALESCE(SUM(CASE WHEN is_wet=1 THEN ran END) OVER sw,0) AS sire_prior_wet_starts,
    COALESCE(SUM(CASE WHEN is_wet=1 THEN won END) OVER sw,0) AS sire_prior_wet_wins,
    COALESCE(SUM(ran) OVER tw,0) AS trainer_30d_starts,
    COALESCE(SUM(won) OVER tw,0) AS trainer_30d_wins,
    AVG(CASE WHEN ran=1 THEN finish_pos END) OVER hl3 AS avg_finish_last3
  FROM v
  WINDOW hw AS (PARTITION BY horse_key ORDER BY race_dt GROUPS BETWEEN UNBOUNDED PRECEDING AND 1 PRECEDING),
         hl3 AS (PARTITION BY horse_key ORDER BY race_dt GROUPS BETWEEN 3 PRECEDING AND 1 PRECEDING),
         sw AS (PARTITION BY sire_key ORDER BY race_dt GROUPS BETWEEN UNBOUNDED PRECEDING AND 1 PRECEDING),
         tw AS (PARTITION BY trainer_key ORDER BY jd RANGE BETWEEN 30 PRECEDING AND 1 PRECEDING)
)
SELECT f.*,
  (SELECT finish_pos FROM v v2 WHERE v2.horse_key=f.horse_key AND v2.race_dt < f.race_dt
     AND v2.ran=1 ORDER BY v2.race_dt DESC LIMIT 1) AS last_finish,
  b.bsp, b.ppwap, b.morningwap,
  (SELECT price FROM odds_snapshots o WHERE o.run_id=f.run_id AND o.price_type='fixed_win'
     ORDER BY captured_at DESC LIMIT 1) AS last_fixed_price
FROM f
LEFT JOIN betfair_bsp b ON b.event_date=f.race_date AND b.track_norm=norm(f.track)
     AND b.race_no=f.race_no AND b.horse_key=f.horse_key
WHERE (:d0 IS NULL OR f.race_date >= :d0) AND (:d1 IS NULL OR f.race_date <= :d1)
ORDER BY f.race_dt, f.race_id, f.barrier
"""

def export(con, out, d0=None, d1=None):
    cur = con.execute(EXPORT_SQL, {"d0": d0, "d1": d1})
    cols = [c[0] for c in cur.description if True]
    n = 0
    with open(out, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f); w.writerow(cols)
        for row in cur:
            d = dict(row); w.writerow([d[c] for c in cols]); n += 1
    print(f"wrote {n} rows -> {out}")
    if out.endswith(".csv"):
        try:
            import pandas as pd
            pd.read_csv(out).to_parquet(out[:-4] + ".parquet")
        except Exception:
            pass

# ------------------------------------------------------------------ Equibase chart parser (text -> tables)
# Charts list runners in OFFICIAL FINISH ORDER, so finish_pos = row order. Pedigree (sire/dam) is only
# printed for the WINNER. The layout below is written from knowledge of the chart format and must be
# validated against real files: run `parse-charts --report` and inspect failures.
EXTRA_SCHEMA = """
CREATE TABLE IF NOT EXISTS us_race_extra(
  race_id TEXT PRIMARY KEY, track_code TEXT, race_date TEXT, race_no INTEGER, surface TEXT, weather TEXT,
  track_condition TEXT, distance_text TEXT, distance_furlongs REAL, race_type TEXT, claiming_price REAL,
  purse REAL, off_time TEXT, fractions_json TEXT, final_time_s REAL, winner_name TEXT, scratched TEXT,
  header_text TEXT, n_runners INTEGER, parse_ok INTEGER, issues TEXT, pdf_url TEXT);
CREATE TABLE IF NOT EXISTS us_run_extra(
  run_id TEXT PRIMARY KEY, program TEXT, equipment TEXT, last_raced TEXT, post_pos INTEGER,
  calls_json TEXT, favorite INTEGER, odds_to_1 REAL, comment TEXT, owner TEXT, raw_line TEXT);
CREATE TABLE IF NOT EXISTS us_payouts(
  race_id TEXT, pool TEXT, combo TEXT, base REAL, payout REAL);
"""
FURLONG_M, MILE_M, YARD_M = 201.168, 1609.344, 0.9144
_WORDS = {"one":1,"two":2,"three":3,"four":4,"five":5,"six":6,"seven":7,"eight":8,"nine":9,"ten":10}
_DEN = {"sixteenth":16,"sixteenths":16,"eighth":8,"eighths":8,"half":2,"halves":2,"quarter":4,"quarters":4,"fourth":4,"fourths":4}
_COND_NUM = {"fast":1,"firm":1,"good":3,"standard":2,"wet fast":4,"yielding":4,"slow":5,"soft":6,"sloppy":6,
             "muddy":7,"heavy":8,"sealed":6,"frozen":2}

def _num_words(tok):
    t = tok.lower().strip()
    m = re.fullmatch(r"(\d+)(?:\s+(\d+)/(\d+))?", t)
    if m: return int(m.group(1)) + (int(m.group(2)) / int(m.group(3)) if m.group(2) else 0)
    m = re.fullmatch(r"(\w+)(?:\s+and\s+(\w+)\s+(\w+))?", t)
    if m and m.group(1) in _WORDS:
        v = float(_WORDS[m.group(1)])
        if m.group(2):
            n = _WORDS.get(m.group(2), 1 if m.group(2) == "a" else None); d = _DEN.get(m.group(3))
            if n and d: v += n / d
        return v
    return None

_ONES = {w: i for i, w in enumerate("one two three four five six seven eight nine ten eleven twelve thirteen fourteen fifteen sixteen seventeen eighteen nineteen".split(), 1)}
_TENS = {w: 10 * i for i, w in enumerate("twenty thirty forty fifty sixty seventy eighty ninety".split(), 2)}
def words_to_int(s):
    """'Eight Hundred And Seventy' -> 870; None if any word is not a number word."""
    cur, seen = 0, False
    for w in re.findall(r"[a-z]+|\d+", s.lower()):
        if w == "and": continue
        if w.isdigit(): cur += int(w)
        elif w in _ONES: cur += _ONES[w]
        elif w in _TENS: cur += _TENS[w]
        elif w == "hundred": cur = max(cur, 1) * 100
        else: return None
        seen = True
    return cur if seen else None

def parse_chart_distance(h):
    ym = re.match(r"(?i)\s*(?:about\s+)?((?:[a-z]+\s+|\d+\s+)+?)yards?\b", h)
    if ym:
        y = words_to_int(ym.group(1))
        if y:
            metres = y * YARD_M
            return f"{y} Yards", round(metres / FURLONG_M, 3), round(metres)
    return _parse_chart_distance_fm(h)

def _parse_chart_distance_fm(h):
    """Return (text, furlongs, metres) from a header like '5 1/2 Furlongs' / 'One And One Sixteenth Miles'."""
    m = re.search(r"(?i)((?:about\s+)?)((?:\d+(?:\s+\d+/\d+)?)|(?:one|two|three|four|five|six|seven|eight|nine|ten)"
                  r"(?:\s+and\s+(?:one|two|three|five|seven|a)\s+(?:sixteenths?|eighths?|halves|half|quarters?|fourths?))?)\s+"
                  r"(furlongs?|miles?|yards?)", h)
    if not m: return None, None, None
    v = _num_words(m.group(2)); unit = m.group(3).lower()
    if v is None: return None, None, None
    metres = v * (FURLONG_M if unit.startswith("f") else MILE_M if unit.startswith("m") else YARD_M)
    ym = re.search(r"(?i)\band\s+(\d+)\s+yards", h[m.end():m.end() + 25])
    if ym: metres += int(ym.group(1)) * YARD_M
    return m.group(0).strip(), round(metres / FURLONG_M, 3), round(metres)

def _ptime(s):
    if not s: return None
    s = s.strip().lstrip(":")
    m = re.fullmatch(r"(?:(\d+):)?(\d+(?:\.\d+)?)", s)
    return (int(m.group(1) or 0) * 60 + float(m.group(2))) if m else None

_HDR = re.compile(r"^\s*(?P<track>\S.*?)\s*-\s*(?P<date>[A-Za-z]+\s+\d{1,2},\s+\d{4})\s*-\s*Race\s+(?P<n>\d{1,2})\s*$")

def split_chart_races(text):
    """[(race_no, race_date_or_None, block_text)] split on 'TRACK - Month D, YYYY - Race N' header lines.
    (pdftotext sometimes splits the track name: 'ALBUQ UERQUE'; the text before the date is ignored.)"""
    lines = text.replace("\f", "\n").splitlines()
    marks = []
    for i, l in enumerate(lines):
        m = _HDR.match(l)
        if m:
            try: d = dt.datetime.strptime(re.sub(r"\s+", " ", m.group("date")), "%B %d, %Y").date().isoformat()
            except ValueError: d = None
            marks.append((i, int(m.group("n")), d))
    blocks = []
    for k, (i, n, d) in enumerate(marks):
        j = marks[k + 1][0] if k + 1 < len(marks) else len(lines)
        if blocks and blocks[-1][0] == n and blocks[-1][1] == d:        # a race that continues on the next page
            blocks[-1] = (n, d, blocks[-1][2] + "\n" + "\n".join(lines[i + 1:j]))
        else:
            blocks.append((n, d, "\n".join(lines[i:j])))
    return blocks

_TABLE_END = re.compile(r"(?i)^\s*(Fractional Times|Final Time|Run-?Up|Split Times|Winner:|Scratched|Total WPS|Trainers?:|Owners?:|Footnotes)")
_RUNNER = re.compile(r"^\s*(?:(?P<last>\d{1,2}[A-Za-z]{3}\d{2}\s+\d{1,2}[A-Za-z0-9]{2,6}|-{2,}|—+)\s+)?(?P<pgm>\d{1,2}[A-Z]?)\s+(?P<rest>\S.*)$")
# after the name: Wgt  M/E  PP  Start  <calls...>  Odds  Comments
_TAIL = re.compile(r"\s(?P<wt>[1-9]\d{2})\s+(?:(?P<me>--|-\s-|[A-Za-z][A-Za-z ]{0,5}?)\s+)?(?P<pp>\d{1,2})\s+(?P<start>\d{1,2})\s+"
                   r"(?P<calls>.*?)\s+(?P<odds>\*?\d{1,3}\.\d{2}\*?)(?:\s+(?P<itime>\d{1,2}\.\d{3})\s+(?P<spidx>\d{1,3}))?(?:\s+(?P<comment>.*))?$")
_MARG_WORDS = {"nose": .05, "head": .2, "neck": .3}

def _margin_text_to_l(t):
    t = (t or "").strip()
    if not t: return None
    if t.lower() in _MARG_WORDS: return _MARG_WORDS[t.lower()]
    m = re.fullmatch(r"(?:(\d+)\s+)?(\d+)/(\d+)", t)
    if m: return int(m.group(1) or 0) + int(m.group(2)) / int(m.group(3))
    m = re.fullmatch(r"(\d+)(?:\s+(\d+)/(\d+))?", t)
    if m: return int(m.group(1)) + (int(m.group(2)) / int(m.group(3)) if m.group(2) else 0)
    return None

_TAIL_NOSTART = re.compile(_TAIL.pattern.replace(r"\s+(?P<start>\d{1,2})\s+", r"\s+"))

def parse_runner_line(line, has_start=True):
    m = _RUNNER.match(line)
    if not m: return None
    rest = m.group("rest")
    t = (_TAIL if has_start else _TAIL_NOSTART).search(" " + rest)
    if not t: return None
    name = (" " + rest)[:t.start()].strip()
    jock = None
    jm = re.search(r"\(([^)]*[ ,][^)]*)\)\s*$", name)               # '(Zamora, Francisco)' but not '(IRE)'
    if jm: jock, name = jm.group(1).strip(), name[:jm.start()].strip()
    calls = [c.strip() for c in re.split(r"\s{2,}", t.group("calls").strip()) if c.strip()]
    od = t.group("odds")
    return dict(last_raced=m.group("last"), program=m.group("pgm"), name=re.sub(r"\s+", " ", name),
                jockey=jock, weight_lb=int(t.group("wt")), equipment=re.sub(r"\s+", "", t.group("me") or "") or None,
                post_pos=int(t.group("pp")), start_pos=int(t.group("start")) if has_start else None, calls=calls,
                odds_to_1=float(od.strip("*")), favorite="*" in od, comment=(t.group("comment") or "").strip() or None,
                ind_time_s=float(t.group("itime")) if t.group("itime") else None, speed_index=int(t.group("spidx")) if t.group("spidx") else None,
                raw=line.rstrip())

def _grab(block, pat, flags=re.I):
    m = re.search(pat, block, flags)
    return next((g.strip() for g in m.groups() if g), None) if m else None

_STOP = r"(?:\n\s*\n|\n\s*(?:Breeder|Owners?|Trainers?|Scratched|Footnotes|Claiming Prices|Total WPS|\d+ Claimed|Run-?Up|Fractional|Final|Split|Winner|Weather)\b|\n\s*\$\d)"
def _joined(block, start_pat, stop_pat=_STOP):
    m = re.search(start_pat, block, re.I)
    if not m: return None
    seg = block[m.end():]; e = re.search(stop_pat, seg, re.I)
    return re.sub(r"\s+", " ", seg[:e.start() if e else len(seg)]).strip()

_SEX = {"colt": "c", "filly": "f", "gelding": "g", "mare": "m", "horse": "h", "ridgling": "r", "stallion": "h"}
def parse_winner_line(txt, race_year=None):
    """'Girls Don't Cry, Bay Filly, by Crossbow out of Lady Don't Cry, by Street Cry (IRE). Foaled Mar 16, 2022 in Texas.'"""
    if not txt: return {}
    m = re.match(r"(?P<name>.+?),\s*(?P<csx>[A-Za-z ]+?),\s*by\s+(?P<sire>.+?)\s+out of\s+(?P<dam>.+?),\s*by\s+(?P<ds>.+?)\.\s*"
                 r"(?:Foaled\s+(?P<foaled>[A-Za-z]{3,9}\s+\d{1,2},\s+\d{4})(?:\s+in\s+(?P<place>[A-Za-z .]+?))?\.?)?\s*$", txt)
    if not m: return {}
    words = m.group("csx").split()
    sexw = words[-1].lower() if words else ""
    out = dict(name=m.group("name").strip(), colour=" ".join(words[:-1]) or None, sex=_SEX.get(sexw), sex_word=sexw or None,
               sire=re.sub(r"\s*\([^)]*\)", "", m.group("sire")).strip(), dam=m.group("dam").strip(),
               dam_sire=re.sub(r"\s*\([^)]*\)", "", m.group("ds")).strip(), foaled=m.group("foaled"), bred_in=m.group("place"))
    fy = re.search(r"(\d{4})$", m.group("foaled") or "")
    out["age"] = (race_year - int(fy.group(1))) if (fy and race_year) else None
    return out

def _times(s):
    return [x for x in (_ptime(t) for t in re.findall(r"(?<![\d/])(?:\d+:)?\d{1,2}\.\d{2}(?![\d/])", s or "")) if x]

def _payouts(block):
    """WIN/PLACE/SHOW per horse (column-aligned) + exotic pools, from the table under 'Pgm Horse Win Place Show Wager Type ...'."""
    pay = []
    lines = block.splitlines()
    hi = next((i for i, l in enumerate(lines) if re.match(r"^\s*Pgm\s+Horse\s+Win\s+Place\s+Show", l)), None)
    if hi is None: return pay
    h = lines[hi]
    ends = {k: h.index(k) + len(k) for k in ("Win", "Place", "Show")}
    for ln in lines[hi + 1:]:
        if not ln.strip() or re.match(r"(?i)^\s*(Past Performance|Trainers?:|Owners?:|Footnotes)", ln): break
        wm = re.search(r"\$(\d+(?:\.\d+)?)\s+([A-Za-z0-9 /]+?)\s{2,}([\d][\d\-/, ]*?)\s+([\d,]+\.\d{2})\s+([\d,]+)\s*$", ln)
        left = ln[:wm.start()] if wm else ln
        hm = re.match(r"^\s*(\d{1,2}[A-Z]?)\s+(.+?)\s{2,}", left + "  ")
        if hm:
            for num in re.finditer(r"\d+\.\d{2}", left[hm.end():] if False else left):
                if num.start() < hm.end() - 2: continue
                col = min(ends, key=lambda k: abs(num.end() - ends[k]))
                pay.append((col.upper(), f"{hm.group(1)} {hm.group(2).strip()}", 2.0, float(num.group(0))))
        if wm:
            pay.append((wm.group(2).strip().upper(), wm.group(3).strip(), float(wm.group(1)), float(wm.group(4).replace(",", ""))))
    return pay

def parse_race_block(block, race_no, race_date=None):
    lines = block.splitlines()
    ti = next((i for i, l in enumerate(lines) if re.search(r"(?i)last\s+raced", l)), None)
    head_lines = lines[:ti] if ti is not None else lines[:14]
    head = "\n".join(head_lines)
    r = dict(race_no=race_no, issues=[])
    dl = re.search(r"Distance:\s*(.+?)(?:\s{2,}|\s+Current Track Record|$)", head, re.M)
    dtxt = dl.group(1) if dl else head
    r["distance_text"], r["distance_furlongs"], r["distance_m"] = parse_chart_distance(dtxt)
    s = re.search(r"(?i)on the\s+(.+)$", dtxt)
    stxt = (s.group(1) if s else "").lower()
    r["surface"] = ("Turf" if "turf" in stxt else "Dirt" if "dirt" in stxt else
                    "Synthetic" if re.search(r"synthetic|all[- ]weather|tapeta|polytrack", stxt) else (s.group(1).strip().title() if s else None))
    tm = next((re.match(r"^\s*([A-Z].*?)\s+-\s+(Thoroughbred|Quarter Horse|Arabian|Paint|Appaloosa|Mixed)\s*$", l)
               for l in head_lines if re.match(r"^\s*[A-Z].*?\s+-\s+(Thoroughbred|Quarter Horse|Arabian|Paint|Appaloosa|Mixed)\s*$", l)), None)
    r["race_type"], r["breed"], r["race_name"], r["grade"] = None, None, None, None
    if tm:
        title, r["breed"] = tm.group(1).strip(), tm.group(2)
        vm = re.match(r"((?:(?:MAIDEN|SPECIAL|WEIGHT|CLAIMING|ALLOWANCE|OPTIONAL|STARTER|STAKES|HANDICAP|TRIAL|INVITATIONAL|AND|OR|STATE|BRED|OPEN|NW\d|FUTURITY|SWEEPSTAKES)\b\s*)+)(.*)$", title)
        r["race_type"] = (vm.group(1).strip() if vm else re.match(r"[A-Z ]+", title).group(0).strip())
        nm = (vm.group(2) if vm else title[len(r["race_type"]):]).strip()
        gm = re.search(r"\bGrade\s+(\d)\b", nm)
        r["grade"] = int(gm.group(1)) if gm else None
        r["race_name"] = re.sub(r"\s*\bGrade\s+\d\b", "", nm).strip() or None
    ci = next((i for i, l in enumerate(head_lines) if tm and l == tm.string), None)
    ww = re.search(r"Wind Speed:\s*(\d+)\s+Wind Direction:\s*([A-Za-z]+)", block)
    r["wind_speed"], r["wind_dir"] = (float(ww.group(1)), ww.group(2)) if ww else (None, None)
    di = next((i for i, l in enumerate(head_lines) if l.strip().startswith("Distance:")), len(head_lines))
    r["conditions"] = re.sub(r"\s+", " ", " ".join(head_lines[ci + 1:di])).strip() if ci is not None else None
    r["purse"] = parse_money(_grab(head, r"Purse:\s*\$([\d,]+)"))
    cp = _grab(re.sub(r"\s+", " ", head), r"Claiming Price:\s*\$([\d,]+)")
    r["claiming_price"] = parse_money(cp)
    wl = re.search(r"Weather:\s*(.+?)\s+Track:\s*(.+?)\s*$", block, re.M)
    r["weather"] = wl.group(1).strip() if wl else None
    r["track_condition"] = wl.group(2).strip() if wl else None
    tf = re.search(r"(-?\d+)\s*°", r["weather"] or "")
    r["temp_f"] = float(tf.group(1)) if tf else None
    om = re.search(r"Off at:\s*([\d:]+)(?:\s+Start:\s*(.+?))?(?:\s+Timing Method:\s*(.+?))?\s*$", block, re.M)
    r["off_time"], r["start_note"], r["timing_method"] = (om.group(1), om.group(2), om.group(3)) if om else (None, None, None)
    fl = re.search(r"Fractional Times:\s*(.*?)(?:\s{2,}Final Time:|\s*$)", block, re.M)
    r["fractions"] = _times(fl.group(1)) if fl else []
    r["final_time_s"] = _ptime(_grab(block, r"Final Time:\s*([\d:.]+)"))
    r["time_from_gate_s"] = _ptime(_grab(block, r"Time from Gate:\s*([\d:.]+)"))
    r["total_wps_pool"] = parse_money(_grab(block, r"Total WPS Pool:\s*\$([\d,]+)"))
    runners = []
    if ti is not None:
        has_start = bool(re.search(r"\bPP\s+Start\b", lines[ti]))
        for l in lines[ti + 1:]:
            if _TABLE_END.match(l): break
            p = parse_runner_line(l, has_start)
            if p: runners.append(p)
    for p in runners:
        p["disqualified"] = 1 if p["name"].startswith("DQ-") else 0
        p["name"] = re.sub(r"^DQ-\s*", "", p["name"])
    cum = 0.0
    for i, p in enumerate(runners, 1):
        p["crossing_pos"] = i
        p["finish_pos"] = i
        fin = p["calls"][-1] if p["calls"] else ""
        mt = fin[len(str(i)):].strip() if fin.startswith(str(i)) else None
        p["finish_call"] = fin
        p["margin_ahead_l"] = _margin_text_to_l(mt)            # lengths ahead of the next horse home (assumed; last runner has none)
        p["beaten_l"] = round(cum, 3)
        cum += p["margin_ahead_l"] or 0
    year = int(race_date[:4]) if race_date else None
    win = parse_winner_line(_joined(block, r"Winner:\s*"), year)
    r["winner"] = win
    # The table lists horses in the order they CROSSED the line. Stewards' changes show in the comments
    # ('PL 1st' = placed first, 'DQ 4' = disqualified to 4th); fall back to the winner line.
    n = len(runners)
    slots = [None] * n
    for p in runners:
        m = re.search(r"\bPL\s*(\d+)", p["comment"] or "") or re.search(r"\bDQ\s*(\d+)", p["comment"] or "")
        if m and 1 <= int(m.group(1)) <= n and slots[int(m.group(1)) - 1] is None:
            slots[int(m.group(1)) - 1] = p; p["_fixed"] = True
    rest = iter([p for p in runners if not p.get("_fixed")])
    slots = [sl if sl is not None else next(rest) for sl in slots]
    if win and slots and norm(slots[0]["name"]) != norm(win.get("name")):
        k = next((j for j, p in enumerate(slots) if norm(p["name"]) == norm(win["name"])), None)
        if k is not None:
            slots.insert(0, slots.pop(k)); r["issues"].append("placing_assumed_from_winner_line")
    for i, p in enumerate(slots, 1): p["finish_pos"] = i
    runners = slots
    r["runners"] = runners
    if not r.get("final_time_s") and runners:
        wt = next((p["ind_time_s"] for p in runners if p["finish_pos"] == 1 and p.get("ind_time_s")), None)
        r["final_time_s"] = wt
    r["winner_breeder"] = _grab(block, r"^\s*Breeder:\s*(.+?)\s*$", re.I | re.M)
    r["winner_owner"] = _grab(block, r"^\s*Owner:\s*(.+?)\s*$", re.I | re.M)
    def pairs(s):
        return {m.group(1).upper(): m.group(2).strip(" ;,.") for m in re.finditer(r"(\d{1,2}[A-Za-z]?)\s*-\s*(.+?)(?=;\s*\d{1,2}[A-Za-z]?\s*-|;?\s*$)", s or "")}
    tmap = pairs(_joined(block, r"\n\s*Trainers:\s*", r"(?:\n\s*(?:Owners:|Footnotes))"))
    omap = pairs(_joined(block, r"\n\s*Owners:\s*", r"(?:\n\s*Footnotes)"))
    cl = {}
    cpl = _joined(block, r"Claiming Prices:\s*", r"(?:\n\s*\n|\n\s*Total WPS)")
    for m in re.finditer(r"(\d{1,2}[A-Za-z]?)\s*-\s*[^:;]+?:\s*\$([\d,]+)", cpl or ""):
        cl[m.group(1).upper()] = float(m.group(2).replace(",", ""))
    for p in runners:
        k = p["program"].upper()
        p["trainer"], p["owner"], p["claiming_price"] = tmap.get(k), omap.get(k), cl.get(k)
    r["scratched"] = _joined(block, r"Scratched Horse\(s\):\s*") or None
    low = block.lower()
    if re.search(r"\bcancel+ed\b", "\n".join(lines[:14]).lower()) and not runners:
        return dict(race_no=race_no, status="cancelled", issues=[])
    if (re.search(r"value of race:\s*\$0\b", low) or "declared-no contest" in low) and not any(p["odds_to_1"] for p in runners):
        return dict(race_no=race_no, status="no_contest", issues=[])
    r["payouts"] = _payouts(block)
    if len(runners) < 2: r["issues"].append("fewer_than_2_runners")
    if not r["distance_m"]: r["issues"].append("no_distance")
    if not r["track_condition"]: r["issues"].append("no_track_condition")
    if not all(p["jockey"] for p in runners): r["issues"].append("missing_jockey")
    if not all(p.get("trainer") for p in runners): r["issues"].append("missing_trainer")
    if not win: r["issues"].append("no_winner_pedigree")
    elif runners and norm(win.get("name")) != norm(runners[0]["name"]): r["issues"].append("winner_line_not_first_row")
    if not r["final_time_s"]: r["issues"].append("no_final_time")
    r["status"] = "ok"
    if not r["breed"]: r["issues"].append("no_race_type_line")
    return r

def _migrate(con):
    want = {"us_race_extra": [("breed", "TEXT"), ("conditions", "TEXT"), ("temp_f", "REAL"), ("start_note", "TEXT"),
                              ("timing_method", "TEXT"), ("winner_breeder", "TEXT"), ("winner_owner", "TEXT"),
                              ("time_from_gate_s", "REAL"), ("total_wps_pool", "REAL"), ("winner_bred_in", "TEXT"),
                              ("race_name", "TEXT"), ("grade", "INTEGER"), ("wind_speed", "REAL"), ("wind_dir", "TEXT"), ("status", "TEXT")],
            "us_run_extra": [("claiming_price", "REAL"), ("margin_ahead_l", "REAL"), ("finish_call", "TEXT"), ("start_pos", "INTEGER"),
                         ("ind_time_s", "REAL"), ("speed_index", "INTEGER"), ("crossing_pos", "INTEGER"), ("disqualified", "INTEGER")]}
    for t, cols in want.items():
        have = {r[1] for r in con.execute(f"PRAGMA table_info({t})")}
        for c, ty in cols:
            if c not in have: con.execute(f"ALTER TABLE {t} ADD COLUMN {c} {ty}")
    con.execute("DROP VIEW IF EXISTS v_us_runs")
    con.execute("""CREATE VIEW v_us_runs AS
      SELECT r.race_date, r.track AS track_code, r.race_no, e.breed, e.surface, e.race_type, e.race_name, e.grade, r.distance_m, e.distance_text,
             e.track_condition, r.track_rating_num, e.weather, e.temp_f, e.wind_speed, e.wind_dir, r.field_size, e.purse, e.claiming_price AS race_claiming_price,
             h.name AS horse, h.sex, h.colour, h.sire, h.dam, h.dam_sire, u.program, u.post_pos, ru.jockey, ru.trainer, u.owner,
             ru.weight_kg, u.equipment, ru.finish_pos, u.finish_call, ru.margin_l AS beaten_l, u.margin_ahead_l, u.odds_to_1,
             u.favorite, u.crossing_pos, u.disqualified, u.ind_time_s, u.speed_index, u.claiming_price AS horse_claiming_price, e.final_time_s, u.comment, r.race_id, ru.run_id
      FROM runs ru JOIN races r ON r.race_id=ru.race_id JOIN horses h ON h.horse_key=ru.horse_key
      LEFT JOIN us_race_extra e ON e.race_id=r.race_id LEFT JOIN us_run_extra u ON u.run_id=ru.run_id""")
    con.commit()

def _purge_race(con, rid):
    """Remove everything previously stored for this race so a re-parse never leaves stale or duplicate rows."""
    con.execute("DELETE FROM us_run_extra WHERE run_id IN (SELECT run_id FROM runs WHERE race_id=?)", (rid,))
    con.execute("DELETE FROM odds_snapshots WHERE run_id IN (SELECT run_id FROM runs WHERE race_id=?)", (rid,))
    con.execute("DELETE FROM runs WHERE race_id=?", (rid,))
    con.execute("DELETE FROM races WHERE race_id=?", (rid,))
    con.execute("DELETE FROM us_payouts WHERE race_id=?", (rid,))

def store_chart_race(con, track, date, race_no, r, pdf_url=None):
    ts = now_iso(); date_s = date if isinstance(date, str) else date.isoformat()
    mid = f"{date_s}_{norm(track)}"; rid = f"{mid}_R{race_no}"
    _purge_race(con, rid)
    cond = (r["track_condition"] or "").strip().lower()
    num = _COND_NUM.get(cond)
    if num is None and cond: num = next((v for k, v in _COND_NUM.items() if k in cond), None)
    if r["surface"] == "Turf" and cond in ("firm", "good", "yielding", "soft", "heavy"):
        num = {"firm": 1, "good": 3, "yielding": 5, "soft": 6, "heavy": 8}[cond]
    hh = None
    if r["off_time"]:
        mm = re.match(r"(\d{1,2}):(\d{2})", r["off_time"])
        if mm: hh = f"{int(mm.group(1)) % 12 + 12:02d}:{mm.group(2)}" if int(mm.group(1)) < 11 else f"{int(mm.group(1)):02d}:{mm.group(2)}"
    upsert(con, "meetings", ["meeting_id"], dict(meeting_id=mid, race_date=date_s, track=track, source="equibase", scraped_at=ts))
    klass = (f"Claiming ${int(r['claiming_price'])}" if r["claiming_price"] and r["race_type"] and "CLAIMING" in r["race_type"] else r["race_type"])
    upsert(con, "races", ["race_id"], dict(
        race_id=rid, meeting_id=mid, race_date=date_s, track=track, race_no=race_no, name=(r.get("race_name") or r["race_type"]), start_time=hh,
        distance_m=r["distance_m"], prize_money=r["purse"], field_size=len(r["runners"]) or None,
        track_rating_label=(r["track_condition"] or None), track_rating_num=num, winning_time_s=r["final_time_s"],
        source="equibase", scraped_at=ts, **{"class": klass}))
    win = r["winner"] or {}
    for p in r["runners"]:
        hk = norm(p["name"])
        if not hk: continue
        w = win if p["finish_pos"] == 1 else {}
        upsert(con, "horses", ["horse_key"], dict(horse_key=hk, name=p["name"], sire=w.get("sire"), dam=w.get("dam"),
               dam_sire=w.get("dam_sire"), sex=w.get("sex"), colour=w.get("colour"), foaled=w.get("foaled"), country=w.get("bred_in")))
        run_id = f"{rid}_{hk}"
        upsert(con, "runs", ["run_id"], dict(run_id=run_id, race_id=rid, horse_key=hk, saddle_cloth=to_int(p["program"]),
               barrier=p["post_pos"], jockey=p["jockey"], trainer=p.get("trainer"), weight_kg=round(p["weight_lb"] * 0.45359237, 2),
               gear=p["equipment"], age=w.get("age"), finish_pos=p["finish_pos"], margin_l=p["beaten_l"], scratched=0,
               source="equibase", scraped_at=ts))
        upsert(con, "odds_snapshots", ["run_id", "captured_at", "source", "price_type"], dict(
            run_id=run_id, captured_at=date_s, source="equibase", price_type="final_odds", price=p["odds_to_1"] + 1))
        upsert(con, "us_run_extra", ["run_id"], dict(
            run_id=run_id, program=p["program"], equipment=p["equipment"], last_raced=p["last_raced"], post_pos=p["post_pos"],
            start_pos=p["start_pos"], calls_json=json.dumps(p["calls"]), favorite=1 if p["favorite"] else 0, odds_to_1=p["odds_to_1"],
            comment=p["comment"], owner=p.get("owner"), claiming_price=p.get("claiming_price"),
            margin_ahead_l=p["margin_ahead_l"], finish_call=p["finish_call"], raw_line=p["raw"],
            ind_time_s=p.get("ind_time_s"), speed_index=p.get("speed_index"), crossing_pos=p.get("crossing_pos"),
            disqualified=p.get("disqualified", 0)))
    upsert(con, "us_race_extra", ["race_id"], dict(
        race_id=rid, track_code=track, race_date=date_s, race_no=race_no, surface=r["surface"], weather=r["weather"],
        track_condition=r["track_condition"], distance_text=r["distance_text"], distance_furlongs=r["distance_furlongs"],
        race_type=r["race_type"], claiming_price=r["claiming_price"], purse=r["purse"], off_time=r["off_time"],
        fractions_json=json.dumps(r["fractions"]), final_time_s=r["final_time_s"],
        winner_name=(r["runners"][0]["name"] if r["runners"] else None), scratched=r["scratched"], n_runners=len(r["runners"]),
        parse_ok=0 if r["issues"] else 1, issues=",".join(r["issues"]), pdf_url=pdf_url, breed=r["breed"], conditions=r["conditions"],
        temp_f=r["temp_f"], start_note=r["start_note"], timing_method=r["timing_method"], winner_breeder=r["winner_breeder"],
        winner_owner=r["winner_owner"], time_from_gate_s=r["time_from_gate_s"], total_wps_pool=r["total_wps_pool"],
        winner_bred_in=win.get("bred_in"), race_name=r.get("race_name"), grade=r.get("grade"),
        wind_speed=r.get("wind_speed"), wind_dir=r.get("wind_dir"), status="ok"))
    con.execute("DELETE FROM us_payouts WHERE race_id=?", (rid,))
    con.executemany("INSERT INTO us_payouts VALUES(?,?,?,?,?)", [(rid, a, b, c, d) for a, b, c, d in r["payouts"]])
    con.commit()
    return rid

def parse_charts(con, track=None, reparse=False, dump_dir=None):
    q = "SELECT pdf_url, track_code, race_date, text FROM chart_text WHERE (? OR parsed=0) AND (? IS NULL OR track_code=?)"
    rows = con.execute(q, (1 if reparse else 0, track, track)).fetchall()
    tot = ok = 0; issue_count = {}; skipped = {}
    for row in rows:
        blocks = split_chart_races(row["text"])
        if not blocks:
            print(f"[{row['track_code']} {row['race_date']}] no 'TRACK - Month D, YYYY - Race N' headers found", file=sys.stderr)
        for n, hdr_date, blk in blocks:
            if hdr_date and hdr_date != row["race_date"]:
                print(f"[{row['track_code']} {row['race_date']}] header date {hdr_date} differs from file-name date; using the header", file=sys.stderr)
            date_s = hdr_date or row["race_date"]
            try:
                r = parse_race_block(blk, n, date_s)
            except Exception as e:                                  # one bad race must not stop the batch
                r = dict(race_no=n, runners=[], winner={}, payouts=[], fractions=[], issues=[f"exception:{type(e).__name__}:{e}"],
                         distance_text=None, distance_furlongs=None, distance_m=None, surface=None, purse=None, claiming_price=None,
                         weather=None, track_condition=None, off_time=None, race_type=None, final_time_s=None, scratched=None,
                         breed=None, conditions=None, temp_f=None, start_note=None, timing_method=None, winner_breeder=None,
                         winner_owner=None, time_from_gate_s=None, total_wps_pool=None, race_name=None, grade=None,
                         wind_speed=None, wind_dir=None, status="ok")
            if r.get("status") in ("cancelled", "no_contest"):
                _purge_race(con, f"{date_s}_{norm(row['track_code'])}_R{n}")
                upsert(con, "us_race_extra", ["race_id"], dict(race_id=f"{date_s}_{norm(row['track_code'])}_R{n}", track_code=row["track_code"],
                       race_date=date_s, race_no=n, n_runners=0, parse_ok=1, issues="", status=r["status"], pdf_url=row["pdf_url"]))
                con.commit(); skipped[r["status"]] = skipped.get(r["status"], 0) + 1
                continue
            store_chart_race(con, row["track_code"], date_s, n, r, row["pdf_url"])
            tot += 1; ok += 0 if r["issues"] else 1
            for i in r["issues"]: issue_count[i.split(":")[0]] = issue_count.get(i.split(":")[0], 0) + 1
            if r["issues"] and dump_dir:
                os.makedirs(dump_dir, exist_ok=True)
                with open(os.path.join(dump_dir, f"{row['track_code']}_{date_s}_R{n}.txt"), "w") as f:
                    f.write("# issues: " + ",".join(r["issues"]) + "\n" + blk)
        con.execute("UPDATE chart_text SET parsed=1 WHERE pdf_url=?", (row["pdf_url"],)); con.commit()
    con.execute("DELETE FROM horses WHERE horse_key LIKE 'dq%' AND horse_key NOT IN (SELECT horse_key FROM runs)"); con.commit()
    print(f"parsed {tot} races from {len(rows)} charts; clean: {ok}; with issues: {tot - ok}"
          + (f"; skipped {', '.join(f'{v} {k}' for k, v in skipped.items())}" if skipped else ""))
    for k, v in sorted(issue_count.items(), key=lambda x: -x[1]): print(f"  {k}: {v}")

# ------------------------------------------------------------------ CLI
def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--db", default=DB_DEFAULT)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("init"); sub.add_parser("stats")
    p = sub.add_parser("ingest-html")
    p.add_argument("--profile", required=True); p.add_argument("--date", required=True)
    p.add_argument("--end"); p.add_argument("--delay", type=float, default=3.0)
    p = sub.add_parser("ingest-punters")
    p.add_argument("--file"); p.add_argument("--url"); p.add_argument("--delay", type=float, default=3.0)
    p = sub.add_parser("crawl-track")
    p.add_argument("--track", required=True, help="e.g. tracks/flemington_45 or a full results URL")
    p.add_argument("--years", type=float, default=2.0); p.add_argument("--since")
    p.add_argument("--max-pages", type=int, default=500); p.add_argument("--delay", type=float, default=3.0)
    p.add_argument("--page-template", help="URL with {n} (and optionally {base}) if history uses numbered pages")
    p = sub.add_parser("list-meetings")
    p.add_argument("--track"); p.add_argument("--file"); p.add_argument("--years", type=float, default=2.0)
    p.add_argument("--delay", type=float, default=3.0)
    p = sub.add_parser("equibase-crawl")
    p.add_argument("--tracks", help="comma-separated codes, e.g. ALB,CD,SA")
    p.add_argument("--all-tracks", action="store_true", help="use every track stored by import-tracks")
    p.add_argument("--countries", help="with --all-tracks: only these countries, e.g. USA,CAN")
    p.add_argument("--exclude", help="with --all-tracks: codes to skip, e.g. LA,CMR")
    p.add_argument("--years", type=float, default=2.0); p.add_argument("--delay", type=float, default=5.0)
    p.add_argument("--calendar-url", default=EQ_CAL, help="override (use {track}); file:// works for tests")
    p.add_argument("--workers", type=int, default=1, help="download/extract threads (request rate stays capped by --delay / robots Crawl-delay)")
    p = sub.add_parser("import-tracks")
    p.add_argument("--file", help="saved Equibase Full Charts page (.html) or its printed .pdf")
    p.add_argument("--list", action="store_true", help="just list tracks already stored")
    p = sub.add_parser("check-robots")
    p.add_argument("urls", nargs="+")
    p = sub.add_parser("parse-charts")
    p.add_argument("--track"); p.add_argument("--reparse", action="store_true")
    p.add_argument("--dump-failures", help="folder to write the text of races that parsed with issues")
    p = sub.add_parser("show-chart")
    p.add_argument("--track", required=True); p.add_argument("--date", required=True); p.add_argument("--lines", type=int, default=90)
    p = sub.add_parser("load-bsp")
    p.add_argument("--url"); p.add_argument("--file"); p.add_argument("--date")
    p = sub.add_parser("import-csv")
    p.add_argument("--kind", required=True, choices=list(CSV_KINDS)); p.add_argument("--file", required=True)
    p = sub.add_parser("export")
    p.add_argument("--out", default="features.csv"); p.add_argument("--from", dest="d0"); p.add_argument("--to", dest="d1")
    a = ap.parse_args(argv)
    con = connect(a.db)
    if a.cmd == "init":
        print(f"database ready: {a.db}")
    elif a.cmd == "stats":
        for t in ("meetings", "races", "horses", "runs", "odds_snapshots", "betfair_bsp"):
            print(f"{t:16}{con.execute(f'SELECT COUNT(*) FROM {t}').fetchone()[0]}")
    elif a.cmd == "ingest-html":
        with open(a.profile) as f: prof = json.load(f)
        d0 = dt.date.fromisoformat(a.date); d1 = dt.date.fromisoformat(a.end) if a.end else d0
        ingest_html(con, Fetcher(con, delay=a.delay), prof, d0, d1)
    elif a.cmd == "ingest-punters":
        if a.file:
            html = open(a.file, encoding="utf-8", errors="ignore").read()
        elif a.url:
            html = Fetcher(con, delay=a.delay).get(a.url)
        else:
            sys.exit("give --file saved.html or --url")
        ingest_punters(con, html)
    elif a.cmd == "crawl-track":
        since = dt.date.fromisoformat(a.since) if a.since else dt.date.today() - dt.timedelta(days=int(365.25 * a.years))
        n, pg, old = crawl_track(con, Fetcher(con, delay=a.delay), a.track, since, a.max_pages, a.page_template)
        print(f"done: {pg} pages, {n} races stored, oldest meeting seen {old}, cutoff {since}")
    elif a.cmd == "list-meetings":
        if a.file:
            html = open(a.file, encoding="utf-8", errors="ignore").read()
        elif a.track:
            html = Fetcher(con, delay=a.delay).get(_track_url(a.track), use_cache=False)
        else:
            sys.exit("give --track tracks/flemington_45 or --file saved.html")
        list_meetings(con, html, dt.date.today() - dt.timedelta(days=int(365.25 * a.years)))
        ingest_punters(con, html)      # latest meeting's full results are on the same page
    elif a.cmd == "import-tracks":
        if a.list:
            for r in con.execute("SELECT * FROM eq_tracks ORDER BY code"): print(f"{r['code']:5} {r['country'] or '':4} {r['name'] or ''}")
        else:
            if not a.file: sys.exit("give --file <saved page> (or --list)")
            import_tracks(con, a.file)
    elif a.cmd == "equibase-crawl":
        if a.all_tracks:
            codes = stored_track_codes(con, a.countries, a.exclude)
            if not codes: sys.exit("no tracks stored - run import-tracks --file <page> first")
        elif a.tracks:
            codes = a.tracks.split(",")
        else:
            sys.exit("give --tracks ALB,SA or --all-tracks")
        since = dt.date.today() - dt.timedelta(days=int(365.25 * a.years))
        crawl_equibase(con, Fetcher(con, delay=a.delay), codes, since, calendar_url=a.calendar_url, workers=a.workers)
    elif a.cmd == "check-robots":
        fx = Fetcher(con)
        for u in a.urls:
            pu = urlparse(u)
            rp, status, detail = fx._load_robots(f"{pu.scheme}://{pu.netloc}")
            ok = fx.allowed(u)
            print(f"{u}\n  robots.txt status: {status}  ({detail})\n  user-agent: {fx.ua}\n  verdict: "
                  f"{'ALLOWED' if ok else 'NOT ALLOWED - ' + fx.deny_reason}")
    elif a.cmd == "parse-charts":
        parse_charts(con, a.track.upper() if a.track else None, a.reparse, a.dump_failures)
    elif a.cmd == "show-chart":
        r = con.execute("SELECT text FROM chart_text WHERE track_code=? AND race_date=?", (a.track.upper(), a.date)).fetchone()
        print("\n".join(r["text"].splitlines()[:a.lines]) if r else "no such chart stored")
    elif a.cmd == "load-bsp":
        fx = Fetcher(con)
        if a.file:
            load_bsp_text(con, open(a.file, encoding="utf-8").read())
        else:
            url = a.url or BSP_URL_TEMPLATE.format(date=dt.date.fromisoformat(a.date))
            load_bsp_text(con, fx.get(url))
    elif a.cmd == "import-csv":
        import_csv(con, a.kind, a.file)
    elif a.cmd == "export":
        export(con, a.out, a.d0, a.d1)

if __name__ == "__main__":
    main()
