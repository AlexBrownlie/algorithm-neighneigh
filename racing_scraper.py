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

def crawl_equibase(con, fetcher, tracks, since, pdf_dir="equibase_pdfs", calendar_url=EQ_CAL):
    for track in tracks:
        track = track.strip().upper()
        cal = calendar_url.format(track=track)
        try:
            html = fetcher.get(cal, use_cache=False)
        except (PermissionError, RuntimeError) as e:
            print(f"[{track}] calendar unavailable: {e}", file=sys.stderr); continue
        days = [(d, u) for d, u in parse_equibase_calendar(html, track, cal) if d >= since]
        print(f"[{track}] {len(days)} race days since {since}")
        if not days:
            print(f"[{track}] no chart-PDF links found in the calendar HTML - it may be built with JavaScript; "
                  "save the page and send it so the link extraction can be adjusted", file=sys.stderr)
        for d, url in days:
            if con.execute("SELECT 1 FROM chart_text WHERE pdf_url=?", (url,)).fetchone(): continue
            dest = os.path.join(pdf_dir, track, url.split("/")[-1])
            try:
                fetcher.get_bytes(url, dest)
                txt = pdf_to_text(dest)
            except (PermissionError, RuntimeError) as e:
                print(f"  [skip {d}] {e}", file=sys.stderr); continue
            con.execute("INSERT OR REPLACE INTO chart_text(pdf_url,track_code,race_date,pdf_path,text,fetched_at) VALUES(?,?,?,?,?,?)",
                        (url, track, d.isoformat(), dest, txt, now_iso()))
            con.commit()
            print(f"  {d} {len(txt)} chars", flush=True)

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
    p.add_argument("--tracks", required=True, help="comma-separated codes, e.g. ALB,CD,SA")
    p.add_argument("--years", type=float, default=2.0); p.add_argument("--delay", type=float, default=5.0)
    p.add_argument("--calendar-url", default=EQ_CAL, help="override (use {track}); file:// works for tests")
    p = sub.add_parser("check-robots")
    p.add_argument("urls", nargs="+")
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
    elif a.cmd == "equibase-crawl":
        since = dt.date.today() - dt.timedelta(days=int(365.25 * a.years))
        crawl_equibase(con, Fetcher(con, delay=a.delay), a.tracks.split(","), since, calendar_url=a.calendar_url)
    elif a.cmd == "check-robots":
        fx = Fetcher(con)
        for u in a.urls:
            pu = urlparse(u)
            rp, status, detail = fx._load_robots(f"{pu.scheme}://{pu.netloc}")
            ok = fx.allowed(u)
            print(f"{u}\n  robots.txt status: {status}  ({detail})\n  user-agent: {fx.ua}\n  verdict: "
                  f"{'ALLOWED' if ok else 'NOT ALLOWED - ' + fx.deny_reason}")
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
