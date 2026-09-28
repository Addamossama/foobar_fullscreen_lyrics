"""Foobar Fullscreen Lyrics v9

Fullscreen synced lyrics for foobar2000 (via Beefweb) with an ambient,
artwork-driven look.  Requires: Python 3.10+, Pillow, foobar2000 + Beefweb.

New in v9
  * Playlist panel (P): browse every playlist, filter, play, multi-select,
    drag to reorder, remove, crop, queue, copy to other playlists, sort,
    randomize, add files / folders / URLs, create / rename / duplicate /
    clear / delete playlists.
  * Shuffle, repeat (off / all / one), full playback-order menu, stop after
    current track, volume slider + mute.
  * Frosted-glass panels, context menus, toasts, "Up next" card,
    per-track lyric offset ([ and ]), and a keyboard shortcut sheet (? / F1).

Settings and the lyric cache live next to the script by default (switchable
to %APPDATA% in Settings -> Data location).
"""
import bisect, colorsys, io, json, math, os, queue, re, sys, threading, time
import urllib.error, urllib.parse, urllib.request
import tkinter as tk
import tkinter.font as tkfont
from tkinter import filedialog
from pathlib import Path
from PIL import (Image, ImageChops, ImageDraw, ImageEnhance, ImageFilter, ImageOps,
                 ImageTk)

try:  # crisp text on Windows high-DPI screens
    import ctypes
    ctypes.windll.shcore.SetProcessDpiAwareness(1)
except Exception:
    pass

# ----------------------------------------------------------------- settings
BEEFWEB = "http://127.0.0.1:8880/api"
LRCLIB = "https://lrclib.net/api"
NETEASE = "https://music.163.com/api"
POLL_S = 0.15          # how often Beefweb is polled
TICK_MS = 16           # UI frame interval (~60 fps)

UI_FONTS = ("Segoe UI Variable Display", "Segoe UI", "SF Pro Display",
            "Helvetica Neue", "Inter", "Noto Sans", "DejaVu Sans", "Helvetica")
DEFAULT_ACCENT = (139, 108, 255)
WHITE = (255, 255, 255)
DANGER = (240, 84, 96)
UA = {"User-Agent": "FoobarLyrics/9.0"}

IS_WIN = sys.platform.startswith("win")
IS_MAC = sys.platform == "darwin"
SHIFT_MASK, CTRL_MASK = 0x1, 0x4
ALT_MASK = 0x20000 if IS_WIN else (0x10 if IS_MAC else 0x8)
MODIFIER_KEYS = {"Shift_L", "Shift_R", "Control_L", "Control_R", "Alt_L", "Alt_R",
                 "Meta_L", "Meta_R", "Super_L", "Super_R", "Caps_Lock", "Num_Lock",
                 "Win_L", "Win_R", "ISO_Level3_Shift", "App"}

PL_COLS = ["%artist%", "%title%", "%album%", "%length%", "%length_seconds%"]
SORT_OPTIONS = [
    ("Title", "%title%"),
    ("Artist", "%artist%|%date%|%album%|%discnumber%|%tracknumber%"),
    ("Album", "%album artist%|%album%|%discnumber%|%tracknumber%"),
    ("Track number", "%discnumber%|%tracknumber%"),
    ("Date", "%date%|%album%|%tracknumber%"),
    ("Duration", "$num(%length_seconds%,6)"),
    ("File path", "%path%"),
]


# ----------------------------------------------------------- storage paths
def _script_dir() -> Path:
    if getattr(sys, "frozen", False):     # PyInstaller / frozen exe
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


SCRIPT_DIR = _script_dir()
APPDATA_DIR = Path(os.getenv("APPDATA") or Path.home()) / "FoobarLyrics"


def _bootstrap_settings_path() -> Path:
    """Locate settings.json before we can read the storage_location setting.
    Script folder wins if both exist; a fresh install uses the script folder."""
    script_settings = SCRIPT_DIR / "settings.json"
    appdata_settings = APPDATA_DIR / "settings.json"
    if script_settings.exists():
        return script_settings
    if appdata_settings.exists():
        return appdata_settings
    return script_settings


def _dir_for(location: str) -> Path:
    return APPDATA_DIR if location == "appdata" else SCRIPT_DIR


DEFAULT_SETTINGS = {
    "lyric_lead": 0.15,          # highlight a line slightly early (seconds)
    "ui_hide_after": 3.5,        # controls fade out after this many idle seconds
    "show_translation": True,    # show NetEase translated lyrics under each line
    "lyric_source": "auto",      # "auto" / "lrclib" / "netease"
    "storage_location": "script",  # "script" (next to the .py) / "appdata"
    "font_scale": 1.0,           # global text size multiplier
    "bg_darkness": 1.0,          # background darkening strength
    "bg_blur": 1.0,              # background blur strength
    "seek_step": 10.0,           # seconds for ← / → and the ±10 buttons
    "volume_step": 5.0,          # % of the volume slider per key press
    "show_up_next": True,        # "Up next" card near the end of a track
    "confirm_destructive": True,  # ask before clearing / deleting playlists
    "show_controls": True,
    "show_hint": True,
}


class Settings:
    """Tiny JSON-backed settings store.  The path is mutable so we can
    migrate to a new storage_location at runtime."""

    def __init__(self, path: Path):
        self.path = Path(path)
        self.data = dict(DEFAULT_SETTINGS)
        self.load()

    def load(self):
        try:
            with open(self.path, "r", encoding="utf-8") as f:
                loaded = json.load(f)
            if isinstance(loaded, dict):
                for k in DEFAULT_SETTINGS:
                    if k in loaded:
                        self.data[k] = loaded[k]
        except Exception:
            pass

    def save(self):
        try:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            tmp = self.path.with_suffix(self.path.suffix + ".tmp")
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.data, f, indent=2, ensure_ascii=False)
            tmp.replace(self.path)
        except Exception:
            pass

    def get(self, k, default=None):
        return self.data.get(k, DEFAULT_SETTINGS.get(k, default))

    def set(self, k, v, save=True):
        self.data[k] = v
        if save:
            self.save()

    def __getitem__(self, k):
        return self.get(k)

    def __setitem__(self, k, v):
        self.set(k, v)

    def reset(self):
        self.data = dict(DEFAULT_SETTINGS)
        self.save()


class LyricCache:
    """Persisted {artist||title||album: [lines, source, offset?]} store."""

    def __init__(self, path: Path):
        self.path = Path(path)
        self.data = {}
        self._dirty = False
        self.load()

    def load(self):
        try:
            with open(self.path, "r", encoding="utf-8") as f:
                d = json.load(f)
            if isinstance(d, dict):
                self.data = {k: v for k, v in d.items()
                             if isinstance(v, list) and len(v) >= 2}
        except Exception:
            self.data = {}

    def save(self, force=False):
        if not self._dirty and not force:
            return
        try:
            self.path.parent.mkdir(parents=True, exist_ok=True)
            tmp = self.path.with_suffix(self.path.suffix + ".tmp")
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.data, f, ensure_ascii=False)
            tmp.replace(self.path)
            self._dirty = False
        except Exception:
            pass

    @staticmethod
    def _key(track) -> str:
        return "||".join(track)

    def get(self, track):
        v = self.data.get(self._key(track))
        if not v:
            return None
        lines = [tuple(x) for x in v[0] if isinstance(x, (list, tuple)) and len(x) >= 2]
        if not lines:
            return None
        norm_lines = []
        for ln in lines:
            t = float(ln[0])
            txt = str(ln[1]) if len(ln) > 1 else ""
            tr = str(ln[2]) if len(ln) > 2 else ""
            norm_lines.append((t, txt, tr))
        return norm_lines, str(v[1])

    def get_offset(self, track) -> float:
        v = self.data.get(self._key(track))
        try:
            return float(v[2]) if v and len(v) > 2 else 0.0
        except Exception:
            return 0.0

    def set_offset(self, track, off, save=False):
        k = self._key(track)
        v = self.data.get(k)
        if v is None:
            if not off:
                return
            v = self.data[k] = [[], "", 0.0]
        while len(v) < 3:
            v.append(0.0)
        v[2] = off
        if not v[0] and not off:
            self.data.pop(k, None)
        self._dirty = True
        if save:
            self.save()

    def put(self, track, lines, source):
        off = self.get_offset(track)
        entry = [[[t, txt, tr] for (t, txt, tr) in lines], source]
        if off:
            entry.append(off)
        self.data[self._key(track)] = entry
        self._dirty = True
        self.save()

    def drop_lines(self, track):
        """Forget cached lyrics for a track but keep its lyric offset."""
        k = self._key(track)
        off = self.get_offset(track)
        if off:
            self.data[k] = [[], "", off]
        else:
            self.data.pop(k, None)
        self._dirty = True
        self.save()

    def clear(self):
        self.data = {}
        self._dirty = True
        self.save(force=True)

    def size(self) -> int:
        return sum(1 for v in self.data.values() if v and v[0])


SETTINGS_PATH = _bootstrap_settings_path()
SETTINGS = Settings(SETTINGS_PATH)
CACHE = LyricCache(SETTINGS_PATH.parent / "lyrics_cache.json")

# name, label, kind, [slider: lo, hi, step, unit] / [choice: options]
SETTINGS_ROWS = [
    ("lyric_lead",          "Lyric lead",           "slider", 0.0, 1.0, 0.05, "s"),
    ("lyric_source",        "Lyric source",         "choice", ["auto", "lrclib", "netease"]),
    ("show_translation",    "Show translation",     "toggle"),
    ("font_scale",          "Font scale",           "slider", 0.75, 1.6, 0.05, "×"),
    ("bg_darkness",         "Background darkness",  "slider", 0.3, 1.6, 0.1, "×"),
    ("bg_blur",             "Background blur",      "slider", 0.5, 2.0, 0.1, "×"),
    ("seek_step",           "Seek step",            "slider", 5.0, 60.0, 5.0, "s"),
    ("volume_step",         "Volume step",          "slider", 1.0, 10.0, 1.0, "%"),
    ("ui_hide_after",       "Auto-hide UI after",   "slider", 1.0, 15.0, 0.5, "s"),
    ("show_controls",       "Show controls",        "toggle"),
    ("show_up_next",        "Show “Up next”",       "toggle"),
    ("show_hint",           "Show hint bar",        "toggle"),
    ("confirm_destructive", "Confirm deletes",      "toggle"),
    ("storage_location",    "Data location",        "choice", ["script", "appdata"]),
]


def migrate_storage(new_location: str):
    """Move settings.json + lyrics_cache.json to the new folder and delete
    the old copies.  Safe to call even if nothing actually moves."""
    new_dir = _dir_for(new_location)
    new_settings = new_dir / "settings.json"
    new_cache = new_dir / "lyrics_cache.json"
    old_settings = SETTINGS.path
    old_cache = CACHE.path

    if new_settings != old_settings:
        SETTINGS.path = new_settings
        SETTINGS.save()
        try:
            if old_settings.exists() and old_settings != new_settings:
                old_settings.unlink()
        except Exception:
            pass

    if new_cache != old_cache:
        CACHE.path = new_cache
        CACHE.save(force=True)
        try:
            if old_cache.exists() and old_cache != new_cache:
                old_cache.unlink()
        except Exception:
            pass


# --------------------------------------------------------------------- http
def get_json(url, timeout=5, headers=None):
    req = urllib.request.Request(url, headers={**UA, **(headers or {})})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read().decode("utf-8"))


def request_bytes(url, timeout=8):
    req = urllib.request.Request(url, headers=UA)
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def post_json(url, data=None, timeout=6):
    body = None if data is None else json.dumps(data).encode()
    req = urllib.request.Request(url, data=body, method="POST",
                                 headers={"Content-Type": "application/json", **UA})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        raw = r.read()
    try:
        return json.loads(raw.decode("utf-8")) if raw.strip() else None
    except Exception:
        return None


def http_error_text(e):
    if isinstance(e, urllib.error.HTTPError):
        msg = ""
        try:
            d = json.loads(e.read().decode("utf-8", "replace"))
            msg = (d.get("error") or {}).get("message") or ""
        except Exception:
            pass
        if e.code == 403:
            return "Beefweb refused" + (f": {msg}" if msg else " — check its permission settings")
        return f"Beefweb error {e.code}" + (f": {msg}" if msg else "")
    if isinstance(e, urllib.error.URLError):
        return "Can't reach Beefweb"
    return str(e) or e.__class__.__name__


def q(s):
    return urllib.parse.quote(str(s), safe="")


# ------------------------------------------------------------------- lyrics
def parse_lrc(text):
    result = []
    for line in (text or "").splitlines():
        tags = re.findall(r"\[(\d+):(\d{2})(?:[.:](\d{1,3}))?\]", line)
        lyric = re.sub(r"\[[0-9:.]+\]", "", line)
        lyric = re.sub(r"<\d+:\d{2}(?:[.:]\d{1,3})?>", "", lyric).strip()
        for m, s, f in tags:
            ms = 0 if not f else int(f.ljust(3, "0")[:3])
            result.append((int(m) * 60 + int(s) + ms / 1000, lyric))
    return sorted(result, key=lambda x: x[0])


def clean_title(t):
    t = re.sub(r"\s*[\(\[][^\)\]]*(remaster|version|edit|mix|live|mono|stereo|deluxe|feat|from)"
               r"[^\)\]]*[\)\]]", "", t, flags=re.I)
    t = re.sub(r"\s*-\s*(\d{4}\s*)?(remaster(ed)?|live|single version|mono|stereo).*$", "",
               t, flags=re.I)
    return t.strip()


def fetch_lrclib(artist, title, album, duration):
    """Exact LRCLIB match first, then a fuzzy search fallback."""
    def synced(obj):
        return parse_lrc(obj.get("syncedLyrics") or "") if isinstance(obj, dict) else []

    qd = {"track_name": title, "artist_name": artist}
    if album:
        qd["album_name"] = album
    if duration:
        qd["duration"] = round(duration)
    try:
        lines = synced(get_json(LRCLIB + "/get?" + urllib.parse.urlencode(qd), 8))
        if lines:
            return lines
    except Exception:
        pass

    for name in dict.fromkeys([title, clean_title(title)]):
        if not name:
            continue
        try:
            res = get_json(LRCLIB + "/search?" + urllib.parse.urlencode(
                {"track_name": name, "artist_name": artist}), 8)
        except Exception:
            continue
        cands = [x for x in res if isinstance(x, dict) and x.get("syncedLyrics")]
        if not cands:
            continue
        if duration:
            cands.sort(key=lambda x: abs((x.get("duration") or 0) - duration))
        best = cands[0]
        if not duration or abs((best.get("duration") or 0) - duration) <= 15:
            lines = synced(best)
            if lines:
                return lines
    return []


NE_HEADERS = {"Referer": "https://music.163.com/",
              "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                            "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"}
CJK_RE = re.compile(r"[\u3040-\u30ff\u3400-\u9fff\uac00-\ud7af]")
CREDIT_RE = re.compile(r"^\s*(作词|作曲|编曲|制作人?|监制|混音|母带|词|曲|lyrics?|composer|arranger|producer)\s*[:：]",
                       re.I)


def norm(s):
    return re.sub(r"[\W_]+", "", (s or "").lower())


def parse_netease_lrc(text):
    out = []
    for t, line in parse_lrc(text):
        if line.startswith("{") and line.endswith("}"):
            continue
        if t < 30 and CREDIT_RE.match(line):      # "作词 : xxx" credit lines
            continue
        out.append((t, line))
    return out


def merge_translation(lines, trans):
    tmap = {round(t * 100): x for t, x in trans if x}
    return [(t, x, tmap.get(round(t * 100), "")) for t, x in lines]


def fetch_netease(artist, title, duration):
    """NetEase Cloud Music: search -> best match -> synced lyric (+ translation)."""
    def title_ok(name):
        a, b = norm(title), norm(name)
        return bool(a and b and (a in b or b in a))

    nartist = norm(artist)
    queries = dict.fromkeys([f"{title} {artist}".strip(),
                             f"{clean_title(title)} {artist}".strip(), clean_title(title)])
    for qs in queries:
        if not qs:
            continue
        try:
            res = get_json(NETEASE + "/search/get?" + urllib.parse.urlencode(
                {"s": qs, "type": 1, "limit": 10, "offset": 0}), 8, NE_HEADERS)
            songs = (res.get("result") or {}).get("songs") or []
        except Exception:
            continue
        best = None
        for s in songs:
            name = s.get("name") or ""
            if not (title_ok(name) or title_ok(clean_title(name))):
                continue
            dur_ms = s.get("duration") or 0
            diff = abs(dur_ms / 1000 - duration) if duration and dur_ms else 0
            if duration and diff > 12:
                continue
            arts = [norm(x.get("name")) for x in (s.get("artists") or [])]
            pen = 0 if any(a and nartist and (a in nartist or nartist in a) for a in arts) else 6
            if best is None or diff + pen < best[0]:
                best = (diff + pen, s.get("id"))
        if not best or best[1] is None:
            continue
        try:
            d = get_json(NETEASE + f"/song/lyric?id={best[1]}&lv=1&kv=1&tv=-1", 8, NE_HEADERS)
        except Exception:
            continue
        lines = parse_netease_lrc((d.get("lrc") or {}).get("lyric") or "")
        if lines:
            trans = parse_netease_lrc((d.get("tlyric") or {}).get("lyric") or "")
            return merge_translation(lines, trans)
    return []


def fetch_lyrics(artist, title, album, duration):
    """Returns (lines, source). Each line is (time, text, translation)."""
    source = SETTINGS["lyric_source"]
    order = ["lrclib", "netease"]
    if source == "netease" or (source == "auto" and CJK_RE.search(artist + title)):
        order.reverse()
    for src in order:
        try:
            if src == "lrclib":
                lines = [(t, x, "") for t, x in fetch_lrclib(artist, title, album, duration)]
            else:
                lines = fetch_netease(artist, title, duration)
        except Exception:
            lines = []
        if lines:
            return lines, ("NetEase" if src == "netease" else "LRCLIB")
    return [], ""


# ------------------------------------------------------------------ helpers
def fmt(t):
    t = max(0, int(t or 0))
    if t >= 3600:
        return f"{t // 3600}:{t % 3600 // 60:02d}:{t % 60:02d}"
    return f"{t // 60}:{t % 60:02d}"


def fmt_long(t):
    t = int(t or 0)
    if t >= 3600:
        return f"{t // 3600} h {t % 3600 // 60} min"
    if t >= 60:
        return f"{t // 60} min"
    return f"{t} s"


def plural(n, word):
    return f"{n} {word}" + ("" if n == 1 else "s")


def mix(a, b, t):
    t = max(0.0, min(1.0, t))
    return tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))


def hexc(c):
    return "#%02x%02x%02x" % tuple(max(0, min(255, int(v))) for v in c)


def ease_out(t):
    t = max(0.0, min(1.0, t))
    return 1 - (1 - t) ** 3


def wrap(text, font, maxw):
    rows, cur = [], ""
    for word in text.split(" "):
        trial = word if not cur else cur + " " + word
        if font.measure(trial) <= maxw:
            cur = trial
            continue
        if cur:
            rows.append(cur)
        if font.measure(word) > maxw:          # very long word / CJK: break by char
            chunk = ""
            for ch in word:
                if font.measure(chunk + ch) <= maxw:
                    chunk += ch
                else:
                    rows.append(chunk)
                    chunk = ch
            cur = chunk
        else:
            cur = word
    if cur or not rows:
        rows.append(cur)
    return rows


def ellipsize(text, font, maxw):
    if font.measure(text) <= maxw:
        return text
    lo, hi = 0, len(text)
    while lo < hi:                        # binary search: far fewer measure() calls
        mid = (lo + hi + 1) // 2
        if font.measure(text[:mid].rstrip() + "…") <= maxw:
            lo = mid
        else:
            hi = mid - 1
    return text[:lo].rstrip() + "…"


def shorten_path(p: Path, maxlen: int = 46) -> str:
    s = str(p)
    if len(s) <= maxlen:
        return s
    return "…" + s[-(maxlen - 1):]


# ---- volume mapping (cube-root curve feels natural for dB volume sliders)
def vol_frac(v):
    if not v:
        return 0.0
    lo, hi, val = float(v.get("min", 0)), float(v.get("max", 0)), float(v.get("value", 0))
    if v.get("type") == "db":
        if val <= lo + 1e-6:
            return 0.0
        return max(0.0, min(1.0, 10 ** ((val - hi) / 60)))
    return max(0.0, min(1.0, (val - lo) / max(1e-6, hi - lo)))


def frac_vol(v, f):
    lo, hi = float(v.get("min", 0)), float(v.get("max", 0))
    f = max(0.0, min(1.0, f))
    if v.get("type") == "db":
        if f <= 0.004:
            return lo
        return max(lo, min(hi, hi + 60 * math.log10(f)))
    return lo + f * (hi - lo)


def vol_label(v):
    if not v:
        return ""
    if v.get("isMuted"):
        return "Muted"
    if v.get("type") == "db":
        val = float(v.get("value", 0))
        if val <= float(v.get("min", -100)) + 1e-6:
            return "Volume −∞ dB"
        return f"Volume {val:.1f} dB".replace("-", "−")
    return f"Volume {round(vol_frac(v) * 100)}%"


# ------------------------------------------------- image / background assets
def cover_crop(im, w, h):
    r, ir = w / h, im.width / im.height
    if ir > r:
        nw = int(im.height * r)
        x = (im.width - nw) // 2
        im = im.crop((x, 0, x + nw, im.height))
    else:
        nh = int(im.width / r)
        y = (im.height - nh) // 2
        im = im.crop((0, y, im.width, y + nh))
    return im.resize((w, h), Image.Resampling.BICUBIC)


def pick_accent(im):
    sm = im.convert("RGB").resize((64, 64), Image.Resampling.BILINEAR).quantize(8)
    pal = sm.getpalette() or []
    best, best_score = None, -1
    for count, idx in sm.getcolors() or []:
        r, g, b = pal[idx * 3: idx * 3 + 3]
        h, s, v = colorsys.rgb_to_hsv(r / 255, g / 255, b / 255)
        score = count * (0.25 + s) * (0.35 + v) * (0.2 if v < 0.18 else 1)
        if score > best_score:
            best, best_score = (h, s, v), score
    if not best:
        return DEFAULT_ACCENT
    h, s, v = best
    r, g, b = colorsys.hsv_to_rgb(h, max(s, 0.45), max(v, 0.85))
    return (int(r * 255), int(g * 255), int(b * 255))


def shade(bg, darkness=1.0):
    """Real-alpha darkening: heavier on the lyric side, soft top/bottom vignette."""
    d = max(0.0, float(darkness))
    w, h = bg.size
    grad = Image.linear_gradient("L")
    hor = grad.rotate(90).resize((w, h), Image.Resampling.BILINEAR)
    bg.paste((0, 0, 0), (0, 0, w, h),
             hor.point(lambda v: min(255, int(v * 0.50 * d))))
    ver = grad.resize((w, h), Image.Resampling.BILINEAR)
    top = ImageOps.invert(ver).point(lambda v: min(255, int((v / 255) ** 3 * 150 * d)))
    bot = ver.point(lambda v: min(255, int((v / 255) ** 3 * 190 * d)))
    bg.paste((0, 0, 0), (0, 0, w, h), top)
    bg.paste((0, 0, 0), (0, 0, w, h), bot)
    return bg


def fallback_bg(w, h, accent):
    ver = Image.linear_gradient("L").resize((w, h), Image.Resampling.BILINEAR)
    bg = ImageOps.colorize(ver, black=mix((8, 8, 14), accent, .20), white=(5, 5, 8))
    glow = ImageOps.invert(Image.radial_gradient("L")).resize((w, h), Image.Resampling.BILINEAR)
    bg.paste(mix((20, 20, 30), accent, .55), (0, 0, w, h), glow.point(lambda v: int(v * .30)))
    return bg


def frame_cover(img, cs):
    """Rounded corners (anti-aliased) + soft drop shadow, as an RGBA image."""
    pad, S, rad = int(cs * .16), 4, .035
    mask = Image.new("L", (cs * S, cs * S), 0)
    ImageDraw.Draw(mask).rounded_rectangle([0, 0, cs * S - 1, cs * S - 1],
                                           radius=int(cs * S * rad), fill=255)
    mask = mask.resize((cs, cs), Image.Resampling.LANCZOS)
    tot, off = cs + 2 * pad, int(cs * .035)
    sh = Image.new("L", (tot, tot), 0)
    ImageDraw.Draw(sh).rounded_rectangle([pad, pad + off, pad + cs, pad + cs + off],
                                         radius=int(cs * rad), fill=170)
    sh = sh.filter(ImageFilter.GaussianBlur(cs * .045))
    out = Image.composite(Image.new("RGBA", (tot, tot), (0, 0, 0, 255)),
                          Image.new("RGBA", (tot, tot), (0, 0, 0, 0)), sh)
    out.paste(img.convert("RGBA"), (pad, pad), mask)
    return out, pad


def placeholder_cover(cs, accent):
    ver = Image.linear_gradient("L").resize((cs, cs))
    img = ImageOps.colorize(ver, black=mix((30, 30, 44), accent, .35), white=(10, 10, 16))
    d, c = ImageDraw.Draw(img), cs / 2
    for r in (.46, .40, .34, .28):
        d.ellipse([c - cs * r, c - cs * r, c + cs * r, c + cs * r],
                  outline=mix((10, 10, 16), accent, .22))
    r = cs * .12
    d.ellipse([c - r, c - r, c + r, c + r], fill=mix((20, 20, 30), accent, .7))
    r = cs * .014
    d.ellipse([c - r, c - r, c + r, c + r], fill=(10, 10, 16))
    return img


def rounded_mask(w, h, r):
    """Anti-aliased rounded-rect mask; only the corners are supersampled."""
    w, h = max(2, int(w)), max(2, int(h))
    r = max(1, min(int(r), w // 2, h // 2))
    m = Image.new("L", (w, h), 255)
    S = 4
    big = Image.new("L", (r * S * 2, r * S * 2), 0)
    ImageDraw.Draw(big).ellipse([0, 0, r * S * 2 - 1, r * S * 2 - 1], fill=255)
    qd = big.crop((0, 0, r * S, r * S)).resize((r, r), Image.Resampling.LANCZOS)
    m.paste(qd, (0, 0))
    m.paste(qd.transpose(Image.Transpose.FLIP_LEFT_RIGHT), (w - r, 0))
    m.paste(qd.transpose(Image.Transpose.FLIP_TOP_BOTTOM), (0, h - r))
    m.paste(qd.transpose(Image.Transpose.ROTATE_180), (w - r, h - r))
    return m


def make_glass(src, box, radius, tint, lift=0.62, veil=0.38):
    """Frosted-glass panel: blurred, dimmed crop of `src` + sheen + hairline."""
    x0, y0, x1, y1 = [int(round(v)) for v in box]
    w, h = max(4, x1 - x0), max(4, y1 - y0)
    veil_col = mix(tint, (16, 16, 26), .55)
    if src is None:
        base = Image.new("RGB", (w, h), veil_col)
    else:
        crop = src.crop((x0, y0, x0 + w, y0 + h))
        sm = crop.resize((max(2, w // 10), max(2, h // 10)), Image.Resampling.BILINEAR)
        base = sm.filter(ImageFilter.GaussianBlur(2.5)).resize((w, h), Image.Resampling.BICUBIC)
        base = ImageEnhance.Brightness(base).enhance(lift)
        base = Image.blend(base, Image.new("RGB", (w, h), veil_col), veil)
    grad = Image.linear_gradient("L").resize((w, h), Image.Resampling.BILINEAR)
    sheen = ImageOps.invert(grad).point(lambda v: int((v / 255) ** 4 * 24))
    base.paste((255, 255, 255), (0, 0, w, h), sheen)
    avg = base.resize((1, 1), Image.Resampling.BOX).getpixel((0, 0))
    mask = rounded_mask(w, h, radius)
    inner = Image.new("L", (w, h), 0)
    inner.paste(rounded_mask(w - 2, h - 2, max(1, radius - 1)), (1, 1))
    ring = ImageChops.subtract(mask, inner)
    base.paste((255, 255, 255), (0, 0, w, h), ring.point(lambda v: v * 40 // 255))
    out = base.convert("RGBA")
    out.putalpha(mask)
    return out, tuple(avg[:3])


def build_assets(raw, w, h, cs, darkness=1.0, blur=1.0):
    if raw is None:
        accent = DEFAULT_ACCENT
        bg = fallback_bg(w, h, accent)
        cover = placeholder_cover(cs, accent)
    else:
        accent = pick_accent(raw)
        sw, sh = max(64, w // 10), max(36, h // 10)
        blur_px = max(2, int(max(6, sw // 9) * max(0.2, blur)))
        small = cover_crop(raw, sw, sh).filter(ImageFilter.GaussianBlur(blur_px))
        small = ImageEnhance.Color(small).enhance(1.45)
        small = ImageEnhance.Brightness(small).enhance(.68)
        bg = small.resize((w, h), Image.Resampling.BICUBIC)
        cover = cover_crop(raw, cs, cs)
    bg = shade(bg, darkness)
    tint = bg.crop((w // 2, 0, w, h)).resize((1, 1), Image.Resampling.BOX).getpixel((0, 0))
    scrim = bg.resize((max(32, w // 14), max(18, h // 14)), Image.Resampling.BILINEAR)
    scrim = ImageEnhance.Brightness(scrim.filter(ImageFilter.GaussianBlur(1.6))).enhance(.45)
    scrim = scrim.resize((w, h), Image.Resampling.BICUBIC)
    cover, pad = frame_cover(cover, cs)
    return {"bg": bg, "scrim": scrim, "cover": cover, "pad": pad, "accent": accent,
            "tint": tuple(tint[:3])}


# ----------------------------------------------------------- shortcut sheet
def P(s):
    """Plain (non-keycap) text inside a shortcut spec."""
    return ("t", s)


SHORTCUTS = {
    "Playback": [
        (["Space"], "Play / pause"),
        (["←", "→"], "Seek backward / forward"),
        (["Shift", P("+"), "←", "→"], "Seek 3× further"),
        (["B", "N"], "Previous / next track"),
        (["0", P("…"), "9"], "Jump to 0 – 90 %"),
        (["X"], "Stop"),
        (["Shift", P("+"), "X"], "Stop after current track"),
    ],
    "Sound & order": [
        (["↑", "↓", P("or"), "+", "−"], "Volume up / down"),
        (["M"], "Mute / unmute"),
        (["Ctrl", P("+"), "S"], "Shuffle on / off"),
        (["Ctrl", P("+"), "R"], "Repeat: off → all → one"),
        (["O"], "All playback orders"),
    ],
    "Lyrics": [
        (["F"], "Follow the current line"),
        (["[", "]"], "Lyrics later / earlier"),
        (["\\"], "Reset lyric offset"),
        (["V"], "Show / hide translation"),
        (["R"], "Search lyrics again"),
        ([P("Wheel · Click")], "Browse · jump to line"),
    ],
    "Playlist": [
        (["P"], "Open / close playlists"),
        (["Tab"], "Next playlist (Shift: previous)"),
        (["↑", "↓"], "Move cursor (Shift extends)"),
        (["Enter"], "Play (or double-click)"),
        (["Del"], "Remove selected tracks"),
        (["Alt", P("+"), "↑", "↓"], "Reorder (or drag)"),
        (["Ctrl", P("+"), "A"], "Select all"),
        (["Q"], "Add to / remove from queue"),
        (["J"], "Jump to playing track"),
        (["/"], "Filter tracks"),
        (["Ctrl", P("+"), "N"], "New playlist"),
        (["F2"], "Rename playlist"),
        (["Ctrl", P("+"), "O"], "Add files"),
        (["Ctrl", P("+"), "W"], "Delete playlist"),
        ([P("Right-click")], "More actions"),
    ],
    "Window": [
        (["S"], "Settings"),
        (["?", P("or"), "F1"], "This sheet"),
        (["F11"], "Toggle fullscreen"),
        (["Esc"], "Close panel / exit fullscreen"),
        (["Ctrl", P("+"), "Q"], "Quit"),
    ],
}
HELP_COLS_WIDE = [["Playback", "Sound & order"], ["Playlist"], ["Lyrics", "Window"]]
HELP_COLS_NARROW = [["Playback", "Sound & order", "Window"], ["Playlist", "Lyrics"]]


# ---------------------------------------------------------------------- app
class App:
    def __init__(self, root):
        self.root = root
        root.title("Foobar Lyrics")
        root.configure(bg="#050508")
        root.minsize(900, 520)
        self.fullscreen = True
        root.attributes("-fullscreen", True)
        self.alive = True

        avail = set(tkfont.families())
        self.family = next((f for f in UI_FONTS if f in avail), "Helvetica")
        self._fonts, self._ell, self._mw = {}, {}, {}

        now = time.perf_counter()
        self.remote = {"seq": 0, "ok": False, "a": "", "t": "", "al": "",
                       "pos": 0.0, "dur": 0.0, "playing": False, "state": "stopped",
                       "stamp": now, "pl_id": None, "idx": -1, "orders": [], "order": None,
                       "order_api": None, "stop_after": None, "vol": None, "perm_pl": True,
                       "playlists": [], "queue": None}
        self.seen_seq = 0
        self.pos_base, self.pos_stamp, self.ignore_until = 0.0, now, 0.0
        self.duration, self.playing, self.connected = 0.0, False, False
        self.state = "stopped"
        self.prev_connected = None
        self.track_key, self.track = None, ("", "", "")

        # player extras
        self.vol = None
        self.orders, self.order, self.order_api = [], None, None
        self.stop_after = None
        self.perm_pl = True
        self.pending = {}                      # optimistic values: key -> (value, until)
        self.last_nonshuffle = None
        self.vol_dirty, self.vol_last_send = False, 0.0
        self.vol_dragging = False

        # playlists
        self.playlists, self.play_pl_id, self.play_idx = [], None, -1
        self.queue_items, self.queue_pos = [], {}
        self.pl_open, self.pl_anim = False, 0.0
        self.pl_view_id, self.pl_view_set_at = None, 0.0
        self.pl_items, self.pl_rows, self.pl_rowpos = [], [], None
        self.pl_sel, self.pl_anchor, self.pl_cursor = set(), None, -1
        self.pl_scroll = self.pl_target = 0.0
        self.pl_filter, self.pl_filter_active = "", False
        self.pl_fetch_pending, self.pl_last_fetch, self.pl_last_edit = False, 0.0, 0.0
        self.pl_want_reveal = False
        self.pl_tab_first, self.pl_tab_reveal = 0, True
        self.pl_tab_boxes, self.pl_tab_arrows = [], []
        self.pl_drag = None
        self.pl_sb_drag = False
        self.pl_base = (24, 24, 34)
        self.sort_desc = False
        self.edit_q = queue.Queue()
        self.edit_gen, self.jobs_pending = 0, 0

        # up next
        self.next_sig, self.up_next, self.upnext_anim = None, None, 0.0

        # lyrics
        self.lines, self.times, self.lines_ver = [], [], 0
        self.lyric_source = ""
        self.lyr_offset = 0.0
        self.line_trows, self.line_oh = [], []
        self.lyric_state = "idle"
        self.focus, self.line_rows, self.line_y, self.line_h = [], [], [], []
        self.lyr_alpha, self.current = 1.0, -1
        self.auto_follow = True
        self.scroll = self.target_scroll = 0.0
        self._cache_save_token = None

        # artwork / assets
        self.art_raw, self.art_ver = None, 0
        self.bg_photo = self.cover_photo = None
        self.bg_pil = self.scrim_pil = None
        self.scrim_photo = None
        self.assets_gen = 0
        self._glass = {}
        self.cover_pad = 0
        self.accent, self.tint = DEFAULT_ACCENT, (10, 10, 16)
        self.asset_seq, self.built_sig, self.want_sig = 0, None, None
        self.want_since, self.immediate = now, False
        self.static_dirty = True
        self.geo, self.size = None, (0, 0)

        # interaction
        self.mx = self.my = -1
        self.last_move = now
        self.ui_alpha = 1.0
        self.hover_hit, self.hover_line = None, -1
        self.dragging, self.drag_frac = False, 0.0
        self.cursor = "arrow"
        self.last_tick = now
        self.events = queue.Queue()

        # overlays
        self.settings_open, self.settings_sel, self.settings_lay = False, 0, None
        self.help_open, self.help_lay = False, None
        self.menu = None
        self.modal = None
        self.toast_msg, self.toast_t0, self.toast_until = "", 0.0, 0.0

        c = self.canvas = tk.Canvas(root, bg="#050508", highlightthickness=0, cursor="arrow")
        c.pack(fill="both", expand=True)
        self.bg_item = c.create_image(0, 0, anchor="nw")
        self.cover_item = c.create_image(0, 0, anchor="nw")

        c.bind("<Motion>", self.on_motion)
        c.bind("<Leave>", lambda e: self.on_leave())
        c.bind("<Button-1>", self.on_press)
        c.bind("<Double-Button-1>", self.on_double)
        c.bind("<B1-Motion>", self.on_drag)
        c.bind("<ButtonRelease-1>", self.on_release)
        c.bind("<Button-3>", self.on_right)
        if IS_MAC:
            c.bind("<Button-2>", self.on_right)
        c.bind("<MouseWheel>", lambda e: self.on_wheel(e.delta * (120 if IS_MAC else 1), e))
        c.bind("<Button-4>", lambda e: self.on_wheel(120, e))
        c.bind("<Button-5>", lambda e: self.on_wheel(-120, e))
        root.bind("<Key>", self.on_keypress)
        root.protocol("WM_DELETE_WINDOW", self.close)

        threading.Thread(target=self.poll_loop, daemon=True).start()
        threading.Thread(target=self.edit_loop, daemon=True).start()
        root.after(30, self.tick)
        root.after(200, lambda: (root.focus_force(), c.focus_set()))

    # ------------------------------------------------------------- plumbing
    def font(self, px, weight="normal"):
        px = max(8, int(round(px * SETTINGS["font_scale"])))
        k = (px, weight)
        if k not in self._fonts:
            self._fonts[k] = tkfont.Font(family=self.family, size=-px, weight=weight)
        return self._fonts[k]

    def ell(self, text, font, maxw):
        k = (text, id(font), int(maxw))
        r = self._ell.get(k)
        if r is None:
            if len(self._ell) > 8000:
                self._ell.clear()
            r = self._ell[k] = ellipsize(text, font, max(10, maxw))
        return r

    def mw(self, text, font):
        k = (text, id(font))
        r = self._mw.get(k)
        if r is None:
            if len(self._mw) > 4000:
                self._mw.clear()
            r = self._mw[k] = font.measure(text)
        return r

    def close(self):
        self.alive = False
        try:
            SETTINGS.save()
            CACHE.save(force=True)
        except Exception:
            pass
        self.root.destroy()

    def toast(self, msg, secs=1.7):
        now = time.perf_counter()
        if not (self.toast_msg and now < self.toast_until):
            self.toast_t0 = now
        self.toast_msg, self.toast_until = msg, now + secs

    def command(self, path, data=None, err=True):
        """Fire-and-forget transport command (parallel, low latency)."""
        def run():
            try:
                post_json(BEEFWEB + path, data)
            except Exception as e:
                if err and self.connected:
                    self.events.put(("toast", http_error_text(e)))
        threading.Thread(target=run, daemon=True).start()

    def serial(self, fn):
        """Queue a job on the ordered worker (playlist edits + refetches)."""
        self.jobs_pending += 1
        self.edit_q.put(fn)

    def edit_loop(self):
        while self.alive:
            try:
                job = self.edit_q.get(timeout=0.5)
            except queue.Empty:
                continue
            try:
                job()
            except Exception as e:
                self.events.put(("toast", http_error_text(e)))
                self.events.put(("resync",))
            self.events.put(("job_done",))

    def poll_loop(self):
        use_queue = True
        seq = 0
        while self.alive:
            t0 = time.perf_counter()
            seq += 1
            try:
                params = {"player": "true", "trcolumns": "%artist%,%title%,%album%",
                          "playlists": "true"}
                if use_queue:
                    params.update(playQueue="true", qcolumns="%title%,%artist%")
                try:
                    d = get_json(BEEFWEB + "/query?" + urllib.parse.urlencode(params), 2.5)
                except urllib.error.HTTPError as e:
                    if use_queue and 400 <= e.code < 500:
                        use_queue = False
                        continue
                    raise
                t1 = time.perf_counter()
                p = d.get("player") or {}
                item = p.get("activeItem") or {}
                cols = item.get("columns") or []
                col = lambda i: str(cols[i]) if len(cols) > i and cols[i] is not None else ""
                orders, order, api, stop_after = [], None, None, None
                for o in p.get("options") or []:
                    if o.get("id") == "playbackOrder":
                        orders, order, api = list(o.get("enumNames") or []), o.get("value"), "options"
                    elif o.get("id") == "stopAfterCurrentTrack":
                        stop_after = bool(o.get("value"))
                if api is None and p.get("playbackModes"):
                    orders, order, api = list(p["playbackModes"]), p.get("playbackMode"), "legacy"
                state = str(p.get("playbackState", "")).lower()
                self.remote = {
                    "seq": seq, "ok": True, "a": col(0), "t": col(1), "al": col(2),
                    "pos": float(item.get("position") or 0),
                    "dur": float(item.get("duration") or 0),
                    "playing": state == "playing", "state": state,
                    "stamp": (t0 + t1) / 2,
                    "pl_id": item.get("playlistId") or None,
                    "idx": item.get("index", -1) if item.get("index") is not None else -1,
                    "orders": orders, "order": order, "order_api": api, "stop_after": stop_after,
                    "vol": p.get("volume"),
                    "perm_pl": (p.get("permissions") or {}).get("changePlaylists", True),
                    "playlists": d.get("playlists") or [],
                    "queue": d.get("playQueue") if use_queue else None}
            except Exception:
                self.remote = dict(self.remote, seq=seq, ok=False)
            time.sleep(max(0.02, POLL_S - (time.perf_counter() - t0)))

    # ----------------------------------------------------------- transport
    def playpause(self):
        self.command("/player/play-pause")

    def seek_to(self, pos):
        pos = max(0.0, pos if not self.duration else min(pos, self.duration))
        self.command("/player", {"position": pos})
        now = time.perf_counter()
        self.pos_base, self.pos_stamp, self.ignore_until = pos, now, now + 0.5

    def skip(self, n):
        self.seek_to(self.est_pos(time.perf_counter()) + n)

    def next_track(self):
        self.command("/player/next")

    def prev_track(self):
        self.command("/player/previous")

    def stop(self):
        self.command("/player/stop")
        self.toast("Stopped")

    def toggle_fullscreen(self, e=None):
        self.fullscreen = not self.fullscreen
        self.root.attributes("-fullscreen", self.fullscreen)

    def exit_fullscreen(self, e=None):
        self.fullscreen = False
        self.root.attributes("-fullscreen", False)

    def est_pos(self, now):
        p = self.pos_base + (now - self.pos_stamp if self.playing else 0)
        if self.duration > 0:
            p = min(p, self.duration)
        return max(0.0, p)

    # ---------------------------------------------------- playback order
    def order_name(self, i=None):
        i = self.order if i is None else i
        if i is None or not self.orders or not (0 <= i < len(self.orders)):
            return ""
        return str(self.orders[i])

    def find_order(self, *needles):
        for n in needles:
            for i, name in enumerate(self.orders):
                if n in str(name).lower():
                    return i
        return None

    @staticmethod
    def _is_shuffle(name):
        n = name.lower()
        return "shuffle" in n or "random" in n

    def shuffle_on(self):
        return self._is_shuffle(self.order_name())

    def repeat_state(self):
        n = self.order_name().lower()
        if "repeat" in n and "track" in n:
            return "one"
        if "repeat" in n:
            return "all"
        return "off"

    def set_order(self, i, msg=None):
        if i is None or not self.orders:
            self.toast("Playback order isn't available")
            return
        self.order = i
        self.pending["order"] = (i, time.perf_counter() + 1.2)
        if self.order_api == "options":
            data = {"options": [{"id": "playbackOrder", "value": i}]}
        else:
            data = {"playbackMode": i}
        self.command("/player", data)
        self.toast(msg or f"Playback order: {self.order_name(i)}")

    def toggle_shuffle(self):
        if not self.orders:
            self.toast("Playback order isn't available")
            return
        if self.shuffle_on():
            tgt = self.last_nonshuffle
            if tgt is None or self._is_shuffle(self.order_name(tgt)):
                tgt = self.find_order("default")
                tgt = 0 if tgt is None else tgt
            self.set_order(tgt, "Shuffle off")
        else:
            self.last_nonshuffle = self.order
            self.set_order(self.find_order("shuffle (tracks)", "shuffle", "random"), "Shuffle on")

    def cycle_repeat(self):
        if not self.orders:
            self.toast("Playback order isn't available")
            return
        was_shuffle = self.shuffle_on()
        st = "off" if was_shuffle else self.repeat_state()
        if st == "off":
            tgt, msg = self.find_order("repeat (playlist)", "repeat (all)", "repeat"), "Repeat playlist"
        elif st == "all":
            tgt, msg = self.find_order("repeat (track)", "repeat (one)"), "Repeat this track"
        else:
            tgt, msg = self.find_order("default"), "Repeat off"
            tgt = 0 if tgt is None else tgt
        if was_shuffle:
            msg += " · shuffle off"
        self.set_order(tgt, msg)

    def toggle_stop_after(self):
        if self.stop_after is None:
            self.toast("“Stop after current” needs a newer Beefweb")
            return
        v = not self.stop_after
        self.stop_after = v
        self.pending["stop_after"] = (v, time.perf_counter() + 1.2)
        self.command("/player", {"options": [{"id": "stopAfterCurrentTrack", "value": v}]})
        self.toast("Will stop after this track" if v else "Won't stop after this track")

    def order_menu(self, x=None, y=None):
        if not self.orders:
            self.toast("Playback order isn't available")
            return
        items = [{"label": str(n), "checked": i == self.order,
                  "fn": (lambda i=i: self.set_order(i))} for i, n in enumerate(self.orders)]
        if self.stop_after is not None:
            items += [None, {"label": "Stop after current track", "checked": bool(self.stop_after),
                             "fn": self.toggle_stop_after, "hint": "⇧X"}]
        if x is None:
            g = self.geo
            x, y = (g["util_pos"]["shuffle"][0], g["util_pos"]["shuffle"][1]) if g else (100, 100)
            y -= 10
        self.open_menu(x, y, items, title="Playback order", up=True)

    # --------------------------------------------------------------- volume
    def set_volume_frac(self, f):
        v = self.vol
        if not v or v.get("type") == "upDown":
            return
        val = frac_vol(v, f)
        v["value"] = val
        self.pending["volume"] = (val, time.perf_counter() + 1.0)
        if v.get("isMuted") and f > 0:
            v["isMuted"] = False
            self.pending["muted"] = (False, time.perf_counter() + 1.0)
            self.command("/player", {"isMuted": False})
        self.vol_dirty = True

    def flush_volume(self, now, force=False):
        if self.vol_dirty and self.vol and (force or now - self.vol_last_send >= 0.06):
            self.vol_dirty = False
            self.vol_last_send = now
            self.command("/player", {"volume": float(self.vol["value"])})

    def volume_step(self, d):
        v = self.vol
        if not v:
            self.toast("Volume isn't available")
            return
        if v.get("type") == "upDown":
            self.command("/player/volume/up" if d > 0 else "/player/volume/down")
            self.toast("Volume up" if d > 0 else "Volume down")
            return
        step = float(SETTINGS["volume_step"]) / 100
        self.set_volume_frac(vol_frac(v) + d * step)
        self.flush_volume(time.perf_counter(), force=True)
        self.toast(vol_label(v))

    def toggle_mute(self):
        v = self.vol
        if not v:
            return
        m = not v.get("isMuted")
        v["isMuted"] = m
        self.pending["muted"] = (m, time.perf_counter() + 1.0)
        self.command("/player", {"isMuted": m})
        self.toast("Muted" if m else vol_label(v))

    # ----------------------------------------------------- state from Beefweb
    def _pend(self, key, remote_val, now):
        p = self.pending.get(key)
        if p and now < p[1]:
            return p[0]
        self.pending.pop(key, None)
        return remote_val

    def sync_remote(self, now):
        r = self.remote
        self.connected = r["ok"]
        if r["seq"] == self.seen_seq:
            return
        self.seen_seq = r["seq"]
        if not r["ok"]:
            self.playing = False
            return
        self.duration, self.playing, self.state = r["dur"], r["playing"], r["state"]
        if now >= self.ignore_until:
            self.pos_base, self.pos_stamp = r["pos"], r["stamp"]

        self.orders, self.order_api = r["orders"], r["order_api"]
        self.order = self._pend("order", r["order"], now)
        self.stop_after = self._pend("stop_after", r["stop_after"], now)
        vol = dict(r["vol"]) if r["vol"] else None
        if vol:
            if not self.vol_dragging:
                vol["value"] = self._pend("volume", vol.get("value", 0), now)
            else:
                vol["value"] = self.vol.get("value", vol.get("value")) if self.vol else vol.get("value")
            vol["isMuted"] = self._pend("muted", vol.get("isMuted", False), now)
        self.vol = vol
        self.perm_pl = r["perm_pl"]

        pl_before = self.play_pl_id
        self.play_pl_id, self.play_idx = r["pl_id"], r["idx"]
        if pl_before != self.play_pl_id:
            self.pl_tab_reveal = True
        self.sync_playlists(r["playlists"], now)
        qi = r["queue"] or []
        self.queue_items = qi
        self.queue_pos = {(x.get("playlistId"), x.get("itemIndex")): n + 1
                          for n, x in enumerate(qi)}

        key = (r["a"], r["t"], r["al"])
        if key != self.track_key and (key[0] or key[1]):
            self.on_track_change(key, r["dur"])

    def sync_playlists(self, pls, now):
        self.playlists = pls
        ids = [p.get("id") for p in pls]
        if self.pl_view_id not in ids and now - self.pl_view_set_at > 2.0:
            fallback = (self.play_pl_id if self.play_pl_id in ids else
                        next((p.get("id") for p in pls if p.get("isCurrent")), ids[0] if ids else None))
            if fallback != self.pl_view_id:
                self.pl_set_view(fallback, reveal=fallback == self.play_pl_id)
        if not self.pl_open or not self.pl_view_id:
            return
        pl = self.pl_by_id(self.pl_view_id)
        if not pl:
            return
        cnt = int(pl.get("itemCount") or 0)
        quiet = (not self.pl_fetch_pending and self.jobs_pending == 0
                 and now - self.pl_last_edit > 0.8 and now - self.pl_last_fetch > 0.8)
        if quiet and (cnt != len(self.pl_items) or
                      (now - self.pl_last_fetch > 6 and cnt < 6000 and not self.pl_drag)):
            self.pl_request_items()

    def on_track_change(self, key, dur):
        self.track_key = self.track = key
        self.lines, self.times, self.focus = [], [], []
        self.lyric_source = ""
        self.lyr_offset = CACHE.get_offset(key)
        self.lines_ver += 1
        self.lyric_state, self.current = "loading", -1
        self.scroll = self.target_scroll = 0.0
        self.auto_follow = True
        self.static_dirty = True
        self.root.title(" — ".join(x for x in key[:2] if x) or "Foobar Lyrics")
        threading.Thread(target=self.lyrics_worker, args=(key, dur, False), daemon=True).start()
        threading.Thread(target=self.art_worker, args=(key,), daemon=True).start()

    def lyrics_worker(self, key, dur, force=False):
        if not force:
            hit = CACHE.get(key)
            if hit:
                self.events.put(("lyrics", key, hit[0], hit[1]))
                return
        try:
            lines, src = fetch_lyrics(key[0], key[1], key[2], dur)
        except Exception:
            lines, src = [], ""
        if lines:
            try:
                CACHE.put(key, lines, src)
            except Exception:
                pass
        self.events.put(("lyrics", key, lines, src))

    def art_worker(self, key):
        raw = None
        for _ in range(3):
            if key != self.track_key:
                return
            try:
                im = Image.open(io.BytesIO(request_bytes(BEEFWEB + "/artwork/current", 8)))
                im.load()
                raw = im.convert("RGB")
                raw.thumbnail((1200, 1200))
                break
            except Exception:
                time.sleep(0.6)
        self.events.put(("art", key, raw))

    def asset_worker(self, seq, raw, w, h, cs, darkness, blur):
        try:
            self.events.put(("assets", seq, build_assets(raw, w, h, cs, darkness, blur)))
        except Exception:
            import traceback
            traceback.print_exc()

    def drain_events(self):
        while True:
            try:
                ev = self.events.get_nowait()
            except queue.Empty:
                return
            kind = ev[0]
            if kind == "lyrics" and ev[1] == self.track_key:
                self.set_lines(ev[2], ev[3])
            elif kind == "art" and ev[1] == self.track_key:
                self.art_raw = ev[2]
                self.art_ver += 1
                self.immediate = True
            elif kind == "assets" and ev[1] == self.asset_seq:
                self.apply_assets(ev[2])
            elif kind == "items":
                self.pl_apply_items(*ev[1:])
            elif kind == "items_fail" and ev[1] == self.pl_view_id:
                self.pl_fetch_pending = False
            elif kind == "upnext" and ev[1] == self.next_sig:
                self.up_next = ev[2]
            elif kind == "toast":
                self.toast(ev[1], 3.2)
            elif kind == "call":
                try:
                    ev[1](ev[2])
                except Exception:
                    import traceback
                    traceback.print_exc()
            elif kind == "job_done":
                self.jobs_pending = max(0, self.jobs_pending - 1)
            elif kind == "resync":
                self.edit_gen += 1
                self.pl_request_items()

    def set_lines(self, lines, source=""):
        self.lines = lines
        self.lyric_source = source
        self.times = [ln[0] for ln in lines]
        self.focus = [0.0] * len(lines)
        self.lines_ver += 1
        self.lyric_state = "found" if lines else "none"
        self.lyr_alpha = 0.0
        self.current = -1
        if self.geo:
            self.layout_lines()
            self.scroll = self.target_scroll = self.center_of(0) if lines else 0.0

    def refetch_lyrics(self):
        if self.track_key is None:
            return
        try:
            CACHE.drop_lines(self.track_key)
        except Exception:
            pass
        self.lines, self.times, self.focus = [], [], []
        self.lyric_source = ""
        self.lines_ver += 1
        self.lyric_state, self.current = "loading", -1
        self.static_dirty = True
        self.toast("Searching lyrics again…")
        threading.Thread(target=self.lyrics_worker,
                         args=(self.track_key, self.duration, True), daemon=True).start()

    def toggle_translation(self):
        SETTINGS["show_translation"] = not SETTINGS["show_translation"]
        if self.geo and self.lines:
            self.layout_lines()
        self.toast("Translation on" if SETTINGS["show_translation"] else "Translation off")

    def adjust_offset(self, d):
        if not self.track_key:
            return
        self.lyr_offset = 0.0 if d is None else round(self.lyr_offset + d, 2)
        CACHE.set_offset(self.track_key, self.lyr_offset)
        if self._cache_save_token:
            self.root.after_cancel(self._cache_save_token)
        self._cache_save_token = self.root.after(1500, lambda: CACHE.save())
        o = self.lyr_offset
        if abs(o) < 1e-6:
            self.toast("Lyric offset reset")
        else:
            self.toast(f"Lyrics {abs(o):.1f}s {'earlier' if o > 0 else 'later'}")

    def manage_assets(self, now):
        w, h = self.size
        sig = (w, h, self.geo["cs"], self.art_ver,
               round(float(SETTINGS["bg_darkness"]), 2),
               round(float(SETTINGS["bg_blur"]), 2))
        if sig != self.want_sig:
            self.want_sig, self.want_since = sig, now
        if sig != self.built_sig and (self.immediate or now - self.want_since >= 0.25):
            self.immediate = False
            self.built_sig = sig
            self.asset_seq += 1
            threading.Thread(
                target=self.asset_worker, daemon=True,
                args=(self.asset_seq, self.art_raw, w, h, self.geo["cs"],
                      SETTINGS["bg_darkness"], SETTINGS["bg_blur"])).start()

    def apply_assets(self, a):
        self.bg_pil, self.scrim_pil = a["bg"], a["scrim"]
        self.scrim_photo = None
        self.assets_gen += 1
        self._glass.clear()
        self.bg_photo = ImageTk.PhotoImage(a["bg"])
        self.cover_photo = ImageTk.PhotoImage(a["cover"])
        self.cover_pad, self.accent, self.tint = a["pad"], a["accent"], a["tint"]
        self.canvas.itemconfig(self.bg_item, image=self.bg_photo)
        self.canvas.itemconfig(self.cover_item, image=self.cover_photo)
        self.place_cover()
        self.static_dirty = True

    def place_cover(self):
        if self.geo and self.cover_photo:
            self.canvas.coords(self.cover_item, self.geo["px"] - self.cover_pad,
                               self.geo["cy"] - self.cover_pad)

    # ----------------------------------------------------------- glass/scrim
    def glass(self, name, box, radius, src="bg", lift=0.62, veil=0.38, strips=None):
        box = tuple(int(round(v)) for v in box)
        k = (name, box, int(radius), src, lift, veil, self.assets_gen)
        hit = self._glass.get(k)
        if hit:
            return hit
        img, avg = make_glass(self.bg_pil if src == "bg" else self.scrim_pil,
                              box, radius, self.tint, lift, veil)
        res = {"img": ImageTk.PhotoImage(img), "avg": avg}
        for sname, (sy0, sy1) in (strips or {}).items():
            sy0, sy1 = max(0, int(sy0)), min(img.height, int(sy1))
            if sy1 > sy0:
                res[sname] = ImageTk.PhotoImage(img.crop((0, sy0, img.width, sy1)))
        if len(self._glass) > 10:
            self._glass.clear()
        self._glass[k] = res
        return res

    def draw_scrim(self):
        g = self.geo
        if self.scrim_pil is not None:
            if self.scrim_photo is None:
                self.scrim_photo = ImageTk.PhotoImage(self.scrim_pil)
            self.canvas.create_image(0, 0, image=self.scrim_photo, anchor="nw", tags="dyn")
        else:
            self.canvas.create_rectangle(0, 0, g["w"], g["h"], fill="#07070b", outline="",
                                         tags="dyn")

    # --------------------------------------------------------------- layout
    def relayout(self):
        c = self.canvas
        w, h = c.winfo_width(), c.winfo_height()
        self.size = (w, h)
        self._ell.clear()
        self._mw.clear()
        F = self.font
        g = {"w": w, "h": h}
        g["f_title"] = F(max(20, int(h * .031)), "bold")
        g["f_artist"] = F(max(15, int(h * .023)))
        g["f_album"] = F(max(13, int(h * .017)))
        g["f_time"] = F(max(11, int(h * .0145)))
        g["f_lyric"] = F(max(30, int(h * .052)), "bold")
        g["f_trans"] = F(max(18, int(h * .029)))
        g["f_msg"] = F(max(20, int(h * .034)), "bold")
        g["f_pill"] = F(max(12, int(h * .0165)), "bold")
        g["f_hint"] = F(max(11, int(h * .0135)))
        g["f_set_title"] = F(max(18, int(h * .026)), "bold")
        g["f_set"] = F(max(14, int(h * .018)))
        g["f_set_val"] = F(max(14, int(h * .018)), "bold")
        g["f_badge"] = F(max(8, int(h * .0105)), "bold")
        g["f_label"] = F(max(10, int(h * .0118)), "bold")
        g["f_pl_head"] = F(max(18, int(h * .025)), "bold")
        g["f_pl_tab"] = F(max(12, int(h * .0148)), "bold")
        g["f_pl_title"] = F(max(13, int(h * .0168)))
        g["f_pl_title_b"] = F(max(13, int(h * .0168)), "bold")
        g["f_pl_sub"] = F(max(11, int(h * .0136)))
        g["f_pl_num"] = F(max(11, int(h * .0132)))
        g["f_pl_foot"] = F(max(11, int(h * .013)))
        g["f_menu"] = F(max(13, int(h * .0158)))
        g["f_menu_hint"] = F(max(11, int(h * .0128)))
        g["f_toast"] = F(max(13, int(h * .0168)), "bold")

        margin = int(w * .055)
        ctl_r = max(22, int(h * .032))
        gap1, gap2 = int(h * .032), int(h * .028)
        tl = g["f_title"].metrics("linespace")
        al = g["f_artist"].metrics("linespace")
        bl = g["f_album"].metrics("linespace")
        info_h = int(tl * 2 + al + bl + h * .006)
        bar_h = int(h * .055)
        ctl_h = int(ctl_r * 2 + h * .035)
        util_r = max(11, int(h * .0155))
        util_h = int(util_r * 2 + h * .018)
        fixed = gap1 + info_h + gap2 + bar_h + ctl_h + util_h
        half = w // 2
        cs = min(half - 2 * margin, int(h * .44))
        cs = max(140, min(cs, int(h * .92) - fixed))
        y0 = max(int(h * .05), (h - (cs + fixed)) // 2)
        px = (half - cs) // 2 + int(w * .01)
        info_y = y0 + cs + gap1
        by = info_y + info_h + gap2 + int(bar_h * .30)
        ctl_top = info_y + info_h + gap2 + bar_h
        ctl_cy = ctl_top + ctl_r + int(h * .005)
        util_cy = ctl_top + ctl_h + util_h // 2 + int(h * .004)
        cx0 = px + cs / 2
        step = min(cs / 5.0, h * .092)
        buttons = [("back", -2), ("prev", -1), ("play", 0), ("next", 1), ("fwd", 2)]

        # utility row: shuffle · repeat · volume ······ help · playlist
        ux_shuf = px + util_r
        ux_rep = ux_shuf + util_r * 2.9
        ux_list = px + cs - util_r
        ux_help = ux_list - util_r * 2.9
        ux_vol = ux_rep + util_r * 3.1
        vx0, vx1 = ux_vol + util_r * 1.5, ux_help - util_r * 2.3
        util = [("shuffle", ux_shuf), ("repeat", ux_rep), ("mute", ux_vol),
                ("help", ux_help), ("list", ux_list)]

        lx = half + int(w * .02)
        pill_txt = "Follow lyrics"
        pw = g["f_pill"].measure(pill_txt) + int(h * .05)
        ph = int(h * .05)
        pill_x0 = lx + (w - lx - margin) / 2 - pw / 2
        pill_y0 = h - int(h * .115)
        g.update(
            cs=cs, px=px, cy=y0, info_y=info_y, title_lh=tl, artist_lh=al, album_lh=bl,
            ctl_r=ctl_r, ctl_cy=ctl_cy, margin=margin,
            bar=(px, px + cs, by), bar_hit=max(14, int(h * .022)),
            buttons=[(n, cx0 + k * step, ctl_cy, (ctl_r + 6) if n == "play" else ctl_r * .9)
                     for n, k in buttons],
            util_r=util_r, util_cy=util_cy,
            util=[(n, x, util_cy, util_r * 1.35) for n, x in util],
            util_pos={n: (x, util_cy) for n, x in util},
            vol=(vx0, vx1, util_cy) if vx1 - vx0 >= 40 else None,
            lx=lx, lw=max(300, w - lx - margin), ay=int(h * .42),
            pill=(pill_x0, pill_y0, pill_x0 + pw, pill_y0 + ph), pill_txt=pill_txt)

        # playlist panel geometry (occupies the lyric column)
        pad = max(16, int(h * .022))
        bx0, bx1 = lx - int(w * .012), w - int(margin * .5)
        by0, by1 = int(h * .045), h - int(h * .045)
        head_lh = g["f_pl_head"].metrics("linespace")
        head_cy = by0 + pad + head_lh / 2
        hb = max(16, int(h * .019))
        hbtns = []
        for i, name in enumerate(("more", "sort", "add")):
            hbtns.append((name, bx1 - pad - hb - i * (hb * 2 + int(h * .008)), head_cy, hb))
        tab_lh = g["f_pl_tab"].metrics("linespace")
        tabs_y0 = int(head_cy + head_lh / 2 + h * .014)
        tabs_h = int(tab_lh + h * .016)
        search_y0 = tabs_y0 + tabs_h + int(h * .014)
        search_h = max(30, int(h * .042))
        list_y0 = search_y0 + search_h + int(h * .012)
        foot_lh = g["f_pl_foot"].metrics("linespace")
        foot_h = int(foot_lh + h * .026)
        list_y1 = by1 - foot_h
        row_h = int(g["f_pl_title"].metrics("linespace") + g["f_pl_sub"].metrics("linespace")
                    + h * .018)
        g["pl"] = dict(x0=bx0, y0=by0, x1=bx1, y1=by1, pad=pad, rad=max(14, int(h * .02)),
                       head_cy=head_cy, hbtns=hbtns, tabs_y0=tabs_y0, tabs_h=tabs_h,
                       search=(bx0 + pad, search_y0, bx1 - pad, search_y0 + search_h),
                       list_y0=list_y0, list_y1=list_y1, row_h=max(34, row_h),
                       foot_cy=(list_y1 + by1) / 2,
                       numw=g["f_pl_num"].measure("0000"))
        self.geo = g
        self.help_lay = None
        self.layout_lines()
        if self.lines:
            self.target_scroll = (self.center_of(max(0, self.current))
                                  if self.auto_follow else self.target_scroll)
            self.scroll = self.target_scroll
        self.pl_clamp_scroll(snap=True)
        self.place_cover()
        self.static_dirty = True

    def layout_lines(self):
        g = self.geo
        f = g["f_lyric"]
        lh = f.metrics("linespace")
        gap = int(lh * .55)
        ft = g["f_trans"]
        tlh = ft.metrics("linespace")
        tgap = int(lh * .12)
        self.line_rows, self.line_y, self.line_h = [], [], []
        self.line_trows, self.line_oh = [], []
        y = 0
        show_trans = bool(SETTINGS["show_translation"])
        for _, txt, tr in self.lines:
            rows = wrap(txt or "♪", f, g["lw"])
            oh = len(rows) * lh
            trows, th = "", 0
            if show_trans and tr:
                tr_rows = wrap(tr, ft, g["lw"])
                trows, th = "\n".join(tr_rows), len(tr_rows) * tlh + tgap
            self.line_rows.append("\n".join(rows))
            self.line_trows.append(trows)
            self.line_oh.append(oh)
            self.line_y.append(y)
            self.line_h.append(oh + th)
            y += oh + th + gap
        g["lh"], g["lgap"], g["tgap"] = lh, gap, tgap

    def center_of(self, i):
        return self.line_y[i] + self.line_h[i] / 2

    # ============================================================ PLAYLISTS
    def pl_by_id(self, pid):
        return next((p for p in self.playlists if p.get("id") == pid), None)

    def pl_view(self):
        return self.pl_by_id(self.pl_view_id)

    def toggle_playlist(self, open_=None):
        self.pl_open = (not self.pl_open) if open_ is None else bool(open_)
        self.menu = None
        if self.pl_open:
            ids = [p.get("id") for p in self.playlists]
            if self.pl_view_id not in ids:
                pid = (self.play_pl_id if self.play_pl_id in ids else
                       next((p.get("id") for p in self.playlists if p.get("isCurrent")),
                            ids[0] if ids else None))
                self.pl_set_view(pid, reveal=True)
            else:
                self.pl_want_reveal = self.pl_view_id == self.play_pl_id
                self.pl_request_items()
            if not self.connected:
                self.toast("Not connected to foobar2000")
        else:
            self.pl_filter_active = False
            self.pl_drag = None

    def pl_set_view(self, pid, reveal=False):
        if pid != self.pl_view_id:
            self.pl_view_id = pid
            self.pl_view_set_at = time.perf_counter()
            self.pl_items, self.pl_rows, self.pl_rowpos = [], [], None
            self.pl_sel, self.pl_anchor, self.pl_cursor = set(), None, -1
            self.pl_scroll = self.pl_target = 0.0
            self.pl_filter, self.pl_filter_active = "", False
            self.pl_tab_reveal = True
            self.pl_drag = None
        self.pl_want_reveal = reveal
        if pid and self.pl_open:
            self.pl_request_items()

    def pl_cycle_view(self, d):
        if not self.playlists:
            return
        ids = [p.get("id") for p in self.playlists]
        i = ids.index(self.pl_view_id) if self.pl_view_id in ids else 0
        self.pl_set_view(ids[(i + d) % len(ids)], reveal=True)

    def pl_request_items(self):
        pid = self.pl_view_id
        if not pid or not self.connected:
            return
        self.pl_fetch_pending = True
        self.pl_last_fetch = time.perf_counter()
        gen = self.edit_gen
        colstr = ",".join(PL_COLS)

        def job():
            items, off, total = [], 0, None
            try:
                while True:
                    url = (f"{BEEFWEB}/playlists/{q(pid)}/items/{off}:4000?"
                           + urllib.parse.urlencode({"columns": colstr}))
                    res = (get_json(url, 10).get("playlistItems") or {})
                    total = int(res.get("totalCount") or 0)
                    batch = res.get("items") or []
                    for it in batch:
                        cols = [str(x) if x is not None else "" for x in (it.get("columns") or [])]
                        cols += [""] * (5 - len(cols))
                        a, t, al, ln, secs = cols[:5]
                        try:
                            secs = float(secs or 0)
                        except ValueError:
                            secs = 0.0
                        items.append((a, t, al, ln, secs, f"{a} {t} {al}".lower()))
                    off += len(batch)
                    if not batch or off >= total:
                        break
            except Exception:
                self.events.put(("items_fail", pid))
                raise
            self.events.put(("items", pid, gen, items))
        self.serial(job)

    def pl_apply_items(self, pid, gen, items):
        if pid != self.pl_view_id:
            return
        self.pl_fetch_pending = False
        if gen != self.edit_gen:
            return
        n = len(items)
        self.pl_items = items
        self.pl_sel = {i for i in self.pl_sel if i < n}
        if self.pl_cursor >= n:
            self.pl_cursor = n - 1
        self.pl_refilter()
        if self.pl_want_reveal:
            self.pl_want_reveal = False
            self.pl_reveal_playing(select=False)

    def pl_refilter(self):
        toks = self.pl_filter.lower().split()
        if toks:
            self.pl_rows = [i for i, it in enumerate(self.pl_items) if all(t in it[5] for t in toks)]
            self.pl_rowpos = {r: k for k, r in enumerate(self.pl_rows)}
        else:
            self.pl_rows = list(range(len(self.pl_items)))
            self.pl_rowpos = None
        self.pl_clamp_scroll()

    def pl_vpos(self, real):
        if real is None or real < 0:
            return None
        if self.pl_rowpos is None:
            return real if real < len(self.pl_rows) else None
        return self.pl_rowpos.get(real)

    def pl_list_h(self):
        P = self.geo["pl"]
        return P["list_y1"] - P["list_y0"]

    def pl_max_scroll(self):
        if not self.geo:
            return 0.0
        return max(0.0, len(self.pl_rows) * self.geo["pl"]["row_h"] - self.pl_list_h() + 8)

    def pl_clamp_scroll(self, snap=False):
        m = self.pl_max_scroll()
        self.pl_target = max(0.0, min(m, self.pl_target))
        if snap:
            self.pl_scroll = self.pl_target

    def pl_ensure_visible(self, real, center=False):
        vp = self.pl_vpos(real)
        if vp is None or not self.geo:
            return
        rh, lh = self.geo["pl"]["row_h"], self.pl_list_h()
        top = vp * rh
        if center:
            self.pl_target = top - lh / 2 + rh / 2
        elif top < self.pl_target:
            self.pl_target = top
        elif top + rh > self.pl_target + lh:
            self.pl_target = top + rh - lh
        self.pl_clamp_scroll()

    def pl_reveal_playing(self, select=True):
        if self.play_pl_id is None or self.play_idx is None or self.play_idx < 0:
            if select:
                self.toast("Nothing is playing")
            return
        if self.pl_view_id != self.play_pl_id:
            self.pl_set_view(self.play_pl_id, reveal=True)
            return
        if self.pl_filter and self.pl_vpos(self.play_idx) is None:
            self.pl_filter = ""
            self.pl_refilter()
        self.pl_cursor = self.play_idx
        if select:
            self.pl_sel, self.pl_anchor = {self.play_idx}, self.play_idx
        self.pl_ensure_visible(self.play_idx, center=True)

    # -- selection
    def pl_selected(self):
        sel = sorted(i for i in self.pl_sel if 0 <= i < len(self.pl_items))
        if not sel and 0 <= self.pl_cursor < len(self.pl_items):
            sel = [self.pl_cursor]
        return sel

    def pl_click_row(self, real, ctrl, shift):
        if shift and self.pl_anchor is not None and self.pl_vpos(self.pl_anchor) is not None:
            a, b = sorted((self.pl_vpos(self.pl_anchor), self.pl_vpos(real)))
            rng = set(self.pl_rows[a:b + 1])
            self.pl_sel = (self.pl_sel | rng) if ctrl else rng
        elif ctrl:
            self.pl_sel ^= {real}
            self.pl_anchor = real
        else:
            self.pl_sel, self.pl_anchor = {real}, real
        self.pl_cursor = real

    def pl_nav(self, dvp, shift=False, absolute=None):
        rows = self.pl_rows
        if not rows:
            return
        cur = self.pl_vpos(self.pl_cursor)
        if absolute is not None:
            vp = absolute
        elif cur is None:
            vp = 0 if dvp > 0 else len(rows) - 1
        else:
            vp = cur + dvp
        vp = max(0, min(len(rows) - 1, vp))
        real = rows[vp]
        if shift:
            if self.pl_anchor is None or self.pl_vpos(self.pl_anchor) is None:
                self.pl_anchor = self.pl_cursor if self.pl_cursor >= 0 else real
            av = self.pl_vpos(self.pl_anchor)
            a, b = sorted((av if av is not None else vp, vp))
            self.pl_sel = set(rows[a:b + 1])
        else:
            self.pl_sel, self.pl_anchor = {real}, real
        self.pl_cursor = real
        self.pl_ensure_visible(real)

    def pl_select_all(self):
        self.pl_sel = set(self.pl_rows)
        if self.pl_rows:
            self.pl_anchor = self.pl_rows[0]
        self.toast(f"{plural(len(self.pl_sel), 'track')} selected")

    # -- actions
    def pl_play(self, real):
        if not self.pl_view_id or not (0 <= real < len(self.pl_items)):
            return
        self.command(f"/player/play/{q(self.pl_view_id)}/{real}")
        self.pl_cursor = real

    def _can_edit(self):
        if not self.connected:
            self.toast("Not connected to foobar2000")
            return False
        if not self.perm_pl:
            self.toast("Playlist editing is disabled in Beefweb's settings")
            return False
        return True

    def pl_edit(self, path, data=None, ok=None, refresh=True):
        if not self._can_edit():
            return False
        if refresh:
            self.edit_gen += 1
            self.pl_last_edit = time.perf_counter()

        def job():
            res = post_json(BEEFWEB + path, data, timeout=15)
            if ok:
                self.events.put(("call", ok, res))
        self.serial(job)
        if refresh:
            self.pl_request_items()
        return True

    def _no_filter_for(self, what):
        if self.pl_filter:
            self.toast(f"Clear the filter to {what}")
            return False
        return True

    def pl_remove_selected(self):
        sel = self.pl_selected()
        if not sel or not self._can_edit():
            return
        s = set(sel)
        self.pl_items = [it for i, it in enumerate(self.pl_items) if i not in s]
        cur = min(sel[0], len(self.pl_items) - 1)
        self.pl_sel = {cur} if cur >= 0 else set()
        self.pl_cursor, self.pl_anchor = cur, cur
        self.pl_refilter()
        self.pl_edit(f"/playlists/{q(self.pl_view_id)}/items/remove", {"items": sel})
        self.toast(f"Removed {plural(len(sel), 'track')}")

    def pl_crop_selected(self):
        sel = set(self.pl_selected())
        if not sel:
            return
        rest = [i for i in range(len(self.pl_items)) if i not in sel]
        if not rest or not self._can_edit():
            return
        keep = [it for i, it in enumerate(self.pl_items) if i in sel]
        self.pl_items = keep
        self.pl_sel = set(range(len(keep)))
        self.pl_cursor = self.pl_anchor = 0
        self.pl_refilter()
        self.pl_edit(f"/playlists/{q(self.pl_view_id)}/items/remove", {"items": rest})
        self.toast(f"Kept {plural(len(keep), 'track')}")

    def pl_move_to(self, sel, gap):
        n = len(self.pl_items)
        sel = sorted({i for i in sel if 0 <= i < n})
        if not sel or not self._no_filter_for("reorder tracks"):
            return
        gap = max(0, min(n, gap))
        s = set(sel)
        pos = gap - sum(1 for i in sel if i < gap)
        k = len(sel)
        if sel == list(range(pos, pos + k)):
            return                                  # no-op
        if not self._can_edit():
            return
        rest = [it for i, it in enumerate(self.pl_items) if i not in s]
        moved = [self.pl_items[i] for i in sel]
        self.pl_items = rest[:pos] + moved + rest[pos:]
        off = sel.index(self.pl_cursor) if self.pl_cursor in s else 0
        self.pl_sel = set(range(pos, pos + k))
        self.pl_cursor, self.pl_anchor = pos + off, pos
        self.pl_refilter()
        self.pl_ensure_visible(self.pl_cursor)
        self.pl_edit(f"/playlists/{q(self.pl_view_id)}/items/move",
                     {"items": sel, "targetIndex": gap})

    def pl_move_step(self, d):
        sel = self.pl_selected()
        if not sel:
            return
        if d < 0:
            if sel[0] == 0 and sel == list(range(len(sel))):
                return
            self.pl_move_to(sel, max(0, sel[0] - 1))
        else:
            n = len(self.pl_items)
            if sel[-1] == n - 1 and sel == list(range(n - len(sel), n)):
                return
            self.pl_move_to(sel, min(n, sel[-1] + 2))

    def pl_toggle_queue(self):
        sel = self.pl_selected()
        pid = self.pl_view_id
        if not sel or not pid or not self.connected:
            return
        added = removed = 0
        for i in sel[:200]:
            if (pid, i) in self.queue_pos:
                path, removed = "/playqueue/remove", removed + 1
            else:
                path, added = "/playqueue/add", added + 1
            self.serial(lambda path=path, i=i: post_json(BEEFWEB + path,
                                                        {"plref": pid, "itemIndex": i}))
        bits = []
        if added:
            bits.append(f"Queued {plural(added, 'track')}")
        if removed:
            bits.append(f"unqueued {removed}")
        self.toast(" · ".join(bits).capitalize() if bits else "")

    def clear_queue(self):
        self.serial(lambda: post_json(BEEFWEB + "/playqueue/clear"))
        self.toast("Queue cleared")

    def pl_sort(self, expr=None, label="", random_=False):
        if not self.pl_view_id:
            return
        data = {"random": True} if random_ else {"by": expr, "desc": bool(self.sort_desc)}
        if self.pl_edit(f"/playlists/{q(self.pl_view_id)}/items/sort", data):
            self.toast("Randomized order" if random_ else
                       f"Sorted by {label.lower()}" + (" (descending)" if self.sort_desc else ""))

    def pl_new(self):
        if not self._can_edit():
            return

        def ok(title):
            def created(res):
                if isinstance(res, dict) and res.get("id"):
                    self.pl_set_view(res["id"])
            self.pl_edit("/playlists/add", {"title": title}, ok=created, refresh=False)
            self.toast(f"Created “{title}”")
        self.prompt("New playlist", "New Playlist", ok, ok_label="Create")

    def pl_rename(self, pid=None):
        pid = pid or self.pl_view_id
        pl = self.pl_by_id(pid)
        if not pl or not self._can_edit():
            return

        def ok(title):
            pl["title"] = title
            self.pl_edit(f"/playlists/{q(pid)}", {"title": title}, refresh=False)
        self.prompt("Rename playlist", pl.get("title", ""), ok, ok_label="Rename")

    def pl_delete(self, pid=None):
        pid = pid or self.pl_view_id
        pl = self.pl_by_id(pid)
        if not pl or not self._can_edit():
            return

        def ok():
            ids = [p.get("id") for p in self.playlists]
            i = ids.index(pid) if pid in ids else 0
            others = [x for x in ids if x != pid]
            if self.pl_edit(f"/playlists/remove/{q(pid)}", refresh=False):
                self.toast(f"Deleted “{pl.get('title', '')}”")
                if pid == self.pl_view_id and others:
                    self.pl_set_view(others[min(i, len(others) - 1)])
        self.confirm("Delete playlist?",
                     f"“{pl.get('title', '')}” and its {plural(int(pl.get('itemCount') or 0), 'track')} "
                     "will be removed from foobar2000.", ok, "Delete")

    def pl_clear(self, pid=None):
        pid = pid or self.pl_view_id
        pl = self.pl_by_id(pid)
        if not pl or not self._can_edit():
            return

        def ok():
            if pid == self.pl_view_id:
                self.pl_items, self.pl_sel, self.pl_cursor = [], set(), -1
                self.pl_refilter()
            if self.pl_edit(f"/playlists/{q(pid)}/clear", refresh=pid == self.pl_view_id):
                self.toast(f"Cleared “{pl.get('title', '')}”")
        self.confirm("Clear playlist?", f"Remove every track from “{pl.get('title', '')}”?",
                     ok, "Clear")

    def pl_duplicate(self, pid=None):
        pid = pid or self.pl_view_id
        pl = self.pl_by_id(pid)
        if not pl or not self._can_edit():
            return
        n = int(pl.get("itemCount") or 0)

        def created(res):
            if isinstance(res, dict) and res.get("id") and n:
                self.pl_edit(f"/playlists/{q(pid)}/{q(res['id'])}/items/copy",
                             {"items": list(range(n))}, refresh=False)
        self.pl_edit("/playlists/add", {"title": f"{pl.get('title', '')} (copy)"},
                     ok=created, refresh=False)
        self.toast(f"Duplicated “{pl.get('title', '')}”")

    def pl_move_playlist(self, pid, d):
        pl = self.pl_by_id(pid)
        if not pl:
            return
        ni = int(pl.get("index", 0)) + d
        if 0 <= ni < len(self.playlists):
            self.pl_edit(f"/playlists/move/{q(pid)}/{ni}", refresh=False)

    def pl_activate(self, pid=None):
        pid = pid or self.pl_view_id
        if pid and self.pl_edit("/playlists", {"current": pid}, refresh=False):
            self.toast("Selected in foobar2000")

    def pl_copy_to(self, dst):
        sel = self.pl_selected()
        if not sel or not self.pl_view_id:
            return
        if self.pl_edit(f"/playlists/{q(self.pl_view_id)}/{q(dst)}/items/copy", {"items": sel},
                        refresh=dst == self.pl_view_id):
            t = (self.pl_by_id(dst) or {}).get("title", "playlist")
            self.toast(f"Copied {plural(len(sel), 'track')} to “{t}”")

    def pl_add_files(self, folder=False):
        if not self.pl_view_id or not self._can_edit():
            return
        was_fs = self.fullscreen
        try:
            if was_fs:
                self.root.attributes("-fullscreen", False)
            if folder:
                p = filedialog.askdirectory(parent=self.root, title="Add folder to playlist")
                paths = [p] if p else []
            else:
                paths = list(filedialog.askopenfilenames(parent=self.root,
                                                         title="Add files to playlist"))
        finally:
            if was_fs:
                self.root.attributes("-fullscreen", True)
            self.root.focus_force()
        if paths:
            self._add_items([os.path.normpath(p) for p in paths])

    def pl_add_url(self):
        if not self.pl_view_id or not self._can_edit():
            return
        self.prompt("Add location", "", lambda u: self._add_items([u]), ok_label="Add",
                    placeholder="https://… stream or file path")

    def _add_items(self, items):
        pid = self.pl_view_id
        if self.pl_edit(f"/playlists/{q(pid)}/items/add", {"items": items, "async": True}):
            self.toast(f"Adding {plural(len(items), 'item')}…")
            self.root.after(1500, lambda: pid == self.pl_view_id and self.pl_request_items())

    # -- menus for playlist UI
    def menu_playlist(self, x, y, pid=None):
        pid = pid or self.pl_view_id
        pl = self.pl_by_id(pid)
        viewing = pid == self.pl_view_id
        items = [
            {"label": "New playlist…", "hint": "Ctrl+N", "fn": self.pl_new},
            {"label": "Rename…", "hint": "F2", "fn": lambda: self.pl_rename(pid), "enabled": bool(pl)},
            {"label": "Duplicate", "fn": lambda: self.pl_duplicate(pid), "enabled": bool(pl)},
            None,
            {"label": "Add files…", "hint": "Ctrl+O", "fn": self.pl_add_files, "enabled": viewing},
            {"label": "Add folder…", "fn": lambda: self.pl_add_files(True), "enabled": viewing},
            {"label": "Add URL / path…", "hint": "Ctrl+U", "fn": self.pl_add_url, "enabled": viewing},
            None,
            {"label": "Sort by", "sub": True, "fn": lambda: self.menu_sort(x, y), "enabled": viewing},
            {"label": "Randomize order", "fn": lambda: self.pl_sort(random_=True), "enabled": viewing},
            None,
            {"label": "Move left", "fn": lambda: self.pl_move_playlist(pid, -1),
             "enabled": bool(pl) and int(pl.get("index", 0)) > 0},
            {"label": "Move right", "fn": lambda: self.pl_move_playlist(pid, 1),
             "enabled": bool(pl) and int(pl.get("index", 0)) < len(self.playlists) - 1},
            {"label": "Select in foobar2000", "fn": lambda: self.pl_activate(pid), "enabled": bool(pl)},
            {"label": "Refresh", "hint": "F5", "fn": self.pl_request_items},
        ]
        if self.queue_items:
            items += [{"label": f"Clear queue ({len(self.queue_items)})", "fn": self.clear_queue}]
        items += [
            None,
            {"label": "Clear playlist…", "fn": lambda: self.pl_clear(pid), "danger": True,
             "enabled": bool(pl)},
            {"label": "Delete playlist…", "hint": "Ctrl+W", "fn": lambda: self.pl_delete(pid),
             "danger": True, "enabled": bool(pl)},
        ]
        self.open_menu(x, y, items, title=(pl or {}).get("title", "Playlist"))

    def menu_sort(self, x, y):
        items = [{"label": lbl, "fn": (lambda e=e, lbl=lbl: self.pl_sort(e, lbl))}
                 for lbl, e in SORT_OPTIONS]
        items += [None,
                  {"label": "Descending", "checked": self.sort_desc, "keep": True,
                   "fn": lambda: setattr(self, "sort_desc", not self.sort_desc)},
                  {"label": "Randomize", "fn": lambda: self.pl_sort(random_=True)}]
        self.open_menu(x, y, items, title="Sort playlist")

    def menu_rows(self, x, y):
        sel = self.pl_selected()
        if not sel:
            return
        pid = self.pl_view_id
        n = len(sel)
        all_q = all((pid, i) in self.queue_pos for i in sel)
        others = [p for p in self.playlists if p.get("id") != pid]
        items = [
            {"label": "Play", "hint": "Enter", "fn": lambda: self.pl_play(sel[0])},
            {"label": ("Remove from queue" if all_q else "Add to queue"), "hint": "Q",
             "fn": self.pl_toggle_queue},
            None,
            {"label": "Move to top", "fn": lambda: self.pl_move_to(sel, 0)},
            {"label": "Move to bottom", "fn": lambda: self.pl_move_to(sel, len(self.pl_items))},
            {"label": "Copy to playlist", "sub": True, "enabled": bool(others),
             "fn": lambda: self.open_menu(x, y, [
                 {"label": p.get("title", "?"), "fn": (lambda d=p.get("id"): self.pl_copy_to(d))}
                 for p in others[:30]], title=f"Copy {plural(n, 'track')} to")},
            {"label": "Keep only selected", "fn": self.pl_crop_selected,
             "enabled": n < len(self.pl_items)},
            {"label": "Select all", "hint": "Ctrl+A", "fn": self.pl_select_all},
            None,
            {"label": f"Remove {plural(n, 'track')}", "hint": "Del", "danger": True,
             "fn": self.pl_remove_selected},
        ]
        self.open_menu(x, y, items, title=(self.pl_items[sel[0]][1] if n == 1 else
                                           f"{n} tracks selected"))

    def menu_general(self, x, y):
        items = [
            {"label": "Hide playlists" if self.pl_open else "Show playlists", "hint": "P",
             "fn": self.toggle_playlist},
            {"label": "Search lyrics again", "hint": "R", "fn": self.refetch_lyrics},
            {"label": "Show translation", "hint": "V", "checked": bool(SETTINGS["show_translation"]),
             "fn": self.toggle_translation},
            {"label": "Reset lyric offset", "hint": "\\", "fn": lambda: self.adjust_offset(None),
             "enabled": abs(self.lyr_offset) > 1e-6},
            None,
            {"label": "Shuffle", "hint": "Ctrl+S", "checked": self.shuffle_on(),
             "fn": self.toggle_shuffle},
            {"label": "Playback order", "sub": True, "hint": "O",
             "fn": lambda: self.order_menu(x, y)},
            None,
            {"label": "Settings", "hint": "S", "fn": self.toggle_settings},
            {"label": "Keyboard shortcuts", "hint": "?", "fn": self.toggle_help},
            {"label": "Exit fullscreen" if self.fullscreen else "Fullscreen", "hint": "F11",
             "fn": self.toggle_fullscreen},
            None,
            {"label": "Quit", "hint": "Ctrl+Q", "fn": self.close},
        ]
        self.open_menu(x, y, items)

    # ============================================================== MENUS
    def open_menu(self, x, y, items, title=None, up=False):
        self.menu = {"x": x, "y": y, "items": items, "title": title, "sel": -1, "up": up,
                     "t0": time.perf_counter()}

    def menu_layout(self):
        m, g = self.menu, self.geo
        f, fh = g["f_menu"], g["f_menu_hint"]
        ih = f.metrics("linespace") + int(g["h"] * .012)
        sh = max(9, int(g["h"] * .011))
        th = fh.metrics("linespace") + int(g["h"] * .014) if m["title"] else 0
        padx = int(g["h"] * .016)
        check_w = f.measure("✓") + 10
        w = 0
        for it in m["items"]:
            if it:
                lw = f.measure(it["label"]) + (fh.measure(it.get("hint", "")) + 30 if it.get("hint") else 0)
                lw += 24 if it.get("sub") else 0
                w = max(w, lw)
        if m["title"]:
            w = max(w, min(fh.measure(m["title"]), int(g["w"] * .3)))
        w = int(max(w + check_w + padx * 2, g["h"] * .2))
        h = th + 12 + sum(ih if it else sh for it in m["items"])
        x, y = m["x"], m["y"]
        if m.get("up"):
            y -= h
        x = max(8, min(g["w"] - w - 8, x))
        y = max(8, min(g["h"] - h - 8, y))
        rows, cy = [], y + 6 + th
        for i, it in enumerate(m["items"]):
            hh = ih if it else sh
            rows.append((i, cy, cy + hh))
            cy += hh
        return {"x0": x, "y0": y, "x1": x + w, "y1": y + h, "rows": rows, "padx": padx,
                "check_w": check_w, "th": th}

    def menu_hover_index(self, lay):
        if not (lay["x0"] <= self.mx <= lay["x1"]):
            return -1
        for i, y0, y1 in lay["rows"]:
            it = self.menu["items"][i]
            if it and it.get("enabled", True) and y0 <= self.my < y1:
                return i
        return -1

    def draw_menu(self):
        if not self.menu:
            return
        c, g = self.canvas, self.geo
        lay = self.menu_layout()
        self.menu["lay"] = lay
        x0, y0, x1, y1 = lay["x0"], lay["y0"], lay["x1"], lay["y1"]
        base = mix(self.tint, (18, 18, 28), .7)
        self.rrect(x0 + 2, y0 + 6, x1 + 2, y1 + 8, 14, fill="#020203", outline="", tags="dyn")
        self.rrect(x0, y0, x1, y1, 14, fill=hexc(base), outline=hexc(mix(base, WHITE, .14)),
                   tags="dyn")
        f, fh = g["f_menu"], g["f_menu_hint"]
        if self.menu["title"]:
            c.create_text(x0 + lay["padx"], y0 + 6 + lay["th"] / 2,
                          text=self.ell(self.menu["title"].upper(), fh, x1 - x0 - 2 * lay["padx"]),
                          anchor="w", font=fh, fill=hexc(mix(base, WHITE, .45)), tags="dyn")
        hov = self.menu_hover_index(lay)
        if hov >= 0:
            self.menu["sel"] = hov
        sel = self.menu["sel"]
        for i, ry0, ry1 in lay["rows"]:
            it = self.menu["items"][i]
            if not it:
                c.create_line(x0 + 12, (ry0 + ry1) / 2, x1 - 12, (ry0 + ry1) / 2,
                              fill=hexc(mix(base, WHITE, .10)), tags="dyn")
                continue
            en = it.get("enabled", True)
            if i == sel and en:
                self.rrect(x0 + 6, ry0 + 1, x1 - 6, ry1 - 1, 8,
                           fill=hexc(mix(base, self.accent, .42)), outline="", tags="dyn")
            cy = (ry0 + ry1) / 2
            col = (DANGER if it.get("danger") else WHITE) if en else mix(base, WHITE, .32)
            if it.get("checked"):
                c.create_text(x0 + lay["padx"], cy, text="✓", anchor="w", font=f,
                              fill=hexc(mix(self.accent, WHITE, .35) if i != sel else WHITE),
                              tags="dyn")
            c.create_text(x0 + lay["padx"] + lay["check_w"], cy, text=it["label"], anchor="w",
                          font=f, fill=hexc(col), tags="dyn")
            right = x1 - lay["padx"]
            if it.get("sub"):
                self._tri(right - 4, cy, 5, "right", hexc(mix(base, WHITE, .6)))
                right -= 20
            if it.get("hint"):
                c.create_text(right, cy, text=it["hint"], anchor="e", font=fh,
                              fill=hexc(mix(base, WHITE, .42)), tags="dyn")

    def menu_activate(self, i):
        it = self.menu["items"][i] if self.menu and 0 <= i < len(self.menu["items"]) else None
        if not it or not it.get("enabled", True):
            return
        if not it.get("keep"):
            self.menu = None
        try:
            it["fn"]()
        except Exception:
            import traceback
            traceback.print_exc()
        if it.get("keep") and self.menu and "checked" in it:
            it["checked"] = not it["checked"]

    def menu_click(self, x, y):
        lay = self.menu.get("lay") or self.menu_layout()
        if not (lay["x0"] <= x <= lay["x1"] and lay["y0"] <= y <= lay["y1"]):
            self.menu = None
            return
        i = self.menu_hover_index(lay)
        if i >= 0:
            self.menu_activate(i)

    def menu_key(self, k):
        m = self.menu
        items = m["items"]
        valid = [i for i, it in enumerate(items) if it and it.get("enabled", True)]
        if k in ("Escape", "Left"):
            self.menu = None
        elif k in ("Up", "Down") and valid:
            cur = m["sel"]
            if cur not in valid:
                m["sel"] = valid[0] if k == "Down" else valid[-1]
            else:
                j = valid.index(cur) + (1 if k == "Down" else -1)
                m["sel"] = valid[j % len(valid)]
            self.mx = self.my = -1           # keyboard takes over from hover
        elif k in ("Return", "KP_Enter", "space", "Right"):
            if m["sel"] in valid:
                self.menu_activate(m["sel"])
        return True

    # ============================================================== MODALS
    def prompt(self, title, initial, on_ok, ok_label="OK", placeholder=""):
        self.menu = None
        self.modal = {"kind": "prompt", "title": title, "text": initial, "caret": len(initial),
                      "all": bool(initial), "on_ok": on_ok, "ok": ok_label,
                      "placeholder": placeholder, "t0": time.perf_counter()}

    def confirm(self, title, body, on_ok, ok_label="OK", danger=True):
        self.menu = None
        if not SETTINGS["confirm_destructive"]:
            on_ok()
            return
        self.modal = {"kind": "confirm", "title": title, "body": body, "on_ok": on_ok,
                      "ok": ok_label, "danger": danger, "t0": time.perf_counter()}

    def modal_ok(self):
        m, self.modal = self.modal, None
        if m["kind"] == "prompt":
            txt = m["text"].strip()
            if txt:
                m["on_ok"](txt)
        else:
            m["on_ok"]()

    def modal_layout(self):
        g, m = self.geo, self.modal
        W, H = g["w"], g["h"]
        pw = int(min(620, W - 80, max(420, W * .34)))
        pad = int(max(22, H * .03))
        title_lh = g["f_set_title"].metrics("linespace")
        body_rows = []
        if m["kind"] == "confirm":
            body_rows = wrap(m["body"], g["f_set"], pw - 2 * pad)
        field_h = int(g["f_set"].metrics("linespace") + H * .022) if m["kind"] == "prompt" else 0
        body_h = len(body_rows) * g["f_set"].metrics("linespace")
        btn_h = int(max(36, H * .045))
        ph = pad + title_lh + int(H * .016) + body_h + field_h + int(H * .026) + btn_h + pad
        x0, y0 = (W - pw) // 2, (H - ph) // 2
        bw = max(110, int(g["f_set"].measure(m["ok"]) + H * .05))
        ok_box = (x0 + pw - pad - bw, y0 + ph - pad - btn_h, x0 + pw - pad, y0 + ph - pad)
        cancel_box = (ok_box[0] - 12 - bw, ok_box[1], ok_box[0] - 12, ok_box[3])
        fy0 = y0 + pad + title_lh + int(H * .016)
        return {"box": (x0, y0, x0 + pw, y0 + ph), "pad": pad, "body": body_rows,
                "field": (x0 + pad, fy0, x0 + pw - pad, fy0 + field_h), "ok": ok_box,
                "cancel": cancel_box, "title_y": y0 + pad + title_lh / 2}

    def draw_modal(self):
        if not self.modal:
            return
        c, g, m = self.canvas, self.geo, self.modal
        lay = self.modal_layout()
        m["lay"] = lay
        x0, y0, x1, y1 = lay["box"]
        gl = self.glass("modal", lay["box"], 18, src="scrim", lift=1.35, veil=.30)
        c.create_image(x0, y0, image=gl["img"], anchor="nw", tags="dyn")
        base = gl["avg"]
        c.create_text(x0 + lay["pad"], lay["title_y"], text=m["title"], anchor="w",
                      font=g["f_set_title"], fill="#ffffff", tags="dyn")
        if m["kind"] == "confirm":
            c.create_text(x0 + lay["pad"], lay["field"][1], text="\n".join(lay["body"]),
                          anchor="nw", font=g["f_set"], fill=hexc(mix(base, WHITE, .72)),
                          tags="dyn")
        else:
            fx0, fy0, fx1, fy1 = lay["field"]
            self.rrect(fx0, fy0, fx1, fy1, 10, fill=hexc(mix(base, (0, 0, 0), .35)),
                       outline=hexc(mix(self.accent, WHITE, .2)), width=2, tags="dyn")
            f = g["f_set"]
            tx, cy = fx0 + 14, (fy0 + fy1) / 2
            txt = m["text"]
            avail = fx1 - fx0 - 28
            if not txt:
                c.create_text(tx, cy, text=m["placeholder"], anchor="w", font=f,
                              fill=hexc(mix(base, WHITE, .35)), tags="dyn")
            # keep the caret visible for long text
            vis_start = 0
            while f.measure(txt[vis_start:m["caret"]]) > avail and vis_start < m["caret"]:
                vis_start += 1
            shown = txt[vis_start:]
            if m["all"] and txt:
                sw = min(avail, f.measure(shown))
                c.create_rectangle(tx - 2, cy - f.metrics("linespace") / 2, tx + sw + 2,
                                   cy + f.metrics("linespace") / 2,
                                   fill=hexc(mix(base, self.accent, .6)), outline="", tags="dyn")
            c.create_text(tx, cy, text=self.ell(shown, f, avail) if shown else "", anchor="w",
                          font=f, fill="#ffffff", tags="dyn")
            if int((time.perf_counter() - m["t0"]) * 1.8) % 2 == 0:
                cx = tx + f.measure(txt[vis_start:m["caret"]])
                lh = f.metrics("linespace") * .42
                c.create_line(cx, cy - lh, cx, cy + lh, fill="#ffffff", width=2, tags="dyn")
        hov = self.modal_button_hover()
        for name, label in (("cancel", "Cancel"), ("ok", m["ok"])):
            bx0, by0, bx1, by1 = lay[name]
            if name == "ok":
                colr = DANGER if m.get("danger") else self.accent
                fill = mix(colr, WHITE if hov == name else (0, 0, 0), .12 if hov == name else .2)
            else:
                fill = mix(base, WHITE, .16 if hov == name else .08)
            self.rrect(bx0, by0, bx1, by1, (by1 - by0) / 2, fill=hexc(fill), outline="",
                       tags="dyn")
            c.create_text((bx0 + bx1) / 2, (by0 + by1) / 2, text=label, font=g["f_set_val"],
                          fill="#ffffff", tags="dyn")

    def modal_button_hover(self):
        lay = self.modal.get("lay") if self.modal else None
        if not lay:
            return None
        for name in ("ok", "cancel"):
            x0, y0, x1, y1 = lay[name]
            if x0 <= self.mx <= x1 and y0 <= self.my <= y1:
                return name
        return None

    def modal_click(self, x, y):
        lay = self.modal.get("lay")
        if not lay:
            return
        hov = self.modal_button_hover()
        if hov == "ok":
            self.modal_ok()
        elif hov == "cancel":
            self.modal = None
        else:
            x0, y0, x1, y1 = lay["box"]
            if not (x0 <= x <= x1 and y0 <= y <= y1):
                self.modal = None

    def modal_key(self, k, ch, ctrl, shift):
        m = self.modal
        if k == "Escape":
            self.modal = None
            return True
        if k in ("Return", "KP_Enter"):
            self.modal_ok()
            return True
        if m["kind"] != "prompt":
            return True
        t, cpos = m["text"], m["caret"]

        def put(s):
            nonlocal t, cpos
            if m["all"]:
                t, cpos = "", 0
            t = t[:cpos] + s + t[cpos:]
            cpos += len(s)
            m["all"] = False
        if ctrl and k == "a":
            m["all"] = True
            cpos = len(t)
        elif ctrl and k == "v":
            try:
                put(self.root.clipboard_get().replace("\n", " ").strip())
            except Exception:
                pass
        elif k == "BackSpace":
            if m["all"]:
                t, cpos = "", 0
            elif ctrl:
                j = len(t[:cpos].rstrip()) - len(t[:cpos].rstrip().split(" ")[-1])
                t, cpos = t[:j] + t[cpos:], j
            elif cpos > 0:
                t, cpos = t[:cpos - 1] + t[cpos:], cpos - 1
            m["all"] = False
        elif k == "Delete":
            if m["all"]:
                t, cpos = "", 0
            else:
                t = t[:cpos] + t[cpos + 1:]
            m["all"] = False
        elif k == "Left":
            cpos, m["all"] = (0 if m["all"] else max(0, cpos - 1)), False
        elif k == "Right":
            cpos, m["all"] = min(len(t), cpos + 1), False
        elif k == "Home":
            cpos, m["all"] = 0, False
        elif k == "End":
            cpos, m["all"] = len(t), False
        elif ch and ch.isprintable() and not ctrl:
            put(ch)
        m["text"], m["caret"], m["t0"] = t, cpos, time.perf_counter()
        return True

    # ============================================================== HELP
    def toggle_help(self):
        self.help_open = not self.help_open
        self.menu = None

    def help_layout(self):
        g = self.geo
        W, H = g["w"], g["h"]
        cols_spec = HELP_COLS_WIDE if W >= 1150 else HELP_COLS_NARROW
        s = 1.0
        for _ in range(12):
            fk = self.font(max(10, int(H * .0138 * s)), "bold")
            fd = self.font(max(11, int(H * .0152 * s)))
            fg = self.font(max(10, int(H * .0128 * s)), "bold")
            ft = self.font(max(18, int(H * .03 * s)), "bold")
            kh = fk.metrics("linespace") + int(6 * s) + 4
            row_h = max(kh, fd.metrics("linespace")) + int(H * .0085 * s)
            grp_h = fg.metrics("linespace") + int(H * .014 * s)
            grp_gap = int(H * .022 * s)
            col_gap = int(W * .03 * s)
            cols = []
            for spec in cols_spec:
                keys_w, desc_w, hh = 0, 0, 0
                for gi, grp in enumerate(spec):
                    hh += grp_h + (grp_gap if gi else 0)
                    for keys, desc in SHORTCUTS[grp]:
                        kw = 0
                        for kx in keys:
                            if isinstance(kx, tuple):
                                kw += fd.measure(kx[1]) + 8
                            else:
                                kw += max(kh, fk.measure(kx) + 16) + 5
                        keys_w = max(keys_w, kw)
                        desc_w = max(desc_w, fd.measure(desc))
                        hh += row_h
                cols.append({"groups": spec, "keys_w": keys_w, "desc_w": desc_w, "h": hh})
            pad = int(H * .04 * s)
            inner_w = sum(c["keys_w"] + 18 + c["desc_w"] for c in cols) + col_gap * (len(cols) - 1)
            title_h = ft.metrics("linespace") + int(H * .03 * s)
            inner_h = max(c["h"] for c in cols)
            pw, ph = inner_w + 2 * pad, inner_h + title_h + 2 * pad + fd.metrics("linespace")
            if pw <= W - 60 and ph <= H - 60:
                break
            s *= .92
        x0, y0 = (W - pw) // 2, (H - ph) // 2
        return {"box": (x0, y0, x0 + pw, y0 + ph), "cols": cols, "pad": pad, "fk": fk, "fd": fd,
                "fg": fg, "ft": ft, "kh": kh, "row_h": row_h, "grp_h": grp_h,
                "grp_gap": grp_gap, "col_gap": col_gap, "title_h": title_h}

    def draw_help(self):
        if not self.help_open:
            return
        c, g = self.canvas, self.geo
        if self.help_lay is None:
            self.help_lay = self.help_layout()
        L = self.help_lay
        x0, y0, x1, y1 = L["box"]
        gl = self.glass("help", L["box"], 22, src="scrim", lift=1.3, veil=.32)
        c.create_image(x0, y0, image=gl["img"], anchor="nw", tags="dyn")
        base = gl["avg"]
        pad = L["pad"]
        c.create_text(x0 + pad, y0 + pad, text="Keyboard shortcuts", anchor="nw", font=L["ft"],
                      fill="#ffffff", tags="dyn")
        c.create_text(x1 - pad, y0 + pad + L["ft"].metrics("linespace") / 2,
                      text="Esc or ? to close", anchor="e", font=L["fd"],
                      fill=hexc(mix(base, WHITE, .45)), tags="dyn")
        cap_fill = hexc(mix(base, WHITE, .13))
        cap_line = hexc(mix(base, WHITE, .26))
        acc = hexc(mix(self.accent, WHITE, .35))
        dim = hexc(mix(base, WHITE, .5))
        desc_col = hexc(mix(base, WHITE, .86))
        cx = x0 + pad
        top = y0 + pad + L["title_h"]
        kh = L["kh"]
        for col in L["cols"]:
            y = top
            for gi, grp in enumerate(col["groups"]):
                if gi:
                    y += L["grp_gap"]
                c.create_text(cx, y, text=grp.upper(), anchor="nw", font=L["fg"], fill=acc,
                              tags="dyn")
                y += L["grp_h"]
                for keys, desc in SHORTCUTS[grp]:
                    cy = y + L["row_h"] / 2
                    kx = cx
                    for kk in keys:
                        if isinstance(kk, tuple):
                            c.create_text(kx + 4, cy, text=kk[1], anchor="w", font=L["fd"],
                                          fill=dim, tags="dyn")
                            kx += L["fd"].measure(kk[1]) + 8
                        else:
                            kw = max(kh, L["fk"].measure(kk) + 16)
                            self.rrect(kx, cy - kh / 2 + 1, kx + kw, cy + kh / 2 + 3, 7,
                                       fill="#000000", outline="", tags="dyn")
                            self.rrect(kx, cy - kh / 2, kx + kw, cy + kh / 2, 7,
                                       fill=cap_fill, outline=cap_line, tags="dyn")
                            c.create_text(kx + kw / 2, cy, text=kk, font=L["fk"], fill="#ffffff",
                                          tags="dyn")
                            kx += kw + 5
                    c.create_text(cx + col["keys_w"] + 18, cy, text=desc, anchor="w",
                                  font=L["fd"], fill=desc_col, tags="dyn")
                    y += L["row_h"]
            cx += col["keys_w"] + 18 + col["desc_w"] + L["col_gap"]
        c.create_text((x0 + x1) / 2, y1 - pad * .6, anchor="s", font=L["fd"], fill=dim,
                      text="In the playlist panel ↑ ↓ move the cursor; use + / − for volume there.",
                      tags="dyn")

    # ------------------------------------------------------------ settings UI
    def toggle_settings(self):
        self.settings_open = not self.settings_open
        self.menu = None
        if self.settings_open:
            self.settings_sel = 0

    def settings_layout(self):
        g = self.geo
        if not g:
            return None
        W, H = g["w"], g["h"]
        n = len(SETTINGS_ROWS)
        min_row = 26
        row_h = min(46, max(min_row, int(H * .04)))
        top_pad, title_h = 34, 50
        btns_h, btns_gap = 40, 14
        info_h = 30
        bottom_pad = 20
        ph = top_pad + title_h + row_h * n + btns_gap + btns_h + info_h + bottom_pad
        if ph > H - 40:
            ph = H - 40
            avail = ph - (top_pad + title_h + btns_gap + btns_h + info_h + bottom_pad)
            row_h = max(min_row, avail // n)
        pw = min(680, W - 80)
        px0 = (W - pw) // 2
        py0 = (H - ph) // 2
        rows = []
        for i, spec in enumerate(SETTINGS_ROWS):
            ry = py0 + top_pad + title_h + i * row_h
            rows.append({"key": spec[0], "spec": spec, "y": ry, "h": row_h,
                         "cy": ry + row_h // 2, "label_x": px0 + 32,
                         "ctrl_x0": px0 + pw - 260, "ctrl_x1": px0 + pw - 32})
        by0 = py0 + ph - bottom_pad - info_h - btns_h
        by1 = by0 + btns_h
        bw = 200
        b_reset = (px0 + 24, by0, px0 + 24 + bw, by1)
        b_clear = (b_reset[2] + 12, by0, b_reset[2] + 12 + bw, by1)
        return {"px0": px0, "py0": py0, "pw": pw, "ph": ph, "row_h": row_h, "rows": rows,
                "title_y": py0 + top_pad + 18, "reset": b_reset, "clear": b_clear,
                "info_y": py0 + ph - 18}

    def _tri(self, cx, cy, size, direction, color):
        if direction == "left":
            pts = [cx + size * .55, cy - size, cx + size * .55, cy + size, cx - size * .55, cy]
        else:
            pts = [cx - size * .55, cy - size, cx - size * .55, cy + size, cx + size * .55, cy]
        self.canvas.create_polygon(pts, fill=color, outline="", tags="dyn")

    def draw_settings(self):
        if not self.settings_open or not self.geo:
            return
        c, g = self.canvas, self.geo
        lay = self.settings_layout()
        if not lay:
            return
        self.settings_lay = lay
        px0, py0, pw, ph = lay["px0"], lay["py0"], lay["pw"], lay["ph"]
        gl = self.glass("settings", (px0, py0, px0 + pw, py0 + ph), 20, src="scrim",
                        lift=1.3, veil=.32)
        c.create_image(px0, py0, image=gl["img"], anchor="nw", tags="dyn")
        base = gl["avg"]
        c.create_text(px0 + 32, lay["title_y"], text="Settings", anchor="w",
                      font=g["f_set_title"], fill="#ffffff", tags="dyn")
        c.create_text(px0 + pw - 32, lay["title_y"], text="↑↓ choose · ←→ change · Esc close",
                      anchor="e", font=g["f_hint"], fill=hexc(mix(base, WHITE, .45)), tags="dyn")
        off_col = hexc(mix(base, WHITE, .14))
        for i, row in enumerate(lay["rows"]):
            spec = row["spec"]
            key, label, kind = spec[0], spec[1], spec[2]
            sel = (i == self.settings_sel)
            if sel:
                self.rrect(px0 + 14, row["y"] + 2, px0 + pw - 14, row["y"] + row["h"] - 2, 10,
                           fill=hexc(mix(base, WHITE, .08)), outline="", tags="dyn")
            c.create_text(row["label_x"], row["cy"], text=label, anchor="w", font=g["f_set"],
                          fill="#ffffff" if sel else hexc(mix(base, WHITE, .75)), tags="dyn")
            val = SETTINGS[key]
            cx0, cx1, cy = row["ctrl_x0"], row["ctrl_x1"], row["cy"]
            arrow = hexc(mix(base, WHITE, .5))
            if kind == "toggle":
                th = min(26, row["h"] - 8)
                tw = th * 2
                tx, ty = cx1 - tw, cy - th / 2
                on = bool(val)
                bg = hexc(mix(base, self.accent, .85)) if on else off_col
                self.rrect(tx, ty, tx + tw, ty + th, th / 2, fill=bg, outline="", tags="dyn")
                kx = tx + tw - th / 2 if on else tx + th / 2
                c.create_oval(kx - th / 2 + 3, ty + 3, kx + th / 2 - 3, ty + th - 3,
                              fill="#ffffff", outline="", tags="dyn")
            elif kind == "choice":
                self._tri(cx0 + 14, cy, 7, "left", arrow)
                self._tri(cx1 - 14, cy, 7, "right", arrow)
                c.create_text((cx0 + cx1) / 2, cy, text=str(val), font=g["f_set_val"],
                              fill="#ffffff", tags="dyn")
            elif kind == "slider":
                _, _, _, lo, hi, step, unit = spec
                self._tri(cx0 + 14, cy, 7, "left", arrow)
                self._tri(cx1 - 14, cy, 7, "right", arrow)
                c.create_text((cx0 + cx1) / 2, cy - 3, text=f"{float(val):g}{unit}",
                              font=g["f_set_val"], fill="#ffffff", tags="dyn")
                tx0, tx1 = cx0 + 40, cx1 - 40
                ly = cy + row["h"] * .32
                c.create_line(tx0, ly, tx1, ly, width=3, capstyle="round", fill=off_col,
                              tags="dyn")
                frac = (float(val) - lo) / max(1e-6, hi - lo)
                xf = tx0 + (tx1 - tx0) * max(0.0, min(1.0, frac))
                c.create_line(tx0, ly, max(tx0 + .1, xf), ly, width=3, capstyle="round",
                              fill=hexc(self.accent), tags="dyn")
        hov = self.settings_button_hover()
        for name, box, label in (("reset", lay["reset"], "Reset to defaults"),
                                 ("clear", lay["clear"], f"Clear cache ({CACHE.size()})")):
            x0, y0, x1, y1 = box
            fill = mix(base, WHITE, .16 if hov == name else .08)
            self.rrect(x0, y0, x1, y1, (y1 - y0) / 2, fill=hexc(fill), outline="", tags="dyn")
            c.create_text((x0 + x1) / 2, (y0 + y1) / 2, text=label, font=g["f_set"],
                          fill="#eeeef6", tags="dyn")
        loc = SETTINGS["storage_location"]
        c.create_text(px0 + pw / 2, lay["info_y"], text=f"{loc}: {shorten_path(CACHE.path, 60)}",
                      font=g["f_hint"], fill=hexc(mix(base, WHITE, .4)), tags="dyn")

    def settings_button_hover(self):
        if not self.settings_lay:
            return None
        for name in ("reset", "clear"):
            x0, y0, x1, y1 = self.settings_lay[name]
            if x0 <= self.mx <= x1 and y0 <= self.my <= y1:
                return name
        return None

    def settings_click(self, x, y):
        lay = self.settings_lay or self.settings_layout()
        if not lay:
            return
        if not (lay["px0"] <= x <= lay["px0"] + lay["pw"]
                and lay["py0"] <= y <= lay["py0"] + lay["ph"]):
            self.settings_open = False
            return
        hov = self.settings_button_hover()
        if hov == "reset":
            SETTINGS.reset()
            migrate_storage(SETTINGS["storage_location"])
            self.settings_apply_all()
            self.toast("Settings reset to defaults")
            return
        if hov == "clear":
            n = CACHE.size()
            CACHE.clear()
            self.toast(f"Cleared {plural(n, 'cached track')}")
            return
        for i, row in enumerate(lay["rows"]):
            if row["y"] <= y <= row["y"] + row["h"]:
                self.settings_sel = i
                spec = row["spec"]
                key, kind = spec[0], spec[2]
                if kind == "toggle":
                    self.change_setting(key, spec, +1)
                else:
                    mid = (row["ctrl_x0"] + row["ctrl_x1"]) / 2
                    self.change_setting(key, spec, -1 if x < mid else +1)
                return

    def settings_apply_all(self):
        self.geo = None
        self.built_sig = None
        self.static_dirty = True

    def change_setting(self, key, spec, direction):
        kind = spec[2]
        if kind == "toggle":
            SETTINGS[key] = not bool(SETTINGS[key])
        elif kind == "slider":
            _, _, _, lo, hi, step, _ = spec
            v = float(SETTINGS[key]) + direction * step
            SETTINGS[key] = round(max(lo, min(hi, v)), 4)
        elif kind == "choice":
            opts = spec[3]
            cur = SETTINGS[key] if SETTINGS[key] in opts else opts[0]
            i = (opts.index(cur) + direction) % len(opts)
            SETTINGS[key] = opts[i]
        self.apply_setting(key)

    def apply_setting(self, key):
        if key == "storage_location":
            migrate_storage(SETTINGS["storage_location"])
            self.toast(f"Data moved to {SETTINGS['storage_location']}")
        if key == "font_scale":
            self.geo = None
        if key in ("bg_darkness", "bg_blur"):
            self.built_sig = None
            self.immediate = True
        if key == "show_translation" and self.geo and self.lines:
            self.layout_lines()
        if key == "lyric_source":
            self.refetch_lyrics()
        self.static_dirty = True

    def settings_key(self, k):
        if k in ("Escape", "s"):
            self.settings_open = False
        elif k == "Up":
            self.settings_sel = (self.settings_sel - 1) % len(SETTINGS_ROWS)
        elif k == "Down":
            self.settings_sel = (self.settings_sel + 1) % len(SETTINGS_ROWS)
        elif k in ("Left", "Right"):
            spec = SETTINGS_ROWS[self.settings_sel]
            self.change_setting(spec[0], spec, -1 if k == "Left" else +1)
        elif k in ("space", "Return", "KP_Enter"):
            spec = SETTINGS_ROWS[self.settings_sel]
            if spec[2] == "toggle":
                self.change_setting(spec[0], spec, +1)
        elif k in ("question", "F1"):
            self.settings_open = False
            self.help_open = True
        return True

    # ---------------------------------------------------------- interaction
    def overlay_open(self):
        return bool(self.modal or self.help_open or self.settings_open)

    def pl_live(self):
        return self.pl_open and self.pl_anim > .97

    def hit_at(self, x, y):
        g = self.geo
        if not g or x < 0:
            return None
        if self.ui_alpha > .25 or self.dragging or self.vol_dragging:
            for name, cx, cy, r in g["buttons"]:
                if (x - cx) ** 2 + (y - cy) ** 2 <= r * r:
                    return ("btn", name)
            x0, x1, by = g["bar"]
            if x0 - 8 <= x <= x1 + 8 and abs(y - by) <= g["bar_hit"]:
                return ("bar", None)
            if SETTINGS["show_controls"] or True:
                for name, cx, cy, r in g["util"]:
                    if abs(x - cx) <= r and abs(y - cy) <= r:
                        return ("util", name)
                if g["vol"] and self.vol and self.vol.get("type") != "upDown":
                    vx0, vx1, vy = g["vol"]
                    if vx0 - 8 <= x <= vx1 + 8 and abs(y - vy) <= g["util_r"]:
                        return ("vol", None)
        if self.pl_live():
            h = self.pl_hit(x, y)
            if h:
                return h
        elif self.pl_open:
            return None
        if not self.auto_follow and self.lines:
            x0, y0, x1, y1 = g["pill"]
            if x0 <= x <= x1 and y0 <= y <= y1:
                return ("pill", None)
        if self.lines and x >= g["lx"] - 40:
            gap = g["lgap"]
            for i in range(len(self.lines)):
                top = g["ay"] + self.line_y[i] - self.scroll
                if top - gap / 2 <= y < top + self.line_h[i] + gap / 2:
                    return ("line", i)
        return None

    def pl_hit(self, x, y):
        P = self.geo["pl"]
        if not (P["x0"] <= x <= P["x1"] and P["y0"] <= y <= P["y1"]):
            return None
        for name, cx, cy, r in P["hbtns"]:
            if (x - cx) ** 2 + (y - cy) ** 2 <= (r + 2) ** 2:
                return ("plbtn", name)
        for pid, (bx0, by0, bx1, by1) in self.pl_tab_boxes:
            if bx0 <= x <= bx1 and by0 <= y <= by1:
                return ("pltab", pid)
        for d, (bx0, by0, bx1, by1) in self.pl_tab_arrows:
            if bx0 <= x <= bx1 and by0 <= y <= by1:
                return ("plarrow", d)
        sx0, sy0, sx1, sy1 = P["search"]
        if sx0 <= x <= sx1 and sy0 <= y <= sy1:
            return ("plsearch", "clear" if self.pl_filter and x >= sx1 - (sy1 - sy0) else None)
        if P["list_y0"] <= y <= P["list_y1"]:
            if self.pl_max_scroll() > 0 and x >= P["x1"] - P["pad"] * .55:
                return ("plsb", None)
            k = int((y - P["list_y0"] + self.pl_scroll) // P["row_h"])
            if 0 <= k < len(self.pl_rows):
                return ("plrow", self.pl_rows[k])
            return ("pllist", None)
        return ("plpanel", None)

    def update_hover(self):
        if self.overlay_open() or self.menu:
            self.hover_hit, self.hover_line = None, -1
            return
        hit = self.hit_at(self.mx, self.my)
        self.hover_hit = hit
        self.hover_line = hit[1] if hit and hit[0] == "line" else -1

    def on_motion(self, e):
        self.mx, self.my = e.x, e.y
        self.last_move = time.perf_counter()

    def on_leave(self):
        self.mx = self.my = -1

    def bar_frac(self, x):
        x0, x1, _ = self.geo["bar"]
        return max(0.0, min(1.0, (x - x0) / max(1, x1 - x0)))

    def vol_bar_frac(self, x):
        x0, x1, _ = self.geo["vol"]
        return max(0.0, min(1.0, (x - x0) / max(1, x1 - x0)))

    def on_press(self, e):
        self.mx, self.my = e.x, e.y
        self.last_move = time.perf_counter()
        ctrl = bool(e.state & CTRL_MASK) or (IS_MAC and bool(e.state & 0x8))
        shift = bool(e.state & SHIFT_MASK)
        if self.modal:
            self.modal_click(e.x, e.y)
            return
        if self.menu:
            self.menu_click(e.x, e.y)
            return
        if self.help_open:
            self.help_open = False
            return
        if self.settings_open:
            self.settings_click(e.x, e.y)
            return
        self.update_hover()
        hit = self.hover_hit
        if self.pl_filter_active and not (hit and hit[0] == "plsearch"):
            self.pl_filter_active = False
        if not hit:
            return
        kind, val = hit
        if kind == "bar":
            self.dragging, self.drag_frac = True, self.bar_frac(e.x)
        elif kind == "vol":
            self.vol_dragging = True
            self.set_volume_frac(self.vol_bar_frac(e.x))
        elif kind == "pill":
            self.follow_now()
        elif kind == "line":
            self.seek_to(self.times[val])
            self.auto_follow = True
        elif kind == "btn":
            if val == "play":
                self.playpause()
            elif val == "prev":
                self.prev_track()
            elif val == "next":
                self.next_track()
            elif val == "back":
                self.skip(-float(SETTINGS["seek_step"]))
            elif val == "fwd":
                self.skip(float(SETTINGS["seek_step"]))
        elif kind == "util":
            {"shuffle": self.toggle_shuffle, "repeat": self.cycle_repeat,
             "mute": self.toggle_mute, "help": self.toggle_help,
             "list": self.toggle_playlist}[val]()
        elif kind == "plbtn":
            _, cx, cy, r = next(b for b in self.geo["pl"]["hbtns"] if b[0] == val)
            if val == "add":
                self.pl_new()
            elif val == "sort":
                self.menu_sort(cx - r, cy + r + 6)
            else:
                self.menu_playlist(cx - r, cy + r + 6)
        elif kind == "pltab":
            self.pl_set_view(val, reveal=val == self.play_pl_id)
        elif kind == "plarrow":
            self.pl_tab_first = max(0, min(len(self.playlists) - 1, self.pl_tab_first + val))
        elif kind == "plsearch":
            if val == "clear":
                self.pl_filter = ""
                self.pl_refilter()
            self.pl_filter_active = True
        elif kind == "plsb":
            self.pl_sb_drag = True
            self.pl_scroll_to_y(e.y)
        elif kind == "plrow":
            pending = None
            if not ctrl and not shift and val in self.pl_sel and len(self.pl_sel) > 1:
                pending = val                   # may be a drag of the whole selection
                self.pl_cursor = val
            else:
                self.pl_click_row(val, ctrl, shift)
            self.pl_drag = {"y0": e.y, "active": False, "gap": None, "pending": pending}

    def pl_scroll_to_y(self, y):
        P = self.geo["pl"]
        lh = self.pl_list_h()
        f = (y - P["list_y0"]) / max(1, lh)
        self.pl_target = self.pl_scroll = max(0.0, min(1.0, f)) * self.pl_max_scroll()

    def pl_gap_at(self, y):
        P = self.geo["pl"]
        g = round((y - P["list_y0"] + self.pl_scroll) / P["row_h"])
        return max(0, min(len(self.pl_items), g))

    def on_double(self, e):
        if self.overlay_open() or self.menu:
            self.on_press(e)
            return
        self.mx, self.my = e.x, e.y
        self.update_hover()
        hit = self.hover_hit
        ctrl = bool(e.state & CTRL_MASK)
        shift = bool(e.state & SHIFT_MASK)
        if hit and hit[0] == "plrow" and not ctrl and not shift:
            self.pl_sel, self.pl_anchor = {hit[1]}, hit[1]
            self.pl_play(hit[1])
            self.pl_drag = None
            return
        self.on_press(e)

    def on_drag(self, e):
        self.mx, self.my = e.x, e.y
        self.last_move = time.perf_counter()
        if self.dragging:
            self.drag_frac = self.bar_frac(e.x)
        elif self.vol_dragging and self.geo and self.geo["vol"]:
            self.set_volume_frac(self.vol_bar_frac(e.x))
        elif self.pl_sb_drag:
            self.pl_scroll_to_y(e.y)
        elif self.pl_drag:
            d = self.pl_drag
            if not d["active"] and abs(e.y - d["y0"]) > 6:
                if self.pl_filter:
                    self.pl_drag = None
                    self.toast("Clear the filter to reorder tracks")
                    return
                d["active"] = True
            if d["active"]:
                d["gap"] = self.pl_gap_at(e.y)

    def on_release(self, e):
        if self.dragging:
            self.dragging = False
            if self.duration > 0:
                self.seek_to(self.drag_frac * self.duration)
        if self.vol_dragging:
            self.vol_dragging = False
            self.flush_volume(time.perf_counter(), force=True)
        self.pl_sb_drag = False
        if self.pl_drag:
            d, self.pl_drag = self.pl_drag, None
            if d["active"] and d["gap"] is not None:
                self.pl_move_to(self.pl_selected(), d["gap"])
            elif d["pending"] is not None:
                self.pl_sel, self.pl_anchor = {d["pending"]}, d["pending"]

    def on_right(self, e):
        self.mx, self.my = e.x, e.y
        if self.modal or self.help_open or self.settings_open:
            return
        if self.menu:
            self.menu = None
            return
        self.update_hover()
        hit = self.hover_hit
        kind = hit[0] if hit else None
        if kind == "plrow":
            if hit[1] not in self.pl_sel:
                self.pl_click_row(hit[1], False, False)
            self.pl_cursor = hit[1]
            self.menu_rows(e.x, e.y)
        elif kind == "pltab":
            self.menu_playlist(e.x, e.y, hit[1])
        elif kind in ("plpanel", "pllist", "plsearch", "plbtn", "plarrow"):
            self.menu_playlist(e.x, e.y)
        elif kind == "util" and hit[1] in ("shuffle", "repeat"):
            self.order_menu(e.x, e.y - 10)
        else:
            self.menu_general(e.x, e.y)

    def on_wheel(self, delta, e=None):
        if e is not None:
            self.mx, self.my = e.x, e.y
        self.last_move = time.perf_counter()
        if self.overlay_open() or self.menu or not self.geo or not delta:
            return
        g = self.geo
        up = delta > 0
        notches = max(1.0, abs(delta) / 120)
        if g["vol"] and self.ui_alpha > .25:
            vx0, vx1, vy = g["vol"]
            ux = g["util_pos"]["mute"][0]
            if ux - g["util_r"] * 1.4 <= self.mx <= vx1 + 10 and abs(self.my - vy) <= g["util_r"] * 1.4:
                self.volume_step(1 if up else -1)
                return
        if self.pl_live():
            P = g["pl"]
            if P["x0"] <= self.mx <= P["x1"] and P["y0"] <= self.my <= P["y1"]:
                if P["tabs_y0"] <= self.my <= P["tabs_y0"] + P["tabs_h"]:
                    self.pl_tab_first = max(0, min(len(self.playlists) - 1,
                                                   self.pl_tab_first + (-1 if up else 1)))
                else:
                    self.pl_target += (-1 if up else 1) * P["row_h"] * 3 * notches
                    self.pl_clamp_scroll()
                return
        if self.pl_open or not self.lines:
            return
        step_dir = -1 if up else 1
        self.auto_follow = False
        step = g["lh"] * 2
        lo, hi = self.center_of(0), self.center_of(len(self.lines) - 1)
        self.target_scroll = max(lo, min(hi, self.target_scroll + step_dir * step))

    def follow_now(self):
        self.auto_follow = True

    # ------------------------------------------------------------ keyboard
    def on_keypress(self, e):
        ks = e.keysym
        if ks in MODIFIER_KEYS:
            return None
        st = e.state
        ctrl = bool(st & CTRL_MASK) or (IS_MAC and bool(st & 0x8))
        shift = bool(st & SHIFT_MASK)
        alt = bool(st & ALT_MASK) and not (IS_MAC and ctrl)
        k = ks.lower() if len(ks) == 1 else ks
        if k == "ISO_Left_Tab":
            k, shift = "Tab", True
        self.last_move = time.perf_counter()
        try:
            handled = self.handle_key(k, e.char, ctrl, shift, alt)
        except Exception:
            import traceback
            traceback.print_exc()
            handled = True
        return "break" if handled else None

    def handle_key(self, k, ch, ctrl, shift, alt):
        if self.modal:
            return self.modal_key(k, ch, ctrl, shift)
        if self.menu:
            return self.menu_key(k)
        if ctrl and k == "q":
            self.close()
            return True
        if self.help_open:
            if k in ("Escape", "question", "h", "F1", "Return", "space"):
                self.help_open = False
            return True
        if self.settings_open:
            return self.settings_key(k)
        if self.pl_open and self.pl_filter_active and self.filter_key(k, ch, ctrl):
            return True
        if self.pl_open and self.pl_key(k, ch, ctrl, shift, alt):
            return True
        return self.global_key(k, ch, ctrl, shift, alt)

    def filter_key(self, k, ch, ctrl):
        if k == "Escape":
            if self.pl_filter:
                self.pl_filter = ""
                self.pl_refilter()
            else:
                self.pl_filter_active = False
            return True
        if k in ("Return", "KP_Enter"):
            self.pl_filter_active = False
            if self.pl_rows:
                real = self.pl_cursor if self.pl_vpos(self.pl_cursor) is not None else self.pl_rows[0]
                self.pl_sel, self.pl_anchor = {real}, real
                self.pl_play(real)
            return True
        if k in ("Up", "Down", "Prior", "Next", "Tab", "F5"):
            return False
        if k == "BackSpace":
            if ctrl:
                self.pl_filter = " ".join(self.pl_filter.rstrip().split(" ")[:-1])
            else:
                self.pl_filter = self.pl_filter[:-1]
        elif ctrl and k == "v":
            try:
                self.pl_filter += self.root.clipboard_get().replace("\n", " ")
            except Exception:
                pass
        elif ch and ch.isprintable() and not ctrl:
            self.pl_filter += ch
        else:
            return True
        self.pl_refilter()
        self.pl_target = 0.0
        if self.pl_rows and self.pl_vpos(self.pl_cursor) is None:
            self.pl_cursor = self.pl_rows[0]
            self.pl_sel, self.pl_anchor = {self.pl_cursor}, self.pl_cursor
        return True

    def pl_key(self, k, ch, ctrl, shift, alt):
        page = max(1, int(self.pl_list_h() // self.geo["pl"]["row_h"]) - 1) if self.geo else 10
        if k in ("Up", "Down"):
            d = -1 if k == "Up" else 1
            if alt or (ctrl and not shift):
                self.pl_move_step(d)
            else:
                self.pl_nav(d, shift)
            return True
        if k in ("Prior", "Next"):
            self.pl_nav(-page if k == "Prior" else page, shift)
            return True
        if k in ("Home", "End") and not ctrl:
            self.pl_nav(0, shift, absolute=0 if k == "Home" else len(self.pl_rows) - 1)
            return True
        if k in ("Return", "KP_Enter"):
            if 0 <= self.pl_cursor < len(self.pl_items):
                self.pl_play(self.pl_cursor)
            return True
        if k == "Delete" or (IS_MAC and k == "BackSpace"):
            self.pl_remove_selected()
            return True
        if ctrl and k == "a":
            self.pl_select_all()
            return True
        if ctrl and k == "n":
            self.pl_new()
            return True
        if ctrl and k == "w":
            self.pl_delete()
            return True
        if ctrl and k == "o":
            self.pl_add_files()
            return True
        if ctrl and k == "u":
            self.pl_add_url()
            return True
        if ctrl and k == "f" or (k == "slash" and not ctrl):
            self.pl_filter_active = True
            return True
        if k == "F2":
            self.pl_rename()
            return True
        if k == "F5":
            self.pl_request_items()
            self.toast("Refreshing playlist…")
            return True
        if k == "Tab":
            self.pl_cycle_view(-1 if shift else 1)
            return True
        if k == "q" and not ctrl:
            self.pl_toggle_queue()
            return True
        if k == "j" and not ctrl:
            self.pl_reveal_playing()
            return True
        if k == "Escape":
            if self.pl_filter:
                self.pl_filter = ""
                self.pl_refilter()
            else:
                self.toggle_playlist(False)
            return True
        if k == "App" or (shift and k == "F10"):
            P = self.geo["pl"]
            vp = self.pl_vpos(self.pl_cursor)
            y = P["list_y0"] + (vp or 0) * P["row_h"] - self.pl_scroll + P["row_h"]
            self.menu_rows(P["x0"] + P["pad"] * 3, y)
            return True
        return False

    def global_key(self, k, ch, ctrl, shift, alt):
        seek = float(SETTINGS["seek_step"])
        if k == "space":
            self.playpause()
        elif k in ("Left", "Right"):
            d = -1 if k == "Left" else 1
            if ctrl:
                self.prev_track() if d < 0 else self.next_track()
            else:
                self.skip(d * seek * (3 if shift else 1))
        elif k in ("Up", "plus", "equal", "KP_Add"):
            self.volume_step(1)
        elif k in ("Down", "minus", "underscore", "KP_Subtract"):
            self.volume_step(-1)
        elif k == "m" and not ctrl:
            self.toggle_mute()
        elif k == "n" and not ctrl:
            self.next_track()
        elif k == "b" and not ctrl:
            self.prev_track()
        elif k == "x" and not ctrl:
            self.toggle_stop_after() if shift else self.stop()
        elif ctrl and k == "s":
            self.toggle_shuffle()
        elif ctrl and k == "r":
            self.cycle_repeat()
        elif k == "o" and not ctrl:
            self.order_menu()
        elif len(k) == 1 and k.isdigit() and not ctrl:
            if self.duration > 0:
                self.seek_to(self.duration * int(k) / 10)
        elif k in ("p", "l") and not ctrl:
            self.toggle_playlist()
        elif k == "s" and not ctrl:
            self.toggle_settings()
        elif k == "r" and not ctrl:
            self.refetch_lyrics()
        elif k == "v" and not ctrl:
            self.toggle_translation()
        elif k == "f" and not ctrl:
            self.follow_now()
        elif k == "bracketright":
            self.adjust_offset(0.1 if not shift else 0.5)
        elif k == "bracketleft":
            self.adjust_offset(-0.1 if not shift else -0.5)
        elif k in ("braceright", "braceleft"):
            self.adjust_offset(0.5 if k == "braceright" else -0.5)
        elif k == "backslash":
            self.adjust_offset(None)
        elif k in ("question", "F1") or (k == "h" and not ctrl):
            self.toggle_help()
        elif k == "F11":
            self.toggle_fullscreen()
        elif k == "Escape":
            if self.pl_open:
                self.toggle_playlist(False)
            elif self.fullscreen:
                self.exit_fullscreen()
        elif k in ("App",) or (shift and k == "F10"):
            self.menu_general(self.geo["w"] // 2, self.geo["h"] // 2)
        else:
            return False
        return True

    # -------------------------------------------------------------- drawing
    def rrect(self, x0, y0, x1, y1, r, **kw):
        r = max(0, min(r, (x1 - x0) / 2, (y1 - y0) / 2))
        pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1,
               x1 - r, y1, x0 + r, y1, x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]
        return self.canvas.create_polygon(pts, smooth=True, **kw)

    def draw_static(self):
        self.static_dirty = False
        c, g, tint = self.canvas, self.geo, self.tint
        c.delete("static")
        a, t, al = self.track
        if self.track_key is None:
            if self.connected:
                t, a, al = "Nothing playing", "Press play in foobar2000", ""
            else:
                t, a, al = "Waiting for foobar2000…", "Is Beefweb running on port 8880?", ""
        rows = wrap(t or "Unknown title", g["f_title"], g["cs"])
        if len(rows) > 2:
            rows = [rows[0], ellipsize(" ".join(rows[1:]), g["f_title"], g["cs"])]
        y = g["info_y"]
        c.create_text(g["px"], y, text="\n".join(rows), anchor="nw", font=g["f_title"],
                      fill="#ffffff", justify="left", tags="static")
        y += len(rows) * g["title_lh"] + int(g["h"] * .004)
        if a:
            c.create_text(g["px"], y, text=ellipsize(a, g["f_artist"], g["cs"]), anchor="nw",
                          font=g["f_artist"], fill=hexc(mix(tint, WHITE, .78)), tags="static")
        y += g["artist_lh"]
        if al:
            c.create_text(g["px"], y, text=ellipsize(al, g["f_album"], g["cs"]), anchor="nw",
                          font=g["f_album"], fill=hexc(mix(tint, WHITE, .45)), tags="static")

    def update_lyrics(self, pos, dt):
        lead = float(SETTINGS["lyric_lead"]) + self.lyr_offset
        idx = bisect.bisect_right(self.times, pos + lead) - 1 if self.times else -1
        self.current = idx
        k = 1 - math.exp(-dt * 10)
        for i, f in enumerate(self.focus):
            tgt = 1.0 if i == idx else 0.0
            if abs(tgt - f) > .002:
                self.focus[i] = f + (tgt - f) * k
        if self.auto_follow and self.lines:
            self.target_scroll = self.center_of(max(0, idx))
        self.scroll += (self.target_scroll - self.scroll) * (1 - math.exp(-dt * 7))
        if abs(self.target_scroll - self.scroll) < .3:
            self.scroll = self.target_scroll
        self.lyr_alpha += (1 - self.lyr_alpha) * (1 - math.exp(-dt * 5))

    def draw_lyrics(self):
        c, g, tint = self.canvas, self.geo, self.tint
        vis = 1 - ease_out(self.pl_anim)
        if vis < .02:
            return
        lx, ay, h = g["lx"] - int((1 - vis) * g["w"] * .03), g["ay"], g["h"]
        if not self.lines:
            if self.track_key is None:
                msg = ""
            else:
                msg = {"loading": "Searching for lyrics…",
                       "none": "No synced lyrics found for this track"}.get(self.lyric_state, "")
            if msg:
                c.create_text(lx, ay, text=msg, anchor="w", font=g["f_msg"],
                              fill=hexc(mix(tint, WHITE, .5 * vis)), tags="dyn")
                if self.lyric_state == "none":
                    c.create_text(lx, ay + g["f_msg"].metrics("linespace") * 1.3,
                                  text="Press R to try again · P for playlists · ? for shortcuts",
                                  anchor="w", font=g["f_hint"],
                                  fill=hexc(mix(tint, WHITE, .3 * vis)), tags="dyn")
            return
        base = mix(tint, WHITE, .44)
        for i in range(len(self.lines)):
            top = ay + self.line_y[i] - self.scroll
            bot = top + self.line_h[i]
            if bot < -40 or top > h + 40:
                continue
            dist = abs((top + bot) / 2 - ay)
            fade = max(.05, 1 - (dist / (h * .6)) ** 2) * self.lyr_alpha * vis
            f = self.focus[i]
            if i == self.hover_line and i != self.current:
                f = max(f, .35)
            col = mix(tint, mix(base, WHITE, f), .12 + .88 * fade)
            c.create_text(lx, top, text=self.line_rows[i], anchor="nw", font=g["f_lyric"],
                          fill=hexc(col), justify="left", tags="dyn")
            if self.line_trows[i]:
                tcol = mix(tint, mix(tint, WHITE, .30 + .45 * f), .12 + .88 * fade)
                c.create_text(lx, top + self.line_oh[i] + g["tgap"], text=self.line_trows[i],
                              anchor="nw", font=g["f_trans"], fill=hexc(tcol),
                              justify="left", tags="dyn")

    # ---- icons
    def icon_shuffle(self, cx, cy, u, col, w):
        a = (u * .55, u * .62, u * .30)
        self.canvas.create_line(cx - u, cy + u * .55, cx - u * .35, cy + u * .55,
                                cx + u * .35, cy - u * .55, cx + u, cy - u * .55,
                                fill=col, width=w, arrow="last", arrowshape=a,
                                joinstyle="round", capstyle="round", tags="dyn")
        self.canvas.create_line(cx - u, cy - u * .55, cx - u * .35, cy - u * .55,
                                cx + u * .35, cy + u * .55, cx + u, cy + u * .55,
                                fill=col, width=w, arrow="last", arrowshape=a,
                                joinstyle="round", capstyle="round", tags="dyn")

    def icon_repeat(self, cx, cy, u, col, w, one=False):
        a = (u * .5, u * .58, u * .28)
        self.canvas.create_line(cx - u, cy + u * .2, cx - u, cy - u * .5, cx + u * .7, cy - u * .5,
                                fill=col, width=w, arrow="last", arrowshape=a,
                                joinstyle="round", capstyle="round", tags="dyn")
        self.canvas.create_line(cx + u, cy - u * .2, cx + u, cy + u * .5, cx - u * .7, cy + u * .5,
                                fill=col, width=w, arrow="last", arrowshape=a,
                                joinstyle="round", capstyle="round", tags="dyn")
        if one:
            r = u * .5
            bx, by = cx + u * .95, cy - u * .85
            self.canvas.create_oval(bx - r, by - r, bx + r, by + r, fill=col, outline="",
                                    tags="dyn")
            self.canvas.create_text(bx, by, text="1", font=self.geo["f_badge"],
                                    fill=hexc((12, 12, 18)), tags="dyn")

    def icon_speaker(self, cx, cy, u, col, w, level, muted):
        c = self.canvas
        x = cx - u * .35
        c.create_polygon(x - u * .75, cy - u * .32, x - u * .3, cy - u * .32, x + u * .2, cy - u * .8,
                         x + u * .2, cy + u * .8, x - u * .3, cy + u * .32, x - u * .75, cy + u * .32,
                         fill=col, outline="", tags="dyn")
        if muted:
            m = u * .32
            ox = x + u * .85
            c.create_line(ox - m, cy - m, ox + m, cy + m, fill=col, width=w, capstyle="round",
                          tags="dyn")
            c.create_line(ox - m, cy + m, ox + m, cy - m, fill=col, width=w, capstyle="round",
                          tags="dyn")
            return
        for i, rr in enumerate((.55, .95)):
            if level > (.02 if i == 0 else .5):
                r = u * rr
                c.create_arc(x + u * .2 - r, cy - r, x + u * .2 + r, cy + r, start=-50, extent=100,
                             style="arc", outline=col, width=w, tags="dyn")

    def icon_list(self, cx, cy, u, col, w):
        c = self.canvas
        for i, dy in enumerate((-.55, 0, .55)):
            c.create_oval(cx - u - 1.6, cy + dy * u - 1.6, cx - u + 1.6, cy + dy * u + 1.6,
                          fill=col, outline="", tags="dyn")
            c.create_line(cx - u * .45, cy + dy * u, cx + u, cy + dy * u, fill=col, width=w,
                          capstyle="round", tags="dyn")

    def icon_help(self, cx, cy, u, col, w):
        self.canvas.create_oval(cx - u, cy - u, cx + u, cy + u, outline=col, width=w, tags="dyn")
        self.canvas.create_text(cx, cy, text="?", font=self.geo["f_badge"], fill=col, tags="dyn")

    def draw_controls(self, pos):
        c, g, tint, ua = self.canvas, self.geo, self.tint, self.ui_alpha
        h = g["h"]
        if not SETTINGS["show_controls"]:
            ua = 0.0
        x0, x1, by = g["bar"]
        dur = self.duration
        frac = self.drag_frac if self.dragging else (pos / dur if dur > 0 else 0)
        frac = max(0.0, min(1.0, frac))
        active = self.dragging or (self.hover_hit and self.hover_hit[0] == "bar")
        th = max(6, int(h * .0085)) if active else max(4, int(h * .0055))
        ba = .5 + .5 * ua
        c.create_line(x0, by, x1, by, width=th, capstyle="round",
                      fill=hexc(mix(tint, WHITE, .05 + .20 * ba)), tags="dyn")
        xf = x0 + (x1 - x0) * frac
        if frac > 0:
            c.create_line(x0, by, max(x0 + .1, xf), by, width=th, capstyle="round",
                          fill=hexc(mix(tint, WHITE, .55 + .45 * ba)), tags="dyn")
        if active:
            r = th * .95
            c.create_oval(xf - r, by - r, xf + r, by + r, fill="#ffffff", outline="", tags="dyn")
            if not self.dragging and dur > 0 and self.mx >= 0:
                hx = max(x0, min(x1, self.mx))
                c.create_text(hx, by - th - 6, text=fmt(self.bar_frac(hx) * dur), anchor="s",
                              font=g["f_time"], fill="#ffffff", tags="dyn")
        shown = frac * dur if self.dragging else pos
        ty = by + int(h * .016)
        tcol = hexc(mix(tint, WHITE, .42 + .25 * ba))
        c.create_text(x0, ty, text=fmt(shown), anchor="nw", font=g["f_time"], fill=tcol, tags="dyn")
        c.create_text(x1, ty, text="-" + fmt(max(0, dur - shown)) if dur else "-:--", anchor="ne",
                      font=g["f_time"], fill=tcol, tags="dyn")
        mid = []
        if self.stop_after:
            mid.append("stops after this track")
        if abs(self.lyr_offset) > 1e-6:
            mid.append(f"lyrics {self.lyr_offset:+.1f}s")
        if mid:
            c.create_text((x0 + x1) / 2, ty, text=" · ".join(mid), anchor="n", font=g["f_time"],
                          fill=hexc(mix(self.accent, WHITE, .45)), tags="dyn")

        if ua > .03:
            r, cy = g["ctl_r"], g["ctl_cy"]
            hov = self.hover_hit[1] if self.hover_hit and self.hover_hit[0] == "btn" else None
            dark = (14, 14, 20)
            for name, cx, _, _ in g["buttons"]:
                col = hexc(mix(tint, WHITE, ua if hov == name else .72 * ua))
                u = r * .42
                if name == "play":
                    pr = r * (1.06 if hov == "play" else 1.0)
                    fillc = mix(tint, WHITE, ua)
                    c.create_oval(cx - pr, cy - pr, cx + pr, cy + pr, fill=hexc(fillc),
                                  outline="", tags="dyn")
                    gc = hexc(mix(fillc, dark, ua))
                    u = r * .45
                    if self.playing:
                        for sx in (-.95, .35):
                            c.create_rectangle(cx + u * sx, cy - u, cx + u * (sx + .6), cy + u,
                                               fill=gc, outline="", tags="dyn")
                    else:
                        c.create_polygon(cx - u * .7, cy - u, cx - u * .7, cy + u, cx + u * 1.05, cy,
                                         fill=gc, outline="", tags="dyn")
                elif name in ("prev", "next"):
                    s = -1 if name == "prev" else 1
                    c.create_rectangle(cx + s * u * 1.0 - u * .16, cy - u * .9,
                                       cx + s * u * 1.0 + u * .16, cy + u * .9,
                                       fill=col, outline="", tags="dyn")
                    c.create_polygon(cx - s * u * 1.0, cy - u * .9, cx - s * u * 1.0, cy + u * .9,
                                     cx + s * u * .55, cy, fill=col, outline="", tags="dyn")
                else:
                    s = -1 if name == "back" else 1
                    a0, a1 = (-1.05, -.1) if s == -1 else (1.05, .1)
                    b0, b1 = (-.1, .85) if s == -1 else (.1, -.85)
                    c.create_polygon(cx + a1 * u, cy - u * .75, cx + a1 * u, cy + u * .75,
                                     cx + a0 * u, cy, fill=col, outline="", tags="dyn")
                    c.create_polygon(cx + b1 * u, cy - u * .75, cx + b1 * u, cy + u * .75,
                                     cx + b0 * u, cy, fill=col, outline="", tags="dyn")
                    c.create_text(cx, cy + u * 1.9, text=f"{float(SETTINGS['seek_step']):g}",
                                  font=g["f_time"], fill=col, tags="dyn")
            self.draw_util_row(ua)

        if not self.auto_follow and self.lines and not self.pl_open:
            x0p, y0p, x1p, y1p = g["pill"]
            hp = self.hover_hit and self.hover_hit[0] == "pill"
            self.rrect(x0p, y0p, x1p, y1p, (y1p - y0p) / 2, tags="dyn", outline="",
                       fill=hexc(mix(tint, self.accent, .75 if hp else .55)))
            c.create_text((x0p + x1p) / 2, (y0p + y1p) / 2, text=g["pill_txt"], font=g["f_pill"],
                          fill="#ffffff", tags="dyn")
        if ua > .05 and SETTINGS["show_hint"] and not self.pl_open:
            bits = []
            if self.lyric_source:
                bits.append(f"Lyrics: {self.lyric_source}")
            bits += ["Scroll to browse", "Click a line to jump", "P playlists", "S settings",
                     "? shortcuts"]
            c.create_text(g["lx"], g["h"] - int(g["h"] * .04), text="   ·   ".join(bits),
                          anchor="sw", font=g["f_hint"],
                          fill=hexc(mix(tint, WHITE, .33 * ua)), tags="dyn")
        # "playing from" label above the cover
        pl = self.pl_by_id(self.play_pl_id)
        if pl and ua > .05 and g["cy"] > g["h"] * .045:
            c.create_text(g["px"], g["cy"] - int(g["h"] * .014),
                          text="PLAYING FROM  " + self.ell(str(pl.get("title", "")).upper(),
                                                           g["f_label"], g["cs"] * .7),
                          anchor="sw", font=g["f_label"],
                          fill=hexc(mix(tint, WHITE, .42 * ua)), tags="dyn")

    def draw_util_row(self, ua):
        c, g, tint = self.canvas, self.geo, self.tint
        u = g["util_r"] * .72
        w = max(2, int(g["util_r"] * .15))
        hov = self.hover_hit[1] if self.hover_hit and self.hover_hit[0] == "util" else None
        acc = mix(self.accent, WHITE, .3)

        def colr(name, on=False):
            if on:
                return hexc(mix(tint, acc, ua))
            return hexc(mix(tint, WHITE, (.95 if hov == name else .6) * ua))

        def dot(cx, cy, on):
            if on:
                c.create_oval(cx - 2, cy + u * 1.45 - 2, cx + 2, cy + u * 1.45 + 2,
                              fill=hexc(mix(tint, acc, ua)), outline="", tags="dyn")
        for name, cx, cy, r in g["util"]:
            if hov == name:
                rr = r * .95
                c.create_oval(cx - rr, cy - rr, cx + rr, cy + rr,
                              fill=hexc(mix(tint, WHITE, .10 * ua)), outline="", tags="dyn")
            if name == "shuffle":
                on = self.shuffle_on()
                self.icon_shuffle(cx, cy, u, colr(name, on), w)
                dot(cx, cy, on)
            elif name == "repeat":
                st = self.repeat_state()
                on = st != "off"
                self.icon_repeat(cx, cy, u, colr(name, on), w, one=st == "one")
                dot(cx, cy, on)
            elif name == "mute":
                v = self.vol
                self.icon_speaker(cx, cy, u, colr(name), w, vol_frac(v) if v else 0,
                                  bool(v and v.get("isMuted")))
            elif name == "help":
                self.icon_help(cx, cy, u * .95, colr(name), max(1, w - 1))
            elif name == "list":
                self.icon_list(cx, cy, u, colr(name, self.pl_open), w)
                dot(cx, cy, self.pl_open)
        if g["vol"] and self.vol and self.vol.get("type") != "upDown":
            vx0, vx1, vy = g["vol"]
            f = 0.0 if self.vol.get("isMuted") else vol_frac(self.vol)
            active = self.vol_dragging or (self.hover_hit and self.hover_hit[0] == "vol")
            th = max(4, int(g["h"] * .006)) if active else max(3, int(g["h"] * .0042))
            c.create_line(vx0, vy, vx1, vy, width=th, capstyle="round",
                          fill=hexc(mix(tint, WHITE, .18 * ua)), tags="dyn")
            xf = vx0 + (vx1 - vx0) * f
            if f > 0:
                c.create_line(vx0, vy, max(vx0 + .1, xf), vy, width=th, capstyle="round",
                              fill=hexc(mix(tint, WHITE, .78 * ua)), tags="dyn")
            if active:
                r = th * 1.2
                c.create_oval(xf - r, vy - r, xf + r, vy + r, fill="#ffffff", outline="", tags="dyn")
                c.create_text(xf, vy - r - 5, text=vol_label(self.vol).replace("Volume ", ""),
                              anchor="s", font=g["f_time"], fill="#ffffff", tags="dyn")

    # ---- up next
    def compute_next_sig(self):
        if self.queue_items:
            q0 = self.queue_items[0]
            cols = tuple(str(x) for x in (q0.get("columns") or []))
            return ("q", q0.get("playlistId"), q0.get("itemIndex"), cols)
        if (self.play_pl_id is None or self.play_idx is None or self.play_idx < 0
                or not self.orders or self.shuffle_on()):
            return None
        rep = self.repeat_state()
        if rep == "one":
            return None
        pl = self.pl_by_id(self.play_pl_id)
        if not pl:
            return None
        cnt = int(pl.get("itemCount") or 0)
        ni = self.play_idx + 1
        if ni >= cnt:
            if rep != "all" or cnt == 0:
                return None
            ni = 0
        return ("pl", self.play_pl_id, ni, cnt)

    def update_up_next(self):
        sig = self.compute_next_sig()
        if sig == self.next_sig:
            return
        self.next_sig = sig
        self.up_next = None
        if sig is None:
            return
        if sig[0] == "q":
            cols = list(sig[3]) + ["", ""]
            if cols[0]:
                self.up_next = (cols[0], cols[1])
                return
            pid, ni = sig[1], sig[2]
        else:
            pid, ni = sig[1], sig[2]

        def work():
            try:
                url = (f"{BEEFWEB}/playlists/{q(pid)}/items/{ni}:1?"
                       + urllib.parse.urlencode({"columns": "%title%,%artist%"}))
                items = (get_json(url, 4).get("playlistItems") or {}).get("items") or []
                if items:
                    cols = [str(x) for x in (items[0].get("columns") or [])] + ["", ""]
                    self.events.put(("upnext", sig, (cols[0], cols[1])))
            except Exception:
                pass
        threading.Thread(target=work, daemon=True).start()

    def draw_up_next(self, pos, dt):
        g = self.geo
        rem = self.duration - pos if self.duration > 0 else 1e9
        want = (bool(SETTINGS["show_up_next"]) and self.up_next is not None and self.playing
                and 0 < rem <= 20 and not self.pl_open)
        self.upnext_anim += ((1.0 if want else 0.0) - self.upnext_anim) * (1 - math.exp(-dt * 6))
        if self.upnext_anim < .02 or not self.up_next:
            return
        c = self.canvas
        e = ease_out(self.upnext_anim)
        t, a = self.up_next
        f1, f2 = g["f_pl_title_b"], g["f_label"]
        maxw = g["lw"] * .55
        line = self.ell(t + (f"  ·  {a}" if a else ""), f1, maxw)
        w = max(f1.measure(line), f2.measure("UP NEXT")) + 40
        hgt = f1.metrics("linespace") + f2.metrics("linespace") + 22
        x1 = g["w"] - g["margin"] + (1 - e) * 60
        y1 = g["h"] - int(g["h"] * .075)
        x0, y0 = x1 - w, y1 - hgt
        base = mix(self.tint, (14, 14, 22), .45)
        self.rrect(x0, y0, x1, y1, 14, fill=hexc(mix(self.tint, base, e)),
                   outline=hexc(mix(self.tint, mix(base, WHITE, .14), e)), tags="dyn")
        c.create_text(x0 + 20, y0 + 10, text="UP NEXT", anchor="nw", font=f2,
                      fill=hexc(mix(self.tint, mix(self.accent, WHITE, .35), e)), tags="dyn")
        c.create_text(x0 + 20, y1 - 10, text=line, anchor="sw", font=f1,
                      fill=hexc(mix(self.tint, WHITE, e)), tags="dyn")

    # ---- playlist panel
    def draw_playlist(self, now):
        g = self.geo
        e = ease_out(self.pl_anim)
        if e < .01:
            return
        c, P = self.canvas, g["pl"]
        ox = (1 - e) * (g["w"] - P["x0"] + 30)
        x0, y0, x1, y1, pad = P["x0"], P["y0"], P["x1"], P["y1"], P["pad"]
        strips = {"head": (0, P["list_y0"] - y0), "foot": (P["list_y1"] - y0, y1 - y0)}
        gl = self.glass("pl", (x0, y0, x1, y1), P["rad"], strips=strips)
        base = self.pl_base = gl["avg"]
        c.create_image(x0 + ox, y0, image=gl["img"], anchor="nw", tags="dyn")

        self.draw_pl_rows(P, ox, base, now)

        # header / footer strips mask rows that scroll out of the list area
        if "head" in gl:
            c.create_image(x0 + ox, y0, image=gl["head"], anchor="nw", tags="dyn")
        if "foot" in gl:
            c.create_image(x0 + ox, P["list_y1"], image=gl["foot"], anchor="nw", tags="dyn")
        c.create_line(x0 + pad + ox, P["list_y0"] - 1, x1 - pad + ox, P["list_y0"] - 1,
                      fill=hexc(mix(base, WHITE, .07)), tags="dyn")
        c.create_line(x0 + pad + ox, P["list_y1"], x1 - pad + ox, P["list_y1"],
                      fill=hexc(mix(base, WHITE, .07)), tags="dyn")

        # header
        c.create_text(x0 + pad + ox, P["head_cy"], text="Playlists", anchor="w",
                      font=g["f_pl_head"], fill="#ffffff", tags="dyn")
        hov = self.hover_hit[1] if self.hover_hit and self.hover_hit[0] == "plbtn" else None
        for name, cx, cy, r in P["hbtns"]:
            cx += ox
            c.create_oval(cx - r, cy - r, cx + r, cy + r,
                          fill=hexc(mix(base, WHITE, .16 if hov == name else .07)), outline="",
                          tags="dyn")
            col = "#ffffff"
            u = r * .45
            if name == "add":
                c.create_line(cx - u, cy, cx + u, cy, fill=col, width=2, capstyle="round", tags="dyn")
                c.create_line(cx, cy - u, cx, cy + u, fill=col, width=2, capstyle="round", tags="dyn")
            elif name == "sort":
                for i, ww in enumerate((1.0, .7, .4)):
                    yy = cy - u * .7 + i * u * .7
                    c.create_line(cx - u, yy, cx - u + 2 * u * ww, yy, fill=col, width=2,
                                  capstyle="round", tags="dyn")
            else:
                for dx in (-u, 0, u):
                    c.create_oval(cx + dx - 1.8, cy - 1.8, cx + dx + 1.8, cy + 1.8, fill=col,
                                  outline="", tags="dyn")

        self.draw_pl_tabs(P, ox, base)
        self.draw_pl_search(P, ox, base, now)

        # footer
        pl = self.pl_view()
        n = len(self.pl_items)
        bits = [plural(n, "track")] if pl or n else []
        if pl and pl.get("totalTime"):
            bits.append(fmt_long(pl.get("totalTime")))
        if len(self.pl_sel) > 1:
            bits.append(f"{len(self.pl_sel)} selected")
        if self.queue_items:
            bits.append(f"{len(self.queue_items)} queued")
        fcol = hexc(mix(base, WHITE, .5))
        c.create_text(x0 + pad + ox, P["foot_cy"], text="  ·  ".join(bits), anchor="w",
                      font=g["f_pl_foot"], fill=fcol, tags="dyn")
        hint = "Enter play   Del remove   Q queue   Right-click more"
        if not self.perm_pl:
            hint = "Read-only: enable playlist changes in Beefweb"
        if x1 - x0 > g["f_pl_foot"].measure(hint) + g["f_pl_foot"].measure("  ·  ".join(bits)) + 3 * pad:
            c.create_text(x1 - pad + ox, P["foot_cy"], text=hint, anchor="e",
                          font=g["f_pl_foot"], fill=hexc(mix(base, WHITE, .34)), tags="dyn")

    def draw_pl_tabs(self, P, ox, base):
        c, g = self.canvas, self.geo
        f = g["f_pl_tab"]
        y0, th = P["tabs_y0"], P["tabs_h"]
        left, right = P["x0"] + P["pad"], P["x1"] - P["pad"]
        cpad = int(th * .55)
        maxw = max(80, (right - left) * .45)
        chips = []
        for p in self.playlists:
            title = self.ell(str(p.get("title", "")) or "Untitled", f, maxw)
            wdt = self.mw(title, f) + 2 * cpad + (th * .45 if p.get("id") == self.play_pl_id else 0)
            chips.append((p.get("id"), title, wdt))
        self.pl_tab_boxes, self.pl_tab_arrows = [], []
        if not chips:
            c.create_text(left + ox, y0 + th / 2, text="No playlists" if self.connected else
                          "Not connected", anchor="w", font=f, fill=hexc(mix(base, WHITE, .45)),
                          tags="dyn")
            return
        total = sum(w for _, _, w in chips) + 8 * (len(chips) - 1)
        overflow = total > right - left
        avail_r = right - (2 * th + 10 if overflow else 0)
        ids = [cid for cid, _, _ in chips]
        self.pl_tab_first = max(0, min(len(chips) - 1, self.pl_tab_first))
        if not overflow:
            self.pl_tab_first = 0
        elif self.pl_tab_reveal and self.pl_view_id in ids:
            vi = ids.index(self.pl_view_id)
            if vi < self.pl_tab_first:
                self.pl_tab_first = vi
            while True:
                span = sum(w + 8 for _, _, w in chips[self.pl_tab_first:vi + 1]) - 8
                if span <= avail_r - left or self.pl_tab_first >= vi:
                    break
                self.pl_tab_first += 1
        self.pl_tab_reveal = False
        hov = self.hover_hit[1] if self.hover_hit and self.hover_hit[0] == "pltab" else None
        x = left
        last_shown = self.pl_tab_first - 1
        for i in range(self.pl_tab_first, len(chips)):
            cid, title, wdt = chips[i]
            if x + wdt > avail_r:
                break
            viewing = cid == self.pl_view_id
            fill = (mix(base, self.accent, .62) if viewing else
                    mix(base, WHITE, .15 if hov == cid else .07))
            self.rrect(x + ox, y0, x + wdt + ox, y0 + th, th / 2, fill=hexc(fill), outline="",
                       tags="dyn")
            tx = x + cpad
            if cid == self.play_pl_id:
                self.draw_eq(tx + th * .12 + ox, y0 + th / 2, th * .34,
                             "#ffffff" if viewing else hexc(mix(self.accent, WHITE, .3)),
                             time.perf_counter())
                tx += th * .45
            c.create_text(tx + ox, y0 + th / 2, text=title, anchor="w", font=f,
                          fill="#ffffff" if viewing else hexc(mix(base, WHITE, .78)), tags="dyn")
            self.pl_tab_boxes.append((cid, (x, y0, x + wdt, y0 + th)))
            x += wdt + 8
            last_shown = i
        if overflow:
            ax = right - 2 * th - 6
            for d, sym in ((-1, "left"), (1, "right")):
                en = (self.pl_tab_first > 0) if d < 0 else (last_shown < len(chips) - 1)
                box = (ax, y0, ax + th, y0 + th)
                h2 = self.hover_hit == ("plarrow", d)
                c.create_oval(box[0] + ox, box[1], box[2] + ox, box[3],
                              fill=hexc(mix(base, WHITE, .16 if h2 else .07)), outline="", tags="dyn")
                self._tri((box[0] + box[2]) / 2 + ox, (box[1] + box[3]) / 2, th * .17, sym,
                          "#ffffff" if en else hexc(mix(base, WHITE, .3)))
                if en:
                    self.pl_tab_arrows.append((d, box))
                ax += th + 6

    def draw_pl_search(self, P, ox, base, now):
        c, g = self.canvas, self.geo
        x0, y0, x1, y1 = P["search"]
        hgt = y1 - y0
        act = self.pl_filter_active
        self.rrect(x0 + ox, y0, x1 + ox, y1, hgt / 2, fill=hexc(mix(base, (0, 0, 0), .28)),
                   outline=hexc(mix(self.accent, WHITE, .2) if act else mix(base, WHITE, .10)),
                   width=2 if act else 1, tags="dyn")
        f = g["f_pl_title"]
        cy = (y0 + y1) / 2
        r = hgt * .17
        mx = x0 + hgt * .55 + ox
        icol = hexc(mix(base, WHITE, .55))
        c.create_oval(mx - r, cy - r - 1, mx + r, cy + r - 1, outline=icol, width=2, tags="dyn")
        c.create_line(mx + r * .7, cy + r * .7 - 1, mx + r * 1.6, cy + r * 1.6 - 1, fill=icol,
                      width=2, capstyle="round", tags="dyn")
        tx = x0 + hgt * 1.05 + ox
        right = x1 - hgt * .6 + ox
        if self.pl_filter:
            n = len(self.pl_rows)
            cnt = f"{n} of {len(self.pl_items)}"
            fc = g["f_pl_sub"]
            cw = fc.measure(cnt)
            # clear button
            cx = x1 - hgt / 2 + ox
            hv = self.hover_hit == ("plsearch", "clear")
            c.create_oval(cx - hgt * .28, cy - hgt * .28, cx + hgt * .28, cy + hgt * .28,
                          fill=hexc(mix(base, WHITE, .25 if hv else .14)), outline="", tags="dyn")
            m = hgt * .1
            c.create_line(cx - m, cy - m, cx + m, cy + m, fill="#ffffff", width=2, tags="dyn")
            c.create_line(cx - m, cy + m, cx + m, cy - m, fill="#ffffff", width=2, tags="dyn")
            c.create_text(cx - hgt * .5, cy, text=cnt, anchor="e", font=fc,
                          fill=hexc(mix(base, WHITE, .45)), tags="dyn")
            right = cx - hgt * .5 - cw - 12
            shown = self.pl_filter
            while shown and f.measure(shown) > right - tx:
                shown = shown[1:]
            c.create_text(tx, cy, text=shown, anchor="w", font=f, fill="#ffffff", tags="dyn")
            caret_x = tx + f.measure(shown)
        else:
            c.create_text(tx, cy, text="Filter tracks" + ("" if act else "   ( / )"), anchor="w",
                          font=f, fill=hexc(mix(base, WHITE, .4)), tags="dyn")
            caret_x = tx
        if act and int(now * 1.8) % 2 == 0:
            lh = f.metrics("linespace") * .4
            c.create_line(caret_x + 1, cy - lh, caret_x + 1, cy + lh, fill="#ffffff", width=2,
                          tags="dyn")

    def draw_eq(self, cx, cy, hgt, col, now):
        """Tiny animated equalizer used for the playing track / playlist."""
        bw = max(2, hgt * .22)
        for i, ph in enumerate((0.0, 1.7, 3.1)):
            if self.playing:
                v = .35 + .65 * abs(math.sin(now * (5.2 + i * 1.3) + ph))
            else:
                v = (.45, .85, .6)[i]
            x = cx + (i - 1) * bw * 1.7
            self.canvas.create_rectangle(x - bw / 2, cy + hgt / 2 - hgt * v, x + bw / 2,
                                         cy + hgt / 2, fill=col, outline="", tags="dyn")

    def draw_pl_rows(self, P, ox, base, now):
        c, g = self.canvas, self.geo
        rows, rh = self.pl_rows, P["row_h"]
        ly0, ly1 = P["list_y0"], P["list_y1"]
        x0, x1, pad = P["x0"], P["x1"], P["pad"]
        rx0, rx1 = x0 + pad * .55 + ox, x1 - pad * .9 + ox
        cx_mid = (x0 + x1) / 2 + ox
        if not rows:
            if self.pl_fetch_pending and not self.pl_items:
                msg, sub = "Loading…", ""
            elif self.pl_filter:
                msg, sub = f"No matches for “{self.pl_filter}”", "Esc clears the filter"
            elif not self.playlists:
                msg, sub = ("No playlists", "Ctrl+N creates one") if self.connected else \
                    ("Not connected", "Is Beefweb running?")
            else:
                msg, sub = "This playlist is empty", "Ctrl+O add files · Right-click for more"
            c.create_text(cx_mid, (ly0 + ly1) / 2 - 10, text=msg, font=g["f_pl_head"],
                          fill=hexc(mix(base, WHITE, .6)), tags="dyn")
            if sub:
                c.create_text(cx_mid, (ly0 + ly1) / 2 + g["f_pl_head"].metrics("linespace"),
                              text=sub, font=g["f_pl_sub"], fill=hexc(mix(base, WHITE, .4)),
                              tags="dyn")
            return
        first = max(0, int(self.pl_scroll // rh) - 1)
        last = min(len(rows), int((self.pl_scroll + (ly1 - ly0)) // rh) + 2)
        numw = P["numw"]
        ft, ftb, fs, fn = g["f_pl_title"], g["f_pl_title_b"], g["f_pl_sub"], g["f_pl_num"]
        dur_w = fn.measure("00:00:00")
        text_x = rx0 + numw + 26
        hov = self.hover_hit[1] if self.hover_hit and self.hover_hit[0] == "plrow" else None
        viewing_playing = self.pl_view_id == self.play_pl_id
        sel_fill = hexc(mix(base, self.accent, .36))
        hov_fill = hexc(mix(base, WHITE, .06))
        play_fill = hexc(mix(base, self.accent, .16))
        dim = hexc(mix(base, WHITE, .5))
        dimmer = hexc(mix(base, WHITE, .36))
        acc_txt = hexc(mix(self.accent, WHITE, .4))
        drag = self.pl_drag if self.pl_drag and self.pl_drag["active"] else None
        for k in range(first, last):
            real = rows[k]
            it = self.pl_items[real]
            top = ly0 + k * rh - self.pl_scroll
            playing_row = viewing_playing and real == self.play_idx
            selected = real in self.pl_sel
            if selected:
                self.rrect(rx0, top + 2, rx1, top + rh - 2, 10, fill=sel_fill, outline="", tags="dyn")
            elif playing_row:
                self.rrect(rx0, top + 2, rx1, top + rh - 2, 10, fill=play_fill, outline="", tags="dyn")
            elif real == hov and not drag:
                self.rrect(rx0, top + 2, rx1, top + rh - 2, 10, fill=hov_fill, outline="", tags="dyn")
            if real == self.pl_cursor and not selected and len(self.pl_sel) > 0:
                self.rrect(rx0, top + 2, rx1, top + rh - 2, 10, fill="",
                           outline=hexc(mix(base, WHITE, .22)), tags="dyn")
            cy = top + rh / 2
            ncx = rx0 + 12 + numw / 2
            if playing_row:
                self.draw_eq(ncx, cy, rh * .3, acc_txt if not selected else "#ffffff", now)
            else:
                c.create_text(ncx, cy, text=str(real + 1), font=fn, fill=dimmer, tags="dyn")
            right = rx1 - 12
            c.create_text(right, cy, text=it[3], anchor="e", font=fn, fill=dim, tags="dyn")
            right -= dur_w * .75 + 10
            qp = self.queue_pos.get((self.pl_view_id, real))
            if qp:
                qt = f"Q{qp}"
                qw = fn.measure(qt) + 14
                qh = fn.metrics("linespace") + 2
                self.rrect(right - qw, cy - qh / 2, right, cy + qh / 2, qh / 2,
                           fill=hexc(mix(base, self.accent, .7)), outline="", tags="dyn")
                c.create_text(right - qw / 2, cy, text=qt, font=fn, fill="#ffffff", tags="dyn")
                right -= qw + 10
            avail = right - text_x
            title = it[1] or "Untitled"
            sub = " — ".join(x for x in (it[0], it[2]) if x)
            c.create_text(text_x, cy + 1, text=self.ell(title, ftb if playing_row else ft, avail),
                          anchor="sw", font=ftb if playing_row else ft,
                          fill=acc_txt if playing_row and not selected else "#ffffff", tags="dyn")
            if sub:
                c.create_text(text_x, cy + 1, text=self.ell(sub, fs, avail), anchor="nw", font=fs,
                              fill=dim if not selected else hexc(mix(base, WHITE, .75)), tags="dyn")
        # drag insertion marker
        if drag and drag["gap"] is not None:
            gy = ly0 + drag["gap"] * rh - self.pl_scroll
            if ly0 - 2 <= gy <= ly1 + 2:
                ac = hexc(mix(self.accent, WHITE, .2))
                c.create_line(rx0 + 8, gy, rx1 - 4, gy, fill=ac, width=3, capstyle="round",
                              tags="dyn")
                c.create_oval(rx0 + 2, gy - 5, rx0 + 12, gy + 5, fill=ac, outline="", tags="dyn")
                n = len(self.pl_selected())
                c.create_text(rx1 - 8, gy - 6, text=f"Move {plural(n, 'track')}", anchor="se",
                              font=g["f_pl_sub"], fill=ac, tags="dyn")
        # scrollbar
        m = self.pl_max_scroll()
        if m > 0:
            lh = ly1 - ly0
            total = lh + m
            th = max(28, lh * lh / total)
            ty = ly0 + (lh - th) * (self.pl_scroll / m)
            sx = x1 - pad * .45 + ox
            act = self.pl_sb_drag or (self.hover_hit and self.hover_hit[0] == "plsb")
            c.create_line(sx, ty + 3, sx, ty + th - 3, width=6 if act else 4, capstyle="round",
                          fill=hexc(mix(base, WHITE, .45 if act else .25)), tags="dyn")

    def draw_toast(self, now):
        if not self.toast_msg or now > self.toast_until + .3:
            return
        c, g = self.canvas, self.geo
        t_in = ease_out((now - self.toast_t0) / .2)
        t_out = ease_out((self.toast_until + .3 - now) / .3) if now > self.toast_until else 1
        e = min(t_in, t_out)
        f = g["f_toast"]
        txt = self.ell(self.toast_msg, f, g["w"] * .6)
        w = f.measure(txt) + 48
        hgt = f.metrics("linespace") + 20
        cx = g["w"] / 2
        y0 = g["h"] * .035 - (1 - e) * (hgt + 30)
        base = mix(self.tint, (14, 14, 22), .6)
        self.rrect(cx - w / 2, y0 + 4, cx + w / 2, y0 + hgt + 4, hgt / 2, fill="#020203",
                   outline="", tags="dyn")
        self.rrect(cx - w / 2, y0, cx + w / 2, y0 + hgt, hgt / 2, fill=hexc(base),
                   outline=hexc(mix(base, self.accent, .5)), tags="dyn")
        c.create_text(cx, y0 + hgt / 2, text=txt, font=f, fill="#ffffff", tags="dyn")

    def update_cursor(self):
        if self.modal:
            want = "hand2" if self.modal_button_hover() else ("xterm" if self.modal["kind"] == "prompt"
                                                              else "arrow")
        elif self.menu:
            lay = self.menu.get("lay")
            want = "hand2" if lay and self.menu_hover_index(lay) >= 0 else "arrow"
        elif self.settings_open:
            want = "hand2" if self.settings_button_hover() else "arrow"
        elif self.help_open:
            want = "arrow"
        elif self.pl_drag and self.pl_drag["active"]:
            want = "sb_v_double_arrow"
        elif (self.ui_alpha < .05 and self.fullscreen and not self.dragging
              and not self.pl_open):
            want = "none"
        elif self.hover_hit and self.hover_hit[0] == "plsearch":
            want = "hand2" if self.hover_hit[1] == "clear" else "xterm"
        elif self.hover_hit and self.hover_hit[0] not in ("plpanel", "pllist"):
            want = "hand2"
        else:
            want = "arrow"
        if want != self.cursor:
            self.cursor = want
            try:
                self.canvas.config(cursor=want)
            except tk.TclError:
                self.canvas.config(cursor="arrow")

    # ------------------------------------------------------------ main loop
    def tick(self):
        if not self.alive:
            return
        now = time.perf_counter()
        dt = min(.1, now - self.last_tick)
        self.last_tick = now
        try:
            self.step(now, dt)
        except Exception:
            import traceback
            traceback.print_exc()
        self.root.after(TICK_MS, self.tick)

    def step(self, now, dt):
        self.drain_events()
        self.sync_remote(now)
        if self.connected != self.prev_connected:
            self.prev_connected = self.connected
            self.static_dirty = True
        w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
        if w < 300 or h < 200:
            return
        if self.geo is None or (w, h) != self.size:
            self.relayout()
        if self.static_dirty:
            self.draw_static()
        self.manage_assets(now)
        self.flush_volume(now)
        self.update_up_next()

        idle = now - self.last_move
        show = (idle < float(SETTINGS["ui_hide_after"]) or not self.playing or self.dragging
                or self.vol_dragging or self.overlay_open() or self.pl_open or self.menu)
        tgt = 1.0 if show else 0.0
        self.ui_alpha += (tgt - self.ui_alpha) * (1 - math.exp(-dt * (12 if tgt > self.ui_alpha else 2.2)))
        ptgt = 1.0 if self.pl_open else 0.0
        self.pl_anim += (ptgt - self.pl_anim) * (1 - math.exp(-dt * 11))
        if abs(ptgt - self.pl_anim) < .004:
            self.pl_anim = ptgt

        # playlist smooth scroll + auto-scroll while dragging near the edges
        if self.pl_drag and self.pl_drag["active"] and self.geo:
            P = self.geo["pl"]
            edge = P["row_h"] * 1.2
            if self.my < P["list_y0"] + edge:
                self.pl_target -= (P["list_y0"] + edge - self.my) * dt * 12
            elif self.my > P["list_y1"] - edge:
                self.pl_target += (self.my - (P["list_y1"] - edge)) * dt * 12
            self.pl_clamp_scroll()
            self.pl_drag["gap"] = self.pl_gap_at(self.my)
        self.pl_scroll += (self.pl_target - self.pl_scroll) * (1 - math.exp(-dt * 16))
        if abs(self.pl_target - self.pl_scroll) < .5:
            self.pl_scroll = self.pl_target

        pos = self.est_pos(now)
        self.update_lyrics(pos, dt)
        self.update_hover()
        self.canvas.delete("dyn")
        if self.overlay_open():
            self.draw_scrim()
            self.draw_settings()
            self.draw_help()
            self.draw_modal()
        else:
            self.draw_lyrics()
            self.draw_controls(pos)
            self.draw_up_next(pos, dt)
            self.draw_playlist(now)
        self.draw_menu()
        self.draw_toast(now)
        self.update_cursor()


if __name__ == "__main__":
    root = tk.Tk()
    App(root)
    root.mainloop()
