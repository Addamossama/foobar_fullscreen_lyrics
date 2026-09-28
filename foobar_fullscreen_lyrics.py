"""Foobar Fullscreen Lyrics v6

Fullscreen synced lyrics for foobar2000 (via Beefweb) with an ambient,
artwork-driven look.  Requires: Python 3.10+, Pillow, foobar2000 + Beefweb.
"""
import bisect, colorsys, io, json, math, queue, re, threading, time
import urllib.parse, urllib.request
import tkinter as tk
import tkinter.font as tkfont
from PIL import Image, ImageDraw, ImageEnhance, ImageFilter, ImageOps, ImageTk

try:  # crisp text on Windows high-DPI screens
    import ctypes
    ctypes.windll.shcore.SetProcessDpiAwareness(1)
except Exception:
    pass

# ----------------------------------------------------------------- settings
BEEFWEB = "http://127.0.0.1:8880/api"
LRCLIB = "https://lrclib.net/api"
POLL_S = 0.15          # how often Beefweb is polled
TICK_MS = 16           # UI frame interval (~60 fps)
LYRIC_LEAD = 0.15      # highlight a line slightly early (seconds)
UI_HIDE_AFTER = 3.5    # controls fade out after this many idle seconds
UI_FONTS = ("Segoe UI Variable Display", "Segoe UI", "SF Pro Display",
            "Helvetica Neue", "Inter", "Noto Sans", "DejaVu Sans", "Helvetica")
DEFAULT_ACCENT = (139, 108, 255)
WHITE = (255, 255, 255)
UA = {"User-Agent": "FoobarLyrics/6.0"}


# --------------------------------------------------------------------- http
def get_json(url, timeout=5):
    req = urllib.request.Request(url, headers=UA)
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read().decode("utf-8"))


def request_bytes(url, timeout=8):
    req = urllib.request.Request(url, headers=UA)
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def post_json(url, data=None):
    body = None if data is None else json.dumps(data).encode()
    req = urllib.request.Request(url, data=body, method="POST",
                                 headers={"Content-Type": "application/json", **UA})
    with urllib.request.urlopen(req, timeout=4):
        pass


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


def fetch_lyrics(artist, title, album, duration):
    """Exact LRCLIB match first, then a fuzzy search fallback."""
    def synced(obj):
        return parse_lrc(obj.get("syncedLyrics") or "") if isinstance(obj, dict) else []

    q = {"track_name": title, "artist_name": artist}
    if album:
        q["album_name"] = album
    if duration:
        q["duration"] = round(duration)
    try:
        lines = synced(get_json(LRCLIB + "/get?" + urllib.parse.urlencode(q), 8))
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


# ------------------------------------------------------------------ helpers
def fmt(t):
    t = max(0, int(t or 0))
    return f"{t // 60}:{t % 60:02d}"


def mix(a, b, t):
    t = max(0.0, min(1.0, t))
    return tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))


def hexc(c):
    return "#%02x%02x%02x" % tuple(max(0, min(255, int(v))) for v in c)


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
    while text and font.measure(text + "…") > maxw:
        text = text[:-1]
    return text.rstrip() + "…"


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


def shade(bg):
    """Real-alpha darkening: heavier on the lyric side, soft top/bottom vignette."""
    w, h = bg.size
    grad = Image.linear_gradient("L")                       # black top -> white bottom
    hor = grad.rotate(90).resize((w, h), Image.Resampling.BILINEAR)
    bg.paste((0, 0, 0), (0, 0, w, h), hor.point(lambda v: int(v * 0.50)))
    ver = grad.resize((w, h), Image.Resampling.BILINEAR)
    top = ImageOps.invert(ver).point(lambda v: int((v / 255) ** 3 * 150))
    bot = ver.point(lambda v: int((v / 255) ** 3 * 190))
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
        d.ellipse([c - cs * r, c - cs * r, c + cs * r, c + cs * r], outline=mix((10, 10, 16), accent, .22))
    r = cs * .12
    d.ellipse([c - r, c - r, c + r, c + r], fill=mix((20, 20, 30), accent, .7))
    r = cs * .014
    d.ellipse([c - r, c - r, c + r, c + r], fill=(10, 10, 16))
    return img


def build_assets(raw, w, h, cs):
    if raw is None:
        accent = DEFAULT_ACCENT
        bg = fallback_bg(w, h, accent)
        cover = placeholder_cover(cs, accent)
    else:
        accent = pick_accent(raw)
        sw, sh = max(64, w // 10), max(36, h // 10)
        small = cover_crop(raw, sw, sh).filter(ImageFilter.GaussianBlur(max(6, sw // 9)))
        small = ImageEnhance.Color(small).enhance(1.45)
        small = ImageEnhance.Brightness(small).enhance(.68)
        bg = small.resize((w, h), Image.Resampling.BICUBIC)
        cover = cover_crop(raw, cs, cs)
    bg = shade(bg)
    tint = bg.crop((w // 2, 0, w, h)).resize((1, 1), Image.Resampling.BOX).getpixel((0, 0))
    cover, pad = frame_cover(cover, cs)
    return {"bg": bg, "cover": cover, "pad": pad, "accent": accent, "tint": tuple(tint[:3])}


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
        self._fonts = {}

        # playback state (remote = written by poll thread, read by UI thread)
        now = time.perf_counter()
        self.remote = {"seq": 0, "ok": False, "a": "", "t": "", "al": "",
                       "pos": 0.0, "dur": 0.0, "playing": False, "stamp": now}
        self.seen_seq = 0
        self.pos_base, self.pos_stamp, self.ignore_until = 0.0, now, 0.0
        self.duration, self.playing, self.connected = 0.0, False, False
        self.prev_connected = None
        self.track_key, self.track = None, ("", "", "")

        # lyrics
        self.lines, self.times, self.lines_ver = [], [], 0
        self.lyric_state = "idle"
        self.focus, self.line_rows, self.line_y, self.line_h = [], [], [], []
        self.lyr_alpha, self.current = 1.0, -1
        self.auto_follow = True
        self.scroll = self.target_scroll = 0.0

        # visuals
        self.art_raw, self.art_ver = None, 0
        self.bg_photo = self.cover_photo = None
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

        c = self.canvas = tk.Canvas(root, bg="#050508", highlightthickness=0, cursor="arrow")
        c.pack(fill="both", expand=True)
        self.bg_item = c.create_image(0, 0, anchor="nw")
        self.cover_item = c.create_image(0, 0, anchor="nw")

        c.bind("<Motion>", self.on_motion)
        c.bind("<Leave>", lambda e: self.on_leave())
        c.bind("<Button-1>", self.on_press)
        c.bind("<B1-Motion>", self.on_drag)
        c.bind("<ButtonRelease-1>", self.on_release)
        c.bind("<MouseWheel>", lambda e: self.wheel(-1 if e.delta > 0 else 1))
        c.bind("<Button-4>", lambda e: self.wheel(-1))
        c.bind("<Button-5>", lambda e: self.wheel(1))
        root.bind("<F11>", self.toggle_fullscreen)
        root.bind("<Escape>", self.exit_fullscreen)
        root.bind("<space>", lambda e: self.playpause())
        root.bind("<Left>", lambda e: self.skip(-10))
        root.bind("<Right>", lambda e: self.skip(10))
        root.bind("<f>", lambda e: self.follow_now())
        root.protocol("WM_DELETE_WINDOW", self.close)

        threading.Thread(target=self.poll_loop, daemon=True).start()
        root.after(30, self.tick)

    # ------------------------------------------------------------- plumbing
    def font(self, px, weight="normal"):
        k = (px, weight)
        if k not in self._fonts:
            self._fonts[k] = tkfont.Font(family=self.family, size=-px, weight=weight)
        return self._fonts[k]

    def close(self):
        self.alive = False
        self.root.destroy()

    def command(self, path, data=None):
        def run():
            try:
                post_json(BEEFWEB + path, data)
            except Exception:
                pass
        threading.Thread(target=run, daemon=True).start()

    def poll_loop(self):
        url = BEEFWEB + "/player?" + urllib.parse.urlencode({"columns": "%artist%,%title%,%album%"})
        seq = 0
        while self.alive:
            t0 = time.perf_counter()
            seq += 1
            try:
                d = get_json(url, 2.5)
                t1 = time.perf_counter()
                p = d.get("player", {})
                item = p.get("activeItem", {}) or {}
                cols = item.get("columns") or []
                col = lambda i: str(cols[i]) if len(cols) > i and cols[i] is not None else ""
                self.remote = {
                    "seq": seq, "ok": True, "a": col(0), "t": col(1), "al": col(2),
                    "pos": float(item.get("position") or 0),
                    "dur": float(item.get("duration") or 0),
                    "playing": str(p.get("playbackState", "")).lower() == "playing",
                    "stamp": (t0 + t1) / 2}
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

    # ----------------------------------------------------- state from Beefweb
    def sync_remote(self, now):
        r = self.remote
        self.connected = r["ok"]
        if r["seq"] == self.seen_seq:
            return
        self.seen_seq = r["seq"]
        if not r["ok"]:
            self.playing = False
            return
        self.duration, self.playing = r["dur"], r["playing"]
        if now >= self.ignore_until:
            self.pos_base, self.pos_stamp = r["pos"], r["stamp"]
        key = (r["a"], r["t"], r["al"])
        if key != self.track_key and (key[0] or key[1]):
            self.on_track_change(key, r["dur"])

    def on_track_change(self, key, dur):
        self.track_key = self.track = key
        self.lines, self.times, self.focus = [], [], []
        self.lines_ver += 1
        self.lyric_state, self.current = "loading", -1
        self.scroll = self.target_scroll = 0.0
        self.auto_follow = True
        self.static_dirty = True
        self.root.title(" — ".join(x for x in key[:2] if x) or "Foobar Lyrics")
        threading.Thread(target=self.lyrics_worker, args=(key, dur), daemon=True).start()
        threading.Thread(target=self.art_worker, args=(key,), daemon=True).start()

    def lyrics_worker(self, key, dur):
        try:
            lines = fetch_lyrics(key[0], key[1], key[2], dur)
        except Exception:
            lines = []
        self.events.put(("lyrics", key, lines))

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

    def asset_worker(self, seq, raw, w, h, cs):
        try:
            self.events.put(("assets", seq, build_assets(raw, w, h, cs)))
        except Exception:
            import traceback
            traceback.print_exc()

    def drain_events(self):
        while True:
            try:
                ev = self.events.get_nowait()
            except queue.Empty:
                return
            if ev[0] == "lyrics" and ev[1] == self.track_key:
                self.set_lines(ev[2])
            elif ev[0] == "art" and ev[1] == self.track_key:
                self.art_raw = ev[2]
                self.art_ver += 1
                self.immediate = True
            elif ev[0] == "assets" and ev[1] == self.asset_seq:
                self.apply_assets(ev[2])

    def set_lines(self, lines):
        self.lines = lines
        self.times = [t for t, _ in lines]
        self.focus = [0.0] * len(lines)
        self.lines_ver += 1
        self.lyric_state = "found" if lines else "none"
        self.lyr_alpha = 0.0
        self.current = -1
        if self.geo:
            self.layout_lines()
            self.scroll = self.target_scroll = self.center_of(0) if lines else 0.0

    def manage_assets(self, now):
        w, h = self.size
        sig = (w, h, self.geo["cs"], self.art_ver)
        if sig != self.want_sig:
            self.want_sig, self.want_since = sig, now
        if sig != self.built_sig and (self.immediate or now - self.want_since >= 0.25):
            self.immediate = False
            self.built_sig = sig
            self.asset_seq += 1
            threading.Thread(target=self.asset_worker, daemon=True,
                             args=(self.asset_seq, self.art_raw, w, h, self.geo["cs"])).start()

    def apply_assets(self, a):
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

    # --------------------------------------------------------------- layout
    def relayout(self):
        c = self.canvas
        w, h = c.winfo_width(), c.winfo_height()
        self.size = (w, h)
        F = self.font
        g = {"w": w, "h": h}
        g["f_title"] = F(max(20, int(h * .031)), "bold")
        g["f_artist"] = F(max(15, int(h * .023)))
        g["f_album"] = F(max(13, int(h * .017)))
        g["f_time"] = F(max(11, int(h * .0145)))
        g["f_lyric"] = F(max(30, int(h * .052)), "bold")
        g["f_msg"] = F(max(20, int(h * .034)), "bold")
        g["f_pill"] = F(max(12, int(h * .0165)), "bold")
        g["f_hint"] = F(max(11, int(h * .0135)))

        margin = int(w * .055)
        ctl_r = max(22, int(h * .032))
        gap1, gap2 = int(h * .032), int(h * .028)
        tl = g["f_title"].metrics("linespace")
        al = g["f_artist"].metrics("linespace")
        bl = g["f_album"].metrics("linespace")
        info_h = int(tl * 2 + al + bl + h * .006)
        bar_h = int(h * .055)
        ctl_h = int(ctl_r * 2 + h * .035)
        fixed = gap1 + info_h + gap2 + bar_h + ctl_h
        half = w // 2
        cs = min(half - 2 * margin, int(h * .46))
        cs = max(140, min(cs, int(h * .92) - fixed))
        y0 = max(int(h * .04), (h - (cs + fixed)) // 2)
        px = (half - cs) // 2 + int(w * .01)
        info_y = y0 + cs + gap1
        by = info_y + info_h + gap2 + int(bar_h * .30)
        ctl_top = info_y + info_h + gap2 + bar_h
        ctl_cy = ctl_top + ctl_r + int(h * .005)
        cx0 = px + cs / 2
        step = min(cs / 5.0, h * .092)
        buttons = [("back", -2), ("prev", -1), ("play", 0), ("next", 1), ("fwd", 2)]
        lx = half + int(w * .02)
        pill_txt = "Follow lyrics"
        pw = g["f_pill"].measure(pill_txt) + int(h * .05)
        ph = int(h * .05)
        pill_x0 = lx + (w - lx - margin) / 2 - pw / 2
        pill_y0 = h - int(h * .115)
        g.update(
            cs=cs, px=px, cy=y0, info_y=info_y, title_lh=tl, artist_lh=al, album_lh=bl,
            ctl_r=ctl_r, ctl_cy=ctl_cy,
            bar=(px, px + cs, by), bar_hit=max(14, int(h * .022)),
            buttons=[(n, cx0 + k * step, ctl_cy, (ctl_r + 6) if n == "play" else ctl_r * .9)
                     for n, k in buttons],
            lx=lx, lw=max(300, w - lx - margin), ay=int(h * .42),
            pill=(pill_x0, pill_y0, pill_x0 + pw, pill_y0 + ph), pill_txt=pill_txt)
        self.geo = g
        self.layout_lines()
        if self.lines:
            self.target_scroll = self.center_of(max(0, self.current)) if self.auto_follow else self.target_scroll
            self.scroll = self.target_scroll
        self.place_cover()
        self.static_dirty = True

    def layout_lines(self):
        g = self.geo
        f = g["f_lyric"]
        lh = f.metrics("linespace")
        gap = int(lh * .55)
        self.line_rows, self.line_y, self.line_h = [], [], []
        y = 0
        for _, txt in self.lines:
            rows = wrap(txt or "♪", f, g["lw"])
            self.line_rows.append("\n".join(rows))
            self.line_y.append(y)
            self.line_h.append(len(rows) * lh)
            y += len(rows) * lh + gap
        g["lh"], g["lgap"] = lh, gap

    def center_of(self, i):
        return self.line_y[i] + self.line_h[i] / 2

    # ---------------------------------------------------------- interaction
    def hit_at(self, x, y):
        g = self.geo
        if not g or x < 0:
            return None
        if self.ui_alpha > .25 or self.dragging:
            for name, cx, cy, r in g["buttons"]:
                if (x - cx) ** 2 + (y - cy) ** 2 <= r * r:
                    return ("btn", name)
            x0, x1, by = g["bar"]
            if x0 - 8 <= x <= x1 + 8 and abs(y - by) <= g["bar_hit"]:
                return ("bar", None)
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

    def update_hover(self):
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

    def on_press(self, e):
        self.mx, self.my = e.x, e.y
        self.last_move = time.perf_counter()
        self.update_hover()
        hit = self.hover_hit
        if not hit:
            return
        kind, val = hit
        if kind == "bar":
            self.dragging, self.drag_frac = True, self.bar_frac(e.x)
        elif kind == "pill":
            self.follow_now()
        elif kind == "line":
            self.seek_to(self.times[val])
            self.auto_follow = True
        elif kind == "btn":
            if val == "play":
                self.playpause()
            elif val == "prev":
                self.command("/player/previous")
            elif val == "next":
                self.command("/player/next")
            elif val == "back":
                self.skip(-10)
            elif val == "fwd":
                self.skip(10)

    def on_drag(self, e):
        self.mx, self.my = e.x, e.y
        self.last_move = time.perf_counter()
        if self.dragging:
            self.drag_frac = self.bar_frac(e.x)

    def on_release(self, e):
        if self.dragging:
            self.dragging = False
            if self.duration > 0:
                self.seek_to(self.drag_frac * self.duration)

    def wheel(self, direction):
        if not self.lines or not self.geo:
            return
        self.auto_follow = False
        step = self.geo["lh"] * 2
        lo, hi = self.center_of(0), self.center_of(len(self.lines) - 1)
        self.target_scroll = max(lo, min(hi, self.target_scroll + direction * step))

    def follow_now(self):
        self.auto_follow = True

    # -------------------------------------------------------------- drawing
    def rrect(self, x0, y0, x1, y1, r, **kw):
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
        idx = bisect.bisect_right(self.times, pos + LYRIC_LEAD) - 1 if self.times else -1
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
        lx, ay, h = g["lx"], g["ay"], g["h"]
        if not self.lines:
            if self.track_key is None:
                msg = ""
            else:
                msg = {"loading": "Searching for lyrics…",
                       "none": "No synced lyrics found for this track"}.get(self.lyric_state, "")
            if msg:
                c.create_text(lx, ay, text=msg, anchor="w", font=g["f_msg"],
                              fill=hexc(mix(tint, WHITE, .5)), tags="dyn")
            return
        base = mix(tint, WHITE, .44)
        for i in range(len(self.lines)):
            top = ay + self.line_y[i] - self.scroll
            bot = top + self.line_h[i]
            if bot < -40 or top > h + 40:
                continue
            dist = abs((top + bot) / 2 - ay)
            fade = max(.05, 1 - (dist / (h * .6)) ** 2) * self.lyr_alpha
            f = self.focus[i]
            if i == self.hover_line and i != self.current:
                f = max(f, .35)
            col = mix(tint, mix(base, WHITE, f), .12 + .88 * fade)
            c.create_text(lx, top, text=self.line_rows[i], anchor="nw", font=g["f_lyric"],
                          fill=hexc(col), justify="left", tags="dyn")

    def draw_controls(self, pos):
        c, g, tint, ua = self.canvas, self.geo, self.tint, self.ui_alpha
        h = g["h"]
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
        shown = frac * dur if self.dragging else pos
        ty = by + int(h * .016)
        tcol = hexc(mix(tint, WHITE, .42 + .25 * ba))
        c.create_text(x0, ty, text=fmt(shown), anchor="nw", font=g["f_time"], fill=tcol, tags="dyn")
        c.create_text(x1, ty, text="-" + fmt(max(0, dur - shown)) if dur else "-:--", anchor="ne",
                      font=g["f_time"], fill=tcol, tags="dyn")

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
                    c.create_oval(cx - pr, cy - pr, cx + pr, cy + pr, fill=hexc(fillc), outline="", tags="dyn")
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
                    c.create_polygon(cx + a1 * u, cy - u * .75, cx + a1 * u, cy + u * .75, cx + a0 * u, cy,
                                     fill=col, outline="", tags="dyn")
                    c.create_polygon(cx + b1 * u, cy - u * .75, cx + b1 * u, cy + u * .75, cx + b0 * u, cy,
                                     fill=col, outline="", tags="dyn")
                    c.create_text(cx, cy + u * 1.9, text="10", font=g["f_time"], fill=col, tags="dyn")

        if not self.auto_follow and self.lines:
            x0p, y0p, x1p, y1p = g["pill"]
            hp = self.hover_hit and self.hover_hit[0] == "pill"
            self.rrect(x0p, y0p, x1p, y1p, (y1p - y0p) / 2, tags="dyn", outline="",
                       fill=hexc(mix(tint, self.accent, .75 if hp else .55)))
            c.create_text((x0p + x1p) / 2, (y0p + y1p) / 2, text=g["pill_txt"], font=g["f_pill"],
                          fill="#ffffff", tags="dyn")
        if ua > .05:
            c.create_text(g["lx"], g["h"] - int(g["h"] * .04),
                          text="Scroll to browse   ·   Click a line to jump   ·   F11 fullscreen",
                          anchor="sw", font=g["f_hint"], fill=hexc(mix(tint, WHITE, .33 * ua)),
                          tags="dyn")

    def update_cursor(self):
        hit = self.hover_hit
        if self.ui_alpha < .05 and self.fullscreen and not self.dragging:
            want = "none"
        elif hit:
            want = "hand2"
        else:
            want = "arrow"
        if want != self.cursor:
            self.cursor = want
            self.canvas.config(cursor=want)

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

        idle = now - self.last_move
        show = idle < UI_HIDE_AFTER or not self.playing or self.dragging
        tgt = 1.0 if show else 0.0
        self.ui_alpha += (tgt - self.ui_alpha) * (1 - math.exp(-dt * (12 if tgt > self.ui_alpha else 2.2)))

        pos = self.est_pos(now)
        self.update_lyrics(pos, dt)
        self.update_hover()
        self.canvas.delete("dyn")
        self.draw_lyrics()
        self.draw_controls(pos)
        self.update_cursor()


if __name__ == "__main__":
    root = tk.Tk()
    App(root)
    root.mainloop()
