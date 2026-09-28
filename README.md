# foobar_fullscreen_lyrics

A fullscreen lyrics app for foobar2000 x86, made to provide a fullscreen music/lyrics experience without needing to work around SMTC or Windows media controls.

## General requirements

* foobar2000 with the Beefweb component, listening on `http://127.0.0.1:8880` (the default).

**Default address:**

```text
http://127.0.0.1:8880
```

## Install

### 1. Via release (independent app)

Install the release, then run the `.exe`.

### 2. Via the `.pyw` file (independent script)

**Requirements:**

* Python 3.10+
* Pillow >= 10.0
* foobar2000 with the Beefweb component, listening on `http://127.0.0.1:8880` (the default).
* Tkinter (bundled with Python on Windows/macOS; `python3-tk` on Linux).

Just double-click it.

### 3. As a component

Install the component in foobar2000.
click view > Foobar Fullscreen Lyrics
