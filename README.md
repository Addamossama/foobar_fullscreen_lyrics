# foobar_fullscreen_lyrics

A fullscreen lyrics app for **foobar2000 x86**, made to provide a fullscreen music/lyrics experience without needing to work around **SMTC** or Windows media controls.

## General requirements

- **foobar2000** with the [Beefweb](https://github.com/hyperblast/beefweb) component, listening on `http://127.0.0.1:8880` (the default).

### Beefweb

The app uses Beefweb to communicate with foobar2000.

Default address:

    http://127.0.0.1:8880

## Install

### 1. Via release

Install the release, then run the `.exe`.

### 2. Via the `.py` file

#### Requirements

- Python **3.10+**
- [Pillow](https://python-pillow.org) `>= 10.0`
- **foobar2000** with the [Beefweb](https://github.com/hyperblast/beefweb) component, listening on `http://127.0.0.1:8880` (the default).
- Tkinter (bundled with Python on Windows/macOS; `python3-tk` on Linux).
