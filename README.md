# foobar_fullscreen_lyrics

A fullscreen lyrics app for **foobar2000 x86**, made to provide a fullscreen music/lyrics experience without needing to work around **SMTC** or Windows media controls.

## General requirements

- **foobar2000** with the [Beefweb](https://github.com/hyperblast/beefweb) component, listening on `http://127.0.0.1:8880` (the default).


Default address:

    http://127.0.0.1:8880

## Install

### 1. Via release

Install the release, then run the `.exe`.

### 2. Via the `.pyw` file

#### Requirements

- Python **3.10+**
- [Pillow](https://python-pillow.org) `>= 10.0`
- **foobar2000** with the [Beefweb](https://github.com/hyperblast/beefweb) component, listening on `http://127.0.0.1:8880` (the default).
- Tkinter (bundled with Python on Windows/macOS; `python3-tk` on Linux).

Just double click it

## keyboard controls

- `P` — open/close playlist panel
- `Enter` — play selected item (panel)
- `Delete` — remove selected item (panel)
- `Ctrl+Up/Down` — move selected item (panel)
- `Up/Down` — move selection (panel / settings)
- `Left/Right` — switch playlist (panel) / change setting (settings panel)
- `R` — refetch lyrics — or refresh playlists when panel is open
- `S` — settings panel
- `V` — toggle translation
- `F` — follow current line
- `F11 / Esc` — fullscreen toggle / leave
- `Space` — play / pause
