# harness_trim

`TRIM.py` — trim **LLM harness stores only** (Cursor / Codex / Claude).

Stdlib-only single file. No pip deps.

## Install

```bash
git clone https://github.com/ivp5/harness_trim.git
cd harness_trim
./install.sh          # symlinks ~/bin/trim → TRIM.py
# ensure ~/bin is on PATH
trim
```

Or run directly: `python3 TRIM.py`

## Commands

```
trim              # menu
trim map          # harness store inventory
trim list         # sessions by size
trim free         # clutter preview, then asks (never live store.db)
trim cut          # pick chat + level (default safe = 160 turns)
trim cut safe     # or normal | tight
trim check        # reliability battery
trim doctor
```

Confirm destructive steps by typing `yes`. No flags.

## Safety

| command | notes |
|--------|--------|
| `free` | Preview first; skips locked chats; **never** touches live `store.db`. Removal is `mv` → macOS Trash only. Cut undo siblings (`bloated-*` / `.pretrim-*`) are never auto-retired. |
| `cut` | Refuses if locked; falsify+smoke before install; fat kept as `bloated-*`. Live store drops old turns. Default **safe** (160 turns). |

## Check

```bash
python3 TRIM.py check
# or
python3 test_reliability.py
```

## License

MIT
