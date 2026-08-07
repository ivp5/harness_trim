#!/usr/bin/env bash
# Install entrypoints that point at this TRIM.py (stdlib-only single file).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
CANON="$ROOT/TRIM.py"
test -f "$CANON"

mkdir -p "$HOME/.cursor" "$HOME/bin"
# One file, no runpy shim — same inode via symlink.
ln -sfn "$CANON" "$HOME/.cursor/TRIM.py"
ln -sfn "$CANON" "$HOME/bin/trim"
chmod +x "$CANON"

echo "Installed (self-contained TRIM.py):"
echo "  $CANON"
echo "  $HOME/.cursor/TRIM.py → $CANON"
echo "  $HOME/bin/trim → $CANON"
