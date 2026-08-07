#!/usr/bin/env python3
"""Reliability battery for TRIM — same teeth as `trim check`. Exit 3 on fail."""
from __future__ import annotations
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
import TRIM  # noqa: E402

if __name__ == "__main__":
    info = TRIM.reliability_battery()
    if info.get("failed"):
        print("CHECK FAIL", info)
        sys.exit(3)
    print("CHECK OK", {k: info[k] for k in info if k != "failed"})
