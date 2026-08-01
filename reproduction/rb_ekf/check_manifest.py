#!/usr/bin/env python3
"""GATE: every file in this package matches MANIFEST.sha256, and the manifest covers every file.

## Why this exists

This package VENDORS copies of files whose originals live in another repository. **A vendored copy
is a fork.** Within one hour of publishing it, a fix landed upstream in `forge` and the copy here
silently kept the old behaviour -- the reproduction re-walk failed on a bug that had already been
fixed, and the failure pointed at a defect that no longer existed.

The manifest already records what each file's bytes ARE. This checks that they still are, and that
nothing was added without being recorded. It cannot detect upstream drift by itself -- **for that,
compare the hashes here against the upstream identity printed in `README.md`** -- but it does make
"somebody edited a vendored file in place" impossible to do quietly.

BOTH DIRECTIONS:
    MISMATCH   a file's bytes differ from its recorded hash
    UNLISTED   a file exists that the manifest does not record
    MISSING    the manifest records a file that is not here

Exit: 0 the package matches its manifest · 1 it does not · 2 the gate could not run.

Usage:  python3 check_manifest.py
"""
from __future__ import annotations

import hashlib
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "MANIFEST.sha256"
SELF = "check_manifest.py"

G, R, Y, RST, B = "\033[32m", "\033[31m", "\033[33m", "\033[0m", "\033[1m"


def lf_sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def listed() -> dict[str, str]:
    out: dict[str, str] = {}
    for line in MANIFEST.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split(None, 2)
        if len(parts) == 3:
            out[parts[2]] = parts[0]
    return out


def on_disk() -> dict[str, str]:
    return {
        str(p.relative_to(HERE)): lf_sha256(p)
        for p in sorted(HERE.rglob("*"))
        if p.is_file()
        and p.name not in (MANIFEST.name, SELF)
        and "__pycache__" not in p.parts
    }


def main() -> int:
    if not MANIFEST.is_file():
        print(f"{Y}{B}MANIFEST CHECK UNAVAILABLE{RST} — no MANIFEST.sha256 beside this script.")
        return 2

    want, have = listed(), on_disk()
    if not want:
        print(f"{Y}{B}MANIFEST CHECK UNAVAILABLE{RST} — the manifest lists no files; "
              f"an empty manifest cannot certify anything.")
        return 2

    mismatch = sorted(f for f in have if f in want and have[f] != want[f])
    unlisted = sorted(f for f in have if f not in want)
    missing = sorted(f for f in want if f not in have)

    print(f"MANIFEST CHECK — {len(want)} recorded, {len(have)} on disk")
    if not (mismatch or unlisted or missing):
        print(f"{G}{B}MANIFEST PASS{RST} — every file present and byte-identical to its record.")
        return 0

    print(f"{R}{B}MANIFEST FAIL{RST}:")
    for label, names in (("MISMATCH (bytes differ from the record)", mismatch),
                         ("UNLISTED (on disk, not in the manifest)", unlisted),
                         ("MISSING  (in the manifest, not on disk)", missing)):
        if names:
            print(f"  {R}{label}: {len(names)}{RST}")
            for n in names:
                print(f"      {n}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
