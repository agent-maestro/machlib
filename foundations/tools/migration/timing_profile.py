"""Elaboration-cost profile of the budget-sensitive modules, captured once per stop.

## Why this exists — the lake-clean lesson, inverted

Stop 1 found `mach_ring`'s permutative catch-all crossing a heartbeat cliff, and then could not answer
*"did the catch-all get slower, or did phase 1 hand it a harder goal?"* — because the `lake clean` that
kept the v4.14.0 `.olean`s from being read by a v4.16.0 kernel also destroyed the only tree that could
have been timed. **The hygiene was right and it cost the measurement.**

    A measurement baseline is an ARTIFACT. Artifacts that a later question will need get
    snapshotted BEFORE hygiene destroys them.

So this runs **before every pin advance**, and *"did X get slower across stop N"* becomes a diff of two
numbers instead of a scheduled excavation of a deleted build tree.

## What it measures, and what it deliberately does not

Wall-clock elaboration of each flagged module, `lake env lean <module>` from source with its
dependencies already built. Not heartbeats: heartbeats are what the *budget* is denominated in, but
they are not comparable across kernel versions in the way a stopwatch is, and the question this answers
is "did this get more expensive", which is a stopwatch question.

**The flagged set is DERIVED, never listed here:** every module containing `set_option maxHeartbeats`
is by its own admission budget-sensitive. That list maintains itself as the library changes, which a
hardcoded one would not (and would be a second place for it to rot).

**Comparability protocol:** same machine, same `--workers` (default 4). Ratios across stops are the
signal; absolute seconds are not portable. A profile captured at a different worker count is a
different instrument, so the count is recorded in the file.

    python3 tools/migration/timing_profile.py                       # capture for the current pin
    python3 tools/migration/timing_profile.py --diff snapshots/timing/v4.16.0.json \
                                                     snapshots/timing/v4.19.0.json
"""
from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
import re
import subprocess
import time

FOUND = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
OUT = os.path.join(FOUND, "snapshots", "timing")
REGRESSION_RATIO = 1.5


def flagged_modules() -> list[str]:
    """Every module that raises its own heartbeat budget -- derived, so the set cannot go stale."""
    lib = os.path.join(FOUND, "MachLib")
    out = []
    for f in sorted(os.listdir(lib)):
        if f.endswith(".lean"):
            p = os.path.join(lib, f)
            if "set_option maxHeartbeats" in open(p, encoding="utf-8").read():
                out.append(f"MachLib/{f}")
    return out


def time_one(mod: str) -> tuple[str, float, int]:
    t0 = time.monotonic()
    p = subprocess.run(["lake", "env", "lean", mod], cwd=FOUND,
                       capture_output=True, text=True)
    return mod, round(time.monotonic() - t0, 2), p.returncode


def capture(workers: int) -> dict:
    mods = flagged_modules()
    print(f"profiling {len(mods)} budget-sensitive modules at {workers} workers "
          f"(derived from `set_option maxHeartbeats`)\n")
    results: dict[str, dict] = {}
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
        for mod, secs, code in ex.map(time_one, mods):
            results[mod] = {"seconds": secs, "exit": code}
            print(f"  {secs:7.2f}s  exit {code}  {mod}")
    toolchain = open(os.path.join(FOUND, "lean-toolchain")).read().strip()
    total = round(sum(r["seconds"] for r in results.values()), 2)
    print(f"\ntotal {total}s across {len(results)} modules")
    return {"toolchain": toolchain, "captured_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
            "workers": workers, "total_seconds": total, "modules": results}


def diff(a_path: str, b_path: str) -> int:
    a, b = json.load(open(a_path)), json.load(open(b_path))
    print(f"before: {a['toolchain']}  total {a['total_seconds']}s  ({a['workers']} workers)")
    print(f"after : {b['toolchain']}  total {b['total_seconds']}s  ({b['workers']} workers)")
    if a["workers"] != b["workers"]:
        print("\n[INCOMPARABLE] different worker counts -- a profile at a different parallelism is a")
        print("               different instrument. Re-capture one of them to match.")
        return 1

    rows = []
    for m, rb in b["modules"].items():
        ra = a["modules"].get(m)
        if ra and ra["seconds"] > 0.5:  # ignore sub-second noise
            rows.append((rb["seconds"] / ra["seconds"], m, ra["seconds"], rb["seconds"]))
    rows.sort(reverse=True)

    print(f"\nslowest {min(8, len(rows))} by ratio:")
    for ratio, m, sa, sb in rows[:8]:
        mark = "  <-- REGRESSION" if ratio >= REGRESSION_RATIO else ""
        print(f"  {ratio:5.2f}x  {sa:7.2f}s -> {sb:7.2f}s  {m}{mark}")

    gone = sorted(set(a["modules"]) - set(b["modules"]))
    new = sorted(set(b["modules"]) - set(a["modules"]))
    for m in gone:
        print(f"  no longer budget-sensitive (or removed): {m}")
    for m in new:
        print(f"  newly budget-sensitive: {m}  ({b['modules'][m]['seconds']}s)")

    regressions = [r for r in rows if r[0] >= REGRESSION_RATIO]
    print(f"\nmodules at or past {REGRESSION_RATIO}x: {len(regressions)}")
    print("\nThis is EVIDENCE, not a gate. A slower module is not a failed stop -- it is the answer to")
    print("\"did this get more expensive\", available in seconds instead of requiring a rebuilt tree.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--diff", nargs=2, metavar=("BEFORE", "AFTER"))
    a = ap.parse_args()
    if a.diff:
        return diff(*a.diff)
    prof = capture(a.workers)
    os.makedirs(OUT, exist_ok=True)
    path = os.path.join(OUT, prof["toolchain"].split(":")[-1] + ".json")
    json.dump(prof, open(path, "w"), indent=1)
    print(f"wrote {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
