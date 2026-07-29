"""WATCH: has the kernel-configuration decision expired yet?

## Why this file exists

`BUMP_PLAN.md`'s decision record chooses **v4.26.0 — unpatched kernel, two independent checkers** over
**v4.32.2 — patched kernel, one checker**, and the whole argument rests on one empirical fact:

    fix ∩ lean4checker ∩ Lean4Lean = ∅        (true on 2026-07-29)

**That is a fact about July 2026, not a fact about software.** A decision recorded as permanent when it
is calendar-contingent rots in the reassuring direction — the record keeps reading "considered, with
the tradeoff owned" long after the consideration expired. So the expiry condition is *monitored*:

    python3 tools/migration/watch_kernel_support.py

    exit 0  nothing has opened; the decision still holds (movement below the threshold is reported)
    exit 2  PARTIAL — one external checker reaches the fix. Leg 2 can launch; grade needs a re-read
    exit 3  OPEN — the intersection is non-empty. The decision has EXPIRED; re-read BUMP_PLAN.md
    exit 1  the watch could not run

## UNAVAILABLE IS FAILURE

An offline run must never be readable as *"still empty"*. That is the same reassuring-direction error
the whole record is written against, so a network failure exits **1** and says so, and never prints a
verdict about the intersection it could not observe.

## What counts as "supported", and why the two sources are asymmetric

* **lean4checker** publishes a tag per release, so its support set is *the set of stable tags*.
  Release-candidate tags are excluded: a checker built from an `-rc` toolchain is a different
  instrument from the stable kernel it would be checking, and `check_kernel_replay.py` rejects exactly
  that mismatch.
* **Lean4Lean** has no tags for this purpose; `.olean` format is version-locked, so it supports
  **exactly the version its `lean-toolchain` pins** — not a range. Hence its support set is a
  singleton, read from the file at `master`.

The threshold — the first release carrying the #14577 kernel fix — is a **historical constant with
provenance** (v4.32.2 release notes: *"fixes a soundness bug in the kernel… nested inductive types
with phantom type parameters"*), not a count, so it is written down here rather than derived.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request

FIX = (4, 32, 2)  # first release containing #14577; see docstring
CHECKER_REPO = "https://github.com/leanprover/lean4checker"
L4L_PIN_URL = "https://raw.githubusercontent.com/digama0/lean4lean/master/lean-toolchain"
STATE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "watch_state.json")


def ver(s: str) -> tuple[int, ...]:
    return tuple(int(x) for x in s.lstrip("v").split("."))


def fmt(v: tuple[int, ...]) -> str:
    return "v" + ".".join(str(x) for x in v)


def checker_stable_tags() -> list[tuple[int, ...]]:
    p = subprocess.run(["git", "ls-remote", "--tags", CHECKER_REPO],
                       capture_output=True, text=True, timeout=120)
    if p.returncode != 0:
        raise RuntimeError(f"git ls-remote {CHECKER_REPO} failed: {p.stderr.strip()[:200]}")
    tags = set()
    for m in re.finditer(r"refs/tags/v(\d+\.\d+(?:\.\d+)?)$", p.stdout, re.M):
        tags.add(ver(m.group(1)))
    if not tags:
        raise RuntimeError("no stable vX.Y.Z tags parsed — the tag scheme changed, or the parse did")
    return sorted(tags)


def l4l_pin() -> tuple[str, tuple[int, ...] | None]:
    with urllib.request.urlopen(L4L_PIN_URL, timeout=60) as r:
        raw = r.read().decode().strip()
    m = re.search(r"v(\d+\.\d+(?:\.\d+)?)$", raw)
    return raw, (ver(m.group(1)) if m else None)


def load_state() -> dict:
    return json.load(open(STATE)) if os.path.exists(STATE) else {}


def report_movement(prev: dict, checker_max: tuple[int, ...], pin: tuple[int, ...] | None) -> None:
    if not prev:
        print("no previous observation on file — this run establishes the reference point.")
        return
    print(f"since {prev['observed_at'][:10]}:")
    for label, was, now in (("lean4checker max stable tag", prev.get("checker_max"), fmt(checker_max)),
                            ("Lean4Lean pin", prev.get("l4l_pin"), fmt(pin) if pin else "unparsed")):
        print(f"  {label:<28} {was} -> {now}" + ("   (moved)" if was != now else "   (unchanged)"))


def main() -> int:
    print(f"KERNEL-SUPPORT WATCH   threshold = {fmt(FIX)} (first release with the #14577 fix)\n")
    try:
        tags = checker_stable_tags()
        raw_pin, pin = l4l_pin()
    except (subprocess.TimeoutExpired, urllib.error.URLError, OSError, RuntimeError) as e:
        print(f"[WATCH_UNAVAILABLE] {type(e).__name__}: {e}")
        print("\nUNAVAILABLE IS FAILURE. This run observed NOTHING and asserts nothing about the")
        print("intersection. Re-run with network access; do not read this as 'still empty'.")
        return 1

    checker_max = tags[-1]
    print(f"lean4checker stable tags : {len(tags)}, newest {fmt(checker_max)}")
    print(f"Lean4Lean pin (master)   : {raw_pin}")
    print()
    report_movement(load_state(), checker_max, pin)

    checker_ok = checker_max >= FIX
    l4l_ok = pin is not None and pin >= FIX
    both = pin is not None and pin in tags and pin >= FIX

    print(f"\nlean4checker reaches the fix : {'YES ' + fmt(checker_max) if checker_ok else 'no'}")
    print(f"Lean4Lean reaches the fix    : {'YES ' + fmt(pin) if l4l_ok else 'no'}")

    json.dump({"observed_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
               "threshold": fmt(FIX), "checker_max": fmt(checker_max),
               "checker_tag_count": len(tags), "l4l_pin": fmt(pin) if pin else raw_pin,
               "intersection_open": both},
              open(STATE, "w"), indent=1)

    print()
    if both:
        print(f"INTERSECTION OPEN at {fmt(pin)} — THE DECISION HAS EXPIRED.")
        print("  Both checkers reach a kernel carrying the fix. The dual-kernel and patched-kernel")
        print("  configurations are no longer alternatives: re-read BUMP_PLAN.md's decision record,")
        print("  retarget the destination to the newest member of the intersection, and note in the")
        print("  record that the tradeoff it defends no longer exists.")
        return 3
    if checker_ok or l4l_ok:
        which = "lean4checker" if checker_ok else "Lean4Lean"
        print(f"PARTIAL — {which} reaches the fix; the other does not.")
        print("  Leg 2's launch condition (at least one external checker at the destination) is MET,")
        print("  so the migration may proceed to the fix — but the grade drops to whatever that one")
        print("  checker earns. If it is lean4checker alone, that is SECOND OPINION, not independent")
        print("  kernel, and the registry row must say so.")
        return 2
    print("STILL EMPTY — the decision holds, and the wait remains monitored rather than standing.")
    print("  Cheapest way to open it from our side: contribute the lean4checker tag upstream. Its")
    print("  history is mechanical per release, so it is plausibly a PR, not a project.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
