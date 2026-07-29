"""GATE: the toolchain is instrument identity, and it drifts silently.

The ledger pins 252 axioms and gates 5 derivations against them. **None of that constrains the kernel
that checks the proofs.** A kernel bug is invisible to every footprint gate in this repo by
construction — `#print axioms` reports what a proof *depends on*, not whether the checker was right
to accept it.

lean4 **#14576** ("Kernel accepts wrong-structure projections, allowing an axiom-free proof of
False", fixed 2026-07-28) is the concrete reason this file exists. See `TOOLCHAIN_EXPOSURE.md`.

BOTH DIRECTIONS, same as every correspondence gate here:
  pin changed, lock not updated   -> FAIL. The recorded instrument is not the one in use.
  lock changed, pin not updated   -> FAIL. Equally wrong, and the direction that feels safe.

Run: python3 tools/axiom_ledger/check_toolchain.py
"""
from __future__ import annotations

import os
import re
import subprocess
import sys

FOUND = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LOCK = os.path.join(FOUND, "TOOLCHAIN.lock")
PIN = os.path.join(os.path.dirname(FOUND), "lean-toolchain")


def main() -> int:
    problems: list[tuple[str, str]] = []
    if not os.path.exists(LOCK):
        print("[NO_LOCK] TOOLCHAIN.lock missing -- the instrument is unrecorded, i.e. UNGATED.")
        return 1
    want = [l.strip() for l in open(LOCK) if l.strip()]
    pin_path = PIN if os.path.exists(PIN) else os.path.join(FOUND, "lean-toolchain")
    have_pin = open(pin_path).read().strip()

    out = subprocess.run(["lean", "--version"], capture_output=True, text=True,
                         cwd=FOUND).stdout
    m = re.search(r"commit ([0-9a-f]+)", out)
    have_commit = m.group(1) if m else "UNKNOWN"

    print(f"lock  : {want[0]}  {want[1] if len(want) > 1 else ''}")
    print(f"in use: {have_pin}  {have_commit}")

    if have_pin != want[0]:
        problems.append(("PIN_DRIFT",
                         f"lean-toolchain says {have_pin!r}, lock says {want[0]!r}. One of them "
                         f"changed without the other -- the recorded instrument is not the one "
                         f"checking the proofs."))
    if len(want) > 1 and have_commit != "UNKNOWN" and not want[1].startswith(have_commit[:12]):
        problems.append(("COMMIT_DRIFT",
                         f"running kernel commit {have_commit}, lock says {want[1]}."))

    print()
    if problems:
        print("TOOLCHAIN GATE: FAIL")
        for c, msg in problems:
            print(f"  [{c}] {msg}")
        print("\n  If the bump is INTENTIONAL: update TOOLCHAIN.lock in the same commit, and "
              "re-read\n  TOOLCHAIN_EXPOSURE.md -- the exposure section is version-specific.")
        return 1
    print("TOOLCHAIN GATE: PASS -- the instrument in use is the instrument on record.")
    print("  NOTE: this gate checks IDENTITY, not soundness. It cannot see a kernel bug; that is")
    print("  what independent re-checking is for. See TOOLCHAIN_EXPOSURE.md.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
