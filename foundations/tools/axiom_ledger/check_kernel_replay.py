"""GATE: replay the compiled environment through an EXTERNAL kernel.

## Why this exists, and why it outranks bumping the pin

Every footprint gate in this repo is blind to kernel bugs BY CONSTRUCTION. `#print axioms` reports
what a proof *depends on*, never whether the checker was right to accept it. lean4 **#14576**
("Kernel accepts wrong-structure projections, allowing an axiom-free proof of False", fixed
2026-07-28) is the concrete case: our pin is v4.14.0, eighteen minor versions behind that fix.

There are two responses and they are not two fixes for one problem:

* **bump the pin** — retires #14576 and eighteen versions of drift, costs a migration across custom
  elaborators and match compilation, and at the end you trust ONE kernel again, just a newer one.
* **replay through a second checker** — runs against the current pin TODAY, no migration, and
  converts "is v4.14.0 sound on our 68 inductives" from unknowable-by-reading into mechanically
  checked on every build. It also partially discharges #14576 directly: if the external checker's
  projection handling does not share the defect, a clean replay is evidence the exploit class is not
  present in OUR code, whatever the kernel would accept in principle.

**Bumping fixes the instance. Replay fixes the class.** Hence this first.

## THE INDEPENDENCE CAVEAT — and the row must say which checker ran

`lean4checker` **shares the kernel's C++ lineage in part.** Against *environment manipulation* —
tactics smuggling unchecked declarations into the environment — it defends at full strength: that is
exactly what its five negative tests exercise. Against *kernel-implementation bugs* its independence
is **partial**, because it re-uses the same kernel implementation to do the checking.

**Lean4Lean** is the genuinely independent re-implementation. The strongest configuration is replay
through **both**.

So this gate earns the phrase *"second opinion"*, and does **not** yet earn *"independent kernel"*.
Only running Lean4Lean would earn the latter, and the difference is not cosmetic — it is which class
of defect two implementations would have to share.

## Two checks

1. **The instrument works.** Run lean4checker's own five negative tests (`AddFalse`,
   `AddFalseConstructor`, `ReplaceAxiom`, `UseFalseConstructor --fresh`, `ReduceBool`). Each must
   FAIL with its expected kernel error. **Historical specimens, pre-built, verified firing here** —
   a checker that has not been seen to reject anything is not a checker.
2. **The environment replays.** `lean4checker MachLib` must exit 0.

UNAVAILABLE IS FAILURE: if the checker is missing or version-mismatched, this gate FAILS rather than
skipping. A soundness check that quietly does not run is worse than none.

Run: python3 tools/axiom_ledger/check_kernel_replay.py
"""
from __future__ import annotations

import os
import subprocess
import sys

FOUND = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def resolve_checker(want: str) -> str:
    """ONE CHECKER PER STOP, because the migration rolls back.

    Added 2026-07-29 for the toolchain bump. The checker must match the pin exactly -- that rule is
    unchanged and enforced below. What changes is *where* it lives: `~/lean4checker-v4.16.0` is
    preferred over `~/lean4checker` when it exists.

    Why not just re-`checkout` the one directory at each stop: the frozen baseline's replay log would
    stop being reproducible the moment the instrument that produced it was overwritten, and every
    fallback position (`BUMP_PLAN.md`: each clean intermediate is one) would need a checker rebuild
    before it could be re-verified. Keeping them side by side makes rollback a `git checkout`, not a
    rebuild.
    """
    ver = want.split(":")[-1]
    versioned = os.path.expanduser(f"~/lean4checker-{ver}")
    return versioned if os.path.exists(versioned) else os.path.expanduser("~/lean4checker")


def main() -> int:
    want = open(os.path.join(FOUND, "TOOLCHAIN.lock")).read().split()[0]
    CHECKER = resolve_checker(want)
    BIN = os.path.join(CHECKER, ".lake", "build", "bin", "lean4checker")
    print(f"checker path     : {CHECKER}")
    if not os.path.exists(BIN):
        ver = want.split(":")[-1]
        print(f"[CHECKER_ABSENT] no lean4checker at {BIN}")
        print("  UNAVAILABLE IS FAILURE. Build it:")
        print(f"    git clone --branch {ver} --depth 1 \\")
        print(f"        https://github.com/leanprover/lean4checker ~/lean4checker-{ver}")
        print(f"    cd ~/lean4checker-{ver} && lake build && ./test.sh")
        print("  The tag MUST match TOOLCHAIN.lock -- a checker built against a different kernel")
        print("  is a different instrument.")
        return 1

    have = open(os.path.join(CHECKER, "lean-toolchain")).read().strip()
    print(f"checker toolchain: {have}")
    print(f"ledger  toolchain: {want}")
    if have != want:
        print(f"\n[CHECKER_VERSION_MISMATCH] the checker was built against {have}, we pin {want}. "
              f"A checker built on a different kernel is a different instrument.")
        return 1

    print("\n1 INSTRUMENT WORKS (lean4checker's own 5 negative tests must all FAIL correctly)")
    t = subprocess.run(["./test.sh"], cwd=CHECKER, capture_output=True, text=True)
    ok1 = t.returncode == 0 and "All commands produced the expected errors" in t.stdout
    print(f"    {'PASS -- all five rejected as expected' if ok1 else 'FAIL'}")
    if not ok1:
        print("   ", (t.stdout + t.stderr).strip()[-500:])

    print("\n2 ENVIRONMENT REPLAYS through the external kernel")
    r = subprocess.run(["lake", "env", BIN, "MachLib"], cwd=FOUND, capture_output=True, text=True)
    ok2 = r.returncode == 0
    print(f"    {'PASS -- MachLib re-checks clean' if ok2 else 'FAIL'}")
    if not ok2:
        print("   ", (r.stdout + r.stderr).strip()[-600:])

    print()
    if ok1 and ok2:
        print("KERNEL-REPLAY GATE: PASS")
        print("  Grade: SECOND OPINION, not INDEPENDENT KERNEL. lean4checker shares the kernel's")
        print("  C++ lineage in part -- full strength against environment manipulation, PARTIAL")
        print("  independence against kernel-implementation bugs. Lean4Lean would earn the")
        print("  stronger phrase and is not yet running.")
        return 0
    print("KERNEL-REPLAY GATE: FAIL")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
