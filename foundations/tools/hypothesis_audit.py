#!/usr/bin/env python3
"""Propositions that are CONSUMED as hypotheses and never PRODUCED.

WHY THIS EXISTS
---------------
`tools/witness_audit.py` watches one half of "conditional theorem, unvalidated": a capstone whose
hypotheses nobody supplies. On 2026-08-27 the corpus produced the other half and nearly shipped it.

`ValueGapBound` was introduced, then taken as a hypothesis by two theorems -- and NOTHING SATISFIED
IT, at any depth. The `positive_branch_impossible` tell-tale was "no caller and no specimen"; this
had CALLERS BUT NO SPECIMEN.

  A Prop with consumers and no producers is not exercised; it is ASSUMED.

That is the easy half to miss, precisely because the consumers make it look exercised. Half the
tell-tale is not half the warning -- it reads as no warning at all. This script measures it.

WHAT IT CHECKS, AND WHAT IT CANNOT
-----------------------------------
For every `def P ... : Prop` under `MachLib/`, it counts:

  producers  theorems whose CONCLUSION is `P ...`   (an `<->` is not a producer -- see canary 9 of
                                                     obligation_ledger_check for why)
  consumers  theorems taking `(h : P ...)`          -- the same test the ledger's `assumes` uses

and reports those with consumers >= 1 and producers == 0. Scope, stated plainly:

  * MANY SUCH PROPS ARE CORRECT. A named open obligation is meant to have consumers and no
    producer -- that is what "open" means. This is a ratchet against a pinned set, not a pass/fail
    on zero, exactly as in witness_audit.
  * It is SYNTACTIC. It asks "does anything conclude this", not "is what concludes it meaningful".
    A producer may itself be vacuous; only a specimen discharging every hypothesis at a concrete
    point sees that. This catches the shape, not the substance.
  * A Prop with NEITHER consumers nor producers is not reported. Nothing is resting on it, so
    nothing is being assumed; that is dead code, which the aggregator gate covers.

So: this catches a hypothesis silently becoming an assumption, not unsoundness.

THE BASELINE IS A SET, NOT A COUNT
-----------------------------------
Same reasoning as witness_audit: a count can stay flat while one entry gains a producer and another
loses one. Pinning names makes the ratchet turn one way -- a NEW unproduced hypothesis fails, and a
fixed one must be removed from the list.

Exit 0 pass, 1 drift, 2 could not read (UNAVAILABLE, never a pass).
"""
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from obligation_ledger_check import declarations, dischargers_of  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
SOURCES = sorted((ROOT / "MachLib").glob("*.lean"))
BASELINE = Path(__file__).resolve().parent / "hypothesis_baseline.json"


def prop_defs(decls):
    """Names of `def P ... : Prop` declarations."""
    out = []
    for kind, name, sig in decls:
        if not kind.endswith("def"):
            continue
        if re.search(r":\s*Prop\s*$", sig.strip()):
            out.append(name)
    return out


def consumers_of(prop, decls):
    """Theorems taking `(h : P ...)` -- the ledger's `assumes` test, widened to allow arguments."""
    out = []
    for kind, name, sig in decls:
        if not kind.endswith("theorem"):
            continue
        if re.search(r"\([^()]*:\s*" + re.escape(prop) + r"(\s|\)|$)", sig):
            out.append(name)
    return out


def unproduced(decls):
    """`{prop: [consumers]}` for props consumed but never concluded."""
    found = {}
    for p in prop_defs(decls):
        if dischargers_of(p, decls):
            continue
        cs = consumers_of(p, decls)
        if cs:
            found[p] = sorted(cs)
    return found


def self_test(decls) -> int:
    """Convict specimens. Synthetic declarations, so none can go stale as the corpus improves."""
    ok = True

    # 1. consumed, never produced -- the shape this script exists for.
    d = [("def", "CanaryProp", "def CanaryProp : Prop"),
         ("theorem", "eats", "theorem eats (h : CanaryProp) : True")]
    fired = list(unproduced(d)) == ["CanaryProp"]
    print(f"  canary 1 (consumed, never produced)          {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 2. DISCRIMINATION: add a producer and it must go quiet. Without this the script would only
    #    be saying that hypotheses are suspicious.
    d2 = d + [("theorem", "makes", "theorem makes : CanaryProp")]
    quiet = unproduced(d2) == {}
    print(f"  canary 2 (a producer silences it)            {'SILENT' if quiet else 'FIRES'}")
    ok &= quiet

    # 3. DISCRIMINATION: no consumer either -- nothing rests on it, so nothing is assumed. Dead
    #    code is the aggregator's job, not this one's.
    d3 = [("def", "CanaryProp", "def CanaryProp : Prop")]
    quiet = unproduced(d3) == {}
    print(f"  canary 3 (unused Prop is not this gate's job) {'SILENT' if quiet else 'FIRES'}")
    ok &= quiet

    # 4. An `<->` is not a producer. Same rule as the ledger's canary 9, and the reason it exists:
    #    `foo : P <-> Q` prefix-matches `P` and would otherwise read as concluding it.
    d4 = d + [("theorem", "iffy", "theorem iffy : CanaryProp ↔ Something")]
    fired = list(unproduced(d4)) == ["CanaryProp"]
    print(f"  canary 4 (an ↔ is not a producer)            {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    print()
    if not ok:
        print("HYPOTHESIS-AUDIT SELF-TEST FAIL — a canary did not fire; the gate is unvalidated")
        return 1
    print("HYPOTHESIS-AUDIT SELF-TEST PASS — every convict specimen fires")
    return 0


def main() -> int:
    decls = []
    for src in SOURCES:
        decls.extend(declarations(src.read_text()))
    if not decls:
        print("UNAVAILABLE: no declarations parsed from MachLib/*.lean", file=sys.stderr)
        return 2

    if "--self-test" in sys.argv:
        rc = self_test(decls)
        if rc:
            return rc
        print()

    found = unproduced(decls)

    if "--update-baseline" in sys.argv:
        BASELINE.write_text(json.dumps(
            {"_comment": "Props consumed as hypotheses with no theorem concluding them. "
                         "A SET, not a count: a new entry fails, a fixed one must be removed. "
                         "Most entries are correct — a named open obligation is meant to be here.",
             "unproduced": sorted(found)}, indent=2) + "\n")
        print(f"baseline written: {len(found)} entries")
        return 0

    if not BASELINE.exists():
        print(f"UNAVAILABLE: {BASELINE} not found — run with --update-baseline", file=sys.stderr)
        return 2
    pinned = set(json.loads(BASELINE.read_text())["unproduced"])
    now = set(found)

    bad = 0
    for p in sorted(now - pinned):
        print(f"  NEW    {p}: consumed by {', '.join(found[p])}, concluded by nothing")
        bad += 1
    for p in sorted(pinned - now):
        print(f"  FIXED  {p}: now has a producer — remove it from the baseline")
        bad += 1

    print()
    if bad:
        print(f"HYPOTHESIS-AUDIT DRIFT — {bad} change(s) against the pinned set")
        return 1
    print(f"HYPOTHESIS-AUDIT OK — {len(now)} consumed-but-unproduced props, exactly the pinned set")
    return 0


if __name__ == "__main__":
    sys.exit(main())
