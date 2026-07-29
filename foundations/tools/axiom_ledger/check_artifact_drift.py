"""TRIPWIRE: does the artifact tree assert declarations the source tree no longer makes?

## The defect class, named because it was new to the taxonomy

**BUILD-ARTIFACT DRIFT.** The broken correspondence is `source-tree ↔ artifact-tree`, and it is the
evil twin of emission determinism: `f47f6c81` proved *source → artifact* is deterministic **for what
gets built**; nothing checked what **stopped** being built. `.lake/build/` accumulates the `.olean`
files of deleted and renamed modules, and **no live path ever looks** — because nothing imports them.

Per the AxiomLedger rule it broke in the direction that feels safe: **deletion**. Removing a scratch
module, renaming a file, moving a theorem to a better home. Found 2026-07-29 by the external kernel
replay, which was installed to defend against kernel bugs and whose first catch was **provenance**:

```
lean4checker found a problem in MachLib.ZZZTestSign
uncaught exception: (kernel) constant has already been declared
  'MachLib.Real.growthCompetitionWitness_deriv_pos_of_quad_pos'
```

26 orphaned modules, one still declaring a theorem that had **moved** — so the tree held it in two
places at once. Anyone auditing that tree (a reviewer, a reproduction attempt, a diligence engineer)
would have received all 26.

## Why a tripwire as well as the checker

The orphan condition is detectable **without replay** — enumerate, enumerate, diff. Seconds, not
minutes. So: **tripwire for the correspondence, checker for the semantics**, the same two-tier shape
as the status-layout lock sitting over the RTL. This one fires the moment a module is deleted or
renamed; the replay remains the deep verification that corresponding artifacts *replay clean*.

## House rule this file obeys

**A summary asserting absence must be COMPUTED, never written.** `orphans=0` printed by the code that
did the enumeration — never "empty above" typed next to a listing. Three reassuring-label errors in
this project were caught only on deliberate re-read, all in the reassuring direction, because nobody
audits good news. The summary and the enumeration must share provenance.

Run: python3 tools/axiom_ledger/check_artifact_drift.py
"""
from __future__ import annotations

import os
import pathlib
import sys

FOUND = pathlib.Path(__file__).resolve().parent.parent.parent
LIB = FOUND / ".lake" / "build" / "lib"
SRC = FOUND


def main() -> int:
    if not LIB.exists():
        print(f"[NO_BUILD] {LIB} missing -- nothing to compare. Build first; an unbuilt tree is "
              f"not a clean tree.")
        return 1

    # Enumerate BOTH trees recursively. The earlier manual pass compared only top-level files and
    # a hand-typed label claimed "no subdirs" while MachLib/Tactic and MachLib/Applications exist.
    # The comparison happened to remain valid; the label did not. Hence: recurse, and compute.
    oleans = {p.relative_to(LIB).with_suffix("") for p in LIB.rglob("*.olean")}
    sources = {p.relative_to(SRC).with_suffix("") for p in SRC.rglob("*.lean")
               if ".lake" not in p.parts}

    orphans = sorted(oleans - sources)
    unbuilt = sorted(sources - oleans)

    print(f"artifact tree : {len(oleans)} .olean")
    print(f"source tree   : {len(sources)} .lean")
    print(f"ORPHANED      : {len(orphans)}   (artifact with no source)")
    print(f"unbuilt       : {len(unbuilt)}   (source with no artifact -- informational)")

    if orphans:
        print("\nORPHANS -- these declarations exist in the build tree and NOWHERE in source:")
        for o in orphans[:30]:
            print(f"    {o}")
        if len(orphans) > 30:
            print(f"    ... and {len(orphans) - 30} more")
        print("\nARTIFACT-DRIFT TRIPWIRE: FAIL")
        print("  The build tree asserts declarations the source tree does not make. Anyone")
        print("  auditing or reproducing from this tree would receive them.")
        print("  Fix: `lake clean && lake build`, or delete the specific stale artifacts.")
        return 1

    print("\nARTIFACT-DRIFT TRIPWIRE: PASS -- every artifact has a source.")
    print("  Scope: this checks the source↔artifact CORRESPONDENCE only. Whether the corresponding")
    print("  artifacts replay clean is check_kernel_replay.py's job -- tripwire, then checker.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
