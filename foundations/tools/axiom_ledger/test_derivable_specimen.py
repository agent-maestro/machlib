"""SPECIMEN for the derivable-axiom gate. A gate with no firing specimen is unvalidated.

Three directions, and the first uses a REAL circular witness rather than a stub -- the registry
standard prefers a historical or genuine fault to a synthetic one, and one is available:
`npow_half_tendsto_zero` genuinely uses `archimedean`, so declaring it as `archimedean`'s DERIVATION
is exactly the circularity the gate exists to catch, with a real footprint from a real compile.

  1. CIRCULAR            (archimedean, npow_half_tendsto_zero)  -- real Lean call, real footprint
  2. NOT_RETAINED_BASE   two entries that derive from each other -- the pairwise-composition trap
  3. control             the ledger's real entries                -- must stay clean

Direction 2 is the one that motivated the gate's second check. Both entries individually satisfy
"does not use itself"; the JOINT claim is false. Stubbed footprints, because constructing a genuine
mutual derivation would mean adding two circular theorems to the library.

Run: python3 tools/axiom_ledger/test_derivable_specimen.py   (exit 0 = all three)
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_derivable as cd  # noqa: E402

REAL = "MachLib.Real."


def main() -> int:
    fails = []
    print(f"{'direction':<44}{'want':>10}{'got':>10}  code")
    print("-" * 86)

    # ── 1. CIRCULAR, with a genuine witness ────────────────────────────────────────────────
    probs = cd.check([(REAL + "archimedean", REAL + "npow_half_tendsto_zero")], verbose=False)
    codes = {c for c, _ in probs}
    ok1 = "CIRCULAR" in codes
    print(f"{'1. CIRCULAR (real: npow_half uses archimedean)':<44}{'FIRE':>10}"
          f"{'FIRE' if probs else 'SILENT':>10}  {sorted(codes)}")
    if not ok1:
        fails.append(f"1: expected CIRCULAR, got {sorted(codes)}")

    # ── 2. NOT_RETAINED_BASE: mutual derivation, each entry individually fine ──────────────
    orig = cd.footprint
    A, B = REAL + "axA", REAL + "axB"
    tA, tB = REAL + "thmA", REAL + "thmB"
    def stub(thm):
        # thmA derives axA but USES axB; thmB derives axB but USES axA. Neither uses its own target.
        return ({B, REAL + "add_comm"} if thm == tA else {A, REAL + "add_comm"}), ""
    cd.footprint = stub
    try:
        probs2 = cd.check([(A, tA), (B, tB)], verbose=False)
    finally:
        cd.footprint = orig
    codes2 = {c for c, _ in probs2}
    ok2 = "NOT_RETAINED_BASE" in codes2 and "CIRCULAR" not in codes2
    print(f"{'2. mutual derivation (pairwise-clean)':<44}{'FIRE':>10}"
          f"{'FIRE' if probs2 else 'SILENT':>10}  {sorted(codes2)}")
    if not ok2:
        fails.append(f"2: expected NOT_RETAINED_BASE and NOT CIRCULAR, got {sorted(codes2)}")

    # ── 3. control: the real ledger entries ───────────────────────────────────────────────
    entries = cd.parse_entries(open(cd.LEDGER).read())
    probs3 = cd.check(entries, verbose=False)
    ok3 = not probs3
    print(f"{'3. control -- the real ledger entries':<44}{'PASS':>10}"
          f"{'PASS' if ok3 else 'FIRE':>10}  {sorted({c for c,_ in probs3})}")
    if not ok3:
        fails.append(f"3: real entries should pass, got {probs3}")

    print()
    if fails:
        print("DERIVABLE-GATE SPECIMEN: FAIL")
        for f in fails:
            print("  -", f)
        return 1
    print("DERIVABLE-GATE SPECIMEN: PASS -- 3/3, including the pairwise-composition trap.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
