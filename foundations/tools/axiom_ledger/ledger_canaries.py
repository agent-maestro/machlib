#!/usr/bin/env python3
"""CANARIES for AxiomLedger.lean's checks (8) and (9). A gate with no firing specimen is unvalidated.

Both checks arrived with the muses' review of E (2026-10-05):

  (8) every name a trust list carries is a LIVE AXIOM. `Lean.collectAxioms` reports axioms only, so a
      listed name that is a theorem, a definition or nothing at all is dead weight that reads as trust.
      Its first run found three real ones (the `_elambda_1` disclosures), which is one firing; this keeps
      it firing.
  (9) a sub-theory primitive is what `subTheoryPrimitives` says: primitive in the smaller theory,
      derived in the larger one, by a theorem of the same statement.

Each canary copies AxiomLedger.lean, plants one defect, compiles the copy and requires the defect's
own message -- not merely a failure, since a copy that fails for another reason would pass a "did it
fail" test. A control compiles the UNMUTATED copy and requires OK, so a copy that cannot compile at
all cannot make every canary look caught. About 6 s per compile; seven compiles.

Run from foundations/: python3 tools/axiom_ledger/ledger_canaries.py   (exit 0 = every canary caught)
"""
from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

FOUNDATIONS = Path(__file__).resolve().parents[2]
LEDGER = FOUNDATIONS / "AxiomLedger.lean"

DERIV = "`MachLib.Real.zero_ne_one_derivable"
SMALL = '"Field", algebraFootprint,'
LARGE = '"OrderedField", orderedFieldFootprint,'

# (name, old text, new text, the message the defect must produce)
CANARIES = [
    ("a theorem in trustedFootprint",
     "def trustedFootprint : List Name := [",
     "def trustedFootprint : List Name := [`MachLib.Real.cos_zero, ",
     "trustedFootprint entr(y/ies) name no live axiom"),
    ("a vanished name in algebraFootprint",
     "def algebraFootprint : List Name := [",
     "def algebraFootprint : List Name := [`MachLib.Real.no_such_axiom, ",
     "algebraFootprint entr(y/ies) name no live axiom"),
    ("the derivation states something else",
     DERIV + ")]",
     "`MachLib.Real.one_ne_zero)]",
     "does not state MachLib.Real.zero_ne_one_ax's statement"),
    ("the derivation lies inside the smaller theory",
     SMALL,
     '"Field", orderedFieldFootprint,',
     "derives MachLib.Real.zero_ne_one_ax inside Field, so it is not primitive there"),
    ("the derivation leaves the larger theory",
     LARGE,
     '"OrderedField", algebraFootprint,',
     "is not a derivation in OrderedField"),
    ("the axiom is outside the smaller allow-list",
     "[(`MachLib.Real.zero_ne_one_ax, " + SMALL,
     "[(`MachLib.Real.zero_ne_one_ax, \"Field\", [`MachLib.Real.zeroR],",
     "is not in the Field allow-list"),
]


def compile_copy(text: str) -> str:
    """Compile `text` as a sibling of AxiomLedger.lean (so `import MachLib` resolves the same way)."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=FOUNDATIONS, delete=False) as f:
        f.write(text)
        path = Path(f.name)
    try:
        proc = subprocess.run(["lake", "env", "lean", path.name], cwd=FOUNDATIONS,
                              capture_output=True, text=True, timeout=900)
        return proc.stdout + proc.stderr
    finally:
        path.unlink(missing_ok=True)


def main() -> int:
    original = LEDGER.read_text()
    failures = []
    out = compile_copy(original)
    ok = "AxiomLedger OK:" in out
    print(f"{'control: the unmutated ledger':<52}{'OK' if ok else 'NOT OK':>8}")
    if not ok:
        failures.append("control: the unmutated ledger did not report OK -- every canary below would be meaningless")
    for name, old, new, says in CANARIES:
        if original.count(old) != 1:
            failures.append(f"{name}: the text to mutate occurs {original.count(old)} times, not once -- the canary is stale")
            print(f"{name:<52}{'STALE':>8}")
            continue
        out = compile_copy(original.replace(old, new))
        caught = says in out and "AxiomLedger FAIL" in out
        print(f"{name:<52}{'caught' if caught else 'MISSED':>8}")
        if not caught:
            failures.append(f"{name}: wanted {says!r} and a FAIL verdict; got:\n{out[-1500:]}")
    if failures:
        print("\nLEDGER-CANARIES FAIL")
        for f in failures:
            print(" -", f)
        return 1
    print(f"\nLEDGER-CANARIES PASS: the control is OK and {len(CANARIES)} of {len(CANARIES)} planted defects are caught")
    return 0


if __name__ == "__main__":
    sys.exit(main())
