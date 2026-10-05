"""GATE: `derivableAxioms` is a CORRESPONDENCE CLAIM, so it gets a correspondence gate.

Each entry asserts "X is a theorem of the retained base, via T". That claim drifts under edits to
EITHER side -- strengthen `sup_exists`, weaken it, or touch a deriving theorem, and the ledger
silently misdescribes the trust boundary. Same shape as the AxiomLedger incident, so it gets the
same treatment: recompile every deriving theorem and read its `#print axioms` footprint.

TWO CHECKS, and the second is the one that is easy to miss:

  1. SELF-USE.  footprint(T) must not contain X.  Otherwise "X is derivable" is circular.

  2. RETAINED BASE.  footprint(T) must not contain ANY declared-derivable axiom.

DERIVABILITY DOES NOT COMPOSE PAIRWISE, which is why check 2 exists. If A derives using B and B
derives using A, BOTH pass check 1, and the effective count DOUBLE-DISCOUNTS: each entry is true
while the joint claim "base minus {A,B} suffices" is false. Requiring every footprint to lie in
(declared - ALL derivable) rather than (declared - itself) is what licenses the effective count as a
NUMBER rather than a bound. Equivalently: it forces the derivation graph to be acyclic over the
retained base, without having to build the graph.

Run: python3 tools/axiom_ledger/check_derivable.py    exit 0 = every entry holds
"""
from __future__ import annotations

import os
import re
import subprocess
import sys
import tempfile

FOUND = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEDGER = os.path.join(FOUND, "AxiomLedger.lean")


def parse_entries(src: str) -> list[tuple[str, str]]:
    """(derived axiom, deriving theorem) pairs from `derivableAxioms`."""
    m = re.search(r"def derivableAxioms : List \(Name × Name\) :=\s*\[(.*?)\]", src, re.S)
    if not m:
        return []
    return [(a, b) for a, b in re.findall(r"\(`([\w.]+),\s*`([\w.]+)\)", m.group(1))]


def footprint(thm: str) -> tuple[set[str], str]:
    """`#print axioms` for one theorem, as a set of axiom names."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=FOUND) as f:
        f.write("import MachLib\n#print axioms " + thm + "\n")
        path = f.name
    try:
        p = subprocess.run(["lake", "env", "lean", path], cwd=FOUND,
                           capture_output=True, text=True)
        out = p.stdout + p.stderr
    finally:
        os.unlink(path)
    m = re.search(r"depends on axioms: \[(.*?)\]", out, re.S)
    if not m:
        return set(), out
    return {a.strip() for a in m.group(1).replace("\n", " ").split(",") if a.strip()}, out


def check(entries: list[tuple[str, str]], verbose: bool = True) -> list[tuple[str, str]]:
    problems: list[tuple[str, str]] = []
    derivable = {a for a, _ in entries}
    for ax, thm in entries:
        fp, raw = footprint(thm)
        if not fp:
            problems.append(("NO_FOOTPRINT",
                             f"{thm}: `#print axioms` produced nothing -- does it compile? "
                             f"A derivation that does not build is not a witness.\n{raw[-400:]}"))
            continue
        if ax in fp:
            problems.append(("CIRCULAR",
                             f"{thm} USES `{ax}`, the very axiom it claims to derive."))
        others = (fp & derivable) - {ax}
        if others:
            problems.append(("NOT_RETAINED_BASE",
                             f"{thm} uses {sorted(others)}, itself declared derivable. Each entry "
                             f"may be true while the JOINT claim is false -- the effective count "
                             f"would double-discount. Derivations must land in "
                             f"(declared - ALL derivable)."))
        if verbose and ax not in fp and not others:
            print(f"  ok  {ax.split('.')[-1]:<22} via {thm.split('.')[-1]:<26} "
                  f"({len(fp)} axioms, retained-base clean)")
    return problems


#: PROVABLE MEANS PROVED (the muses' E round, 2026-10-04: "make provable => proved policy: the 'could
#: prove but still states' count goes to zero and stays there"). Four of the five axioms this ledger had
#: declared derivable -- archimedean, one_div_pos_of_pos, HasDerivAt_neg, HasDerivAt_sub -- are THEOREMS at
#: their own declaration sites now. A derivation found later is a reason to CONVERT the axiom, so a
#: non-empty `derivableAxioms` fails, with its derivations still checked so the failure says whether the
#: conversion will go through.
#:
#: "PROVABLE" IS JUDGED WITHIN THE SUB-THEORY AN AXIOM SERVES. The fifth, zero_ne_one_ax, stays an axiom: it
#: follows from the ORDER axioms, not from the FIELD axioms (the zero ring satisfies those), and the
#: ledger's `algebraFootprint` holds 326 algebra-spine theorems to the field axioms alone. Converted, it put
#: the order into 33 of them -- AxiomLedger's algebra-spine check failed, which is how this was found. Before
#: converting, run AxiomLedger.lean: a derivation that crosses a footprint it holds is not a conversion.
POLICY = "provable means proved"


def main() -> int:
    src = open(LEDGER).read()
    entries = parse_entries(src)
    print(f"derivableAxioms: {len(entries)} entr{'y' if len(entries)==1 else 'ies'}")
    if not entries:
        print(f"DERIVABLE-AXIOM GATE: PASS -- no axiom is declared derivable ({POLICY}: the count is zero "
              f"and stays there)")
        return 0
    problems = check(entries)
    print()
    print(f"DERIVABLE-AXIOM GATE: FAIL -- {POLICY}: convert each axiom to its derivation at its own "
          f"declaration site instead of recording it here")
    for code, msg in problems:
        print(f"  [{code}] {msg}")
    if not problems:
        print(f"  (all {len(entries)} derivations check against the retained base, so each conversion "
              f"will go through)")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
