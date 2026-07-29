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


def main() -> int:
    src = open(LEDGER).read()
    entries = parse_entries(src)
    print(f"derivableAxioms: {len(entries)} entr{'y' if len(entries)==1 else 'ies'}")
    if not entries:
        print("DERIVABLE-AXIOM GATE: PASS (vacuous -- no entries declared)")
        return 0
    problems = check(entries)
    print()
    if not problems:
        print(f"DERIVABLE-AXIOM GATE: PASS -- {len(entries)} derivations verified against the "
              f"RETAINED base.")
        print(f"  Effective independent axiom count is {len(entries)} lower than the pinned count.")
        return 0
    print("DERIVABLE-AXIOM GATE: FAIL")
    for code, msg in problems:
        print(f"  [{code}] {msg}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
