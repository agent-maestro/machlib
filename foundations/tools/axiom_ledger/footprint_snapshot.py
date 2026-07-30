"""Snapshot every headline theorem's axiom footprint, for before/after migration comparison.

## What this is for

Criterion 2 of `BUMP_PLAN.md`, and the one that makes a toolchain migration **verified** rather than
hopeful: **the same theorems must rest on the same axioms after the bump as before.**

`.olean` hashes are useless across versions — the format changes, so artifact identity would fail for
reasons that say nothing about correctness. **Footprint equality is the invariant that survives a
format change**, because it is a statement about the proofs, not the files.

    A footprint that CHANGES means the migration altered what something rests on,
    which is the one thing a bump must never do.

## Usage

    python3 footprint_snapshot.py > snapshots/v4.14.0.json     # before the first step
    ... migrate ...
    python3 footprint_snapshot.py > snapshots/v4.26.0.json     # after
    python3 footprint_snapshot.py --diff snapshots/v4.14.0.json snapshots/v4.26.0.json

## House rule

The theorem list is **enumerated from the ledger**, never hardcoded, and the count is **printed by the
code that enumerated it**. `AxiomLedger.headlines` has 49 entries while `check_ledger.py` reports 57
"headline footprints" — two numbers for adjacent things, which is exactly why neither is written down
here by hand.
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import tempfile

FOUND = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LEDGER = os.path.join(FOUND, "AxiomLedger.lean")


def headline_names() -> list[str]:
    r"""Extract the list by BRACKET COUNTING, not a non-greedy regex.

    The first attempt used `\[(.*?)\]\s*\n` and overshot: the list spans many lines with `--`
    comments inside, and its closing `]` is followed by more text on the same line, so the regex
    ran on to a later bracket and swept up 122 "names" including `.`, `1` and
    `GaussianConjugacy.lean`. It still captured the right 57 footprints -- the junk simply produced
    none -- which is precisely the kind of error that hides behind a plausible result.
    """
    t = open(LEDGER).read()
    i = t.find("def headlines")
    if i < 0:
        print("[NO_HEADLINES] `def headlines` not found in AxiomLedger.lean", file=sys.stderr)
        sys.exit(1)
    start = t.index("[", i)
    depth, j = 0, start
    while j < len(t):
        if t[j] == "[":
            depth += 1
        elif t[j] == "]":
            depth -= 1
            if depth == 0:
                break
        j += 1
    body = t[start + 1:j]
    # strip `--` line comments before harvesting names
    body = re.sub(r"--[^\n]*", "", body)
    return sorted(set(re.findall(r"`([\w.]+)", body)))


def snapshot() -> dict:
    names = headline_names()
    src = "import MachLib\n" + "".join(f"#print axioms {n}\n" for n in names)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False, dir=FOUND) as f:
        f.write(src)
        path = f.name
    try:
        p = subprocess.run(["lake", "env", "lean", path], cwd=FOUND,
                           capture_output=True, text=True)
        out = p.stdout + p.stderr
    finally:
        os.unlink(path)

    fps: dict[str, list[str]] = {}
    for name, ax in re.findall(r"'([\w.]+)' depends on axioms: \[(.*?)\]", out, re.S):
        fps[name] = sorted({a.strip() for a in ax.replace("\n", " ").split(",") if a.strip()})
    for name, in re.findall(r"'([\w.]+)' does not depend on any axioms", out):
        fps.setdefault(name, [])

    toolchain = open(os.path.join(FOUND, "lean-toolchain")).read().strip()
    missing = [n for n in names if n not in fps]
    return {"toolchain": toolchain, "enumerated": len(names), "captured": len(fps),
            "missing": missing, "footprints": fps}


def main() -> int:
    if "--diff" in sys.argv:
        i = sys.argv.index("--diff")
        a, b = json.load(open(sys.argv[i + 1])), json.load(open(sys.argv[i + 2]))
        print(f"before: {a['toolchain']}   {a['captured']} footprints")
        print(f"after : {b['toolchain']}   {b['captured']} footprints")
        fa, fb = a["footprints"], b["footprints"]
        changed = [n for n in sorted(set(fa) & set(fb)) if fa[n] != fb[n]]
        only_a = sorted(set(fa) - set(fb))
        only_b = sorted(set(fb) - set(fa))
        print(f"CHANGED footprints : {len(changed)}")
        print(f"lost theorems      : {len(only_a)}")
        print(f"gained theorems    : {len(only_b)}")
        for n in changed[:10]:
            print(f"  ~ {n}\n      -{sorted(set(fa[n]) - set(fb[n]))}\n      +{sorted(set(fb[n]) - set(fa[n]))}")
        for n in only_a[:10]:
            print(f"  - {n}  (present before, ABSENT after)")
        ok = not changed and not only_a and not only_b
        print("\nFOOTPRINT EQUALITY: " + ("PASS -- same theorems, same axioms, different kernel"
                                          if ok else "FAIL -- the migration moved a dependency"))
        return 0 if ok else 1

    s = snapshot()
    print(json.dumps(s, indent=1))
    print(f"\n// toolchain {s['toolchain']}: enumerated {s['enumerated']}, "
          f"captured {s['captured']}, missing {len(s['missing'])}", file=sys.stderr)
    if s["missing"]:
        print(f"// MISSING (declared in headlines, no footprint captured): {s['missing'][:8]}",
              file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
