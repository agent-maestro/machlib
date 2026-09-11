#!/usr/bin/env python3
"""Count `theorem` DECLARATIONS — not the word "theorem" at the start of a sentence.

WHY THIS EXISTS (found 2026-09-11). The headline theorem count — on the README, in CLAUDE.md, and
on the **public site** — was produced by

    find MachLib -name '*.lean' -not -path '*/Discovered/*' \\
      -exec grep -hcE '^ *theorem ' {} + | paste -sd+ | bc

and that grep cannot tell a declaration from a docstring. **47 of the lines it counted were
prose.** They are sentences in module docstrings where the word `theorem` happens to land at the
start of a wrapped line:

    theorem applies. Each conditional ensures is discharged by invoking
    theorem is exactly that properness is impossible. -/
    theorem (`polyDerivative_degreeUpper_lt_after_simplify`) to MultiPoly 1. -/

plus a handful of illustrative `theorem foo (...) : ... := by` examples inside ``` fences. Core went
7709 -> **7662**; `all` 8429 -> **8382**; `Discovered/` is unchanged at 720, which is a useful
cross-check — the generated corpus has no hand-written docstrings to trip over.

It was found because a docstring written the same day line-wrapped to put `theorem consumes the`
at the start of a line, and the prose gate reported the corpus had gained a theorem that nobody
had proved. The instrument had been miscounting for as long as it had existed; what was new was
a change small enough to make the miscount visible.

WHAT IT DOES. Strips Lean block comments `/- ... -/` (nesting honoured, `/-- -/` docstrings
included) and then counts `^ *theorem `. Line comments need no handling: a `-- theorem foo` line
starts with `--`, so the pattern never matched them in the first place.

It is still a PATTERN COUNT, not an elaboration. It cannot tell you a counted declaration compiles,
and it counts `theorem` inside a string literal if one ever begins a line that way. It is exactly
one defect narrower than what it replaces, and the number it prints is the number the documents
quote.

    python3 tools/count_theorems.py --scope core        # outside Discovered/
    python3 tools/count_theorems.py --scope all
    python3 tools/count_theorems.py --scope discovered
    python3 tools/count_theorems.py --self-test
"""
from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
FOUND = HERE.parent
DECL = re.compile(r"^ *theorem ", re.M)


def strip_block_comments(s: str) -> str:
    """Blank out `/- ... -/` regions, nesting honoured.

    Newlines are preserved so line numbers and line starts still align — blanking to spaces rather
    than deleting is what keeps `^ *theorem ` from matching text pulled up from a later line.
    """
    out: list[str] = []
    depth = 0
    i = 0
    while i < len(s):
        if s.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if s.startswith("-/", i) and depth:
            depth -= 1
            i += 2
            continue
        ch = s[i]
        out.append(ch if (depth == 0 or ch == "\n") else " ")
        i += 1
    return "".join(out)


def count_file(p: Path) -> int:
    return len(DECL.findall(strip_block_comments(p.read_text(encoding="utf-8", errors="ignore"))))


def files(scope: str, root: Path) -> list[Path]:
    allf = sorted((root / "MachLib").rglob("*.lean"))
    if scope == "all":
        return allf
    inside = [p for p in allf if "Discovered" in p.parts]
    return inside if scope == "discovered" else [p for p in allf if "Discovered" not in p.parts]


_SPECIMEN = '''/-- A docstring whose prose wraps so that a line begins with the word we count. Rolle's
theorem is the usual culprit, and this line is exactly the shape that was miscounted.

An illustrative declaration inside a fence:

    theorem not_a_real_one (x : Real) : x = x := rfl
-/
theorem really_a_theorem : True := trivial

/- a nested /- block -/ whose inner text says
theorem still_not_real
-/
theorem also_real : True := trivial
'''


def self_test() -> int:
    """Two verdicts on one specimen: the naive grep must overcount it, and this must not.

    A counter that has only ever agreed with itself is not evidence. The specimen carries all three
    shapes actually found in the corpus — wrapped prose, a fenced example, and a nested block.
    """
    ok = True
    with tempfile.TemporaryDirectory(prefix="machlib_count_") as tmp:
        d = Path(tmp) / "MachLib"
        d.mkdir(parents=True)
        f = d / "Specimen.lean"
        f.write_text(_SPECIMEN, encoding="utf-8")

        naive = len(DECL.findall(_SPECIMEN))
        mine = count_file(f)
        print(f"  specimen: naive grep says {naive}, this counter says {mine} (2 real declarations)")
        if naive != 5:
            print(f"  SELFTEST FAIL — specimen no longer exercises the defect (naive={naive}, want 5)")
            ok = False
        else:
            print("  FIRES    the naive pattern overcounts the specimen 5 vs 2")
        if mine != 2:
            print(f"  SELFTEST FAIL — this counter got {mine}, want 2")
            ok = False
        else:
            print("  SILENT   this counter returns 2, the real declarations")

    live = count_file(FOUND / "MachLib" / "EMLToC.lean") if (FOUND / "MachLib" / "EMLToC.lean").exists() else None
    if live is not None:
        print(f"  CONTROL  EMLToC.lean (theorems indented inside `mutual`) still counts {live} — "
              f"indentation is not what is being filtered")
        if live == 0:
            print("  SELFTEST FAIL — a file of real indented theorems counted zero")
            ok = False

    print("SELFTEST OK" if ok else "SELFTEST FAIL")
    return 0 if ok else 1


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--scope", choices=("core", "all", "discovered"), default="core")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)
    if args.self_test:
        return self_test()
    fs = files(args.scope, FOUND)
    if not fs:
        print("UNAVAILABLE — no .lean files found; this is not a zero", file=sys.stderr)
        return 2
    print(sum(count_file(p) for p in fs))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
