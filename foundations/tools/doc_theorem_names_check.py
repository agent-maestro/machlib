#!/usr/bin/env python3
"""Every `theorem`/`def` name shown in a docs code block must EXIST in the corpus.

WHY THIS EXISTS. CLAUDE.md records a blind spot in the claim auditor, in its own words:

    the claim auditor pins prose to the axiom footprint of a theorem that EXISTS; it is
    structurally blind to a claim about a theorem that does not.

`check_obligations.sh` covers exactly one case of that (an obligation row naming a theorem that
cannot be found). This covers another, and it is the one that reads as strongest evidence to a
human: a ```lean block in the documentation, displaying a theorem statement, as if quoting the
corpus.

THE LIVE SPECIMEN THAT MOTIVATED IT. `docs/what_is_proven.md` displayed

    theorem emitted_loop_is_the_exact_trajectory (r x0 i0 p0 : Real) (n : Nat) : ...

under the heading "Demonstrated on Forge's actual output", naming `pid_loop2_step_def` as "the
compiler's output verbatim". **Neither name has ever existed in any `.lean` file.** The real
theorem is `emittedStepSpecimen_iterates_to_exactPID` over `emittedStepSpecimen`, with a different
signature (`A B C` are arguments). A reader who greps either displayed name finds nothing, and the
displayed block is the most quotable thing in the section.

WHAT IT CHECKS. Every `theorem NAME` and `def NAME` inside a ```lean fence in the registered
documents must appear as a declaration in `MachLib/`. Declarations are found by pattern, not by
`#print axioms`, so this is a NAME check and nothing more — it cannot tell you the displayed
STATEMENT matches the real one. That is a real limit and is why the message says "exists", not
"agrees".

SELF-TEST (`--self-test`): a doctored copy naming a theorem that cannot exist must FIRE, and the
unmodified corpus must stay SILENT. An instrument that has not been shown capable of both verdicts
is not evidence for either.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FOUND = HERE.parent
DOCS = ["docs/what_is_proven.md", "../CLAUDE.md", "../README.md", "../CHANGELOG.md"]

FENCE = re.compile(r"```lean\n(.*?)```", re.S)
DECL = re.compile(r"^\s*(?:private\s+)?(?:noncomputable\s+)?(theorem|def)\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.M)


def corpus_names() -> set[str]:
    names: set[str] = set()
    pat = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?"
                     r"(?:noncomputable\s+)?(?:theorem|def|abbrev|axiom|structure|inductive)\s+"
                     r"([A-Za-z_][A-Za-z0-9_'.]*)", re.M)
    for f in (FOUND / "MachLib").rglob("*.lean"):
        names.update(pat.findall(f.read_text(encoding="utf-8", errors="ignore")))
    return names


def scan(docs: list[str], names: set[str], emit=print) -> int:
    missing = 0
    checked = 0
    for d in docs:
        p = FOUND / d
        if not p.exists():
            continue
        text = p.read_text(encoding="utf-8", errors="ignore")
        for block in FENCE.findall(text):
            for kind, nm in DECL.findall(block):
                checked += 1
                base = nm.split(".")[-1]
                if nm not in names and base not in names:
                    missing += 1
                    emit(f"  MISSING  {d}: `{kind} {nm}` is displayed but no such declaration "
                         f"exists in MachLib/")
    if missing:
        emit(f"DOC-THEOREM-NAMES FAIL — {missing} displayed name(s) of {checked} do not exist")
        return 1
    emit(f"DOC-THEOREM-NAMES OK — all {checked} displayed declaration names exist in the corpus")
    return 0


def self_test() -> int:
    print("=== DOC-THEOREM-NAMES SELFTEST ===")
    names = corpus_names()
    sink: list[str] = []
    rc_ctrl = scan(DOCS, names, emit=sink.append)
    print(f"  canary 1 (real corpus must be SILENT): rc={rc_ctrl} "
          f"{'SILENT' if rc_ctrl == 0 else 'FIRES — see below'}")
    if rc_ctrl != 0:
        for l in sink:
            print("   ", l)
    # canary 2: a name that cannot exist must FIRE
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        f = Path(tmp) / "doctored.md"
        f.write_text("```lean\ntheorem zzz_no_such_theorem_zzz : True := trivial\n```\n")
        sink2: list[str] = []
        rc = scan([str(Path("..") / f.relative_to(Path(tmp).anchor))
                   if False else str(f)], names, emit=sink2.append)
    fired = rc == 1
    print(f"  canary 2 (impossible name must FIRE): rc={rc} "
          f"{'FIRES' if fired else 'SILENT — BROKEN'}")
    ok = rc_ctrl == 0 and fired
    print("DOC-THEOREM-NAMES SELFTEST " + ("PASS — 1 control silent, 1 specimen fires" if ok
                                           else "FAIL"))
    return 0 if ok else 1


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        return self_test()
    print("=== displayed theorem names vs the corpus ===")
    return scan(DOCS, corpus_names())


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
