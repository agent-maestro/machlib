#!/usr/bin/env python3
"""Every constant named in a TRUST DISCLOSURE string must exist, or be declared historical.

WHY THIS EXISTS. `tools/doc_theorem_names_check.py` (gates 21-22) closed one half of a blind spot:
a ```lean fence in the documentation displaying a theorem that does not exist. This closes the
other half, in a place that matters more.

`AxiomLedger.lean`'s `disclosedTrusted` is the corpus's machine-readable answer to "what, exactly,
are you asking me to take on trust?" — one free-text string per trusted axiom, and the artifact an
auditor reads before anything else. The Lean-side `run_cmd` checks that every disclosed axiom is in
`trustedFootprint` and is load-bearing in some headline. **Nothing checked the TEXT.**

THE LIVE SPECIMEN THAT MOTIVATED IT (found 2026-09-10). Ten of those strings read

    "libm model: runtime exp within real_exp_eps of Real.exp — un-witnessable in Lean"

naming `real_exp_eps`, `real_log_eps`, `real_tanh_eps`, `real_sqrt_eps`, `real_log10_eps`,
`real_asin_eps`, `real_acos_eps`, `real_sinh_eps`, `real_cosh_eps`, `real_tan_eps` — **ten
constants that the 2026-07-22 erratum had DELETED the same day**, folding each into a `u`-relative,
domain-restricted bound. The retroactive audit note directly below the definition records the fix
in prose. The machine-readable list above it went on describing the pre-erratum state for seven
weeks, and described it as UNCONDITIONAL, which the repaired axioms deliberately are not.

That direction matters. A disclosure that overstates what you assume is not a soundness hole, but
it is a lie about the trust boundary in the one document whose whole job is to describe it — and a
reader who greps `real_exp_eps` to find out how big it is finds nothing at all.

WHAT IT CHECKS. Every token shaped like a corpus declaration (`real_*`, `pid_*` — the two families
these strings actually use) appearing inside a `disclosedTrusted` string must either

  * exist as a declaration in `MachLib/` or `AxiomLedger.lean`, or
  * appear in `HISTORICAL` below with a reason, AND sit in a string that carries a historical
    marker.

The second condition is the point of the allowlist and the reason it is not just a mute list of
exceptions: an erratum narration legitimately names a thing that no longer exists ("the first
version used a single fixed `real_round_eps` constant"), but it must SAY so in the same breath.
Allowlisting a name and then citing it as live fails, which is the failure this gate was built for.

This is a NAME check, exactly like gate 21. It cannot tell you the disclosed BOUND matches the
axiom's actual bound — only that every constant the sentence names can be looked up. The message
says "exists", not "agrees".

SELF-TEST (`--self-test`): three verdicts, because two would not be enough. A fabricated live name
must FIRE; the unmodified ledger must stay SILENT; and an allowlisted name placed in a string with
no historical marker must FIRE. An instrument shown capable of only one verdict is not evidence.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FOUND = HERE.parent
LEDGER = FOUND / "AxiomLedger.lean"

#: Tokens shaped like the declarations these strings cite. Deliberately narrow: a general
#: identifier scan over free prose is all false positives, and the families that actually appear
#: here are the float-bridge constants and the grounded headlines.
TOKEN = re.compile(r"\b(?:real_|pid_)[A-Za-z0-9_]+")

#: Words that mark a sentence as talking about the PAST. A string citing a deleted constant must
#: contain one, so the reader is told the name is dead at the moment they meet it.
HISTORICAL_MARKERS = ("HISTORICAL", "no longer", "does not exist", "no real_", "dropped",
                      "the first version", "was re-stated", "were re-stated", "superseded",
                      "which is why no")

#: name -> why it is legitimately absent from the corpus.
HISTORICAL: dict[str, str] = {
    "real_round_eps": "deleted by the 2026-07-22 real_round_bounds erratum; the row narrates its "
                      "own removal (the bound became u*M directly)",
    "real_exp_eps":   "one of the ten eps constants dropped 2026-07-22 in favour of u-relative "
                      "bounds; named only in the note recording that they do not exist",
    "real_log_eps":   "as real_exp_eps — named only in the note recording its removal",
}


def corpus_names() -> set[str]:
    """Declarations the disclosure may cite. Same pattern as gate 21, plus the ledger itself."""
    pat = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?"
                     r"(?:noncomputable\s+)?(?:theorem|def|abbrev|axiom|structure|inductive)\s+"
                     r"([A-Za-z_][A-Za-z0-9_'.]*)", re.M)
    names: set[str] = set()
    files = list((FOUND / "MachLib").rglob("*.lean"))
    if LEDGER.exists():
        files.append(LEDGER)
    for f in files:
        names.update(pat.findall(f.read_text(encoding="utf-8", errors="ignore")))
    return names


def disclosure_strings(text: str) -> list[str]:
    """The string literals of `disclosedTrusted`, which is written on a single line."""
    line = next((l for l in text.splitlines() if l.startswith("def disclosedTrusted")), None)
    if line is None:
        return []
    return re.findall(r'"((?:[^"\\]|\\.)*)"', line)


def scan(strings: list[str], names: set[str], emit=print) -> int:
    if not strings:
        emit("UNAVAILABLE — no `disclosedTrusted` strings found; this is not a pass")
        return 2
    bad: list[str] = []
    checked = 0
    for st in strings:
        historical_here = any(m in st for m in HISTORICAL_MARKERS)
        for tok in TOKEN.findall(st):
            checked += 1
            if tok in names:
                continue
            if tok not in HISTORICAL:
                bad.append(f"  NAMES A CONSTANT THAT DOES NOT EXIST — {tok}\n"
                           f"    in: {st[:130]}...")
            elif not historical_here:
                bad.append(f"  ALLOWLISTED BUT CITED AS LIVE — {tok}\n"
                           f"    allowlisted as: {HISTORICAL[tok]}\n"
                           f"    but its string carries no historical marker: {st[:130]}...")
    emit(f"=== disclosure names vs corpus ===")
    emit(f"  {len(strings)} disclosure strings, {checked} cited names")
    if bad:
        emit(f"DISCLOSURE-NAMES DRIFT — {len(bad)} problem(s):")
        for b in bad:
            emit(b)
        return 1
    emit(f"DISCLOSURE-NAMES OK — every cited name exists or is declared historical")
    return 0


def self_test() -> int:
    """Three verdicts. A checker that has only ever passed is not evidence."""
    text = LEDGER.read_text(encoding="utf-8")
    names = corpus_names()
    ok = True

    sink: list[str] = []
    if scan(disclosure_strings(text), names, sink.append) != 0:
        print("SELFTEST FAIL — the real ledger does not pass; fix that before reading a self-test")
        print("\n".join(sink))
        return 1
    print("  SILENT   on the unmodified ledger")

    # 1. a fabricated live name must fire
    doctored = text.replace("libm model: runtime exp within",
                            "libm model: runtime real_totally_invented_eps exp within", 1)
    if scan(disclosure_strings(doctored), names, lambda *_: None) != 1:
        print("SELFTEST FAIL — a fabricated constant did not fire the gate")
        ok = False
    else:
        print("  FIRES    on a fabricated constant name")

    # 2. an allowlisted name with no historical marker must fire
    live_cite = text.replace("IEEE-754 denotation Float→Real (Float opaque, no in-Lean semantics)",
                             "the bound is real_round_eps, see above", 1)
    rc = scan(disclosure_strings(live_cite), names, lambda *_: None)
    if rc != 1:
        print(f"SELFTEST FAIL — an allowlisted name cited as live did not fire (rc={rc})")
        ok = False
    else:
        print("  FIRES    on an allowlisted name cited as live")

    # 3. a ledger with no disclosure block is UNAVAILABLE, never a pass
    if scan(disclosure_strings("-- nothing here\n"), names, lambda *_: None) != 2:
        print("SELFTEST FAIL — a missing disclosure block did not report UNAVAILABLE")
        ok = False
    else:
        print("  UNAVAILABLE on a ledger with no disclosure block (not a pass)")

    print("SELFTEST OK" if ok else "SELFTEST FAIL")
    return 0 if ok else 1


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)
    if not LEDGER.exists():
        print(f"UNAVAILABLE — {LEDGER} not found; this is not a pass")
        return 2
    if args.self_test:
        return self_test()
    return scan(disclosure_strings(LEDGER.read_text(encoding="utf-8")), corpus_names())


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
