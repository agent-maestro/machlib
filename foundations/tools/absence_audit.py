#!/usr/bin/env python3
"""Prose claims that something DOES NOT EXIST, re-checked against the corpus.

WHY THIS EXISTS
---------------
`claim_audit.py` pins prose to the axiom footprint of a theorem that EXISTS. CLAUDE.md says so, and
says what follows:

    "it is structurally blind to a claim about a theorem that does not -- including 'this obligation
     is still open'. check_obligations.sh covers that one case."

ONE case. The general shape -- "the corpus does not contain X", "these lemmas do not exist here",
"the existing machinery cannot answer this" -- is checked by nothing, and it decays silently: someone
adds the thing, and the sentence saying it is missing stays true-looking forever.

On 2026-08-28 a single session made SIX wrong claims of this shape, every one under-estimating the
corpus. Two were duplicate DEFINITIONS and the compiler caught them in seconds. Four were assertions
of ABSENCE and nothing caught them at all -- one was found only because Lean rejected a duplicate
name I happened to choose identically, and twice they became recommendations AGAINST machinery that
already existed for exactly the purpose.

Then this script's first registry pass found three MORE, sitting in CLAUDE.md:

    "These order lemmas do NOT exist here: ... mul_lt_mul_of_pos_left ..."   -- it exists
    "`min` and `abs` do not exist."                                          -- both exist, in
                                                                                Basic.lean, and are
                                                                                actively used

The `min`/`abs` line then tells the reader to hand-roll a replacement. An unchecked absence claim is
not merely stale; it actively costs work.

WHAT IT CHECKS
--------------
For each registered claim: the claim TEXT still appears in its source file, and the registered SEARCH
still returns nothing. If the search now matches, the absence claim has become false -- FAIL.

  claim_text  substrings that must appear (whitespace-normalised), as in claim_audit
  search      a regex, and the paths to run it over
  expect      "no_match" -- the only supported expectation; absence is the whole subject

WHAT IT CANNOT
--------------
* It checks SEARCHES, not meanings. "The existing machinery cannot answer this" is only as well
  checked as the search someone wrote for it. A vague absence claim can be registered with a search
  too narrow to falsify it; that is a registration quality problem, and no script fixes it.
* It cannot find absence claims nobody registered. Registration stays a human act -- the same limit
  claim_audit has, and stated for the same reason.
* An absence claim can be true and useless (nobody was going to look). This measures decay, not value.

Exit 0 pass, 1 a registered absence is now false or its text is gone, 2 could not read (UNAVAILABLE,
never a pass).
"""
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REGISTRY = Path(__file__).resolve().parent / "absence_claims.json"

RED, GREEN, YELLOW, DIM, BOLD, RST = (
    "\033[31m", "\033[32m", "\033[33m", "\033[2m", "\033[1m", "\033[0m")


def norm(s: str) -> str:
    """Whitespace-normalised, so a claim surviving a re-wrap is still found."""
    return re.sub(r"\s+", " ", s)


def run_search(pattern: str, paths: str) -> list:
    """Hits for `pattern` under `paths`, as a list of `file:line:text`.

    `-r` with an explicit path list and NO shell glob: the unquoted-glob trap CLAUDE.md documents
    would make this script's own searches depend on its working directory.
    """
    try:
        r = subprocess.run(
            ["grep", "-rnE", pattern, paths, "--include=*.lean"],
            cwd=ROOT, capture_output=True, text=True, timeout=180)
    except Exception:
        return None
    if r.returncode not in (0, 1):
        return None
    return [ln for ln in r.stdout.splitlines() if "/Discovered/" not in ln]


def check(entry: dict) -> list:
    """Problems with one registered absence claim; empty means it still holds."""
    problems = []
    src = ROOT / entry["source_file"] if not entry["source_file"].startswith("..") \
        else ROOT.parent / entry["source_file"][3:]
    try:
        text = norm(src.read_text(encoding="utf-8"))
    except OSError:
        return [("UNAVAILABLE", f"cannot read {entry['source_file']}")]
    for frag in entry["claim_text"]:
        if norm(frag) not in text:
            problems.append(("TEXT-GONE",
                             f"claim text no longer in {entry['source_file']}: {frag[:60]!r}"))
    hits = run_search(entry["search"]["pattern"], entry["search"]["paths"])
    if hits is None:
        return problems + [("UNAVAILABLE", "search could not be run")]
    if hits:
        problems.append(("NOW-FALSE",
                         f"{len(hits)} hit(s), first: {hits[0][:100]}"))
    return problems


def self_test() -> int:
    """Three convict specimens and one control. Each must behave as stated or the gate is unvalidated."""
    ok = True
    print(f"{YELLOW}{BOLD}[self-test] canary 1: an absence claim that is NOW FALSE must fire …{RST}")
    bad = {"id": "c1", "source_file": "MachLib.lean", "claim_text": ["import"],
           "search": {"pattern": "^import ", "paths": "MachLib.lean"}}
    p = check(bad)
    if not any(k == "NOW-FALSE" for k, _ in p):
        print(f"{RED}[self-test] FAILED: a search with hits did not fire NOW-FALSE.{RST}"); ok = False
    else:
        print(f"{GREEN}[self-test] canary 1 fires. ✓{RST}")

    print(f"{YELLOW}{BOLD}[self-test] canary 2: a claim whose TEXT has gone must fire …{RST}")
    gone = {"id": "c2", "source_file": "MachLib.lean",
            "claim_text": ["this string is not in the aggregator at all, zzq"],
            "search": {"pattern": "zzq_no_such_pattern_zzq", "paths": "MachLib"}}
    p = check(gone)
    if not any(k == "TEXT-GONE" for k, _ in p):
        print(f"{RED}[self-test] FAILED: a vanished claim text did not fire.{RST}"); ok = False
    else:
        print(f"{GREEN}[self-test] canary 2 fires. ✓{RST}")

    print(f"{YELLOW}{BOLD}[self-test] canary 3: an unreadable source is UNAVAILABLE, not a pass …{RST}")
    miss = {"id": "c3", "source_file": "no/such/file.lean", "claim_text": ["x"],
            "search": {"pattern": "x", "paths": "MachLib"}}
    if not any(k == "UNAVAILABLE" for k, _ in check(miss)):
        print(f"{RED}[self-test] FAILED: a missing source read as clean.{RST}"); ok = False
    else:
        print(f"{GREEN}[self-test] canary 3 fires. ✓{RST}")

    print(f"{YELLOW}{BOLD}[self-test] canary 4 (control): a TRUE absence claim must stay SILENT …{RST}")
    good = {"id": "c4", "source_file": "MachLib.lean", "claim_text": ["import"],
            "search": {"pattern": "zzq_definitely_absent_zzq", "paths": "MachLib"}}
    if check(good):
        print(f"{RED}[self-test] FAILED: a true absence claim reported problems.{RST}"); ok = False
    else:
        print(f"{GREEN}[self-test] canary 4 stays silent. ✓{RST}")
    print(f"{DIM}           A gate whose control also fires convicts everything and discriminates "
          f"nothing.{RST}\n")
    return 0 if ok else 1


def main() -> int:
    rc = 0
    if "--self-test" in sys.argv:
        rc |= self_test()
    try:
        entries = json.loads(REGISTRY.read_text(encoding="utf-8"))["claims"]
    except Exception as e:                                        # noqa: BLE001
        print(f"{YELLOW}ABSENCE-AUDIT UNAVAILABLE: cannot read {REGISTRY}: {e}{RST}",
              file=sys.stderr)
        return 2
    bad = 0
    unavailable = 0
    for entry in entries:
        for kind, msg in check(entry):
            if kind == "UNAVAILABLE":
                unavailable += 1
                print(f"{YELLOW}  UNAVAILABLE  {entry['id']}: {msg}{RST}")
            else:
                bad += 1
                print(f"{RED}  {kind}  {entry['id']}: {msg}{RST}")
    if unavailable:
        print(f"{YELLOW}ABSENCE-AUDIT UNAVAILABLE — {unavailable} claim(s) could not be "
              f"checked.{RST}")
        return 2
    if bad:
        print(f"{RED}{BOLD}ABSENCE-AUDIT FAIL — {bad} registered absence claim(s) no longer "
              f"hold.{RST}")
        return 1
    print(f"{GREEN}{BOLD}ABSENCE-AUDIT PASS — all {len(entries)} registered absence claims still "
          f"hold.{RST}")
    return rc


if __name__ == "__main__":
    sys.exit(main())
