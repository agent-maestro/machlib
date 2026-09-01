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
  search      a regex and the paths to run it over -- for "no such DECLARATION" claims
  probe       a Lean snippet that must FAIL to compile -- for "no such TACTIC" claims

The two kinds are not interchangeable, and the difference is the point. A grep for
`^syntax "linarith"` proves nobody DECLARED it here; it does not prove it is unavailable, since a
tactic can arrive from a dependency. Only compiling a snippet answers the question the gotcha
actually asks -- "can I write this?" -- so tactic claims use probes.

A probe failing for the WRONG reason is not evidence of absence: if the expected error does not
appear, the probe is reported broken rather than passing. Fail closed -- a typo in a probe would
otherwise read exactly like the absence it was meant to establish.

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


def run_probe(snippet: str, expect_err: str) -> tuple:
    """(compiled_clean, saw_expected_error) for a snippet compiled against `import MachLib`."""
    import os
    import tempfile
    fd, path = tempfile.mkstemp(suffix=".lean")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            fh.write("import MachLib\n" + snippet + "\n")
        r = subprocess.run(["lake", "env", "lean", path], cwd=ROOT,
                           capture_output=True, text=True, timeout=600)
        out = r.stdout + r.stderr
        return (r.returncode == 0, expect_err in out)
    except Exception:                                             # noqa: BLE001
        return (None, None)
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass


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
    if "search" in entry:
        # POSITIVE CONTROL, required. The probe branch below has always demanded that a probe fail
        # for the RIGHT reason -- "a broken probe is not evidence of absence". Searches had no such
        # requirement, and a pattern that cannot match returns exactly what a true absence returns.
        # Paid for 2026-08-31: `PIrred \[` was run against source reading `PIrred ([0, 1] : ...)`,
        # a bracket where the code has a paren, and the resulting false absence reached a changelog.
        pc = entry["search"].get("positive_control")
        if pc is None:
            problems.append(("UNAVAILABLE",
                             "search has no positive_control — an instrument that has not been "
                             "shown capable of a hit cannot evidence a miss"))
        elif not re.search(entry["search"]["pattern"], pc, re.M):
            problems.append(("UNAVAILABLE",
                             f"pattern does not match its own positive control {pc[:48]!r} — "
                             f"a broken search is not evidence of absence"))
        hits = run_search(entry["search"]["pattern"], entry["search"]["paths"])
        if hits is None:
            return problems + [("UNAVAILABLE", "search could not be run")]
        if hits:
            problems.append(("NOW-FALSE", f"{len(hits)} hit(s), first: {hits[0][:100]}"))
    if "probe" in entry:
        clean, saw = run_probe(entry["probe"]["snippet"], entry["probe"]["must_fail_with"])
        if clean is None:
            problems.append(("UNAVAILABLE", "probe could not be run"))
        elif clean:
            problems.append(("NOW-FALSE",
                             "the probe COMPILED — what it says is unavailable is available"))
        elif not saw:
            problems.append(("UNAVAILABLE",
                             f"probe failed but not with {entry['probe']['must_fail_with']!r} — "
                             f"a broken probe is not evidence of absence"))
    if "search" not in entry and "probe" not in entry:
        problems.append(("UNAVAILABLE",
                         "registered with neither a search nor a probe — nothing could falsify it"))
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
    print(f"{YELLOW}{BOLD}[self-test] canary 5: a claim with NOTHING that could falsify it is "
          f"UNAVAILABLE …{RST}")
    naked = {"id": "c5", "source_file": "MachLib.lean", "claim_text": ["import"]}
    if not any(k == "UNAVAILABLE" for k, _ in check(naked)):
        print(f"{RED}[self-test] FAILED: an unfalsifiable registration read as a pass. That is the "
              f"anti-pattern this registry exists to discourage; it must not be silent.{RST}")
        ok = False
    else:
        print(f"{GREEN}[self-test] canary 5 fires. ✓{RST}")
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
