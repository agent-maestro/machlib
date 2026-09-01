#!/usr/bin/env python3
"""Registered capstones that nobody has ever instantiated.

WHY THIS EXISTS
---------------
On 2026-08-24 `positive_branch_impossible` -- the `S > 0` flagship, registered as a claim and
green under all seven gates for weeks -- was found to be VACUOUS: two of its pole hypotheses were
unsatisfiable for every `q`, so it proved nothing about any germ. `False -> P` is provable, cites
no forbidden axiom, and discharges any obligation, so the build, the claim auditor and the
obligation ledger were all structurally blind to it.

The one signal that was there, and unread, was that the theorem had **no caller and no specimen
anywhere in the corpus**. Nobody had ever supplied its hypotheses. This script measures that.

WHAT IT CHECKS, AND WHAT IT CANNOT
-----------------------------------
It reports every registered claim-theorem that (a) takes at least one hypothesis and (b) is
referenced nowhere else in `MachLib/` outside its own declaration. That is a PROXY for "nobody has
supplied its hypotheses", and the scope is worth stating plainly:

  * A capstone is legitimately terminal. No-caller is NOT a defect on its own, which is why this
    is a ratchet against a pinned set rather than a pass/fail on zero.
  * A theorem concluding `False` is MEANT to have an unsatisfiable hypothesis set -- that is what
    an impossibility statement is. The real question for those is whether everything EXCEPT the
    existence hypothesis discharges, and this script cannot see that. Only a specimen can.
  * `forall r, P r -> Q r` is not vacuous just because `P 0` is false; it stays usable at r >= 1.
    Vacuity needs contradiction under every instantiation.

So: this catches DRIFT (a new uninstantiated capstone appearing), not vacuity itself.

THE BASELINE IS A SET, NOT A COUNT
-----------------------------------
A count is a lossy proxy: it can stay flat while one entry is witnessed and another regresses. The
baseline pins the explicit names, so a NEW orphan fails and a FIXED one must be removed from the
list -- the ratchet only turns one way.
"""
import json, re, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLAIMS = ROOT / "tools/claim_audit/claims.json"
BASELINE = ROOT / "tools/witness_baseline.json"
RED, GREEN, YELLOW, DIM, RST = "\033[31m", "\033[32m", "\033[33m", "\033[2m", "\033[0m"


def corpus_text() -> str:
    return subprocess.run(
        ["bash", "-c",
         "find MachLib -name '*.lean' -not -path 'MachLib/Discovered/*' -exec cat {} +"],
        cwd=ROOT, capture_output=True, text=True).stdout


def unwitnessed(src: str, claims: list) -> list:
    arity = {c["theorem"]: c["hypotheses_count"]
             for c in claims if "hypotheses_count" in c}
    out = []
    for t in sorted({c["theorem"] for c in claims}):
        if arity.get(t, 0) <= 0:
            continue
        short = t.split(".")[-1]
        uses = len(re.findall(r"(?<![A-Za-z0-9_.'])" + re.escape(short) + r"(?![A-Za-z0-9_'])", src))
        decls = len(re.findall(r"^\s*(?:private\s+)?theorem\s+" + re.escape(short) + r"\b", src, re.M))
        if uses - decls <= 0:
            out.append(t)
    return out


def not_applicable(src: str, claims: list) -> list:
    """Registered theorems this audit is STRUCTURALLY unable to examine, with the reason.

    A theorem concluding `False` is MEANT to have an unsatisfiable hypothesis set, so it is excluded
    by design (see this file's header). That exclusion was correct and invisible: `WITNESS-AUDIT OK`
    printed beside the whole log-junction arc for a day while unable to comment on it. A gate that
    reports PASS where the honest value is NOT_APPLICABLE has no way to say so unless it counts.

    Ported from Forge's obligation axis, which reports `preserved / not-applicable / unknown` with a
    reason on every not-applicable row rather than folding them into the pass count.
    """
    out = []
    for t in sorted({c["theorem"] for c in claims}):
        short = t.split(".")[-1]
        m = re.search(r"^\s*(?:private\s+)?theorem\s+" + re.escape(short) + r"\b(.*?):=",
                      src, re.M | re.S)
        if m and re.search(r":\s*False\s*$", m.group(1).rstrip()):
            out.append((t, "concludes False — unsatisfiable hypotheses are its content"))
    return out


def self_test(src: str, claims: list) -> int:
    """A convict specimen: a synthetic capstone nobody references must be reported."""
    fake = [{"theorem": "MachLib.CanaryNeverInstantiated", "hypotheses_count": 3}]
    fired = unwitnessed(src, fake) == ["MachLib.CanaryNeverInstantiated"]
    print(f"  canary 1 (an uninstantiated capstone is reported)  {'FIRES' if fired else 'SILENT'}")
    # and one that IS referenced must not be
    ref = [{"theorem": "MachLib.pIrred_X", "hypotheses_count": 1}]
    quiet = unwitnessed(src, ref) == []
    print(f"  canary 2 (a witnessed capstone stays silent)       {'SILENT' if quiet else 'FIRES'}")
    if not (fired and quiet):
        print(f"{RED}WITNESS-AUDIT SELF-TEST FAIL — the gate is unvalidated{RST}")
        return 1
    print(f"{GREEN}self-test PASS — both specimens discriminate{RST}\n")
    return 0


def main() -> int:
    claims = json.loads(CLAIMS.read_text())["claims"]
    src = corpus_text()
    if self_test(src, claims):
        return 1
    now = set(unwitnessed(src, claims))
    base = set(json.loads(BASELINE.read_text())["unwitnessed"])
    new, fixed = sorted(now - base), sorted(base - now)
    for t in new:
        print(f"{RED}✗ NEW uninstantiated capstone: {t}{RST}")
        print(f"{DIM}    nobody supplies its hypotheses; add a specimen, or add it to the baseline "
              f"with a reason{RST}")
    for t in fixed:
        print(f"{YELLOW}• now witnessed (remove from baseline): {t}{RST}")
    print()
    if new:
        print(f"{RED}WITNESS-AUDIT FAIL — {len(new)} capstone(s) newly uninstantiated "
              f"({len(now)} total, baseline {len(base)}).{RST}")
        return 1
    if fixed:
        print(f"{YELLOW}WITNESS-AUDIT: baseline is stale — {len(fixed)} entr(ies) now witnessed. "
              f"Ratchet it down.{RST}")
        return 1
    na = not_applicable(src, claims)
    if na:
        print(f"{DIM}    NOT APPLICABLE ({len(na)}): this audit cannot examine these — "
              f"{na[0][1]}{RST}")
        for t, _ in na:
            print(f"{DIM}      · {t}{RST}")
    print(f"{GREEN}WITNESS-AUDIT OK — {len(now)} uninstantiated capstones, exactly the pinned set; "
          f"{len(na)} refutation theorem(s) NOT APPLICABLE.{RST}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
