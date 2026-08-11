#!/usr/bin/env python3
"""
claim_audit.py — MachLib CLAIM AUDITOR.

Generalizes the narrow `@verify` binding-integrity gate to natural-language claims.
For every registered PROSE CLAIM (a headline in README / CHANGELOG / a blog post),
it resolves the claim against the ACTUAL `#print axioms` footprint of the theorem
the claim cites, and fails loud when a headline outruns its trail:

  (A) AXIOM DRIFT — a claimed-forbidden axiom (`sorryAx`, `zero_count_bound_classical`,
      ...) appears in the theorem's transitive axiom closure while the doc still calls
      it clean. This is the "renamed-not-resolved axiom / closed that isn't closed" failure.
  (B) CLAIM DRIFT — the claim text has moved/changed out of its source doc, so the
      registry no longer describes what the repo says. Forces a re-audit rather than
      letting a headline silently mutate away from what was verified.

Design note: the claim text is whitespace-normalized before matching, so line-wrapping
in the source doc does not cause false drift. The `#print axioms` output is trusted as
the ground truth (same trail this repo has used to verify every close).

Run (from foundations/):
    python3 tools/claim_audit/claim_audit.py            # audit the registry
    python3 tools/claim_audit/claim_audit.py --self-test # + prove the gate goes RED on a canary

Exit 0 = every claim's footprint matches its prose. Non-zero = a headline outran its
footprint (or, in --self-test, the canary was NOT caught, i.e. the gate is broken).
"""
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))          # foundations/tools/claim_audit
FOUNDATIONS = os.path.abspath(os.path.join(HERE, "..", ".."))  # foundations/
REPO = os.path.abspath(os.path.join(FOUNDATIONS, ".."))    # machlib/
REGISTRY = os.path.join(HERE, "claims.json")

GREEN, RED, YELLOW, DIM, BOLD, RST = "\033[32m", "\033[31m", "\033[33m", "\033[2m", "\033[1m", "\033[0m"


def _norm(s: str) -> str:
    """Collapse all whitespace to single spaces (robust to line-wrapping)."""
    return re.sub(r"\s+", " ", s).strip()


def print_axioms_output(lean_source: str) -> str:
    """Run `lake env lean` on a self-contained snippet; return combined stdout+stderr."""
    fd, path = tempfile.mkstemp(suffix=".lean", dir=FOUNDATIONS)
    try:
        with os.fdopen(fd, "w") as f:
            f.write(lean_source)
        proc = subprocess.run(
            ["lake", "env", "lean", os.path.relpath(path, FOUNDATIONS)],
            cwd=FOUNDATIONS, capture_output=True, text=True, timeout=900)
        return proc.stdout + proc.stderr
    finally:
        os.unlink(path)


def axiom_footprint(module: str, theorem: str) -> str:
    """`#print axioms theorem` for an imported theorem."""
    return print_axioms_output(f"import {module}\n#print axioms {theorem}\n")


def statement_of(module: str, theorem: str) -> str:
    """The theorem's TYPE, via `#check @thm`.

    Distinct from `axiom_footprint` on purpose. The footprint says what a theorem RESTS ON; this
    says what it TALKS ABOUT. A claim of the form "guarantee G is derived from artifact A" is only
    backed if `A` appears in the STATEMENT — if it appears solely in the proof, or nowhere, the
    theorem does not say what the prose says.

    Added 2026-08-10 after exactly that failure: `pid_trajectory_from_bits` was documented as
    carrying the bit-level truncation into the trajectory bound, and its statement mentions no
    bit-level object at all (it quantifies `ε` universally). Every existing check passed.
    """
    return print_axioms_output(f"import {module}\n#check @{theorem}\n")


_IDENT = re.compile(r"MachLib\.[A-Za-z0-9_.']+")
_deep_cache: dict = {}


def statement_mentions_deep(module: str, theorem: str, targets: list,
                            max_defs: int = 24) -> tuple:
    """Subject integrity **modulo definitional unfolding**.

    `statement_mentions` is syntactic on the printed type, so it cannot see a constant that enters
    one δ-step away — e.g. `fxaffine_traj_tracks_exact` names `fxTraj`, whose *definition* is what
    calls `RTL.fxaffine`. That is a false negative in the safe direction, documented when the
    theorem was registered; this closes it.

    Walks the theorem's type, then the printed body of each `MachLib.*` constant it names, to a
    bounded budget. Returns `(missing, truncated)`. **`truncated` is reported, never swallowed** —
    a budget-limited search that finds nothing has not shown absence.
    """
    key = (module, theorem, max_defs, tuple(sorted(targets)))
    if key not in _deep_cache:
        seen, texts, frontier, spent = set(), [], [theorem], 0
        found_all = False
        while frontier and spent < max_defs and not found_all:
            nxt = []
            for decl in frontier:
                if decl in seen or spent >= max_defs:
                    continue
                seen.add(decl)
                spent += 1
                t = print_axioms_output(f"import {module}\n#print {decl}\n")
                texts.append(t)
                # stop the moment every target is accounted for: a search that FOUND what it
                # sought is complete regardless of budget. Truncation only matters for absence.
                if all(x in "\n".join(texts) for x in targets):
                    found_all = True
                    break
                for m in sorted(set(_IDENT.findall(t))):
                    if m not in seen:
                        nxt.append(m)
            frontier = nxt
        _deep_cache[key] = ("\n".join(texts), (spent >= max_defs) and not found_all)
    blob, truncated = _deep_cache[key]
    return ([t for t in targets if t not in blob], truncated)


_OPEN, _CLOSE = "([{⟨", ")]}⟩"


def proof_term_of(module: str, theorem: str) -> str:
    """The theorem's PROOF TERM — everything after `:=` in `#print thm`.

    A **third** question, distinct from the two the auditor already asks:

      `#print axioms`  what could this rest on          (trust base)
      statement/concl  what does this talk about        (subject)
      proof term       what does this actually go through (composition)

    Asymmetry, opposite in direction to the unfolding check: a lemma *named* here was genuinely
    invoked, so presence is decisive for DIRECT use. Absence is **not** decisive for non-use — the
    lemma could be reached transitively through another. So `proof_uses` is a positive obligation
    only; never read a passing `proof_uses` as "nothing else was involved".
    """
    out = print_axioms_output(f"import {module}\n#print {theorem}\n")
    return out.split(":=", 1)[1] if ":=" in out else ""


def conclusion_of(stmt: str) -> str:
    """The CONCLUSION of a printed type: strip top-level `∀ …,` binders and `→` antecedents.

    Why this is a different question from `statement_mentions`. A constant occurring in a
    *hypothesis* is not something the theorem concludes about — and an **unused** hypothesis
    mentioning it changes nothing at all while making the subject check pass. That attack was named
    by an outside reader; this is the check that blocks it.

    Depth-tracked so arrows inside a hypothesis's own type (`(h : ∀ k, P k → Q k)`) are ignored.
    """
    body = stmt.split(" : ", 1)[1] if " : " in stmt else stmt
    body = re.sub(r"\s+", " ", body).strip()
    changed = True
    while changed:
        changed = False
        # drop a leading `∀ …,` binder at depth 0
        if body.startswith("∀"):
            depth = 0
            for i, ch in enumerate(body):
                if ch in _OPEN:
                    depth += 1
                elif ch in _CLOSE:
                    depth -= 1
                elif ch == "," and depth == 0:
                    body, changed = body[i + 1:].strip(), True
                    break
            if changed:
                continue
        # drop the first top-level `→` antecedent
        depth = 0
        for i, ch in enumerate(body):
            if ch in _OPEN:
                depth += 1
            elif ch in _CLOSE:
                depth -= 1
            elif ch == "→" and depth == 0:
                body, changed = body[i + 1:].strip(), True
                break
    return body


def statement_resolved(text: str) -> bool:
    """Did `#check` actually print a type (vs. an error)?"""
    return " : " in text and "error" not in text.lower()


def resolved(text: str) -> bool:
    """Did `#print axioms` actually run (vs. a build/resolve error)?"""
    return ("depends on axioms" in text) or ("does not depend on any axioms" in text)


def parsed_axioms(text: str) -> set:
    """Extract the EXACT axiom names from a `#print axioms` footprint.

    Needed for `forbid_axioms_exact`: plain substring forbids can't distinguish
    `MachLib.Real.rolle` from `MachLib.Real.rolle_ct` (the sound closed-interval
    Rolle), so the unsound-Rolle regression gate must match whole tokens.
    """
    m = re.search(r"depends on axioms:\s*\[(.*)\]", text, re.S)
    if not m:
        return set()
    return {a.strip() for a in m.group(1).split(",") if a.strip()}


def check_claim(c: dict) -> list:
    """Return a list of problem strings (empty = the claim holds)."""
    problems = []

    # (B) claim-drift: the asserted text must still be present in its source doc.
    src = os.path.join(REPO, c["source_file"])
    if not os.path.exists(src):
        problems.append(f"source doc missing: {c['source_file']}")
    else:
        body = _norm(open(src, encoding="utf-8").read())
        for phrase in c["claim_text"]:
            if _norm(phrase) not in body:
                problems.append(f"claim text drifted out of {c['source_file']}: {phrase!r}")

    # (A) axiom-drift: resolve the actual footprint and check the forbidden axioms are absent.
    text = axiom_footprint(c["module"], c["theorem"])
    if not resolved(text):
        problems.append(f"could not resolve axioms of {c['theorem']} (build error?)\n"
                        + DIM + "\n".join(text.strip().splitlines()[-6:]) + RST)
    else:
        for ax in c["forbid_axioms"]:
            if ax in text:
                problems.append(f"FORBIDDEN axiom `{ax}` present in footprint of {c['theorem']}")
        # Exact whole-token forbids (e.g. the unsound `MachLib.Real.rolle`, which is a
        # substring of the SOUND `MachLib.Real.rolle_ct` and so can't be a plain forbid).
        names = parsed_axioms(text)
        for ax in c.get("forbid_axioms_exact", []):
            if ax in names:
                problems.append(f"FORBIDDEN axiom `{ax}` (exact) present in footprint of {c['theorem']}")

    # (C) statement-drift: a claim that names an artifact must be backed by a theorem whose
    # STATEMENT mentions it. Catches "G is derived from A" where the theorem never mentions A.
    want = c.get("statement_mentions", [])
    if want:
        stmt = statement_of(c["module"], c["theorem"])
        if not statement_resolved(stmt):
            problems.append(f"could not resolve the STATEMENT of {c['theorem']} (build error?)\n"
                            + DIM + "\n".join(stmt.strip().splitlines()[-6:]) + RST)
        else:
            for ident in want:
                if ident not in stmt:
                    problems.append(
                        f"STATEMENT of {c['theorem']} does not mention `{ident}` — "
                        f"the prose claims a dependency the theorem does not express")

    # (D) subject integrity modulo unfolding: catches constants that enter via a definition.
    deep = c.get("statement_mentions_deep", [])
    if deep:
        missing, truncated = statement_mentions_deep(c["module"], c["theorem"], deep)
        for ident in missing:
            problems.append(
                f"`{ident}` does not occur in {c['theorem']}'s statement even after unfolding "
                f"definitions — the prose claims a subject the theorem does not reach")
        if truncated and not missing:
            problems.append(
                f"unfolding budget exhausted while checking {c['theorem']} — a bounded search that "
                f"found everything may still have missed a counterexample; raise max_defs or "
                f"narrow the claim")

    # (E) conclusion integrity: the artifact must appear in what the theorem CONCLUDES,
    # not merely somewhere in its statement. Blocks the unused-hypothesis attack.
    concl_want = c.get("conclusion_mentions", [])
    if concl_want:
        stmt = statement_of(c["module"], c["theorem"])
        if not statement_resolved(stmt):
            problems.append(f"could not resolve the STATEMENT of {c['theorem']} (build error?)")
        else:
            concl = conclusion_of(stmt)
            for ident in concl_want:
                if ident not in concl:
                    problems.append(
                        f"`{ident}` is absent from the CONCLUSION of {c['theorem']} "
                        f"(it may appear only in a hypothesis) — the prose claims the theorem "
                        f"concludes something about it, and it does not")

    # (F) composition integrity: the proof must actually go through the lemmas the prose credits.
    uses = c.get("proof_uses", [])
    if uses:
        term = proof_term_of(c["module"], c["theorem"])
        if not term.strip():
            problems.append(f"could not extract a proof term for {c['theorem']}")
        else:
            for ident in uses:
                if ident not in term:
                    problems.append(
                        f"proof of {c['theorem']} does not invoke `{ident}` — the prose credits a "
                        f"composition the proof does not perform")

    return problems


def audit(claims: list) -> int:
    fails = 0
    for c in claims:
        problems = check_claim(c)
        if problems:
            fails += 1
            print(f"{RED}{BOLD}✗ {c['id']}{RST}  ({c['source_file']})")
            for p in problems:
                print(f"    {RED}{p}{RST}")
        else:
            print(f"{GREEN}✓ {c['id']}{RST}  {DIM}{c['theorem']} — footprint matches prose{RST}")
    print()
    if fails:
        print(f"{RED}{BOLD}CLAIM-AUDIT FAIL — {fails}/{len(claims)} headline(s) outran their footprint.{RST}")
    else:
        print(f"{GREEN}{BOLD}CLAIM-AUDIT PASS — all {len(claims)} claims resolve against #print axioms.{RST}")
    return 1 if fails else 0


def self_test() -> int:
    """Prove the gate goes RED: a deliberately-sorry theorem claimed `sorryAx`-free MUST be caught.
    A gate that never fails on a known violation is decoration (the repo's own rule)."""
    print(f"{YELLOW}{BOLD}[self-test] canary 2: a claim asserting a statement mentions what it does not …{RST}")
    stmt = statement_of("MachLib.PIDCapstone", "MachLib.Real.pid_trajectory_from_bits")
    if not statement_resolved(stmt):
        print(f"{RED}[self-test] FAILED: could not resolve the specimen statement{RST}")
        return 1
    if "fxpid" in stmt:
        print(f"{RED}[self-test] FAILED: specimen no longer fires — "
              f"pid_trajectory_from_bits now mentions fxpid, so pick a new specimen{RST}")
        return 1
    print(f"{GREEN}[self-test] canary 2 fires: pid_trajectory_from_bits's statement has no "
          f"bit-level object, so a 'derived from the datapath' claim on it is REJECTED.{RST}")
    print(f"{DIM}           ⚠ When this specimen expires it means ONLY that the first semantic gate\n"
          f"           has been crossed — `fxpid` now occurs in the statement. It does NOT mean the\n"
          f"           'derived from the datapath' claim became true: an unused hypothesis mentioning\n"
          f"           `fxpid` would expire the specimen while changing nothing. On expiry, replace\n"
          f"           this with a RELATION check (does the statement assert the error SOURCE?) and a\n"
          f"           COMPOSITION check (is fxpid_real_trunc_lt_3ulp's conclusion the quantity the\n"
          f"           trajectory bound consumes?). Staged, not satisfied.{RST}")

    print(f"{YELLOW}{BOLD}[self-test] canary 3: the DEEP check must see through a definition …{RST}")
    shallow = statement_of("MachLib.FixedPointRealBridge",
                           "MachLib.Real.fxaffine_traj_tracks_exact")
    if not statement_resolved(shallow):
        print(f"{RED}[self-test] FAILED: could not resolve the specimen statement{RST}")
        return 1
    if "fxaffine" in shallow.replace("fxaffine_traj_tracks_exact", ""):
        print(f"{RED}[self-test] FAILED: specimen no longer discriminates — `fxaffine` is now "
              f"syntactically present, so it no longer exercises the deep check.{RST}")
        return 1
    missing, trunc = statement_mentions_deep(
        "MachLib.FixedPointRealBridge", "MachLib.Real.fxaffine_traj_tracks_exact",
        ["MachLib.RTL.fxaffine"])
    if trunc or missing:
        print(f"{RED}[self-test] FAILED: the deep check could not reach `fxaffine` through "
              f"`fxTraj`'s definition (missing={missing}, truncated={trunc}).{RST}")
        return 1
    print(f"{GREEN}[self-test] canary 3 fires: `fxaffine` is INVISIBLE to the syntactic check and "
          f"VISIBLE to the deep one — level 2 does something level 1 cannot. ✓{RST}")
    print(f"{DIM}           ⚠ Asymmetry, and it is not an implementation limit: bounded unfolding "
          f"can certify PRESENCE\n           (stop when found) but never ABSENCE (budget exhausted "
          f"≠ unreachable). So the flagship\n           specimen stays on the SYNTACTIC check, "
          f"which is decisive for the statement as printed.\n           Same lesson this corpus "
          f"learned from grid search: a bounded search cannot prove a negative.{RST}")

    print(f"{YELLOW}{BOLD}[self-test] canary 4: hypothesis-only occurrences must be REJECTED …{RST}")
    st = statement_of("MachLib.EMLDepth2InvX", "MachLib.depth3_bounded_left_absurd")
    if not statement_resolved(st):
        print(f"{RED}[self-test] FAILED: could not resolve the specimen statement{RST}")
        return 1
    cc = conclusion_of(st)
    if "t1" not in st:
        print(f"{RED}[self-test] FAILED: specimen no longer mentions `t1` at all{RST}")
        return 1
    if "t1" in cc:
        print(f"{RED}[self-test] FAILED: specimen no longer discriminates — `t1` is now in the "
              f"conclusion, so it does not exercise the conclusion check.{RST}")
        return 1
    print(f"{GREEN}[self-test] canary 4 fires: `t1` occurs in the STATEMENT of "
          f"depth3_bounded_left_absurd but NOT in its conclusion (`False`), so a claim that the "
          f"theorem concludes something about `t1` is REJECTED. ✓{RST}")

    print(f"{YELLOW}{BOLD}[self-test] canary 5: the flagship gap must also be caught at the "
          f"COMPOSITION level …{RST}")
    term = proof_term_of("MachLib.PIDCapstone", "MachLib.Real.pid_trajectory_from_bits")
    if not term.strip():
        print(f"{RED}[self-test] FAILED: could not extract the specimen proof term{RST}")
        return 1
    if "fxpid_trunc_lt_3ulp" in term:
        print(f"{RED}[self-test] FAILED: pid_trajectory_from_bits now invokes "
              f"fxpid_trunc_lt_3ulp — retire this specimen and re-audit the flagship claim.{RST}")
        return 1
    print(f"{GREEN}[self-test] canary 5 fires: pid_trajectory_from_bits's proof never invokes "
          f"fxpid_trunc_lt_3ulp, so a 'composes bits with trajectory' claim is REJECTED. ✓{RST}")
    print(f"{DIM}           The flagship claim now fails independently at THREE levels — subject, "
          f"conclusion, and\n           composition. One gate can be fooled; three agreeing is "
          f"evidence the gap is real.{RST}")

    print(f"{YELLOW}{BOLD}[self-test] injecting a canary: a `by sorry` theorem falsely claimed sorryAx-free …{RST}")
    canary_src = "theorem _claim_audit_canary_bad : True := by sorry\n#print axioms _claim_audit_canary_bad\n"
    text = print_axioms_output(canary_src)
    if not resolved(text):
        print(f"{RED}[self-test] BROKEN: canary snippet did not compile — cannot exercise the gate.{RST}")
        return 1
    caught = "sorryAx" in text  # the auditor's forbidden-axiom logic keys on this substring
    if caught:
        print(f"{GREEN}[self-test] gate went RED on the canary (sorryAx detected in its footprint). ✓{RST}\n")
        return 0
    print(f"{RED}{BOLD}[self-test] FAIL: the canary uses `sorry` but the gate did NOT detect sorryAx. "
          f"The auditor is blind — fix before trusting it.{RST}")
    return 1


def main() -> int:
    ap = argparse.ArgumentParser(description="MachLib prose-claim auditor.")
    ap.add_argument("--self-test", action="store_true",
                    help="also inject a canary and prove the gate goes red on a known violation")
    ap.add_argument("--registry", default=REGISTRY,
                    help="path to the claims registry (default: claims.json next to this script)")
    args = ap.parse_args()

    rc = 0
    if args.self_test:
        rc |= self_test()
    claims = json.load(open(args.registry, encoding="utf-8"))["claims"]
    rc |= audit(claims)
    return rc


if __name__ == "__main__":
    sys.exit(main())
