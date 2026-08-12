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
import hashlib
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


_stmt_cache: dict = {}


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
    key = (module, theorem)
    if key not in _stmt_cache:
        _stmt_cache[key] = print_axioms_output(f"import {module}\n#check @{theorem}\n")
    return _stmt_cache[key]


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



def _binder_precedes_arrow(body: str) -> bool:
    """Does a depth-0 `∀`/`∃` appear before the first depth-0 `→`?

    If so the arrow is inside that binder's body and the antecedent chain has ended. Decidable from
    the printed form, and cheap: one left-to-right pass tracking bracket depth.
    """
    depth = 0
    for i, ch in enumerate(body):
        if ch in _OPEN:
            depth += 1
        elif ch in _CLOSE:
            depth -= 1
        elif depth == 0:
            if ch in "∀∃":
                return True
            if body.startswith("→", i):
                return False
    return False


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
        # A depth-0 binder opens a body that runs to the end of the type, so every `→` after it is
        # INSIDE that body rather than a top-level antecedent. The leading `∀ …,` telescope has
        # already been stripped above, so any binder still reachable at depth 0 before the first
        # depth-0 `→` is nested — inside an existential, or inside a disjunct of a classification.
        # Without this the splitter reports a subterm as the conclusion: it read a theorem that
        # PRODUCES a neighbourhood as one merely bounding a value pointwise, and a five-way
        # classification as a two-hypothesis implication.
        if _binder_precedes_arrow(body):
            break
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


def hypotheses_of(stmt: str) -> list:
    """The theorem's top-level antecedents, in order.

    Quantifier/strength integrity. `conclusion_of` throws these away; this keeps them, because the
    number and shape of a theorem's hypotheses IS its strength. The failure this catches is the
    mirror of the flagship one: not prose that outruns a theorem, but a theorem quietly WEAKENED
    later — a hypothesis added — while the prose describing it stays put.

    Decidable both ways: the antecedents are a syntactic prefix of the printed type.
    """
    body = stmt.split(" : ", 1)[1] if " : " in stmt else stmt
    body = re.sub(r"\s+", " ", body).strip()
    hyps, changed = [], True
    while changed:
        changed = False
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
        # A depth-0 binder opens a body that runs to the end of the type, so every `→` after it is
        # INSIDE that body rather than a top-level antecedent. The leading `∀ …,` telescope has
        # already been stripped above, so any binder still reachable at depth 0 before the first
        # depth-0 `→` is nested — inside an existential, or inside a disjunct of a classification.
        # Without this the splitter reports a subterm as the conclusion: it read a theorem that
        # PRODUCES a neighbourhood as one merely bounding a value pointwise, and a five-way
        # classification as a two-hypothesis implication.
        if _binder_precedes_arrow(body):
            break
        depth = 0
        for i, ch in enumerate(body):
            if ch in _OPEN:
                depth += 1
            elif ch in _CLOSE:
                depth -= 1
            elif ch == "→" and depth == 0:
                hyps.append(body[:i].strip())
                body, changed = body[i + 1:].strip(), True
                break
    return hyps


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


# ── Level 5: relation integrity ─────────────────────────────────────────────────────────────────
#
# The rungs above are all string questions about a printed form. "Does the statement assert THIS
# RELATION between these objects" is not, and pretending a substring search answers it would be the
# same error this whole ladder exists to catch.
#
# So the relation is not verified — it is made BINDING. Declaring a relation obliges the claim to
# carry the structural checks that relation entails, and the prose is GENERATED from the record
# rather than checked against it. You cannot write a sentence stronger than the record, because the
# sentence *is* the record; and you cannot declare a strong relation while quietly omitting the
# obligations, because the vocabulary names them.
#
# Each entry: (template, obligations that MUST be present in the claim record).
RELATIONS = {
    "implementation_error_bound": (
        "The {bound} bound on {subject}'s implementation error holds in {object}.",
        ["conclusion_mentions", "hypotheses_count"],
    ),
    "end_to_end_tracking": (
        "{subject} tracks {object} to within {bound}, with the bound derived from the "
        "implementation rather than assumed.",
        ["conclusion_mentions", "hypotheses_count", "proof_uses"],
    ),
    # Near-0 bounds come in two strengths, and the difference is the whole content of an
    # asymptotic claim: does the theorem PRODUCE the neighbourhood, or is it handed one?
    # `asymptotic_` obliges `conclusion_mentions` precisely so the existential can be demanded
    # there; a theorem that takes its interval as a hypothesis cannot satisfy it.
    "asymptotic_upper_bound": (
        "{subject} is bounded above by {bound} on a neighbourhood of 0 whose existence the "
        "theorem asserts rather than assumes.",
        ["conclusion_mentions", "hypotheses_count"],
    ),
    "pointwise_upper_bound": (
        "{subject} is bounded above by {bound} on {object}.",
        ["conclusion_mentions", "hypotheses_count"],
    ),
}

EPISTEMIC = {"PROVED", "MEASURED", "ASSUMED", "ATTESTED", "COMPUTED", "CHECKED", "DERIVED"}

# ---------------------------------------------------------------------------
# Relation entailment: DECLARED, never inferred.
#
# A human reading `asymptotic_upper_bound` and `pointwise_upper_bound` will infer that the first
# implies the second — it is even true. The machinery must not act on that inference. Every
# entailment a claim may rely on lives here as an explicit pair, and a declared entailment is
# checked for obligation-monotonicity: if R1 ⇒ R2 then R2's obligations must be a SUBSET of R1's,
# or the "stronger" relation would license a sentence while carrying fewer duties.
#
# Deliberately EMPTY. Nothing in the corpus needs an entailment yet, and an unused table that
# already refuses the obvious inference is the point: the default is no hierarchy at all.
# ---------------------------------------------------------------------------
ENTAILS: set = set()


def entails(strong: str, weak: str) -> bool:
    """Does `strong` license `weak`? Only if someone declared it. No transitive closure either —
    a chain R1⇒R2⇒R3 does not give R1⇒R3 unless that pair is also declared."""
    return (strong, weak) in ENTAILS


def check_entailment_table() -> list:
    problems = []
    for strong, weak in sorted(ENTAILS):
        for r in (strong, weak):
            if r not in RELATIONS:
                problems.append(f"entailment names unknown relation `{r}`")
        if strong in RELATIONS and weak in RELATIONS:
            so, wo = set(RELATIONS[strong][1]), set(RELATIONS[weak][1])
            if not wo <= so:
                problems.append(
                    f"declared entailment `{strong}` ⇒ `{weak}` is not obligation-monotone: "
                    f"{sorted(wo - so)} obliged by the weaker relation and not by the stronger")
    return problems


# ---------------------------------------------------------------------------
# The relation table is an AUTHORITY-BEARING ARTIFACT, so it is pinned like the axiom base.
#
# Level 5 replaced "is this prose faithful?" with "does the doc contain the licensed sentence?".
# That trade moves all the remaining trust into two places: the sentence TEMPLATES and the
# OBLIGATION LISTS. A template that renders prose stronger than its obligations warrant is the
# original overclaim, one layer down, wearing a green checkmark — and no check can catch it,
# because "is this sentence stronger than these three checks warrant?" is the same unanswerable
# semantics question level 5 deleted rather than solved.
#
# So it is not verified. It is made EXPENSIVE. Editing a template or an obligation list breaks the
# pin and fails the gate until `--bless-relations` is run deliberately, exactly as extending the
# axiom base is a ceremony rather than a commit.
# ---------------------------------------------------------------------------
RELATIONS_LOCK = os.path.join(os.path.dirname(os.path.abspath(__file__)), "relations.lock.json")


def relations_digest() -> tuple:
    """Canonical serialisation of the authority-bearing table, and its digest."""
    canon = {r: {"template": t, "obligations": list(o)} for r, (t, o) in sorted(RELATIONS.items())}
    canon["_entails"] = sorted(list(x) for x in ENTAILS)
    blob = json.dumps(canon, sort_keys=True, ensure_ascii=False, indent=2)
    return canon, hashlib.sha256(blob.encode("utf-8")).hexdigest()


def check_relations_pin() -> list:
    canon, digest = relations_digest()
    if not os.path.exists(RELATIONS_LOCK):
        return [f"relations lock missing: {RELATIONS_LOCK} — run --bless-relations"]
    lock = json.load(open(RELATIONS_LOCK, encoding="utf-8"))
    if lock.get("sha256") == digest:
        return []
    problems = [f"RELATION TABLE CHANGED without ceremony (lock {lock.get('sha256','?')[:12]}, "
                f"computed {digest[:12]}) — a template or an obligation list was edited"]
    old = lock.get("relations", {})
    for r in sorted(set(old) | set(k for k in canon if k != "_entails")):
        o, n = old.get(r), canon.get(r)
        if o is None:
            problems.append(f"  + relation `{r}` ADDED — obligations {n['obligations']}")
        elif n is None:
            problems.append(f"  - relation `{r}` REMOVED")
        else:
            if o["obligations"] != n["obligations"]:
                problems.append(f"  ~ `{r}` obligations {o['obligations']} → {n['obligations']}")
            if o["template"] != n["template"]:
                problems.append(f"  ~ `{r}` TEMPLATE changed — the licensed sentence is now "
                                f"different prose under the same name")
    return problems


def bless_relations() -> int:
    canon, digest = relations_digest()
    json.dump({"_comment": "Pinned relation vocabulary. Regenerate ONLY with intent: each entry "
                           "is a sentence this system is willing to assert on its own authority.",
               "sha256": digest, "relations": {k: v for k, v in canon.items() if k != "_entails"},
               "entails": canon["_entails"]},
              open(RELATIONS_LOCK, "w", encoding="utf-8"), indent=2, ensure_ascii=False)
    open(RELATIONS_LOCK, "a", encoding="utf-8").write("\n")
    print(f"{GREEN}relations blessed: {digest}{RST}")
    return 0


def render_claim(c: dict) -> str:
    """The sentence a typed claim licenses. Generated, never hand-written."""
    tmpl, _ = RELATIONS[c["relation"]]
    return tmpl.format(subject=c["subject"], object=c["object"], bound=c["bound"])


def hypothesis_scope_violations(stmt: str) -> list:
    """Hypotheses that contain a **depth-0 binder** — always a splitter bug, never real.

    The pretty-printer parenthesises a higher-order hypothesis (`(∀ (x : …), …)`), and a telescope
    binder is stripped before hypotheses are collected. So a `∀`/`∃` still sitting at depth 0 inside
    an extracted hypothesis means the splitter walked into a binder's body and cut a subterm out of
    it. Both shape bugs found on 2026-08-11 — existential conclusion, disjunctive conclusion —
    violate this, and it is decidable from the printed form.

    Checking it for every registered claim turns "wait for the next shape to bite" into a census
    over the shapes the corpus actually contains.
    """
    bad = []
    for h in hypotheses_of(stmt):
        depth = 0
        for ch in h:
            if ch in _OPEN:
                depth += 1
            elif ch in _CLOSE:
                depth -= 1
            elif depth == 0 and ch in "∀∃":
                bad.append(h)
                break
    return bad


def check_relation(c: dict) -> list:
    """Relation integrity: vocabulary, mandatory obligations, epistemic type, rendered prose."""
    problems = []
    rel = c["relation"]
    if rel not in RELATIONS:
        return [f"unknown relation `{rel}` — the vocabulary is closed on purpose; adding a relation "
                f"means deciding what it obliges, not just naming it"]
    if c.get("epistemic_type") not in EPISTEMIC:
        problems.append(f"claim declares no valid epistemic_type (one of {sorted(EPISTEMIC)})")
    _, obligations = RELATIONS[rel]
    for ob in obligations:
        if ob not in c:
            problems.append(
                f"relation `{rel}` obliges `{ob}`, and the claim does not carry it — a strong "
                f"relation may not be declared while its structural obligations are omitted")
    # the doc must contain the RENDERED sentence, not an author's paraphrase of it
    src = os.path.join(REPO, c["source_file"])
    if os.path.exists(src):
        if _norm(render_claim(c)) not in _norm(open(src, encoding="utf-8").read()):
            problems.append(
                f"the sentence this claim licenses is absent from {c['source_file']}:\n"
                + DIM + "    " + render_claim(c) + RST)
    return problems


def check_claim(c: dict) -> list:
    """Return a list of problem strings (empty = the claim holds)."""
    problems = []

    # (A) splitter-scope census: run on EVERY claim, whatever it declares. Cheap (the statement is
    # cached) and it audits the auditor against the statement shapes actually in the corpus.
    for bad in hypothesis_scope_violations(statement_of(c["module"], c["theorem"])):
        problems.append(
            f"SPLITTER BUG on {c['theorem']}: extracted hypothesis contains a depth-0 binder, so "
            f"the antecedent chain was cut inside a binder body:\n" + DIM + "    " + bad[:160] + RST)

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

    # (H) relation integrity: obligations follow from the declared relation.
    if "relation" in c:
        problems.extend(check_relation(c))

    # (G) strength integrity: the theorem's hypothesis count must be what the prose was written for.
    want_n = c.get("hypotheses_count")
    if want_n is not None:
        stmt = statement_of(c["module"], c["theorem"])
        if not statement_resolved(stmt):
            problems.append(f"could not resolve the STATEMENT of {c['theorem']} (build error?)")
        else:
            got = hypotheses_of(stmt)
            if len(got) != want_n:
                problems.append(
                    f"{c['theorem']} now has {len(got)} top-level hypotheses, not {want_n} — "
                    f"the theorem's STRENGTH changed under prose written for the old one"
                    + (f"; hypotheses: {got}" if len(got) <= 8 else ""))

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

    print(f"{YELLOW}{BOLD}[self-test] canary 6: the hypothesis counter must DISCRIMINATE …{RST}")
    a = hypotheses_of(statement_of("MachLib.FixedPointRealBridge",
                                   "MachLib.Real.fxaffine_traj_tracks_exact"))
    b = hypotheses_of(statement_of("MachLib.PIDCapstone",
                                   "MachLib.Real.pid_trajectory_from_bits"))
    if len(a) == 0 or len(b) == 0 or len(a) >= len(b):
        print(f"{RED}[self-test] FAILED: counter does not discriminate "
              f"(end-to-end={len(a)}, capstone={len(b)}); a counter that always returns the same "
              f"number would pass a strength check vacuously.{RST}")
        return 1
    print(f"{GREEN}[self-test] canary 6 fires: {len(a)} hypothesis on the end-to-end theorem vs "
          f"{len(b)} on the capstone — the counter distinguishes theorem strength. ✓{RST}")

    print(f"{YELLOW}{BOLD}[self-test] canary 7: a strong relation may not shed its obligations …{RST}")
    rogue = {"id": "_canary", "source_file": "CHANGELOG.md",
             "subject": "X", "object": "Y", "bound": "Z",
             "relation": "end_to_end_tracking", "epistemic_type": "PROVED"}
    probs = check_relation(rogue)
    missing_obs = [p for p in probs if "obliges" in p]
    # Pin the obligation NAMES, not their number. Cardinality is a weak proxy: swapping one
    # obligation for a feebler one at constant count sails past a count check. Named by an outside
    # reader, and they were right — this specimen previously asserted `len(...) != 3` and would
    # have certified exactly that swap. Canary 9 below is the swap it now catches.
    want = {"conclusion_mentions", "hypotheses_count", "proof_uses"}
    got = {ob for ob in want | {"statement_mentions", "statement_mentions_deep"}
           if any(f"`{ob}`" in p for p in missing_obs)}
    if got != want:
        print(f"{RED}[self-test] FAILED: `end_to_end_tracking` declared bare was objected to for "
              f"{sorted(got)}, expected exactly {sorted(want)}.{RST}")
        return 1
    print(f"{GREEN}[self-test] canary 7 fires: `end_to_end_tracking` declared bare is REJECTED, "
          f"by NAME, for each of {sorted(want)}. ✓{RST}")
    print(f"{DIM}           The relation is not verified — it is BINDING. Naming a stronger "
          f"relation buys stronger\n           obligations, not a stronger sentence.{RST}")

    print(f"{YELLOW}{BOLD}[self-test] canary 8: `asymptotic_` must reject a POINTWISE theorem …{RST}")
    # The distinction the relation exists to enforce: producing the neighbourhood vs being given
    # one. `neg_log_bound_under_rung_one` is a genuine, sorryAx-free bound near 0 — and it is
    # pointwise, so it must NOT be able to wear the asymptotic relation. A specimen drawn from a
    # FALSE theorem would only prove the auditor rejects nonsense; this one is true and still
    # rejected, which is what shows the two strengths are actually distinguished.
    concl = conclusion_of(statement_of("MachLib.EMLGrowthEnvelope",
                                       "MachLib.neg_log_bound_under_rung_one"))
    strong = conclusion_of(statement_of("MachLib.EMLGrowthEnvelope",
                                        "MachLib.depth_le_two_neg_log_bound"))
    if not concl.strip() or not strong.strip():
        print(f"{RED}[self-test] BROKEN: could not extract the specimen conclusions.{RST}")
        return 1
    if "∃" in concl or "∃" not in strong:
        print(f"{RED}[self-test] FAILED: the existential test does not discriminate — pointwise "
              f"conclusion {concl!r} vs asymptotic {strong!r}.{RST}")
        return 1
    print(f"{GREEN}[self-test] canary 8 fires: a true-but-pointwise bound cannot claim "
          f"`asymptotic_upper_bound`; only the theorem that PRODUCES its interval can. ✓{RST}")
    print(f"{DIM}           Both specimens are true theorems. The gate separates them by STRENGTH, "
          f"not by\n           truth — which is the failure mode prose actually has.{RST}")

    print(f"{YELLOW}{BOLD}[self-test] canary 9: a CONSTANT-COUNT obligation swap must be caught …{RST}")
    # The attack canary 7 used to miss. Replace `proof_uses` — the composition obligation, the one
    # that caught the flagship gap — with a feebler `statement_mentions`. Count unchanged at 3.
    saved = RELATIONS["end_to_end_tracking"]
    try:
        RELATIONS["end_to_end_tracking"] = (
            saved[0], ["conclusion_mentions", "hypotheses_count", "statement_mentions"])
        weakened = check_relations_pin()
        _, dig_after = relations_digest()
    finally:
        RELATIONS["end_to_end_tracking"] = saved
    _, dig_before = relations_digest()
    if dig_after == dig_before:
        print(f"{RED}[self-test] FAILED: the digest is blind to an obligation swap.{RST}")
        return 1
    if not any("obligations" in w and "proof_uses" in w for w in weakened):
        print(f"{RED}[self-test] FAILED: the pin did not name the swapped obligation; it reported "
              f"{weakened}{RST}")
        return 1
    print(f"{GREEN}[self-test] canary 9 fires: swapping `proof_uses` → `statement_mentions` at "
          f"constant count breaks the pin, and the pin NAMES the loss. ✓{RST}")
    print(f"{DIM}           The templates and obligation lists are where all the trust went once "
          f"level 5 traded\n           semantics for set membership. They are pinned like the axiom "
          f"base, not checked — because\n           'is this sentence stronger than these checks "
          f"warrant?' is the question level 5 deleted.{RST}")

    print(f"{YELLOW}{BOLD}[self-test] canary 10: an OBVIOUS entailment must still be refused …{RST}")
    # `asymptotic_upper_bound` really does imply `pointwise_upper_bound`, and their obligation lists
    # are identical, so a monotonicity check would happily admit it. The machinery must still say
    # no, because the pair was never declared. A specimen built on a TRUE implication is the only
    # kind that shows the refusal is about declaration rather than about correctness.
    if entails("asymptotic_upper_bound", "pointwise_upper_bound"):
        print(f"{RED}[self-test] FAILED: an undeclared entailment was granted.{RST}")
        return 1
    if set(RELATIONS["asymptotic_upper_bound"][1]) != set(RELATIONS["pointwise_upper_bound"][1]):
        print(f"{RED}[self-test] BROKEN: specimen assumes identical obligation lists.{RST}")
        return 1
    if check_entailment_table():
        print(f"{RED}[self-test] FAILED: the entailment table is inconsistent.{RST}")
        return 1
    print(f"{GREEN}[self-test] canary 10 fires: a TRUE implication between two relations with "
          f"IDENTICAL obligations is still refused, because nobody declared it. ✓{RST}")
    print(f"{DIM}           No implicit hierarchy. Otherwise a reader eventually infers an ordering "
          f"the machinery\n           never checked — and inference is exactly what this layer "
          f"exists to stop being free.{RST}")

    print(f"{YELLOW}{BOLD}[self-test] canary 11: a DISJUNCTIVE conclusion must not be split …{RST}")
    # Second instance of the binder-scope defect, found the same way as the first: by pointing the
    # auditor at a statement SHAPE no existing specimen had. A five-way classification ends in an
    # unparenthesised `∀` disjunct, and the splitter walked into it and reported 2 hypotheses.
    cst = statement_of("MachLib.EMLSizeNineShape", "MachLib.depth_le_one_classification")
    chyps = hypotheses_of(cst)
    cconcl = conclusion_of(cst)
    if len(chyps) != 1 or "∨" not in cconcl:
        print(f"{RED}[self-test] FAILED: classification split into {len(chyps)} hypotheses with "
              f"conclusion {cconcl[:80]!r}; expected 1 and a disjunction.{RST}")
        return 1
    print(f"{GREEN}[self-test] canary 11 fires: the five-way classification keeps its 1 hypothesis "
          f"and its whole disjunction. ✓{RST}")
    print(f"{DIM}           Coverage is over the SHAPE of the parser's input, not the number of "
          f"claims. Two shapes\n           have now bitten: existential conclusion, disjunctive "
          f"conclusion. Both were one specimen away.{RST}")

    print(f"{YELLOW}{BOLD}[self-test] canary 12: the SPLITTER CENSUS must catch both historic bugs …{RST}")
    # The census only earns its keep if it would have caught the two shape bugs found on
    # 2026-08-11 rather than merely agreeing with today's fixed code. Restore each historic
    # behaviour in turn and require violations to appear.
    import sys as _sys
    _mod = _sys.modules[__name__]
    real_guard = _mod._binder_precedes_arrow
    ex_stmt = statement_of("MachLib.EMLGrowthEnvelope", "MachLib.depth_le_two_neg_log_bound")
    dj_stmt = statement_of("MachLib.EMLSizeNineShape", "MachLib.depth_le_one_classification")
    try:
        _mod._binder_precedes_arrow = lambda body: False           # before any guard existed
        v1 = hypothesis_scope_violations(ex_stmt)
        v2 = hypothesis_scope_violations(dj_stmt)
        _mod._binder_precedes_arrow = lambda body: body.startswith("∃")   # the ∃-only patch
        v3 = hypothesis_scope_violations(dj_stmt)
    finally:
        _mod._binder_precedes_arrow = real_guard
    if not v1 or not v2 or not v3:
        print(f"{RED}[self-test] FAILED: census blind to a historic bug — "
              f"no-guard existential={len(v1)}, no-guard disjunctive={len(v2)}, "
              f"∃-only-guard disjunctive={len(v3)}; all must be non-zero.{RST}")
        return 1
    if hypothesis_scope_violations(ex_stmt) or hypothesis_scope_violations(dj_stmt):
        print(f"{RED}[self-test] FAILED: guard was not restored.{RST}")
        return 1
    print(f"{GREEN}[self-test] canary 12 fires: the census catches BOTH historic splitter bugs "
          f"({len(v1)}, {len(v2)}, {len(v3)} violations) and is clean under the current guard. ✓{RST}")
    print(f"{DIM}           Including the ∃-only patch, which fixed the first bug and left the "
          f"second. Specimens drawn\n           from HISTORICAL faults, not invented ones — they "
          f"prove the check catches what got past me.{RST}")

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
    ap.add_argument("--bless-relations", action="store_true",
                    help="re-pin the relation vocabulary; a ceremony, not a fixup")
    args = ap.parse_args()

    if args.bless_relations:
        return bless_relations()

    rc = 0
    # The authority-bearing table is checked on the SHIPPING PATH, not only under --self-test.
    for problem in check_relations_pin() + check_entailment_table():
        print(f"{RED}{BOLD}✗ relation vocabulary{RST}  {RED}{problem}{RST}")
        rc = 1
    if args.self_test:
        rc |= self_test()
    claims = json.load(open(args.registry, encoding="utf-8"))["claims"]
    rc |= audit(claims)
    return rc


if __name__ == "__main__":
    sys.exit(main())
