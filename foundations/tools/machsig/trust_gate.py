#!/usr/bin/env python3
"""MachSig trust-footprint ratchet -- gate 14.

FAILS when a watched theorem changes in a way that has not been reviewed.

  statement UNCHANGED, an axiom ENTERED   -> FAIL (the same claim now rests on something new)
  statement UNCHANGED, axioms only left   -> PASS; the baseline is stale (a reviewed rebaseline)
  statement CHANGED (restated)            -> FAIL until a reviewed rebaseline, whatever its axioms
  statement same, DEFINITIONS changed     -> FAIL until a reviewed rebaseline (redefined)
  theorem REMOVED from the watched set    -> FAIL until a reviewed rebaseline
  sorryAx (not allowlisted), compiler
    trust or an UNDECLARED axiom in ANY
    watched theorem, new or old           -> FAIL, always (policy-violation)
  an AXIOM restated under the same name   -> FAIL until a reviewed rebaseline (axiom-restated)
  trustedFootprint or the sorry allowlist
    GREW since the baseline               -> FAIL until a reviewed rebaseline (policy-widened)
  new theorem on declared axioms          -> INFO

v0.4 (2026-10-13). `redefined` closes E3 of the independent review: StatementDigest hashes the stored
type, so redefining `clamp` changed thirty watched theorems' meaning with no digest change; each
theorem now also carries a DefClosureDigest over the definitions its statement reaches.
`axiom-restated` closes the pinning gap: sixteen Certcom axioms were restated under their old names
in one window. `policy-widened` makes E1/E2 visible: `pi_lower_bound` and `realPow` entered
trustedFootprint in the very commits that started using them, and the gate classed nothing.

CLOSED BY DEFAULT (2026-10-13, after an independent review). Until then a restatement and a removal
were INFO, and both laundered a growth: change a statement cosmetically and let sorryAx in, or move a
theorem out of the watched set, and the gate printed OK (attacks 5 and 6 of the review; selftest
cases B23-B26). The cost is friction: deleting or restating a theorem now needs a reviewed
rebaseline. The owner may relax either; the default is closed.

The ratchet compares axiom SETS (MachSig v0.3). Until 2026-10-13 it compared COUNTS, which convicts
every growth but misses a swap -- one axiom out, another in, same count -- and cannot say which axiom
entered. Every count growth is a set growth, so nothing the old rule convicted escapes this one.

WHY THE GATE NOW REFUSES BEFORE IT COMPARES (the owner's ruling, 2026-10-13). From 2026-09-03 to
2026-10-13 this gate compared a signature set extracted on 2026-09-03 with the baseline of the same
day, and passed: the set is generated and gitignored, and nothing recorded which tree it described.
Regenerated on 2026-10-13, it showed 1,810 growths, 1,642 shrinkages, 476 additions. A gate that
cannot fire must not read as "checked and clean", so each of these is now its own refusal:

  UNAVAILABLE (exit 2)   [no-signature-set] [no-baseline] [no-git]
  REFUSED     (exit 3)   [signatures-unidentified]   the set carries no source identity (pre-v0.3)
                         [signatures-corrupt]        its records do not match its own header
                         [signatures-stale]          extracted from other Lean sources than these
                         [signatures-stale-extractor] extracted by another extractor than this one
                         [baseline-untracked]        the baseline is not committed
                         [baseline-modified]         the baseline differs from the committed one
                         [baseline-provenance-absent] it does not say what revision/extractor made it
                         [baseline-provenance-unresolvable] it names a commit this repo lacks
                         [baseline-malformed]        its entries contradict themselves
                         [extractor-mismatch]        baseline and signatures from different extractors
                         [baseline-unreviewed]       written by --update, never reviewed
                         [review-unbound]            the stamp names another baseline's content
                         [review-report-invalid]     the stamp's report is not a transition report
                         [review-report-mismatch]    the report does not start at the last REVIEWED
                                                     baseline, or binds this baseline to itself
                         [review-report-rows]        its gate_transition rows differ from the recompute
                         [baseline-history-unavailable] the previous baseline cannot be read from git
                         [signatures-not-this-run]   MACHSIG_RUN_ID is set and the set is from another run
                         [toolchain-mismatch]        extracted with another Lean than the baseline's
                         [runner-changed]            tools/capped_lean.sh differs from the baseline's commit
                         [anchor-unreachable]        --anchor names a commit this history lacks
                         [anchor-not-in-chain]       the review chain does not run through the anchor's
  FAIL        (exit 1)   see the table above

`--selftest` proves every one of these red paths by fault injection (trust_gate_selftest.py).

TRUST MODEL (third independent review, 2026-10-14). This gate catches honest mistakes and unreviewed
drift, and -- run from the base commit, isolated (`python3 -I -S <base>/.../trust_gate.py --tree T
--anchor <base>`) -- stops a change from judging itself with an edited gate. It is NOT a boundary
against a hostile committer: the signature set is produced by building the change, and Lean
elaboration runs arbitrary code, so a change can forge its own set. That boundary is required human
review (CODEOWNERS made required by branch protection), a repository setting.

STANDALONE RUNS ARE ADVISORY. The set's identity is self-declared: a stale set relabelled with a fresh
header passes (attack 2 of the review). check_all.sh and CI therefore regenerate the set in the same
run and export MACHSIG_RUN_ID; regen.py records it and the gate refuses a set with another run's id.
Run standalone (no MACHSIG_RUN_ID), the gate says its verdict is advisory.

    python3 tools/machsig/regen.py               # extract signatures for THIS tree
    python3 tools/machsig/trust_gate.py           # the gate
    python3 tools/machsig/trust_gate.py --selftest       # red paths, then the gate
    python3 tools/machsig/trust_gate.py --selftest-only  # red paths only
    python3 tools/machsig/trust_gate.py --mutate  # 15 mutant gates: the selftest must kill each
    python3 tools/machsig/trust_gate.py --update  # write an UNREVIEWED baseline from fresh signatures
    python3 tools/machsig/trust_gate.py --content-digest [FILE]  # what a stamp must name

NO AUTOMATIC REBASELINE. `--update` writes `review.status: UNREVIEWED`, which this gate refuses. A
baseline becomes usable only when its `review` block says REVIEWED, names a reviewer, and BINDS:
  * `baseline_sha256` must equal the baseline's own content digest (`--content-digest`: sha256 of
    the canonical JSON without the review block). Pasting an old stamp onto a fresh `--update` --
    attack 3 of the 2026-10-13 review, which passed -- now fails [review-unbound].
  * `transition_report` must be a committed `machsig-transition/*` JSON (tools/machsig/transition.py)
    whose `binding.new_baseline_sha256` is this baseline, whose `binding.old_baseline_sha256` is the
    LAST REVIEWED baseline (computed over the WHOLE commit graph from the pre-review origin commit,
    merges included, counting only versions whose own stamp passes these checks against EVERY
    reviewed line they join), and whose `gate_transition` equals the transition
    the gate recomputes between the two, row for row. Citing lakefile.lean -- attack 4 of the first
    review -- fails [review-report-invalid]; a two-commit --update-then-stamp with a hollow
    "this -> itself" report -- H1 of the second review -- fails [review-report-mismatch], and any
    report that omits a change fails [review-report-rows].
WHAT THIS CANNOT DO: authenticate a person. Anyone with commit access can write a stamp and generate
a matching report. The gate binds CONTENT -- the stamp, the report and the two baselines must
describe one transition -- so a stamp cannot be reused, borrowed or forgotten; that a review
HAPPENED remains a process recorded in git (who committed it, and the review packet's sign-off).
Partial acceptance by hand-editing entries -- the practice of c3046961 -- is gone.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import identity  # noqa: E402

FOUND = identity.FOUND
BASE_REL = "tools/machsig/trust_baseline.json"
BASE = FOUND / BASE_REL
SIGS = FOUND / "artifacts" / "machsig_signatures.jsonl"
OK, FAIL, UNAVAILABLE, REFUSED = 0, 1, 2, 3
BASELINE_SCHEMA = "machsig-trust-baseline/v3"
SORRY = "sorryAx"
#: tools/theorem_ledger/ledger.py's compiler-trust test, copied: native_decide leaves `_native...ax_N`.
COMPILER_TRUST = ("Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler")
NATIVE_AXIOM = re.compile(r"(^|\.)_native\..+\.ax(_\d+)*$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")
REGEN = "python3 tools/machsig/regen.py"
HEX40 = re.compile(r"^[0-9a-f]{40}$")
SHA256 = re.compile(r"^sha256:[0-9a-f]{64}$")
PROVENANCE_FIELDS = ("machlib_commit", "machlib_sources", "content_digest", "extractor_digest",
                     "lean_toolchain", "signature_version")


# ── the signature set ──────────────────────────────────────────────────────────────────────────────

def parse_records(body: bytes) -> tuple[dict, dict, list[str]]:
    """({theorem: {"d", "c", "ax", "axioms"}} for every theorem whose trust layer is known,
        {axiom: statement digest}, problems)."""
    out, axioms_pinned, bad, seen = {}, {}, [], set()
    for ln in body.decode("utf-8").split("\n"):
        if not ln.strip():
            continue
        j = json.loads(ln)
        if j.get("object") in seen:
            bad.append(f"{j.get('object')} (twice)")   # last-write-wins would hide whichever came first
            continue
        seen.add(j.get("object"))
        if j.get("kind") == "axiom":
            if not HEX64.match(str(j.get("AxiomStatementDigest"))):
                bad.append(f"{j.get('object')} (axiom without a statement digest)")
            else:
                axioms_pinned[j["object"]] = j["AxiomStatementDigest"]
            continue
        if j.get("kind") != "theorem":
            continue          # StatementDigest is meaningless for non-theorems
        ax = None
        for p in j.get("TrustSig", j.get("ProofSig", "")).split("-"):
            if p.startswith("AX"):
                try:
                    ax = int(p[2:])
                except ValueError:
                    ax = None
        axioms = j.get("TrustAxioms")
        if ax is None or axioms is None:
            continue          # trust layer unknown (out of the census's scope): not watched
        if len(axioms) != ax or not HEX64.match(str(j.get("DefClosureDigest"))):
            bad.append(j["object"])
            continue
        out[j["object"]] = {"d": j["StatementDigest"][:32], "c": j["DefClosureDigest"], "ax": ax,
                            "axioms": sorted(axioms)}
    return out, axioms_pinned, bad


def read_signature_set(path: Path):
    """(provenance or None, {"theorems", "axioms", "policy"}, refusal or None)."""
    data = path.read_bytes()
    nl = data.find(b"\n")
    try:
        head = json.loads(data[:nl]) if nl > 0 else {}
    except json.JSONDecodeError:
        head = {}
    if head.get("kind") != identity.PROVENANCE_KIND:
        return None, {}, ("signatures-unidentified",
                          f"{path.name} carries no source identity (a pre-v0.3 set, or not written by "
                          f"regen.py). It cannot be shown to describe this tree. Regenerate: {REGEN}")
    body = data[nl + 1:]
    digest = "sha256:" + hashlib.sha256(body).hexdigest()
    n = sum(1 for ln in body.split(b"\n") if ln.strip())
    if digest != head.get("records_sha256") or n != head.get("records"):
        return head, {}, ("signatures-corrupt",
                          f"{path.name} holds {n} records (sha256 {digest[7:23]}...) but its header "
                          f"records {head.get('records')} ({str(head.get('records_sha256'))[7:23]}...): "
                          f"truncated or edited. Regenerate: {REGEN}")
    theorems, axioms_pinned, bad = parse_records(body)
    if bad:
        return head, {}, ("signatures-corrupt", f"{len(bad)} record(s) duplicated, lacking a v0.4 digest, or whose "
                                                f"TrustAxioms disagree with their AX count, first {bad[0]}. "
                                                f"Regenerate: {REGEN}")
    policy = head.get("policy")
    if not (isinstance(policy, dict) and all(isinstance(policy.get(k), list)
                                             for k in ("known", "trusted", "allowed_sorry"))):
        return head, {}, ("signatures-unidentified", f"{path.name} records no declared axiom policy (pre-v0.4): "
                                                     f"the gate cannot judge footprints. Regenerate: {REGEN}")
    return head, {"theorems": theorems, "axioms": axioms_pinned, "policy": norm_policy(policy)}, None


def norm_policy(p: dict) -> dict:
    return {k: sorted(set(p[k])) for k in ("known", "trusted", "allowed_sorry")}


def freshness(head: dict, live: dict) -> list[tuple[str, str]]:
    out = []
    if head.get("content_digest") != live["content_digest"]:
        moved = identity.changed_files(head.get("content_files", {}), live["content_files"])
        out.append(("signatures-stale",
                    f"the signature set was extracted from other Lean sources: commit "
                    f"{str(head.get('machlib_commit'))[:12]} ({str(head.get('content_digest'))[7:23]}...), "
                    f"this tree is {live['machlib_commit'][:12]} ({live['content_digest'][7:23]}...). "
                    f"Moved: {', '.join(moved) or '(file list unavailable)'}. Regenerate: {REGEN}"))
    if head.get("extractor_digest") != live["extractor_digest"]:
        moved = identity.changed_files(head.get("extractor_files", {}), live["extractor_files"])
        out.append(("signatures-stale-extractor",
                    f"the signature set was produced by another extractor ({', '.join(moved)}). "
                    f"Regenerate: {REGEN}"))
    return out


# ── the baseline ───────────────────────────────────────────────────────────────────────────────────

def baseline_git_state(root: Path) -> list[tuple[str, str]]:
    if not identity.git_ok(root, "ls-files", "--error-unmatch", "--", BASE_REL):
        return [("baseline-untracked", f"{BASE_REL} is not committed: an untracked baseline is a local "
                                       "opinion, not a reviewed record")]
    st = identity.git(root, "status", "--porcelain", "--", BASE_REL)
    if st.strip():
        return [("baseline-modified", f"{BASE_REL} differs from the committed baseline ({st.strip()[:2]}): "
                                      "the gate compares against what was reviewed, never a local edit")]
    return []


def decode_baseline(b) -> tuple[dict | None, dict | None, tuple[str, str] | None]:
    """(provenance, {theorem: {"d","ax","axioms"}}, refusal)."""
    if not isinstance(b, dict) or b.get("schema") != BASELINE_SCHEMA or not isinstance(b.get("provenance"), dict):
        return None, None, ("baseline-provenance-absent",
                            f"{BASE_REL} records no provenance (schema {BASELINE_SCHEMA} required): nothing "
                            "says which source revision and extractor it was derived from, so a comparison "
                            "against it is not evidence. The pre-2026-10-13 baseline is of this kind.")
    prov = b["provenance"]
    missing = [k for k in PROVENANCE_FIELDS if not prov.get(k)]
    if missing or not HEX40.match(str(prov.get("machlib_commit"))) \
            or not SHA256.match(str(prov.get("content_digest"))) \
            or not SHA256.match(str(prov.get("extractor_digest"))):
        return None, None, ("baseline-provenance-absent",
                            f"{BASE_REL} provenance is incomplete or malformed (missing {missing or 'none'}; "
                            "commit must be 40 hex, digests sha256:<64 hex>)")
    sets, thms = b.get("axiom_sets"), b.get("theorems")
    pins, policy = b.get("axiom_statements"), b.get("policy")
    if not isinstance(sets, dict) or not isinstance(thms, dict) or not isinstance(pins, dict) \
            or not (isinstance(policy, dict) and all(isinstance(policy.get(k), list)
                                                     for k in ("known", "trusted", "allowed_sorry"))):
        return prov, None, ("baseline-malformed", f"{BASE_REL} lacks axiom_sets/theorems/axiom_statements/policy")
    out, bad = {}, []
    for name, e in thms.items():
        axs = sets.get(e.get("set")) if isinstance(e, dict) else None
        if axs is None or len(axs) != e.get("ax") or not isinstance(e.get("d"), str) \
                or not HEX64.match(str(e.get("c"))):
            bad.append(name)
            continue
        out[name] = {"d": e["d"], "c": e["c"], "ax": e["ax"], "axioms": list(axs)}
    bad += [f"axiom pin {a}" for a, h in pins.items() if not HEX64.match(str(h))]
    for sid, axs in sets.items():
        if set_id(axs) != sid:
            bad.append(f"axiom set {sid}")
    if bad:
        return prov, None, ("baseline-malformed", f"{len(bad)} entr(ies) in {BASE_REL} contradict themselves "
                                                  f"(set missing, count != set size, or set id != content), "
                                                  f"first {bad[0]}")
    return prov, {"theorems": out, "axioms": dict(pins), "policy": norm_policy(policy)}, None


def set_id(axioms) -> str:
    return hashlib.sha256("\n".join(sorted(axioms)).encode()).hexdigest()[:16]


def baseline_content_digest(doc) -> str:
    """sha256 of the canonical JSON of a baseline WITHOUT its review block: what a stamp binds to.
    Formatting-independent, and defined for the pre-v2 counts-only baselines too (no review key)."""
    body = {k: v for k, v in doc.items() if k != "review"} if isinstance(doc, dict) else doc
    return "sha256:" + hashlib.sha256(json.dumps(body, sort_keys=True, separators=(",", ":"),
                                                 ensure_ascii=False).encode("utf-8")).hexdigest()


class HistoryUnavailable(Exception):
    pass


#: THE PRE-REVIEW ORIGIN. Every chain of reviewed baselines starts here, ONCE: the counts-only baseline
#: committed at c3046961 on 2026-10-13 (the 2026-09-03 baseline of 23e0d047 plus ten hand edits, never
#: reviewed as such). Named by COMMIT and checked by CONTENT. The chain starts at that commit and
#: nowhere else: a later commit that re-commits the same content (a "revert", or an orphan history
#: holding it) is an unreviewed version like any other -- the third review's RESTART attack.
ORIGIN_COMMIT = "c3046961e6c253759611621e559de150be275f42"
ORIGIN_CONTENT = "sha256:4994f4eadc3a4afb5e419479f958956ef3f85ffb8a4daa8bc0f09e2f4eb1abe2"
ORIGIN_LABEL = "the pre-review origin (c3046961's counts-only baseline)"


def _is_shallow(root: Path) -> bool:
    return identity.git_ok(root, "rev-parse", "--is-shallow-repository") and \
        identity.git(root, "rev-parse", "--is-shallow-repository").strip() == "true"


def _blobs(root: Path, commits: list[str]) -> dict:
    """{commit: blob sha of the baseline file, or None}, in one git process."""
    prefix = identity.git(root, "rev-parse", "--show-prefix").strip()
    inp = "".join(f"{c}:{prefix}{BASE_REL}\n" for c in commits)
    r = subprocess.run(["git", "cat-file", "--batch-check"], cwd=root, input=inp, capture_output=True,
                       text=True, env=identity._git_env())
    if r.returncode != 0:
        raise HistoryUnavailable(f"git cat-file --batch-check failed: {r.stderr.strip()[:200]}")
    out = {}
    for c, ln in zip(commits, r.stdout.splitlines()):
        out[c] = None if ln.endswith(" missing") else ln.split()[0]
    return out


def reviewed_chain(root: Path, anchor: str | None = None):
    """The reviewed state of the baseline, computed over the WHOLE commit graph reachable from HEAD.

    Every commit gets the set of REFERENCES it inherits -- content digests of reviewed baselines -- the
    union over ALL its parents (no history simplification: the third review's MERGE attack hid the
    reviewed baseline by taking a pre-review branch's file in a merge, and git's default simplification
    then dropped the reviewed line from a path-limited log). A commit that introduces a new version
    of the file makes it the single reference only if its stamp passes every check against EVERY
    inherited reference; otherwise the references pass through unchanged, pending a real review.

    Returns (references at HEAD {digest: (label, doc)}, lineage {digest: {digests it was reviewed from}},
    references at `anchor` or None, digest -> doc)."""
    lines = identity.git(root, "rev-list", "--topo-order", "--reverse", "--parents", "HEAD").splitlines()
    order, parents = [], {}
    for ln in lines:
        parts = ln.split()
        if parts:
            order.append(parts[0])
            parents[parts[0]] = parts[1:]
    if ORIGIN_COMMIT not in parents:
        why = "this is a shallow clone (fetch-depth: 0 needed)" if _is_shallow(root) else \
            "HEAD does not descend from it"
        raise HistoryUnavailable(f"{ORIGIN_LABEL}, commit {ORIGIN_COMMIT[:12]}, is not in this history: {why}")
    if anchor is not None and anchor not in parents:
        raise AnchorUnreachable(anchor)
    blobs = _blobs(root, order)
    cache: dict = {}

    def doc(blob):
        if blob not in cache:
            try:
                cache[blob] = json.loads(identity.git(root, "cat-file", "-p", blob))
            except (json.JSONDecodeError, identity.Unavailable):
                cache[blob] = None
        return cache[blob]

    refs: dict = {}
    lineage: dict = {}
    known: dict = {}                               # every reference ever made: digest -> (label, doc)
    for c in order:
        if c == ORIGIN_COMMIT:
            d = doc(blobs[c]) if blobs[c] else None
            if d is None or baseline_content_digest(d) != ORIGIN_CONTENT:
                raise HistoryUnavailable(f"commit {ORIGIN_COMMIT[:12]} does not hold the origin content")
            refs[c] = {ORIGIN_CONTENT: (ORIGIN_LABEL, d)}
            known.update(refs[c])
            continue
        inherited: dict = {}
        for p in parents[c]:
            if refs.get(p):
                inherited.update(refs[p])
        if not inherited:
            refs[c] = None                         # not descended from the origin: no chain here
            continue
        b = blobs[c]
        if b is None or all(blobs.get(p) == b for p in parents[c]):
            refs[c] = inherited                    # file absent, or unchanged against every parent
            continue
        v = doc(b)
        dv = baseline_content_digest(v) if v is not None else None
        if v is None or all(dv == k for k in inherited):
            refs[c] = inherited
            continue
        if all(dv == k or not review_problems(v, rdoc, label, _report_at(root, c))
               for k, (label, rdoc) in inherited.items()):
            refs[c] = {dv: (f"the baseline reviewed at {c[:12]}", v)}
            known.update(refs[c])
            known.update(inherited)
            lineage.setdefault(dv, set()).update(k for k in inherited if k != dv)
        else:
            refs[c] = inherited
    return refs[order[-1]], lineage, (refs.get(anchor) if anchor else None), known


class AnchorUnreachable(Exception):
    pass


def descends(mine: str, ref: str, lineage: dict) -> bool:
    """Is `ref` the reviewed baseline `mine` itself, or one it was (transitively) reviewed from?"""
    seen, stack = set(), [mine]
    while stack:
        x = stack.pop()
        if x == ref:
            return True
        if x not in seen:
            seen.add(x)
            stack.extend(lineage.get(x, ()))
    return False


def anchor_problems(mine: str, anchor_refs: dict | None, lineage: dict) -> list[tuple[str, str]]:
    """CI passes the BASE commit (--anchor): the committed baseline's review chain must run through the
    base's reviewed reference. Independent of what the change's own history claims; a decision on
    lineage alone, unit-tested on synthetic input in the selftest."""
    if not anchor_refs:
        return []                                  # the anchor predates the origin (bootstrap)
    missing = [k for k in anchor_refs if not descends(mine, k, lineage)]
    if missing:
        return [("anchor-not-in-chain", f"the base commit's reviewed baseline {missing[0][:23]}... is not in the "
                                        f"review chain of this baseline {mine[:23]}...: the change does not build "
                                        "on what the base accepted")]
    return []


def _report_at(root: Path, commit: str):
    """Report reader for a HISTORICAL stamp: the file as committed in that commit."""
    def read(rep: str):
        if not identity.git_ok(root, "cat-file", "-e", f"{commit}:./{rep}"):
            return None, f"transition report {rep} does not exist at {commit[:12]}"
        return identity.git(root, "show", f"{commit}:./{rep}"), None
    return read


def _report_in_tree(root: Path):
    """Report reader for the COMMITTED baseline: the file in the tree, which must be committed unmodified."""
    def read(rep: str):
        if not (root / rep).is_file():
            return None, f"transition report {rep} does not exist"
        if not identity.git_ok(root, "ls-files", "--error-unmatch", "--", rep) \
                or identity.git(root, "status", "--porcelain", "--", rep).strip():
            return None, f"transition report {rep} is not committed unmodified"
        return (root / rep).read_text(encoding="utf-8"), None
    return read


def _theorems_of(doc) -> tuple[dict, dict | None, dict | None, str]:
    """Any baseline -> ({theorem: d/ax/c/axioms}, axiom pins, policy, format). Never raises: a
    malformed entry decodes with missing fields and shows up in the rows."""
    if isinstance(doc, dict) and doc.get("schema") == BASELINE_SCHEMA:
        sets = doc.get("axiom_sets") if isinstance(doc.get("axiom_sets"), dict) else {}
        out = {}
        for k, e in (doc.get("theorems") or {}).items():
            e = e if isinstance(e, dict) else {}
            axs = sets.get(e.get("set"))
            out[k] = {"d": e.get("d"), "ax": e.get("ax"), "c": e.get("c"),
                      "axioms": sorted(axs) if isinstance(axs, list) else None}
        return out, doc.get("axiom_statements"), doc.get("policy"), "v3"
    if isinstance(doc, dict) and all(isinstance(v, dict) and "ax" in v and "d" in v for v in doc.values()):
        return ({k: {"d": v["d"], "ax": v["ax"], "c": None, "axioms": None} for k, v in doc.items()},
                None, None, "legacy-counts")
    return {}, None, None, "unreadable"


def gate_transition(old_doc, new_doc) -> dict:
    """The transition between two baselines, recomputed from their content alone: what a REVIEWED
    stamp's report must reproduce EXACTLY (`gate_transition` in machsig-transition/v3), so a report
    can no longer be a pair of hashes around nothing. Where the old side is the counts-only origin,
    kinds come from statement digests and counts (a swap or a redefinition is invisible there)."""
    o, opins, opol, ofmt = _theorems_of(old_doc)
    n, npins, npol, nfmt = _theorems_of(new_doc)
    rows = []
    for k in sorted(set(o) | set(n)):
        a, b = o.get(k), n.get(k)
        ent, left = [], []
        if a is None:
            kind = "new"
        elif b is None:
            kind = "removed"
        else:
            sets = a["axioms"] is not None and b["axioms"] is not None
            if sets:
                ent = sorted(set(b["axioms"]) - set(a["axioms"]))
                left = sorted(set(a["axioms"]) - set(b["axioms"]))
            if a["d"] != b["d"]:
                kind = "restated"
            elif a["c"] and b["c"] and a["c"] != b["c"]:
                kind = "redefined"
            elif sets:
                kind = "swap" if ent and left and len(ent) == len(left) else \
                    "grew" if ent else "shrank" if left else "unchanged"
            else:
                kind = "grew" if (b["ax"] or 0) > (a["ax"] or 0) else \
                    "shrank" if (b["ax"] or 0) < (a["ax"] or 0) else "unchanged"
            if kind == "unchanged" and a["ax"] != b["ax"]:
                kind = "malformed"
        if kind == "unchanged":
            continue
        rows.append([k, kind, None if a is None else a["ax"], None if b is None else b["ax"], ent, left])
    if isinstance(opins, dict) and isinstance(npins, dict):
        axioms = {"restated": sorted(x for x in opins if x in npins and opins[x] != npins[x]),
                  "new": sorted(x for x in npins if x not in opins), "gone": sorted(x for x in opins if x not in npins)}
    else:
        axioms = {"established": sorted(npins) if isinstance(npins, dict) else None}
    if isinstance(opol, dict) and isinstance(npol, dict):
        policy = {lst: {"added": sorted(set(npol.get(lst, [])) - set(opol.get(lst, []))),
                        "removed": sorted(set(opol.get(lst, [])) - set(npol.get(lst, [])))}
                  for lst in ("known", "trusted", "allowed_sorry")}
    else:
        policy = {"established": npol if isinstance(npol, dict) else None}
    return {"schema": "machsig-gate-transition/v1", "old_format": ofmt, "new_format": nfmt,
            "theorems": rows, "axioms": axioms, "policy": policy}


def review_problems(b: dict, ref, ref_label: str, read_report) -> list[tuple[str, str]]:
    """A REVIEWED stamp, checked in steps that stop at the first failure (one tag per fault). It is a
    process record bound to content, not authentication (module docstring).
      1. status REVIEWED and a reviewer named                       else [baseline-unreviewed]
      2. baseline_sha256 = this baseline's content digest           else [review-unbound]
      3. the report: a relative path inside foundations/, present (and, for the committed baseline,
         committed unmodified), JSON, schema machsig-transition/*, with `binding` and
         `gate_transition` blocks                                    else [review-report-invalid]
      4. binding.new = this baseline; not a self-binding that hides rows; binding.old = the LAST
         REVIEWED baseline `ref` (reviewed_chain)                   else [review-report-mismatch]
      5. gate_transition = the transition recomputed from `ref` to this baseline, row for row
                                                                    else [review-report-rows]"""
    r = b.get("review") if isinstance(b.get("review"), dict) else {}
    why = []
    if r.get("status") != "REVIEWED":
        why.append(f"review.status is {r.get('status')!r}")
    if not r.get("reviewer"):
        why.append("no reviewer named")
    if why:
        return [("baseline-unreviewed", f"{BASE_REL}: {'; '.join(why)}. A baseline is accepted by a person who "
                                        "reviewed its committed transition report, never by --update.")]
    mine = baseline_content_digest(b)
    if r.get("baseline_sha256") != mine:
        return [("review-unbound", f"the stamp names baseline content {str(r.get('baseline_sha256'))[:23]}..., "
                                   f"this baseline is {mine[:23]}...: the stamp was not written for this content "
                                   "(a stamp copied onto a fresh --update is exactly this)")]
    rep = r.get("transition_report")
    bad, report_doc = None, None
    if not rep or not isinstance(rep, str):
        bad = "no transition report named"
    elif Path(rep).is_absolute() or ".." in Path(rep).parts \
            or not (FOUND / rep).resolve().is_relative_to(FOUND.resolve()):
        bad = f"transition report {rep!r} is not a path inside foundations/"
    if bad is None:
        text, bad = read_report(rep)
        if bad is None:
            try:
                report_doc = json.loads(text)
            except (json.JSONDecodeError, TypeError):
                bad = f"{rep} is not JSON, so not a transition report (cite the .json transition.py writes)"
    if bad is None and not (isinstance(report_doc, dict)
                            and str(report_doc.get("schema", "")).startswith("machsig-transition/")
                            and isinstance(report_doc.get("binding"), dict)
                            and isinstance(report_doc.get("gate_transition"), dict)):
        bad = (f"{rep} is not a machsig-transition report with `binding` and `gate_transition` blocks "
               "(transition.py v3 writes both)")
    if bad:
        return [("review-report-invalid", bad)]
    want_old = baseline_content_digest(ref)
    bind = report_doc["binding"]
    recomputed = gate_transition(ref, b)
    if bind.get("new_baseline_sha256") != mine:
        return [("review-report-mismatch", f"{rep} describes a transition to {str(bind.get('new_baseline_sha256'))[:23]}..., "
                                           f"not to this baseline {mine[:23]}...")]
    if bind.get("old_baseline_sha256") == bind.get("new_baseline_sha256") and \
            (report_doc["gate_transition"].get("theorems") or want_old != mine):
        return [("review-report-mismatch", f"{rep} is a self-binding ({mine[:23]}... -> itself), but "
                                           f"{len(recomputed['theorems'])} theorem row(s) separate this baseline from "
                                           f"{ref_label}: a report must start at the last reviewed baseline")]
    if bind.get("old_baseline_sha256") != want_old:
        return [("review-report-mismatch",
                 f"{rep} starts at {str(bind.get('old_baseline_sha256'))[:23]}...; the last reviewed baseline is "
                 f"{ref_label}, {want_old[:23]}... (an unreviewed --update in between does not count)")]
    if report_doc["gate_transition"] != recomputed:
        got = report_doc["gate_transition"].get("theorems")
        got = got if isinstance(got, list) else []
        want = recomputed["theorems"]
        names = sorted({r[0] for r in got if isinstance(r, list) and r} ^ {r[0] for r in want}
                       | {w[0] for g, w in zip(got, want) if g != w})
        return [("review-report-rows",
                 f"{rep}'s gate_transition does not reproduce the transition from {ref_label} to this baseline: "
                 f"{len(got)} theorem row(s) reported, {len(want)} recomputed"
                 + (f"; first difference at {names[0]}" if names else "; the axiom or policy part differs")
                 + ". A report must list every change the stamp accepts.")]
    return []


def review_state(b: dict, root: Path, anchor: str | None = None) -> list[tuple[str, str]]:
    """The committed baseline's stamp, against the reviewed references the whole history leaves at HEAD."""
    r = b.get("review") if isinstance(b.get("review"), dict) else {}
    if not (r.get("status") == "REVIEWED" and r.get("reviewer") and r.get("baseline_sha256") == baseline_content_digest(b)):
        return review_problems(b, None, ORIGIN_LABEL, _report_in_tree(root))     # fails at step 1 or 2
    try:
        final, lineage, anchor_refs, known = reviewed_chain(root, anchor)
    except AnchorUnreachable as e:
        return [("anchor-unreachable", f"the base commit {str(e)[:12]} given by --anchor is not in this history: "
                                       "the change does not contain what it is judged against")]
    except (HistoryUnavailable, identity.Unavailable) as e:
        return [("baseline-history-unavailable", f"cannot establish the review chain: {e}")]
    mine = baseline_content_digest(b)
    if set(final) == {mine}:
        # the content was reviewed somewhere in history; the stamp committed NOW must still be a valid
        # one for it -- a later commit that rewrote only the review block (lakefile.lean as the report,
        # say) does not inherit the earlier review's validity
        preds = sorted(lineage.get(mine, ()))
        if not preds:
            return [("review-report-mismatch", "no review chain leads to this baseline")]
        for k in preds:
            label, ref = known[k]
            probs = review_problems(b, ref, label, _report_in_tree(root))
            if probs:
                return probs
    else:
        if len(final) > 1:
            return [("review-report-mismatch",
                     f"a merge joined {len(final)} reviewed lines ({', '.join(lab for lab, _ in final.values())}) and "
                     "no stamp since is valid against every one of them: review the merged baseline against each")]
        (label, ref), = final.values()
        probs = review_problems(b, ref, label, _report_in_tree(root))
        if probs:
            return probs
        lineage.setdefault(mine, set()).update(k for k in final if k != mine)   # reviewed in the tree as it stands
    return anchor_problems(mine, anchor_refs, lineage)


# ── the comparison ─────────────────────────────────────────────────────────────────────────────────

def compare(base: dict, cur: dict) -> dict:
    """The ratchet's whole decision. Pure: the selftest calls exactly this. Every list but `shrank`
    and `new` is a conviction."""
    acquired, shrank, restated, redefined, new = [], [], [], [], []
    for k in sorted(cur):
        v = cur[k]
        if k not in base:
            new.append(k)
            continue
        b = base[k]
        entered = sorted(set(v["axioms"]) - set(b["axioms"]))
        left = sorted(set(b["axioms"]) - set(v["axioms"]))
        if b["d"] != v["d"]:
            # A restatement is never a pass by itself any more: whatever the axioms did, the claim is
            # different and the baseline says nothing about it until a person has looked.
            restated.append({"theorem": k, "entered": entered, "left": left, "from": b["ax"], "to": v["ax"]})
            continue
        if b.get("c") != v.get("c"):
            # Same stored statement, different definitions under it: the claim's MEANING moved.
            redefined.append({"theorem": k, "entered": entered, "left": left, "from": b["ax"], "to": v["ax"]})
        if entered:
            acquired.append({"theorem": k, "entered": entered, "left": left, "from": b["ax"], "to": v["ax"]})
        elif left and b.get("c") == v.get("c"):
            shrank.append(k)
    gone = sorted(k for k in base if k not in cur)
    return {"acquired": acquired, "shrank": shrank, "restated": restated, "redefined": redefined, "new": new,
            "removed": gone}


def is_compiler_trust(a: str) -> bool:
    return a in COMPILER_TRUST or bool(NATIVE_AXIOM.search(a))


def policy_violations(theorems: dict, policy: dict) -> list[dict]:
    """theorem_ledger's `unchecked` reasons, in ANY watched theorem: sorryAx outside the allowlist, a
    compiler-trust axiom, an axiom the policy does not declare. Judged against the policy the tree
    declares now (the signature set's), so no baseline can grandfather one in."""
    declared = set(policy["known"]) | set(policy["trusted"])
    allowed = set(policy["allowed_sorry"])
    out = []
    for k in sorted(theorems):
        bad = sorted(a for a in theorems[k]["axioms"]
                     if (a == SORRY and k not in allowed) or is_compiler_trust(a)
                     or (a != SORRY and a not in declared))
        if bad:
            out.append({"theorem": k, "axioms": bad})
    return out


def judge(base: dict, cur: dict) -> dict:
    """Everything the gate decides, from a decoded baseline and a read signature set. Pure."""
    res = compare(base["theorems"], cur["theorems"])
    res["policy-violation"] = policy_violations(cur["theorems"], cur["policy"])
    res["axiom-restated"] = sorted(a for a in base["axioms"] if a in cur["axioms"]
                                   and base["axioms"][a] != cur["axioms"][a])
    res["axioms-gone"] = sorted(a for a in base["axioms"] if a not in cur["axioms"])
    res["axioms-new"] = sorted(a for a in cur["axioms"] if a not in base["axioms"])
    res["policy-widened"] = [f"trustedFootprint + {a}" for a in cur["policy"]["trusted"]
                             if a not in base["policy"]["trusted"]] + \
                            [f"allowedSorry + {a}" for a in cur["policy"]["allowed_sorry"]
                             if a not in base["policy"]["allowed_sorry"]]
    return res


CONVICTIONS = (
    ("acquired", "same statement, an axiom ENTERED its footprint"),
    ("restated", "statement CHANGED: a different claim the baseline has not reviewed"),
    ("redefined", "statement unchanged, but a DEFINITION it rests on changed: its meaning moved"),
    ("removed", "theorem LEFT the watched set (deleted, renamed, made private or moved): unreviewed"),
    ("policy-violation", "sorryAx outside the allowlist, compiler trust or an UNDECLARED axiom in a watched theorem"),
    ("axiom-restated", "an AXIOM's statement changed under the same name"),
    ("policy-widened", "trustedFootprint or the sorry allowlist GREW since the baseline"),
)


def _describe(key: str, item) -> str:
    if isinstance(item, str):
        return f"  - {item}"
    if key == "policy-violation":
        return f"  - {item['theorem']}  rests on {', '.join(item['axioms'])}"
    ent = f"entered {', '.join(item['entered'][:3])}" + (f" (+{len(item['entered']) - 3} more)"
                                                         if len(item["entered"]) > 3 else "")
    if key in ("restated", "redefined"):
        moved = ent if item["entered"] else ("axioms shrank" if item["left"] else "axioms unchanged")
        return f"  - {item['theorem']}  {item['from']} -> {item['to']}  {moved}"
    return f"  - {item['theorem']}  {item['from']} -> {item['to']}  {ent}"


def report(res: dict, n: int) -> int:
    print(f"  theorems compared : {n}")
    print(f"  new: {len(res['new'])}   footprint shrank: {len(res['shrank'])}   "
          f"axioms gone: {len(res.get('axioms-gone', []))}   axioms new: {len(res.get('axioms-new', []))}")
    for key, text in CONVICTIONS:
        print(f"  {key:<17} : {len(res[key])}")
    bad = [(k, t) for k, t in CONVICTIONS if res[k]]
    if bad:
        for key, text in bad:
            print(f"\nMACHSIG-TRUST FAIL [{key}] {text}")
            items = res[key]
            if key in ("acquired",):
                items = sorted(items, key=lambda a: (-len(a["entered"]), a["theorem"]))
            for it in items[:12]:
                print(_describe(key, it))
            if len(items) > 12:
                print(f"  ... and {len(items) - 12} more")
        print(f"\nMACHSIG-TRUST FAIL — {', '.join(k for k, _ in bad)}; a reviewed rebaseline is the only way through.")
        return FAIL
    print("\nMACHSIG-TRUST OK — no watched theorem was restated, redefined, removed or acquired an axiom; "
          "no axiom was restated; the policy did not widen; nothing rests on sorry or an undeclared axiom.")
    return OK


# ── the gate ───────────────────────────────────────────────────────────────────────────────────────

def refuse(items: list[tuple[str, str]]) -> int:
    for tag, msg in items:
        print(f"MACHSIG-TRUST REFUSED [{tag}] {msg}")
    print(f"\nMACHSIG-TRUST REFUSED — {len(items)} reason(s); nothing was compared, and this is not a pass.")
    return REFUSED


def unavailable(tag: str, msg: str) -> int:
    print(f"MACHSIG-TRUST UNAVAILABLE [{tag}] {msg}")
    return UNAVAILABLE


#: Scripts the extraction executes that are not extractor files (identity.EXTRACTOR_FILES is part of the
#: extractor digest; changing that list would change the digest both reviewed candidates carry). They
#: must equal the files at the baseline's provenance commit, which a review accepted.
RUNNER_FILES = ("tools/capped_lean.sh",)
LEAN_VERSION = re.compile(r"version\s+(\S+?),.*commit\s+([0-9a-f]+)")


def toolchain_key(v) -> str:
    """The toolchain that ran, minus the platform: 'Lean (version 4.32.2, aarch64-unknown-linux-gnu, commit
    f3b06c70..., Release)' -> '4.32.2 f3b06c70...', so a baseline made on aarch64 matches a CI run on x86_64."""
    m = LEAN_VERSION.search(str(v))
    return f"{m.group(1)} {m.group(2)}" if m else str(v)


def provenance_problems(root: Path, prov: dict, head: dict) -> list[tuple[str, str]]:
    out = []
    if prov.get("lean_toolchain") != head.get("lean_toolchain") or \
            toolchain_key(prov.get("lean_version")) != toolchain_key(head.get("lean_version")):
        out.append(("toolchain-mismatch",
                    f"the signatures were extracted with {head.get('lean_toolchain')} / {head.get('lean_version')}, the "
                    f"baseline with {prov.get('lean_toolchain')} / {prov.get('lean_version')}: a toolchain change moves "
                    "footprints and needs a reviewed rebaseline"))
    moved = []
    for rel in RUNNER_FILES:
        here = identity.sha256_file(root / rel) if (root / rel).is_file() else "absent"
        there = "absent"
        if identity.git_ok(root, "cat-file", "-e", f"{prov['machlib_commit']}:./{rel}"):
            r = subprocess.run(["git", "show", f"{prov['machlib_commit']}:./{rel}"], cwd=root, capture_output=True,
                               env=identity._git_env())
            there = hashlib.sha256(r.stdout).hexdigest()
        if here != there:
            moved.append(rel)
    if moved:
        out.append(("runner-changed", f"{', '.join(moved)} differ(s) from the baseline's provenance commit "
                                      f"{prov['machlib_commit'][:12]}: the extraction ran other code than the "
                                      "reviewed baseline's. Rebaseline and review."))
    return out


def gate(root: Path = FOUND, anchor: str | None = None) -> int:
    sigs, base_p = root / "artifacts" / "machsig_signatures.jsonl", root / BASE_REL
    if not sigs.is_file():
        return unavailable("no-signature-set", f"no signature set at artifacts/{sigs.name} (generated, "
                                               f"gitignored). Extract it for this tree: {REGEN}")
    if not base_p.is_file():
        return unavailable("no-baseline", f"no baseline at {BASE_REL}")
    try:
        live = identity.live_identity(root)
    except identity.Unavailable as e:
        return unavailable("no-git", f"cannot identify the live tree: {e}")
    refusals: list[tuple[str, str]] = []
    head, cur, problem = read_signature_set(sigs)
    run_id = os.environ.get("MACHSIG_RUN_ID") or None
    if problem:
        refusals.append(problem)
    else:
        refusals += freshness(head, live)
        if run_id and head.get("run_id") != run_id:
            refusals.append(("signatures-not-this-run",
                             f"MACHSIG_RUN_ID is {run_id!r} but the signature set was extracted in run "
                             f"{head.get('run_id')!r}: this run did not regenerate it. Regenerate: {REGEN}"))
    git_refusals = baseline_git_state(root)
    refusals += git_refusals
    try:
        raw = json.loads(base_p.read_text())
    except json.JSONDecodeError as e:
        raw = None
        refusals.append(("baseline-malformed", f"{BASE_REL} is not JSON: {e}"))
    base = None
    if raw is not None:
        prov, base, bproblem = decode_baseline(raw)
        if bproblem:
            refusals.append(bproblem)
        if prov is not None and bproblem is None:
            if not identity.git_ok(root, "cat-file", "-e", f"{prov['machlib_commit']}^{{commit}}"):
                refusals.append(("baseline-provenance-unresolvable",
                                 f"{BASE_REL} says it was derived from {prov['machlib_commit'][:12]}, which this "
                                 "repository does not contain (a shallow clone needs fetch-depth: 0)"))
            if head is not None and problem is None and prov["extractor_digest"] != head.get("extractor_digest"):
                refusals.append(("extractor-mismatch",
                                 f"the baseline was derived with extractor {prov['extractor_digest'][7:23]}..., the "
                                 f"signatures with {str(head.get('extractor_digest'))[7:23]}...: a comparison "
                                 "across extractors measures the extractor, not the proofs. Rebaseline and review."))
            if head is not None and problem is None:
                refusals += provenance_problems(root, prov, head)
            if not git_refusals:        # a stamp binds the COMMITTED baseline; a local edit has none
                refusals += review_state(raw, root, anchor)
    if refusals:
        return refuse(refusals)
    print(f"  signatures: {head['version']} from {head['machlib_commit'][:12]} "
          f"(sources {head['content_digest'][7:23]}..., matches this tree)"
          + (f", regenerated in this run ({run_id})" if run_id else ""))
    print(f"  baseline  : derived from {raw['provenance']['machlib_commit'][:12]}, reviewed by "
          f"{raw['review']['reviewer']} ({raw['review']['transition_report']})")
    rc = report(judge(base, cur), len(cur["theorems"]))
    if not run_id:
        print("MACHSIG-TRUST ADVISORY — standalone run: MACHSIG_RUN_ID is unset, so nothing shows this run "
              "regenerated the signature set; its identity is self-declared. The verdict holds only for a set "
              "regen.py extracted from this tree. check_all.sh and CI regenerate it in the same run.")
    return rc


def update(root: Path = FOUND) -> int:
    """Write an UNREVIEWED baseline from a fresh, clean-tree signature set. Never makes CI green."""
    sigs = root / "artifacts" / "machsig_signatures.jsonl"
    if not sigs.is_file():
        return unavailable("no-signature-set", f"nothing to baseline. Extract first: {REGEN}")
    head, cur, problem = read_signature_set(sigs)
    try:
        refusals = [problem] if problem else freshness(head, identity.live_identity(root))
    except identity.Unavailable as e:
        return unavailable("no-git", f"cannot identify the live tree: {e}")
    if not refusals and not head.get("sources_clean"):
        refusals.append(("signatures-dirty", "the signature set was extracted from uncommitted sources "
                                             f"{head.get('dirty_source_paths')[:5]}: a baseline must name a "
                                             "revision that actually holds what it describes. Commit, then "
                                             f"{REGEN}"))
    if refusals:
        return refuse(refusals)
    sets: dict[str, list[str]] = {}
    thms = {}
    for k, v in cur["theorems"].items():
        sid = set_id(v["axioms"])
        sets[sid] = v["axioms"]
        thms[k] = {"ax": v["ax"], "c": v["c"], "d": v["d"], "set": sid}
    viol = policy_violations(cur["theorems"], cur["policy"])
    if viol:
        print(f"MACHSIG-TRUST WARNING — {len(viol)} theorem(s) violate the declared policy (first "
              f"{viol[0]['theorem']}: {', '.join(viol[0]['axioms'])}); the gate FAILS on them whatever the baseline says.")
    doc = {
        "schema": BASELINE_SCHEMA,
        "provenance": {
            "machlib_commit": head["machlib_commit"], "machlib_sources": head["machlib_sources"],
            "content_digest": head["content_digest"], "extractor_digest": head["extractor_digest"],
            "extractor_files": head["extractor_files"], "lean_toolchain": head["lean_toolchain"],
            "lean_version": head["lean_version"], "signature_version": head["version"],
            "signature_records_sha256": head["records_sha256"],
        },
        "review": {"status": "UNREVIEWED", "reviewer": None, "transition_report": None, "baseline_sha256": None,
                   "note": "written by trust_gate.py --update; the gate refuses it until a person who "
                           "reviewed the transition report sets status REVIEWED, names themselves, cites the "
                           "committed transition JSON and copies --content-digest into baseline_sha256"},
        "policy": cur["policy"],
        "axiom_statements": dict(sorted(cur["axioms"].items())),
        "axiom_sets": sets,
        "theorems": thms,
    }
    (root / BASE_REL).write_text(dump_baseline(doc))
    print(f"MACHSIG-TRUST baseline written: {len(thms)} theorems, {len(sets)} distinct axiom sets, from "
          f"{head['machlib_commit'][:12]}. It is UNREVIEWED: the gate refuses it until reviewed.")
    return OK


def dump_baseline(doc: dict) -> str:
    """Deterministic, one table entry per line, so a review diff shows one line per changed theorem."""
    lines = ["{"]
    keys = sorted(doc)
    for i, k in enumerate(keys):
        tail = "," if i < len(keys) - 1 else ""
        v = doc[k]
        if k in ("axiom_sets", "theorems", "axiom_statements"):
            lines.append(f"{json.dumps(k)}: {{")
            items = sorted(v.items())
            for j, (name, e) in enumerate(items):
                lines.append(f"{json.dumps(name)}: {json.dumps(e, sort_keys=True)}"
                             f"{',' if j < len(items) - 1 else ''}")
            lines.append("}" + tail)
        else:
            lines.append(f"{json.dumps(k)}: {json.dumps(v, sort_keys=True)}{tail}")
    lines.append("}")
    return "\n".join(lines) + "\n"


def set_tree(path) -> None:
    """Judge another tree than the one this file sits in (CI runs the BASE's gate, isolated, from
    outside the tree under test: `python3 -I -S <base>/tools/machsig/trust_gate.py --tree <tree>`)."""
    global FOUND, BASE, SIGS
    FOUND = Path(path).resolve()
    BASE = FOUND / BASE_REL
    SIGS = FOUND / "artifacts" / "machsig_signatures.jsonl"


def _opt(argv: list[str], name: str) -> str | None:
    if name in argv:
        i = argv.index(name)
        if i + 1 >= len(argv):
            raise SystemExit(f"{name} needs a value")
        return argv[i + 1]
    return None


def main(argv: list[str]) -> int:
    tree, anchor = _opt(argv, "--tree"), _opt(argv, "--anchor")
    if tree:
        set_tree(tree)
        import trust_gate as _self               # the module the selftest imports is not __main__
        _self.set_tree(tree)
    if anchor and not re.fullmatch(r"[0-9a-f]{40}", anchor):
        raise SystemExit("--anchor takes a full 40-hex commit id")
    if "--content-digest" in argv:
        rest = [a for a in argv if a != "--content-digest"]
        p = Path(rest[0]) if rest else BASE
        print(baseline_content_digest(json.loads(p.read_text())))
        return OK
    if "--update" in argv:
        return update(FOUND)
    if "--mutate" in argv:
        import trust_gate_selftest
        return trust_gate_selftest.mutate()
    if "--selftest" in argv or "--selftest-only" in argv:
        import trust_gate_selftest
        rc = trust_gate_selftest.run()
        if rc != OK or "--selftest-only" in argv:
            return rc
    return gate(FOUND, anchor)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
