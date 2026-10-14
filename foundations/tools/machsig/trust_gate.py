#!/usr/bin/env python3
"""MachSig trust-footprint ratchet -- gate 14.

FAILS when a theorem ACQUIRES an axiom while its statement is unchanged.

  statement UNCHANGED, an axiom ENTERED   -> FAIL (the same claim now rests on something new)
  statement UNCHANGED, axioms only left   -> PASS; the baseline is stale (a reviewed rebaseline)
  statement CHANGED                       -> INFO: a different claim, not a trust regression
  new / removed theorem                   -> INFO

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
  FAIL        (exit 1)   an axiom entered an unchanged statement's footprint

`--selftest` proves every one of these red paths by fault injection (trust_gate_selftest.py).

    python3 tools/machsig/regen.py               # extract signatures for THIS tree
    python3 tools/machsig/trust_gate.py           # the gate
    python3 tools/machsig/trust_gate.py --selftest       # red paths, then the gate
    python3 tools/machsig/trust_gate.py --selftest-only  # red paths only
    python3 tools/machsig/trust_gate.py --mutate  # 15 mutant gates: the selftest must kill each
    python3 tools/machsig/trust_gate.py --update  # write an UNREVIEWED baseline from fresh signatures

NO AUTOMATIC REBASELINE. `--update` writes `review.status: UNREVIEWED`, which this gate refuses. A
baseline becomes usable only when a person sets status REVIEWED, names themselves, and points at the
transition report they reviewed (tools/machsig/transition.py). Partial acceptance by hand-editing
entries -- the practice of c3046961 -- is gone: an edited baseline has no single provenance.
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import identity  # noqa: E402

FOUND = identity.FOUND
BASE_REL = "tools/machsig/trust_baseline.json"
BASE = FOUND / BASE_REL
SIGS = FOUND / "artifacts" / "machsig_signatures.jsonl"
OK, FAIL, UNAVAILABLE, REFUSED = 0, 1, 2, 3
BASELINE_SCHEMA = "machsig-trust-baseline/v2"
REGEN = "python3 tools/machsig/regen.py"
HEX40 = re.compile(r"^[0-9a-f]{40}$")
SHA256 = re.compile(r"^sha256:[0-9a-f]{64}$")
PROVENANCE_FIELDS = ("machlib_commit", "machlib_sources", "content_digest", "extractor_digest",
                     "lean_toolchain", "signature_version")


# ── the signature set ──────────────────────────────────────────────────────────────────────────────

def parse_records(body: bytes) -> tuple[dict, list[str]]:
    """{theorem: {"d", "ax", "axioms"}} for every theorem whose trust layer is known."""
    out, bad, seen = {}, [], set()
    for ln in body.decode("utf-8").split("\n"):
        if not ln.strip():
            continue
        j = json.loads(ln)
        if j.get("object") in seen:
            bad.append(f"{j.get('object')} (twice)")   # last-write-wins would hide whichever came first
            continue
        seen.add(j.get("object"))
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
        if len(axioms) != ax:
            bad.append(j["object"])
            continue
        out[j["object"]] = {"d": j["StatementDigest"][:32], "ax": ax, "axioms": sorted(axioms)}
    return out, bad


def read_signature_set(path: Path):
    """(provenance or None, records, refusal or None)."""
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
    records, bad = parse_records(body)
    if bad:
        return head, {}, ("signatures-corrupt", f"{len(bad)} record(s) duplicated or whose TrustAxioms "
                                                f"disagree with their AX count, first {bad[0]}. Regenerate: {REGEN}")
    return head, records, None


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
    if not isinstance(sets, dict) or not isinstance(thms, dict):
        return prov, None, ("baseline-malformed", f"{BASE_REL} lacks axiom_sets/theorems tables")
    out, bad = {}, []
    for name, e in thms.items():
        axs = sets.get(e.get("set")) if isinstance(e, dict) else None
        if axs is None or len(axs) != e.get("ax") or not isinstance(e.get("d"), str):
            bad.append(name)
            continue
        out[name] = {"d": e["d"], "ax": e["ax"], "axioms": list(axs)}
    for sid, axs in sets.items():
        if set_id(axs) != sid:
            bad.append(f"axiom set {sid}")
    if bad:
        return prov, None, ("baseline-malformed", f"{len(bad)} entr(ies) in {BASE_REL} contradict themselves "
                                                  f"(set missing, count != set size, or set id != content), "
                                                  f"first {bad[0]}")
    return prov, out, None


def set_id(axioms) -> str:
    return hashlib.sha256("\n".join(sorted(axioms)).encode()).hexdigest()[:16]


def review_state(b: dict, root: Path) -> list[tuple[str, str]]:
    """The REVIEWED stamp is a process record, not authentication: anyone who can commit can write
    one. What the gate can enforce is that it names a person and a transition report that is part of
    the reviewed tree -- relative, inside foundations/, committed and unmodified. An absolute path
    used to satisfy this check (`Path(root) / "/etc/hostname"` is `/etc/hostname`): found by an
    independent review on 2026-10-13, now selftest cases B19-B20 and a mutant."""
    r = b.get("review") if isinstance(b.get("review"), dict) else {}
    rep = r.get("transition_report")
    why = []
    if r.get("status") != "REVIEWED":
        why.append(f"review.status is {r.get('status')!r}")
    if not r.get("reviewer"):
        why.append("no reviewer named")
    if not rep or not isinstance(rep, str):
        why.append("no transition report named")
    elif Path(rep).is_absolute() or ".." in Path(rep).parts \
            or not (root / rep).resolve().is_relative_to(root.resolve()):
        why.append(f"transition report {rep!r} is not a path inside foundations/")
    elif not (root / rep).is_file():
        why.append(f"transition report {rep} does not exist")
    elif not identity.git_ok(root, "ls-files", "--error-unmatch", "--", rep) \
            or identity.git(root, "status", "--porcelain", "--", rep).strip():
        why.append(f"transition report {rep} is not committed unmodified")
    if why:
        return [("baseline-unreviewed", f"{BASE_REL}: {'; '.join(why)}. A baseline is accepted by a person who "
                                        "reviewed its committed transition report, never by --update.")]
    return []


# ── the comparison ─────────────────────────────────────────────────────────────────────────────────

def compare(base: dict, cur: dict) -> dict:
    """The ratchet's whole decision. Pure: the selftest calls exactly this."""
    acquired, shrank, restated, new = [], [], [], []
    for k in sorted(cur):
        v = cur[k]
        if k not in base:
            new.append(k)
            continue
        b = base[k]
        if b["d"] != v["d"]:
            restated.append(k)
            continue
        entered = sorted(set(v["axioms"]) - set(b["axioms"]))
        left = sorted(set(b["axioms"]) - set(v["axioms"]))
        if entered:
            acquired.append({"theorem": k, "entered": entered, "left": left, "from": b["ax"], "to": v["ax"]})
        elif left:
            shrank.append(k)
    gone = sorted(k for k in base if k not in cur)
    return {"acquired": acquired, "shrank": shrank, "restated": restated, "new": new, "removed": gone}


def report(res: dict, n: int) -> int:
    print(f"  theorems compared : {n}")
    print(f"  statement restated: {len(res['restated'])}   new: {len(res['new'])}   removed: {len(res['removed'])}")
    print(f"  footprint shrank  : {len(res['shrank'])}")
    print(f"  axioms ACQUIRED   : {len(res['acquired'])}")
    if res["acquired"]:
        print("\nMACHSIG-TRUST FAIL — same statement, an axiom entered its footprint")
        for a in sorted(res["acquired"], key=lambda a: (-len(a["entered"]), a["theorem"]))[:12]:
            more = f" (+{len(a['entered']) - 3} more)" if len(a["entered"]) > 3 else ""
            print(f"  - {a['theorem']}  {a['from']} -> {a['to']}  entered {', '.join(a['entered'][:3])}{more}")
        return FAIL
    print("\nMACHSIG-TRUST OK — no theorem acquired an axiom without its statement changing.")
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


def gate(root: Path = FOUND) -> int:
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
    if problem:
        refusals.append(problem)
    else:
        refusals += freshness(head, live)
    refusals += baseline_git_state(root)
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
            refusals += review_state(raw, root)
    if refusals:
        return refuse(refusals)
    print(f"  signatures: {head['version']} from {head['machlib_commit'][:12]} "
          f"(sources {head['content_digest'][7:23]}..., matches this tree)")
    print(f"  baseline  : derived from {raw['provenance']['machlib_commit'][:12]}, reviewed by "
          f"{raw['review']['reviewer']} ({raw['review']['transition_report']})")
    return report(compare(base, cur), len(cur))


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
    for k, v in cur.items():
        sid = set_id(v["axioms"])
        sets[sid] = v["axioms"]
        thms[k] = {"ax": v["ax"], "d": v["d"], "set": sid}
    doc = {
        "schema": BASELINE_SCHEMA,
        "provenance": {
            "machlib_commit": head["machlib_commit"], "machlib_sources": head["machlib_sources"],
            "content_digest": head["content_digest"], "extractor_digest": head["extractor_digest"],
            "extractor_files": head["extractor_files"], "lean_toolchain": head["lean_toolchain"],
            "lean_version": head["lean_version"], "signature_version": head["version"],
            "signature_records_sha256": head["records_sha256"],
        },
        "review": {"status": "UNREVIEWED", "reviewer": None, "transition_report": None,
                   "note": "written by trust_gate.py --update; the gate refuses it until a person who "
                           "reviewed the transition report sets status REVIEWED and names themselves"},
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
        if k in ("axiom_sets", "theorems"):
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


def main(argv: list[str]) -> int:
    if "--update" in argv:
        return update()
    if "--mutate" in argv:
        import trust_gate_selftest
        return trust_gate_selftest.mutate()
    if "--selftest" in argv or "--selftest-only" in argv:
        import trust_gate_selftest
        rc = trust_gate_selftest.run()
        if rc != OK or "--selftest-only" in argv:
            return rc
    return gate()


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
