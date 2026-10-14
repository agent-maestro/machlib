#!/usr/bin/env python3
"""MachSig transition report: an old trust baseline against new signatures, every change classified.

    python3 tools/machsig/transition.py --evidence DIR --out-md M --out-json J --packet P

The owner's ruling of 2026-10-13, steps 3-4 (and the machinery for 6): "Produce a deterministic
old-versus-new transition report. Classify changes by type and trust implications." The output is a
pure function of the evidence files, whose sha256 it prints: rerun on the same evidence and the
report is byte-identical (no clock, no environment, every collection sorted).

THE EVIDENCE (one directory, file names fixed; see collect_evidence.py for how each is produced)
  committed_baseline_23e0d047.json   the 2026-09-03 baseline as committed (git show)
  legacy_regen_23e0d047.json         that baseline REBUILT: cold build of 23e0d047, that commit's
                                     own extractor and --update. Byte-identical = reconstructed.
  committed_baseline_c3046961.json   the baseline as of c3046961 (the 2026-09-03 one + 10 hand edits)
  legacy_regen_c3046961.json         the pre-v0.3 pipeline at c3046961 (what the gate saw on 10-13)
  sigs_23e0d047.jsonl                v0.3 signatures (axiom SETS) at 23e0d047
  sigs_new.jsonl                     v0.3 signatures at the new revision
  policy_23e0d047.json / policy_new.json   AxiomLedger knownAxioms + trustedFootprint at each side
  statements_23e0d047.json / statements_new.json   pretty-printed statements (probe.statements)
  axiom_history.json                 for each axiom that appeared or disappeared, the commits (pickaxe)
  targeted.json                      optional: the seeded `#print axioms` checks (targeted_check.py)

ATTRIBUTION. A change between the old baseline and the new signatures can come from three places,
and each is measured separately rather than inferred:
  baseline edit   the committed baseline differs from what its own revision extracts
                  (committed_baseline_c3046961 vs the 2026-09-03 baseline)
  extractor       the SAME revision under the old vs the new extractor
                  (legacy_regen_X vs sigs_X, compared on statement digest and axiom count)
  source          the SAME (new) extractor on the old vs the new revision (sigs_23e0d047 vs sigs_new)
"""
from __future__ import annotations

import argparse
import collections
import hashlib
import json
import re
import sys
from pathlib import Path

STD = ("Classical.choice", "Quot.sound", "propext")
SORRY = "sorryAx"
COMPILER = ("Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler")
NATIVE = re.compile(r"(^|\.)_native\..+\.ax(_\d+)*$")

EVIDENCE = {
    "committed_0903": "committed_baseline_23e0d047.json",
    "recon_0903": "legacy_regen_23e0d047.json",
    "committed_c3": "committed_baseline_c3046961.json",
    "legacy_new": "legacy_regen_c3046961.json",
    "sigs_old": "sigs_23e0d047.jsonl",
    "sigs_new": "sigs_new.jsonl",
    "policy_old": "policy_23e0d047.json",
    "policy_new": "policy_new.json",
    "stmts_old": "statements_23e0d047.json",
    "stmts_new": "statements_new.json",
    "history": "axiom_history.json",
    "targeted": "targeted.json",
    "stale_local": "stale_local_sigs_20260903.jsonl",
    "legacy_sigs_old": "legacy_sigs_23e0d047.jsonl",
    "candidate": "trust_baseline.candidate.json",
}
OPTIONAL = {"targeted", "stale_local", "legacy_sigs_old", "candidate"}

# Trust classes, in precedence order: a change belongs to the FIRST that applies.
TRUST_CLASSES = [
    ("sorry", "sorryAx entered or left (must be only the allowlisted theorem)"),
    ("other", "a compiler-trust or undeclared axiom entered or left"),
    ("assumption-conditional", "a conditional MachLib axiom (declared, OUTSIDE trustedFootprint) entered or left: "
                               "what the theorem is conditional on changed"),
    ("assumption-foundation", "only MachLib axioms INSIDE trustedFootprint (the approved foundation) entered or "
                              "left, possibly with standard Lean axioms"),
    ("standard-only", "only propext / Classical.choice / Quot.sound entered or left"),
    ("no-axiom-change", "the axiom set is identical"),
]


# ── loading ────────────────────────────────────────────────────────────────────────────────────────

def sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def load_sigset(p: Path) -> tuple[dict, dict]:
    """(header, {name: record}) for every object; theorems carry d (32 hex), ax, axioms."""
    head, recs = {}, {}
    for i, ln in enumerate(p.read_text().split("\n")):
        if not ln.strip():
            continue
        j = json.loads(ln)
        if i == 0 and j.get("kind") == "machsig-provenance":
            head = j
            continue
        ax = None
        for part in j.get("TrustSig", "").split("-"):
            if part.startswith("AX") and part[2:].isdigit():
                ax = int(part[2:])
        recs[j["object"]] = {"kind": j["kind"], "module": j["module"], "d": j["StatementDigest"][:32],
                             "ax": ax, "axioms": j.get("TrustAxioms")}
    return head, recs


def watched(recs: dict) -> dict:
    """The gate's population: theorems whose trust layer is known."""
    return {k: v for k, v in recs.items() if v["kind"] == "theorem" and v["axioms"] is not None}


def load_legacy(p: Path) -> dict:
    return {k: {"d": v["d"], "ax": v["ax"]} for k, v in json.loads(p.read_text()).items()}


# ── classification ─────────────────────────────────────────────────────────────────────────────────

def axiom_class(a: str, policy: dict) -> str:
    if a in STD:
        return "std"
    if a == SORRY:
        return "sorry"
    if a in COMPILER or NATIVE.search(a):
        return "compiler"
    if a in policy["trusted_set"]:
        return "trusted"
    if a in policy["known_set"]:
        return "conditional"
    return "undeclared"


def tier(axioms: list[str], policy: dict) -> tuple[str, list[str]]:
    """tools/theorem_ledger/ledger.py classify(), on the same two lists."""
    fp = set(axioms)
    bad = [a for a in fp if a == SORRY or a in COMPILER or NATIVE.search(a)
           or a not in policy["known_set"] | policy["trusted_set"]]
    if bad:
        return "unchecked", sorted(bad)
    if fp <= policy["trusted_set"]:
        return "approved_policy", []
    return "conditional", sorted(fp - policy["trusted_set"])


def trust_class(entered: list[str], left: list[str], p_old: dict, p_new: dict) -> str:
    cls = {axiom_class(a, p_new) for a in entered} | {axiom_class(a, p_old) for a in left}
    if "sorry" in cls:
        return "sorry"
    if cls & {"compiler", "undeclared"}:
        return "other"
    if "conditional" in cls:
        return "assumption-conditional"
    if "trusted" in cls:
        return "assumption-foundation"
    if "std" in cls:
        return "standard-only"
    return "no-axiom-change"


def kind_of(old: dict | None, new: dict | None) -> str:
    """The pre-v0.3 gate's own categories (count-based), plus `swap`, which it could not see."""
    if old is None:
        return "new"
    if new is None:
        return "removed"
    if old["d"] != new["d"]:
        return "restated"
    if new["ax"] > old["ax"]:
        return "grew"
    if new["ax"] < old["ax"]:
        return "shrank"
    if old.get("axioms") is not None and sorted(old["axioms"]) != sorted(new["axioms"]):
        return "swap"
    return "unchanged"


def prepare_policy(raw: dict) -> dict:
    return dict(raw, known_set=set(raw["known"]), trusted_set=set(raw["trusted"]))


# ── the transition ─────────────────────────────────────────────────────────────────────────────────

def build(ev: dict) -> dict:
    """Every number in the report comes out of this function."""
    base = load_legacy(ev["committed_0903"])
    recon_identical = ev["committed_0903"].read_bytes() == ev["recon_0903"].read_bytes()
    recon = load_legacy(ev["recon_0903"])
    c3 = load_legacy(ev["committed_c3"])
    legacy_new = load_legacy(ev["legacy_new"])
    head_old, all_old = load_sigset(ev["sigs_old"])
    head_new, all_new = load_sigset(ev["sigs_new"])
    old_w, new_w = watched(all_old), watched(all_new)
    p_old = prepare_policy(json.loads(ev["policy_old"].read_text()))
    p_new = prepare_policy(json.loads(ev["policy_new"].read_text()))

    def same(a: dict | None, b: dict | None) -> bool:
        return (a is None) == (b is None) and (a is None or (a["d"] == b["d"] and a["ax"] == b["ax"]))

    # extractor: the same revision, old pipeline vs v0.3 pipeline
    ext_old = sorted(k for k in set(recon) | set(old_w) if not same(recon.get(k), old_w.get(k)))
    ext_new = sorted(k for k in set(legacy_new) | set(new_w) if not same(legacy_new.get(k), new_w.get(k)))
    # baseline edits: what c3046961 changed by hand, and whether it equals what the tree extracts
    edits = sorted(k for k in set(c3) | set(base) if not same(c3.get(k), base.get(k)))
    edit_rows = [{"theorem": k, "baseline_0903": base.get(k), "baseline_c3046961": c3.get(k),
                  "extracted_new": ({"d": new_w[k]["d"], "ax": new_w[k]["ax"]} if k in new_w else None),
                  "matches_extraction": same(c3.get(k), {"d": new_w[k]["d"], "ax": new_w[k]["ax"]}
                                             if k in new_w else None)} for k in edits]

    rows = []
    for k in sorted(set(base) | set(new_w)):
        b = base.get(k)
        o = old_w.get(k)
        n = new_w.get(k)
        old = None
        if b is not None:
            old = dict(b, axioms=(sorted(o["axioms"]) if o is not None and same(b, o) else None))
        kind = kind_of(old, n)
        if kind == "unchanged":
            continue
        row = {"theorem": k, "kind": kind,
               "module": (n or all_old.get(k) or {}).get("module"),
               "old": None, "new": None, "entered": [], "left": []}
        if old is not None:
            row["old"] = {"d": old["d"], "ax": old["ax"], "axioms": old["axioms"]}
            if old["axioms"] is not None:
                row["old"]["tier"], row["old"]["outside_policy"] = tier(old["axioms"], p_old)
        if n is not None:
            row["new"] = {"d": n["d"], "ax": n["ax"], "axioms": sorted(n["axioms"])}
            row["new"]["tier"], row["new"]["outside_policy"] = tier(n["axioms"], p_new)
        if old is not None and n is not None and old["axioms"] is not None:
            row["entered"] = sorted(set(n["axioms"]) - set(old["axioms"]))
            row["left"] = sorted(set(old["axioms"]) - set(n["axioms"]))
            row["trust_class"] = trust_class(row["entered"], row["left"], p_old, p_new)
        elif kind == "new":
            row["trust_class"] = "new:" + row["new"]["tier"]
        elif kind == "removed":
            row["trust_class"] = "removed:" + (row["old"].get("tier") or "set-unknown")
        else:
            row["trust_class"] = "set-unknown"
        causes = []
        if k in edits:
            causes.append("baseline-edit")
        if k in ext_old or k in ext_new:
            causes.append("extractor")
        if not same(o, n) or (o is not None and n is not None and sorted(o["axioms"]) != sorted(n["axioms"])):
            causes.append("source")
        row["causes"] = causes
        rows.append(row)

    # delta groups: theorems sharing exactly the same (entered, left) pair
    groups = collections.defaultdict(list)
    for r in rows:
        if r["kind"] in ("grew", "shrank", "swap", "restated") and r["old"] and r["old"]["axioms"] is not None:
            groups[(tuple(r["entered"]), tuple(r["left"]))].append(r["theorem"])
    order = sorted(groups.items(), key=lambda kv: (-len(kv[1]), kv[0]))
    gid = {key: f"G{i + 1:03d}" for i, (key, _) in enumerate(order)}
    for r in rows:
        key = (tuple(r["entered"]), tuple(r["left"]))
        if key in gid and r["kind"] in ("grew", "shrank", "swap", "restated"):
            r["group"] = gid[key]
    group_list = [{"id": gid[key], "entered": list(key[0]), "left": list(key[1]), "size": len(names),
                   "trust_class": trust_class(list(key[0]), list(key[1]), p_old, p_new),
                   "theorems": sorted(names)} for key, names in order]

    # axioms whose STATUS changed between the revisions (an axiom at one side and not the other)
    ax_old = {k for k, v in all_old.items() if v["kind"] == "axiom"}
    ax_new = {k for k, v in all_new.items() if v["kind"] == "axiom"}
    moved_axioms = {
        "axiom_then_not_now": sorted(ax_old - ax_new),
        "axiom_now_not_then": sorted(ax_new - ax_old),
        "now_theorem": sorted(a for a in ax_old - ax_new if all_new.get(a, {}).get("kind") == "theorem"),
        "now_definition": sorted(a for a in ax_old - ax_new if all_new.get(a, {}).get("kind") == "def"),
        "now_absent": sorted(a for a in ax_old - ax_new if a not in all_new),
    }
    policy_delta = {
        "trusted_added": sorted(p_new["trusted_set"] - p_old["trusted_set"]),
        "trusted_removed": sorted(p_old["trusted_set"] - p_new["trusted_set"]),
        "known_added": sorted(p_new["known_set"] - p_old["known_set"]),
        "known_removed": sorted(p_old["known_set"] - p_new["known_set"]),
    }
    sorry_now = sorted(k for k, v in new_w.items() if SORRY in v["axioms"])

    # MECHANISM (the owner's step 6: reproducible classification of the big groups). An axiom that
    # stopped being an axiom between the revisions was DISCHARGED (proved, or made a definition); every
    # theorem that used it now uses its proof instead, so the axiom LEAVES its footprint and the axioms
    # of that proof ENTER. A change is EXPLAINED BY DISCHARGE when every entered axiom lies in the new
    # footprint of some discharged axiom that left. Anything else is listed for a person to read.
    gone, born = set(moved_axioms["axiom_then_not_now"]), set(moved_axioms["axiom_now_not_then"])
    for r in rows:
        if r["kind"] not in ("grew", "shrank", "swap", "restated") or r["old"]["axioms"] is None:
            continue
        left, entered = set(r["left"]), set(r["entered"])
        discharged, kept = left & gone, left - gone
        union = set()
        for x in discharged:
            fx = all_new.get(x, {}).get("axioms")
            if fx is not None:
                union |= set(fx)
        if entered & born:
            mech = "new-axiom-entered"
        elif discharged and not kept:
            mech = "discharge"
        elif discharged:
            mech = "discharge+proof-change"
        elif entered or left:
            mech = "proof-change"
        else:
            mech = "statement-only"
        r["mechanism"] = mech
        r["discharged_left"] = sorted(discharged)
        r["unexplained_entered"] = sorted(entered - union)
        r["explained_by_discharge"] = not (entered - union) and not kept and not (entered & born)
    # a removed theorem whose exact statement now lives under another name was renamed or moved
    by_digest = collections.defaultdict(list)
    for k, v in new_w.items():
        by_digest[v["d"]].append(k)
    for r in rows:
        if r["kind"] == "removed":
            r["statement_now_held_by"] = sorted(n for n in by_digest.get(r["old"]["d"], []) if n not in base)
            r["still_in_new_environment"] = r["theorem"] in all_new
    # what the pre-v0.3 gate itself reported on 2026-10-13: c3046961's committed baseline against the
    # pre-v0.3 pipeline run at c3046961 (count rule)
    gate_view = collections.Counter(kind_of(c3.get(k), legacy_new.get(k)) for k in set(c3) | set(legacy_new))
    certcom_unwatched = sum(1 for k, v in all_new.items()
                            if v["kind"] == "theorem" and k.startswith("Certcom.") and v["axioms"] is None)
    candidate = None
    if "candidate" in ev:
        # The baseline a reviewer would commit: it must hold exactly the new side of this report.
        cb = json.loads(ev["candidate"].read_text())
        sets, thms = cb.get("axiom_sets", {}), cb.get("theorems", {})
        decoded = {k: {"d": e["d"], "ax": e["ax"], "axioms": sorted(sets.get(e["set"], []))} for k, e in thms.items()}
        want = {k: {"d": v["d"], "ax": v["ax"], "axioms": sorted(v["axioms"])} for k, v in new_w.items()}
        candidate = {"theorems": len(decoded), "axiom_sets": len(sets), "equals_new_side": decoded == want,
                     "provenance": cb.get("provenance", {}).get("machlib_commit"),
                     "signature_records_sha256": cb.get("provenance", {}).get("signature_records_sha256"),
                     "matches_signature_set": cb.get("provenance", {}).get("signature_records_sha256")
                     == head_new.get("records_sha256"),
                     "review_status": (cb.get("review") or {}).get("status")}
    return {
        "candidate": candidate,
        "legacy_gate_view_c3046961": dict(sorted(gate_view.items())),
        "certcom_theorems_unwatched": certcom_unwatched,
        "recon_identical": recon_identical,
        "recon_value_diffs": sorted(k for k in set(base) | set(recon) if not same(base.get(k), recon.get(k))),
        "extractor_delta_old": ext_old, "extractor_delta_new": ext_new,
        "baseline_edits": edit_rows,
        "rows": rows, "groups": group_list,
        "moved_axioms": moved_axioms, "policy_delta": policy_delta,
        "sorry_now": sorry_now, "sorry_allowlist": sorted(p_new.get("allowed_sorry", [])),
        "population": {"baseline_0903": len(base), "baseline_c3046961": len(c3), "old_watched": len(old_w),
                       "new_watched": len(new_w), "legacy_new": len(legacy_new)},
        "heads": {"old": {k: head_old.get(k) for k in ("machlib_commit", "machlib_sources", "content_digest",
                                                       "extractor_digest", "lean_toolchain", "lean_version",
                                                       "records", "records_sha256", "sources_clean")},
                  "new": {k: head_new.get(k) for k in ("machlib_commit", "machlib_sources", "content_digest",
                                                       "extractor_digest", "lean_toolchain", "lean_version",
                                                       "records", "records_sha256", "sources_clean")}},
        "policy_counts": {"old": {"known": len(p_old["known"]), "trusted": len(p_old["trusted"])},
                          "new": {"known": len(p_new["known"]), "trusted": len(p_new["trusted"])}},
    }


def evidence_paths(d: Path) -> dict:
    ev = {}
    for key, name in EVIDENCE.items():
        p = d / name
        if p.is_file():
            ev[key] = p
        elif key not in OPTIONAL:
            raise SystemExit(f"transition: missing evidence file {p}")
    return ev


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--evidence", required=True, type=Path)
    ap.add_argument("--out-md", type=Path)
    ap.add_argument("--out-json", type=Path)
    ap.add_argument("--packet", type=Path)
    a = ap.parse_args(argv)
    ev = evidence_paths(a.evidence)
    t = build(ev)
    import transition_render as render
    manifest = {EVIDENCE[k]: sha256(p) for k, p in sorted(ev.items())}
    if a.out_json:
        a.out_json.write_text(render.as_json(t, manifest, ev))
    if a.out_md:
        a.out_md.write_text(render.as_markdown(t, manifest, ev))
    if a.packet:
        a.packet.write_text(render.packet(t, manifest, ev))
    print(render.summary_line(t))
    return 0


if __name__ == "__main__":
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    sys.exit(main(sys.argv[1:]))
