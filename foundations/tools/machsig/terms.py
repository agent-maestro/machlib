#!/usr/bin/env python3
"""MachSig Phase 1b — term-record driver. Reads extract_terms.lean output, emits
artifacts/machsig_terms.jsonl and the term census statistics."""
import json, subprocess, collections, statistics, pathlib, sys

FOUND = pathlib.Path(__file__).resolve().parent.parent.parent
RAW = FOUND / "artifacts" / "machsig_terms_raw.tsv"
SCHEMA = "MachSig-terms/v0.1"

# grammar-specific meaning of the three generic counters emitted by the walker
COUNTERS = {
    "EMLTree":    ["eml_node_count", "const_node_count", "var_node_count"],
    "CertcomEML": ["trans1_head_total", "elet_count", "cond_node_count"],
}
DEPTH_FIELD = {"EMLTree": "emltree_depth", "CertcomEML": "certcom_eml_depth"}


def main():
    sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=FOUND,
                         capture_output=True, text=True).stdout.strip()[:12]
    recs = []
    for ln in RAW.read_text().split("\n"):
        if not ln.startswith("TERM\t"):
            continue
        f = ln.rstrip("\n").split("\t")
        if len(f) != 11:
            continue
        rep = f[2]
        names = COUNTERS.get(rep, ["c1", "c2", "c3"])
        recs.append({
            "schema_version": SCHEMA,
            "term_record_id": f"{f[1]}#{rep}#{f[3]}",
            "parent_declaration": f[1],
            "representation_kind": rep,
            "term_occurrence": int(f[3]),
            "structural_features": {
                "syntactic_node_count": int(f[4]),
                DEPTH_FIELD.get(rep, "unqualified_depth_BUG"): int(f[6]),
                names[0]: int(f[7]), names[1]: int(f[8]), names[2]: int(f[9]),
            },
            "completeness": {
                "opaque_leaf_count": int(f[5]),
                # a term with opaque leaves is a LOWER BOUND on the tree it denotes
                "structure_complete": f[10].strip() == "true",
                "node_count_is_lower_bound": f[10].strip() != "true",
            },
            "canonical_views": [],
            "availability": {"canonical_views": "unsupported_representation"},
            "provenance": {"extractor": "tools/machsig/extract_terms.lean",
                           "maximality": "records are MAXIMAL grammar occurrences; the walker does "
                                         "not descend past a root of the same grammar",
                           "commit": sha},
        })
    (FOUND / "artifacts").mkdir(exist_ok=True)
    with open(FOUND / "artifacts" / "machsig_terms.jsonl", "w") as fh:
        for r in recs:
            fh.write(json.dumps(r, sort_keys=True) + "\n")
    print(f"terms: {len(recs)}  reps={dict(collections.Counter(r['representation_kind'] for r in recs))}"
          f"  parents={len({r['parent_declaration'] for r in recs})}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
