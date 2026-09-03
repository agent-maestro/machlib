#!/usr/bin/env python3
"""MachSig Phase 1 — typed, representation-aware census.

Reads the TSV emitted by tools/machsig/extract.lean and produces:
    artifacts/machsig_census.jsonl   (AUTHORITATIVE — nested, heterogeneous)
    artifacts/machsig_census.csv     (flattened union, explicit nulls, convenience only)
    docs/machsig/CENSUS_REPORT.md

Design constraints taken from the Phase 1 amendment:
  * every feature carries representation_scope / semantic_kind / value_type / epistemic_type
  * absence is TYPED (unsupported_representation / not_applicable / not_computed), never bare null
  * no bare `depth` field is ever emitted
  * bounds are never presented as counts
"""
import json, os, subprocess, sys, collections, statistics, pathlib

FOUND = pathlib.Path(__file__).resolve().parent.parent.parent
RAW = FOUND / "artifacts" / "machsig_raw.tsv"
SCHEMA_VERSION = "MachSig-census/v0.1"


def commit() -> str:
    try:
        return subprocess.run(["git", "rev-parse", "HEAD"], cwd=FOUND,
                              capture_output=True, text=True).stdout.strip()[:12]
    except Exception:
        return "unknown"


def read_rows():
    rows = []
    for ln in RAW.read_text().split("\n"):
        if not ln.startswith("MSIG\t"):
            continue
        f = ln.split("\t")
        if len(f) != 11:
            continue
        rows.append({
            "name": f[1], "kind": f[2], "module": f[3],
            "binder_count": int(f[4]), "prop_binder_count": int(f[5]),
            "axiom_count": int(f[6]), "depends_on_sorry": f[7] == "true",
            "type_direct_consts": int(f[8]), "value_direct_consts": int(f[9]),
            "has_value": f[10] == "true",
        })
    return rows


def record(r, sha):
    """One census record. Nested by provenance family, per the amendment."""
    non_prop = r["binder_count"] - r["prop_binder_count"]
    return {
        "schema_version": SCHEMA_VERSION,
        "identity": {
            "object_name": r["name"],
            "namespace": r["name"].rsplit(".", 1)[0] if "." in r["name"] else "",
            "declaration_kind": r["kind"],
            "source_module": r["module"],
            "commit": sha,
        },
        # Declaration-level type structure. NOT a grammar term: see availability below.
        "source_views": [{
            "representation_kind": "LeanDeclarationType",
            "structural_features": {
                "binder_count": r["binder_count"],
                "prop_binder_count": r["prop_binder_count"],
                "non_prop_binder_count": non_prop,
            },
            "sharing_features": None,
            "constructor_distribution": None,
        }],
        "canonical_views": [],
        "proof_structure": {
            "axiom_dependency_count": r["axiom_count"],
            "depends_on_sorry": r["depends_on_sorry"],
            "type_direct_const_count": r["type_direct_consts"],
            "value_direct_const_count": r["value_direct_consts"] if r["has_value"] else None,
            "transitive_dependency_count": None,
            "proof_dependency_depth": None,
        },
        "certified_bounds": [],
        "derived_metrics": {
            # documented formula; guarded denominator
            "prop_binder_fraction": (
                round(r["prop_binder_count"] / r["binder_count"], 4)
                if r["binder_count"] > 0 else None),
        },
        "availability": {
            "canonical_views": "unsupported_representation",
            "grammar_term_features": "not_applicable",
            "certified_bounds": "not_computed",
            "transitive_dependency_count": "not_computed",
            "proof_dependency_depth": "not_computed",
            "value_direct_const_count": "available" if r["has_value"] else "not_applicable",
            "sharing_features": "not_applicable",
        },
        "provenance": {
            "extractor": "tools/machsig/extract.lean",
            "proof_spine": "Lean.collectAxioms + getEnv (same mechanism as AxiomLedger.lean)",
            "driver": "tools/machsig/census.py",
        },
    }


NUMERIC = [
    ("source_views[0].structural_features.binder_count", lambda x: x["source_views"][0]["structural_features"]["binder_count"]),
    ("source_views[0].structural_features.prop_binder_count", lambda x: x["source_views"][0]["structural_features"]["prop_binder_count"]),
    ("source_views[0].structural_features.non_prop_binder_count", lambda x: x["source_views"][0]["structural_features"]["non_prop_binder_count"]),
    ("proof_structure.axiom_dependency_count", lambda x: x["proof_structure"]["axiom_dependency_count"]),
    ("proof_structure.type_direct_const_count", lambda x: x["proof_structure"]["type_direct_const_count"]),
    ("proof_structure.value_direct_const_count", lambda x: x["proof_structure"]["value_direct_const_count"]),
    ("derived_metrics.prop_binder_fraction", lambda x: x["derived_metrics"]["prop_binder_fraction"]),
]


def stats(vals):
    present = [v for v in vals if v is not None]
    if not present:
        return None
    return {
        "coverage": len(present), "null_rate": round(1 - len(present) / len(vals), 4),
        "distinct": len(set(present)), "min": min(present), "max": max(present),
        "median": statistics.median(present),
    }


def main():
    sha = commit()
    rows = read_rows()
    recs = [record(r, sha) for r in rows]
    (FOUND / "artifacts").mkdir(exist_ok=True)
    with open(FOUND / "artifacts" / "machsig_census.jsonl", "w") as f:
        for rec in recs:
            f.write(json.dumps(rec, sort_keys=True) + "\n")

    # CSV: flattened union, explicit nulls. Convenience only; JSONL is authoritative.
    import csv
    cols = ["object_name", "declaration_kind", "source_module", "binder_count",
            "prop_binder_count", "non_prop_binder_count", "axiom_dependency_count",
            "depends_on_sorry", "type_direct_const_count", "value_direct_const_count",
            "prop_binder_fraction", "canonical_views_availability"]
    with open(FOUND / "artifacts" / "machsig_census.csv", "w", newline="") as f:
        w = csv.writer(f); w.writerow(cols)
        for x in recs:
            sv = x["source_views"][0]["structural_features"]
            w.writerow([x["identity"]["object_name"], x["identity"]["declaration_kind"],
                        x["identity"]["source_module"], sv["binder_count"],
                        sv["prop_binder_count"], sv["non_prop_binder_count"],
                        x["proof_structure"]["axiom_dependency_count"],
                        x["proof_structure"]["depends_on_sorry"],
                        x["proof_structure"]["type_direct_const_count"],
                        "" if x["proof_structure"]["value_direct_const_count"] is None
                           else x["proof_structure"]["value_direct_const_count"],
                        "" if x["derived_metrics"]["prop_binder_fraction"] is None
                           else x["derived_metrics"]["prop_binder_fraction"],
                        x["availability"]["canonical_views"]])

    kinds = collections.Counter(x["identity"]["declaration_kind"] for x in recs)
    sorry_ct = sum(1 for x in recs if x["proof_structure"]["depends_on_sorry"])
    lines = [f"""# MachSig Phase 1 — Census Report

`{SCHEMA_VERSION}` · commit `{sha}` · **{len(recs)} declarations**

Authoritative output: `artifacts/machsig_census.jsonl`.
`artifacts/machsig_census.csv` is a flattened union with explicit blanks and is convenience only.

## Population, and what it is NOT

The population is **MachLib Lean declarations** — every non-internal constant under the `MachLib`
namespace, taken from `getEnv`. That is {len(recs)} objects, which is roughly 2.5× the ~5,455 figure
this project's notes carry for "declarations"; that older number was a narrower scope (theorems
reached by the sorry audit), and the two should not be quoted interchangeably.

**The grammar-level features of Phase 0.5 are absent from this census, and absent is not null.**
`eml_node_count`, `fOcc` and `trans1_head_counts` are properties of *terms*. A Lean declaration does
not *have* an `EMLTree` unless one occurs inside it, so these are recorded as
`grammar_term_features: not_applicable` at declaration scope. Extracting them needs a separate
term-level walker over the specific grammars, which Phase 1 has not built.

## Declaration kinds

| kind | count |
|---|---:|
""" + "\n".join(f"| `{k}` | {v} |" for k, v in kinds.most_common()) + f"""

## Feature statistics

| feature | coverage | null rate | distinct | min | max | median |
|---|---:|---:|---:|---:|---:|---:|
"""]
    for label, get in NUMERIC:
        s = stats([get(x) for x in recs])
        if s:
            lines.append(f"| `{label}` | {s['coverage']} | {s['null_rate']} | {s['distinct']} | "
                         f"{s['min']} | {s['max']} | {s['median']} |")
    lines.append(f"""

## Epistemic status of every column above

All of them are `computed` — machine-counted from the kernel's own data structures. **None is a
mathematical measurement**, and none is a bound. Specifically:

* `binder_count` / `prop_binder_count` count `∀`-binders in the declaration's *type*, with
  `prop_binder_count` decided by `Meta.isProp`. They are syntactic properties of a statement, not
  of the mathematics it describes.
* `axiom_dependency_count` is `Lean.collectAxioms` — the kernel's transitive axiom footprint. It is
  exact and machine-checked, and it is the one column here with real trust weight.
* `type_direct_const_count` / `value_direct_const_count` are **direct** surface references, not the
  transitive closure. They are deliberately not called dependencies-of-the-proof.

## Sorry status

`depends_on_sorry = true`: **{sorry_ct}** of {len(recs)}. This should agree with
`tools/sorry_audit.lean`; if it does not, one of the two is wrong and the disagreement is the
finding. See `PHASE1_ISSUES.md`.

## What is deliberately empty

| family | availability | why |
|---|---|---|
| `canonical_views` | `unsupported_representation` | Phase 0 Finding 3: no canonicalizer exists for a Lean declaration. Substituting the source form would make Phase 6's drift gate unable to fire. |
| `certified_bounds` | `not_computed` | Phase 0 Finding 4: counts like `ZeroCountOn` are *propositions carrying a bound as a parameter*. Extracting them needs statement-shape analysis, not a counter. |
| `transitive_dependency_count` | `not_computed` | `collectAxioms` gives the transitive *axiom* view; a general transitive const closure was not computed. |
| `proof_dependency_depth` | `not_computed` | No depth calculation exists. Per the amendment, it is not called `proof_depth` and not guessed. |
| grammar term features | `not_applicable` | wrong scope — see above. |
""")
    (FOUND / "docs" / "machsig").mkdir(parents=True, exist_ok=True)
    (FOUND / "docs" / "machsig" / "CENSUS_REPORT.md").write_text("\n".join(lines))
    print(f"census: {len(recs)} records; sorry-dependent {sorry_ct}; kinds {dict(kinds)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
