#!/usr/bin/env python3
"""MachSig Phase 2A/2B — statement census, digests, and natural stability cases."""
import json, hashlib, subprocess, collections, pathlib, sys

FOUND = pathlib.Path(__file__).resolve().parent.parent.parent
RAW = FOUND / "artifacts" / "machsig_stmt_raw.tsv"
SCHEMA = "MachSig-statement/v0.1"


def load():
    rows, pop = [], {}
    for ln in RAW.read_text().split("\n"):
        if ln.startswith("STMT_POPULATION"):
            for kv in ln.split("\t")[1:]:
                k, v = kv.split("="); pop[k] = int(v)
        if not ln.startswith("STMT\t"):
            continue
        f = ln.rstrip("\n").split("\t")
        if len(f) != 17:
            continue
        rows.append({
            "name": f[1], "kind": f[2], "module": f[3],
            "nodes": int(f[4]), "depth": int(f[5]), "eqs": int(f[6]), "imps": int(f[7]),
            "ands": int(f[8]), "ors": int(f[9]), "exists": int(f[10]),
            "distinct_consts": int(f[11]), "ser_len": int(f[12]), "ser": f[13],
            "proof_fp64": f[15], "proof_approx_depth": f[14], "has_value": f[16] == "true",
        })
    return rows, pop


def main():
    sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=FOUND,
                         capture_output=True, text=True).stdout.strip()[:12]
    rows, pop = load()
    for r in rows:
        r["statement_digest"] = hashlib.sha256(r["ser"].encode()).hexdigest()

    # axiom footprints from the Phase 1 declaration census (join on name)
    ax = {}
    cen = FOUND / "artifacts" / "machsig_census.jsonl"
    if cen.exists():
        for ln in cen.read_text().split("\n"):
            if ln.strip():
                j = json.loads(ln)
                ax[j["identity"]["object_name"]] = j["proof_structure"]["axiom_dependency_count"]

    # ---- natural stability cases ----
    # RESTRICTED TO THEOREMS. For a `def`, the "statement" is only its type signature, which many
    # defs share (`Type`, `Real -> Real`); grouping those produced 282 spurious "refactor" groups
    # of unrelated objects on the first run. Only Prop-valued theorems make the digest meaningful.
    by_stmt = collections.defaultdict(list)
    for r in rows:
        if r["kind"] == "theorem":
            by_stmt[r["statement_digest"]].append(r)
    groups = {d: g for d, g in by_stmt.items() if len(g) > 1}

    cases = []
    for d, g in groups.items():
        fps = {x["proof_fp64"] for x in g}
        axv = {x["name"]: ax.get(x["name"]) for x in g}
        seen_ax = {v for v in axv.values() if v is not None}
        cls = "identical_representation"
        if len(fps) > 1:
            cls = "D_trust_surface" if len(seen_ax) > 1 else "A_proof_refactor"
        cases.append({
            "schema_version": SCHEMA, "commit": sha,
            "statement_digest": d[:16], "members": [x["name"] for x in g][:6],
            "member_count": len(g), "distinct_proof_fingerprints": len(fps),
            "class": cls,
            "axiom_footprints": {k.split(".")[-1]: v for k, v in axv.items() if v is not None},
            "axiom_spread": (max(seen_ax) - min(seen_ax)) if len(seen_ax) > 1 else 0,
            "statement_features_identical": True,
        })
    (FOUND / "artifacts").mkdir(exist_ok=True)
    with open(FOUND / "artifacts" / "machsig_stability_cases.jsonl", "w") as f:
        for c in sorted(cases, key=lambda c: -c["member_count"]):
            f.write(json.dumps(c, sort_keys=True) + "\n")

    refac = [c for c in cases if c["class"] == "A_proof_refactor"]
    trust = [c for c in cases if c["class"] == "D_trust_surface"]
    ident = [c for c in cases if c["class"] == "identical_representation"]
    print(f"analyzed={len(rows)} raw={pop.get('raw')} generated_excluded={pop.get('generated_excluded')}")
    print(f"distinct statement digests: {len(by_stmt)}")
    print(f"groups sharing a digest: {len(groups)}  "
          f"(Class A proof-refactor: {len(refac)}, Class D trust-surface: {len(trust)}, "
          f"identical repr: {len(ident)})")
    # feature variation
    for k in ["nodes", "depth", "eqs", "imps", "ands", "ors", "exists", "distinct_consts"]:
        vals = [r[k] for r in rows]
        print(f"  {k:<16} min {min(vals):>3} max {max(vals):>5} distinct {len(set(vals)):>4} "
              f"median {sorted(vals)[len(vals)//2]}")
    if refac:
        top = sorted(refac, key=lambda c: -c["member_count"])[:3]
        for c in top:
            print(f"  refactor group n={c['member_count']} fps={c['distinct_proof_fingerprints']}: {c['members'][:3]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
