#!/usr/bin/env python3
"""MachSig v0.2 — text signatures.

    MachSig tells you whether a formal result changed in WHAT IT CLAIMS, HOW IT IS PROVED,
    or WHAT IT TRUSTS.

THREE LAYERS, and the third is not cosmetic. `ProofSig` and `TrustSig` answer different questions:

    ProofSig   did the proof REPRESENTATION change?
    TrustSig   did what this theorem ultimately RELIES UPON change?

Two proofs can be syntactically unalike while resting on an identical trusted base; conversely a
statement and most of its proof can look unchanged while a new axiom quietly enters the dependency
closure. Nesting trust under proof hides exactly that second case, which is the one worth catching.

    machsig inspect <object-name>
    machsig sigs                     # emit signatures for the whole corpus

TWO LAYERS, NOT THREE. Phase 2 established that the canonical layer has no referent in this corpus
(docs/machsig/CANONICALIZER_BRIDGE.md), so `CanonicalSig` is reported as explicitly UNAVAILABLE
rather than silently filled with the source form.

FIELD SELECTION IS EVIDENCE-DRIVEN. Every field below was classified STATEMENT_SENSITIVE or
TRUST_SURFACE_SIGNAL with usable variation in docs/machsig/STABILITY_REPORT.md. Two candidates were
DROPPED for being degenerate: disjunction_count (5 distinct values, median 0) and existential_count
(9, median 0). They are not in the signature and this docstring is why.
"""
import json, hashlib, sys, pathlib, collections

FOUND = pathlib.Path(__file__).resolve().parent.parent.parent
VERSION = "MachSig/v0.2"

# field abbreviation -> (source key, meaning). Documented in docs/machsig/SIGNATURE_SPEC.md.
STMT_FIELDS = [("N", "nodes",           "statement_expr_node_count"),
               ("D", "depth",           "statement_expr_depth"),
               ("C", "distinct_consts", "distinct_constant_reference_count"),
               ("I", "imps",            "implication_count"),
               ("E", "eqs",             "equality_head_count"),
               ("A", "ands",            "conjunction_count")]
# HOW it is proved -- representation of the proof term.
PROOF_FIELDS = [("PD", "proof_approx_depth",     "proof term approximate depth"),
                ("R",  "value_direct_const_count", "DIRECT constant refs in the proof term")]
# WHAT it trusts -- the dependency closure. Elevated to its own layer in v0.2.
TRUST_FIELDS = [("AX", "axiom_dependency_count", "TRANSITIVE kernel axiom footprint"),
                ("S",  "depends_on_sorry",       "transitive sorryAx reachability")]


def load():
    stmt = {}
    raw = FOUND / "artifacts" / "machsig_stmt_raw.tsv"
    for ln in raw.read_text().split("\n"):
        if not ln.startswith("STMT\t"):
            continue
        f = ln.rstrip("\n").split("\t")
        if len(f) != 17:
            continue
        stmt[f[1]] = {"kind": f[2], "module": f[3], "nodes": int(f[4]), "depth": int(f[5]),
                      "eqs": int(f[6]), "imps": int(f[7]), "ands": int(f[8]), "ors": int(f[9]),
                      "exists": int(f[10]), "distinct_consts": int(f[11]),
                      "statement_digest": hashlib.sha256(f[13].encode()).hexdigest(),
                      "proof_approx_depth": f[14], "proof_expr_fp64": f[15]}
    dec = {}
    cen = FOUND / "artifacts" / "machsig_census.jsonl"
    if cen.exists():
        for ln in cen.read_text().split("\n"):
            if ln.strip():
                j = json.loads(ln)
                dec[j["identity"]["object_name"]] = j["proof_structure"]
    return stmt, dec


def sig_for(name, stmt, dec):
    s = stmt.get(name)
    if s is None:
        return None
    p = dec.get(name, {})
    st = "-".join(f"{ab}{s[k]}" for ab, k, _ in STMT_FIELDS)

    def render(fields):
        pieces = []
        for ab, k, _ in fields:
            if k == "proof_approx_depth":
                v = s.get(k)
                pieces.append(f"{ab}{v}" if v not in (None, "-") else f"{ab}?")
            elif k == "depends_on_sorry":
                v = p.get(k)
                pieces.append(f"{ab}{1 if v else 0}" if v is not None else f"{ab}?")
            else:
                v = p.get(k)
                pieces.append(f"{ab}{v}" if v is not None else f"{ab}?")
        return "-".join(pieces)
    return {
        "version": VERSION, "object": name, "kind": s["kind"], "module": s["module"],
        "StatementSig": st, "ProofSig": render(PROOF_FIELDS),
        "TrustSig": render(TRUST_FIELDS),
        "StatementDigest": s["statement_digest"],
        "ProofFingerprint64": s["proof_expr_fp64"],
        "CanonicalSig": None,
        "canonical_status": "unavailable: no MachLib canonicalizer has an extractable input "
                            "for this representation (see CANONICALIZER_BRIDGE.md)",
        "statement_digest_meaningful": s["kind"] == "theorem",
    }


def main(argv):
    stmt, dec = load()
    if len(argv) >= 2 and argv[0] == "inspect":
        name = argv[1]
        cands = [n for n in stmt if n == name or n.split(".")[-1] == name]
        if not cands:
            print(f"no such object in the census: {name}"); return 1
        for n in cands[:5]:
            r = sig_for(n, stmt, dec)
            print(f"\n{r['version']}\nObject: {r['object']}   [{r['kind']}]   {r['module']}\n")
            print(f"  StatementSig       {r['StatementSig']}   (what it claims)")
            print(f"  ProofSig           {r['ProofSig']}      (how it is proved)")
            print(f"  TrustSig           {r['TrustSig']}      (what it relies upon)")
            print(f"  CanonicalSig       UNAVAILABLE")
            print(f"                     {r['canonical_status']}")
            print(f"  StatementDigest    {r['StatementDigest'][:32]}…")
            print(f"  ProofFingerprint   {r['ProofFingerprint64']}  (64-bit, non-cryptographic)")
            if not r["statement_digest_meaningful"]:
                print("\n  NOTE: this is not a theorem. Its 'statement' is a bare type signature,")
                print("        which many declarations share, so StatementDigest does not identify it.")
        return 0
    if argv and argv[0] == "sigs":
        out = FOUND / "artifacts" / "machsig_signatures.jsonl"
        n = 0
        with open(out, "w") as fh:
            for name in sorted(stmt):
                r = sig_for(name, stmt, dec)
                if r:
                    fh.write(json.dumps(r, sort_keys=True) + "\n"); n += 1
        # how discriminating is the composed StatementSig?
        sigs = collections.Counter()
        for name in stmt:
            if stmt[name]["kind"] == "theorem":
                sigs["-".join(f"{ab}{stmt[name][k]}" for ab, k, _ in STMT_FIELDS)] += 1
        print(f"signatures: {n} written to {out.name}")
        print(f"theorem StatementSig values: {len(sigs)} distinct over {sum(sigs.values())} theorems")
        print(f"  largest collision class: {sigs.most_common(1)[0][1]}")
        return 0
    print(__doc__); return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
