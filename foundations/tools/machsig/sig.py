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

v0.3 (2026-10-13): TrustSig carries the axiom SET (`TrustAxioms`), not only its size, and every
signature set begins with a PROVENANCE record naming the source tree, the extractor and the
toolchain it was extracted from (tools/machsig/identity.py). `sigs` refuses to write a set unless the
raw extraction was produced by tools/machsig/regen.py, which is what binds it to an identity: a
signature set nobody can date is the defect that left the trust gate blind from 2026-09-03 to
2026-10-13.

TWO LAYERS, NOT THREE. Phase 2 established that the canonical layer has no referent in this corpus
(docs/machsig/CANONICALIZER_BRIDGE.md), so `CanonicalSig` is reported as explicitly UNAVAILABLE
rather than silently filled with the source form.

FIELD SELECTION IS EVIDENCE-DRIVEN. Every field below was classified STATEMENT_SENSITIVE or
TRUST_SURFACE_SIGNAL with usable variation in docs/machsig/STABILITY_REPORT.md. Two candidates were
DROPPED for being degenerate: disjunction_count (5 distinct values, median 0) and existential_count
(9, median 0). They are not in the signature and this docstring is why.
"""
import json, hashlib, sys, pathlib, collections

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import identity  # noqa: E402

FOUND = pathlib.Path(__file__).resolve().parent.parent.parent
VERSION = "MachSig/v0.3"
EXTRACTION = FOUND / "artifacts" / "machsig_extraction.json"
RAW_FILES = ("machsig_stmt_raw.tsv", "machsig_raw.tsv")

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


class Refused(Exception):
    """The inputs cannot yield a faithful signature set. Fatal, never skipped."""


def load():
    stmt = {}
    raw = FOUND / "artifacts" / "machsig_stmt_raw.tsv"
    bad, analyzed = [], None
    for ln in raw.read_text().split("\n"):
        if ln.startswith("STMT_POPULATION\t"):
            analyzed = int(dict(kv.split("=") for kv in ln.split("\t")[1:])["analyzed"])
        if not ln.startswith("STMT\t"):
            continue
        f = ln.rstrip("\n").split("\t")
        if len(f) != 17:
            # A tab or newline inside a string literal in a statement would split the row. Until
            # v0.3 such a row was skipped silently -- a theorem the gate then never watched.
            bad.append(f[1] if len(f) > 1 else ln[:80])
            continue
        if f[1] in stmt:
            # a dict keyed by name keeps the LAST row: a second row would silently replace the first
            bad.append(f"{f[1]} (twice)")
            continue
        stmt[f[1]] = {"kind": f[2], "module": f[3], "nodes": int(f[4]), "depth": int(f[5]),
                      "eqs": int(f[6]), "imps": int(f[7]), "ands": int(f[8]), "ors": int(f[9]),
                      "exists": int(f[10]), "distinct_consts": int(f[11]),
                      "statement_digest": hashlib.sha256(f[13].encode()).hexdigest(),
                      "proof_approx_depth": f[14], "proof_expr_fp64": f[15]}
    if bad:
        raise Refused(f"{len(bad)} unreadable STMT row(s) in {raw.name}; first: {bad[0]}")
    if analyzed is None or analyzed != len(stmt):
        raise Refused(f"{raw.name}: STMT_POPULATION analyzed={analyzed} but {len(stmt)} rows read "
                      "(truncated or interrupted extraction)")
    dec = {}
    cen = FOUND / "artifacts" / "machsig_census.jsonl"
    if cen.exists():
        for ln in cen.read_text().split("\n"):
            if ln.strip():
                j = json.loads(ln)
                if j["identity"]["object_name"] in dec:
                    raise Refused(f"{cen.name} names {j['identity']['object_name']} twice")
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
    axs = p.get("axiom_dependencies")
    return {
        "version": VERSION, "object": name, "kind": s["kind"], "module": s["module"],
        "StatementSig": st, "ProofSig": render(PROOF_FIELDS),
        "TrustSig": render(TRUST_FIELDS),
        # The set behind TrustSig's AX count; None exactly when AX is `?` (no census record).
        "TrustAxioms": sorted(axs) if axs is not None else None,
        "StatementDigest": s["statement_digest"],
        "ProofFingerprint64": s["proof_expr_fp64"],
        "CanonicalSig": None,
        "canonical_status": "unavailable: no MachLib canonicalizer has an extractable input "
                            "for this representation (see CANONICALIZER_BRIDGE.md)",
        "statement_digest_meaningful": s["kind"] == "theorem",
    }


def extraction_identity() -> dict:
    """The identity regen.py bound to the raw extraction, checked against the raw files and the
    live extractor. Raises Refused when the raw files cannot be shown to come from it."""
    if not EXTRACTION.is_file():
        raise Refused(f"no {EXTRACTION.name}: the raw extraction carries no source identity. "
                      "Run `python3 tools/machsig/regen.py` (it builds, extracts and records the identity).")
    ext = json.loads(EXTRACTION.read_text())
    for name in RAW_FILES:
        live = identity.sha256_file(FOUND / "artifacts" / name)
        if ext.get("raw", {}).get(name) != live:
            raise Refused(f"artifacts/{name} is not the file regen.py extracted (sha256 {live[:16]}... vs "
                          f"recorded {str(ext.get('raw', {}).get(name))[:16]}...). Re-run regen.py.")
    msig = sum(1 for ln in (FOUND / "artifacts" / "machsig_raw.tsv").read_text().split("\n")
               if ln.startswith("MSIG\t"))
    cen = [json.loads(ln) for ln in (FOUND / "artifacts" / "machsig_census.jsonl").read_text().split("\n")
           if ln.strip()]
    if len(cen) != msig or any(c["proof_structure"].get("axiom_dependencies") is None for c in cen):
        raise Refused(f"artifacts/machsig_census.jsonl ({len(cen)} records) was not built from this raw "
                      f"extraction ({msig} MSIG rows), or predates v0.3 (no axiom names). Re-run regen.py.")
    if ext.get("extractor_digest") != identity.extractor_digest(FOUND):
        raise Refused("the extractor changed since this raw extraction was made "
                      f"(recorded {ext.get('extractor_digest')}, live {identity.extractor_digest(FOUND)}). "
                      "Re-run regen.py.")
    return ext


def provenance_record(ext: dict, body: bytes, n: int) -> dict:
    keep = ("machlib_commit", "machlib_sources", "sources_clean", "dirty_source_paths", "content_digest",
            "content_files", "extractor_digest", "extractor_files", "lean_toolchain", "lean_version", "raw")
    rec = {k: ext[k] for k in keep}
    rec.update({"kind": identity.PROVENANCE_KIND, "schema": identity.PROVENANCE_SCHEMA, "version": VERSION,
                "records": n, "records_sha256": "sha256:" + hashlib.sha256(body).hexdigest()})
    return rec


def main(argv):
    try:
        stmt, dec = load()
    except Refused as e:
        print(f"sig: REFUSED -- {e}", file=sys.stderr)
        return 1
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
        try:
            ext = extraction_identity()
        except Refused as e:
            print(f"sig: REFUSED -- {e}", file=sys.stderr)
            return 1
        out = FOUND / "artifacts" / "machsig_signatures.jsonl"
        lines = []
        for name in sorted(stmt):
            r = sig_for(name, stmt, dec)
            if r:
                lines.append(json.dumps(r, sort_keys=True) + "\n")
        n = len(lines)
        body = "".join(lines).encode("utf-8")
        head = json.dumps(provenance_record(ext, body, n), sort_keys=True) + "\n"
        # Written to a temp name and renamed: a half-written set must never be the one the gate reads.
        tmp = out.with_suffix(".jsonl.tmp")
        tmp.write_bytes(head.encode("utf-8") + body)
        tmp.replace(out)
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
