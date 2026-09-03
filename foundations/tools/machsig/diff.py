#!/usr/bin/env python3
"""MachSig/v0.1 — MachDiff.

    machsig diff <objectA> <objectB>          compare two objects in the current corpus
    machsig diff --snapshot A.jsonl B.jsonl   compare two signature snapshots (same object names)

CLASSIFICATION comes from which layer moved, and nothing is inferred beyond that:

    StatementDigest SAME, ProofFingerprint SAME              -> IDENTICAL_REPRESENTATION
    StatementDigest SAME, Proof CHANGED, axioms SAME         -> PROOF_REFACTOR
    StatementDigest SAME, Proof CHANGED, axioms CHANGED      -> TRUST_SURFACE_CHANGE
    StatementDigest CHANGED                                  -> STATEMENT_CHANGED

The roadmap's fifth state -- "source SAME, canonical CHANGED" -- CANNOT BE EMITTED, because this
corpus has no canonical view at all (CANONICALIZER_BRIDGE.md). MachDiff says so explicitly rather
than leaving a category that silently never fires and reads as "no drift detected".
"""
import json, sys, pathlib, subprocess

FOUND = pathlib.Path(__file__).resolve().parent.parent.parent


def classify(a, b):
    if a["StatementDigest"] != b["StatementDigest"]:
        return "STATEMENT_CHANGED", "the kernel-facing claim differs"
    if a["ProofFingerprint64"] == b["ProofFingerprint64"]:
        return "IDENTICAL_REPRESENTATION", "same statement and same proof term"
    ax_a, ax_b = _ax(a), _ax(b)
    if ax_a is not None and ax_b is not None and ax_a != ax_b:
        return "TRUST_SURFACE_CHANGE", f"same claim; axiom footprint {ax_a} -> {ax_b}"
    return "PROOF_REFACTOR", "same claim and same axiom footprint; different proof term"


def _ax(r):
    for part in r.get("TrustSig", r["ProofSig"]).split("-"):
        if part.startswith("AX"):
            try:
                return int(part[2:])
            except ValueError:
                return None
    return None


def field_deltas(a, b):
    out = []
    for lay in ("StatementSig", "ProofSig", "TrustSig"):
        fa = dict((p[:1] if p[:2] not in ("AX", "PD") else p[:2],
                   p[1:] if p[:2] not in ("AX", "PD") else p[2:]) for p in a[lay].split("-"))
        fb = dict((p[:1] if p[:2] not in ("AX", "PD") else p[:2],
                   p[1:] if p[:2] not in ("AX", "PD") else p[2:]) for p in b[lay].split("-"))
        for k in fa:
            if fa[k] != fb.get(k):
                out.append(f"{lay}.{k}: {fa[k]} -> {fb.get(k)}")
    return out


def load_sigs():
    p = FOUND / "artifacts" / "machsig_signatures.jsonl"
    d = {}
    for ln in p.read_text().split("\n"):
        if ln.strip():
            j = json.loads(ln); d[j["object"]] = j
    return d


def resolve(sigs, name):
    if name in sigs:
        return sigs[name]
    c = [n for n in sigs if n.split(".")[-1] == name]
    return sigs[c[0]] if len(c) == 1 else (None if not c else sigs[c[0]])


def render(a, b, as_json=False):
    cls, why = classify(a, b)
    deltas = field_deltas(a, b)
    if as_json:
        print(json.dumps({"a": a["object"], "b": b["object"], "classification": cls,
                          "reason": why, "field_deltas": deltas,
                          "canonical": "unavailable_in_this_corpus"}, indent=2))
        return
    print(f"\nMachSig/v0.1  diff\n  A: {a['object']}\n  B: {b['object']}\n")
    print(f"  STATEMENT   {'SAME' if a['StatementDigest']==b['StatementDigest'] else 'CHANGED'}")
    print(f"  PROOF       {'SAME' if a['ProofFingerprint64']==b['ProofFingerprint64'] else 'CHANGED'}")
    print(f"  CANONICAL   UNAVAILABLE (no canonical view exists in this corpus)")
    print(f"\n  classification: {cls}\n  {why}\n")
    if deltas:
        print("  field deltas:")
        for d in deltas:
            print(f"    {d}")
    print()


def main(argv):
    as_json = "--json" in argv
    argv = [a for a in argv if a != "--json"]
    if len(argv) == 3 and argv[0] == "--snapshot":
        A = {json.loads(l)["object"]: json.loads(l) for l in open(argv[1]) if l.strip()}
        B = {json.loads(l)["object"]: json.loads(l) for l in open(argv[2]) if l.strip()}
        common = sorted(set(A) & set(B))
        changed = [(n, classify(A[n], B[n])) for n in common
                   if classify(A[n], B[n])[0] != "IDENTICAL_REPRESENTATION"]
        print(f"snapshot diff: {len(common)} common objects, {len(changed)} changed")
        for n, (c, w) in changed[:40]:
            print(f"  {c:<24} {n}   ({w})")
        only_a, only_b = sorted(set(A) - set(B)), sorted(set(B) - set(A))
        print(f"  removed: {len(only_a)}   added: {len(only_b)}")
        return 0
    if len(argv) == 2:
        sigs = load_sigs()
        a, b = resolve(sigs, argv[0]), resolve(sigs, argv[1])
        if a is None or b is None:
            print("object not found in the signature set"); return 1
        render(a, b, as_json)
        return 0
    print(__doc__); return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
