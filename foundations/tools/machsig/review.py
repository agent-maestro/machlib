#!/usr/bin/env python3
"""MachSig Review — the human-facing layer.

    MachSig tells you whether a formal result changed in WHAT IT CLAIMS, HOW IT IS PROVED,
    or WHAT IT TRUSTS.

    machsig review <objectA> <objectB>   render a review card
    machsig review --pairs [N]           the trust-divergent pairs already in MachLib

The card exists because the useful signal turned out to be a comparison, not a fingerprint: two
declarations asserting the SAME thing while relying on DIFFERENT trusted bases. A reader gets that
in five lines instead of reading two large proof terms.

PROGRESSIVE DISCLOSURE. The card is level 1. Level 2 is the signature triple, level 3 the axiom
delta, level 4 the Lean declaration itself (`#print`). Nothing is trapped in the card -- every line
names the field it came from so it can be traced back.
"""
import json, subprocess, sys, pathlib, collections

FOUND = pathlib.Path(__file__).resolve().parent.parent.parent


def load():
    sigs = {}
    for ln in (FOUND / "artifacts" / "machsig_signatures.jsonl").read_text().split("\n"):
        if ln.strip():
            j = json.loads(ln); sigs[j["object"]] = j
    terms = collections.defaultdict(list)
    tp = FOUND / "artifacts" / "machsig_terms.jsonl"
    if tp.exists():
        for ln in tp.read_text().split("\n"):
            if ln.strip():
                j = json.loads(ln); terms[j["parent_declaration"]].append(j)
    return sigs, terms


def field(sig, layer, ab):
    for p in sig.get(layer, "").split("-"):
        if p.startswith(ab) and p[len(ab):].lstrip("-").isdigit():
            return int(p[len(ab):])
    return None


def term_view(terms, name):
    ts = terms.get(name, [])
    if not ts:
        return "none extracted"
    complete = sum(1 for t in ts if t["completeness"]["structure_complete"])
    if complete == len(ts):
        return f"{len(ts)} term(s), fully visible"
    return f"{len(ts)} term(s), {len(ts)-complete} with quantified subtrees (counts are LOWER BOUNDS)"


def card(a, b, sigs, terms):
    A, B = sigs[a], sigs[b]
    claim = "same" if A["StatementDigest"] == B["StatementDigest"] else "DIFFERENT"
    proof = "same" if A["ProofFingerprint64"] == B["ProofFingerprint64"] else "different"
    axa, axb = field(A, "TrustSig", "AX"), field(B, "TrustSig", "AX")
    sa, sb = field(A, "TrustSig", "S"), field(B, "TrustSig", "S")
    trust = "same" if (axa, sa) == (axb, sb) else "DIFFERENT"
    print(f"\n  {a}\n     ↕\n  {b}\n")
    print(f"  CLAIM             {claim}")
    print(f"  PROOF             {proof}")
    print(f"  TRUST FOOTPRINT   {trust}")
    print()
    arrow = lambda x, y: f"{x} ↔ {y}" + ("" if x == y else ("   ← grew" if (y or 0) > (x or 0) else "   ← shrank"))
    print(f"  axioms            {arrow(axa, axb)}")
    print(f"  sorry             {arrow(sa, sb)}")
    print(f"  proof refs        {arrow(field(A,'ProofSig','R'), field(B,'ProofSig','R'))}   (DIRECT refs, not a transitive closure)")
    print(f"  proof depth       {arrow(field(A,'ProofSig','PD'), field(B,'ProofSig','PD'))}")
    print()
    print(f"  term view         A: {term_view(terms, a)}")
    print(f"                    B: {term_view(terms, b)}")
    print(f"  canonical view    unavailable — no MachLib canonicalizer has an extractable input")
    print()
    print(f"  StatementSig      {A['StatementSig']}")
    print(f"                    {B['StatementSig']}")
    print(f"  StatementDigest   {A['StatementDigest'][:24]}…")
    print(f"                    {B['StatementDigest'][:24]}…")
    print(f"\n  expand level 3 (axiom delta):  python3 tools/machsig/diff.py {a} {b} --json")
    print(f"  expand level 4 (declaration): lake env lean tools/machsig/print_decl.lean -- {a}\n")


def pairs(sigs, limit):
    by = collections.defaultdict(list)
    for n, j in sigs.items():
        if j["kind"] == "theorem":
            by[j["StatementDigest"]].append(n)
    out = []
    for d, g in by.items():
        if len(g) < 2:
            continue
        axs = {n: field(sigs[n], "TrustSig", "AX") for n in g}
        vals = {v for v in axs.values() if v is not None}
        if len(vals) > 1:
            out.append((max(vals) - min(vals), sorted(axs.items(), key=lambda t: t[1] or 0)))
    out.sort(key=lambda t: -t[0])
    print(f"\n  {len(out)} theorem groups asserting the SAME claim with DIFFERENT trusted bases\n")
    for spread, members in out[:limit]:
        lo, hi = members[0], members[-1]
        print(f"  axioms {lo[1]:>3} ↔ {hi[1]:<3} (spread {spread:>2})   "
              f"{lo[0].split('.')[-1]}  ↔  {hi[0].split('.')[-1]}")
    print()


def main(argv):
    sigs, terms = load()
    if argv and argv[0] == "--pairs":
        pairs(sigs, int(argv[1]) if len(argv) > 1 else 15); return 0
    if len(argv) == 2:
        res = []
        for nm in argv:
            c = [n for n in sigs if n == nm or n.split(".")[-1] == nm]
            if not c:
                print(f"not found: {nm}"); return 1
            res.append(c[0])
        card(res[0], res[1], sigs, terms); return 0
    print(__doc__); return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
