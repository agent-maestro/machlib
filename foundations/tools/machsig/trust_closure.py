#!/usr/bin/env python3
"""Read extract_trust.lean's output: axiom statement digests, the theorem population, and one
definition-closure digest per theorem.

DEFINITION-CLOSURE DIGEST. The closure graph has one node per constant reachable from a statement
(through definition bodies, stopping at axioms, opaque constants and theorems), each with a 128-bit
fingerprint of its own type and value. Cycles exist (an inductive and its constructors). So the
graph is condensed into strongly connected components (Tarjan, iterative), and each component gets
    D(scc) = sha256( sorted "name kind h1 h2" of its members  +  sorted D of its successor sccs )
which is order-independent and changes when any constant anywhere below changes. A theorem's digest
is sha256 over the sorted D of the components of the constants its statement mentions. The
theorem's own statement is NOT in it: StatementDigest covers that.
"""
from __future__ import annotations

import hashlib
import sys
from pathlib import Path

SORRY = "sorryAx"


class Malformed(Exception):
    pass


def parse(path: Path) -> dict:
    axioms, theorems, nodes, total = {}, {}, {}, None
    for ln in path.read_text(encoding="utf-8").split("\n"):
        if not ln:
            continue
        f = ln.split("\t")
        tag = f[0]
        if tag == "TAX":
            if len(f) != 4 or f[1] in axioms:
                raise Malformed(f"bad or duplicate TAX row: {ln[:100]}")
            axioms[f[1]] = {"module": f[2],
                            "statement_sha256": hashlib.sha256(f[3].encode("utf-8")).hexdigest()}
        elif tag == "TTHM":
            if len(f) != 7 or f[1] in theorems:
                raise Malformed(f"bad or duplicate TTHM row: {ln[:100]}")
            theorems[f[1]] = {"module": f[2], "private": f[3] == "true", "aux": f[4],
                              "axioms": sorted(a for a in f[5].split(",") if a),
                              "stmt_consts": sorted(set(c for c in f[6].split(",") if c))}
        elif tag == "TCON":
            if len(f) != 6 or f[1] in nodes:
                raise Malformed(f"bad or duplicate TCON row: {ln[:100]}")
            nodes[f[1]] = {"kind": f[2], "h": f"{f[3]} {f[4]}",
                           "deps": sorted(set(d for d in f[5].split(",") if d))}
        elif tag == "TRUST_TOTAL":
            total = dict(kv.split("=") for kv in f[1:])
    if total is None:
        raise Malformed(f"{path.name}: no TRUST_TOTAL trailer (truncated or interrupted extraction)")
    if (int(total["axioms"]), int(total["theorems"]), int(total["closure_nodes"])) != \
            (len(axioms), len(theorems), sum(1 for n in nodes.values() if n["kind"] != "missing")):
        raise Malformed(f"{path.name}: trailer {total} disagrees with the rows read")
    missing = sorted(n for n, v in nodes.items() if v["kind"] == "missing")
    if missing:
        raise Malformed(f"{path.name}: {len(missing)} closure constant(s) absent from the environment: {missing[:3]}")
    return {"axioms": axioms, "theorems": theorems, "nodes": nodes}


def scc_digests(nodes: dict) -> dict:
    """{node: component digest} via iterative Tarjan; components finish in reverse topological
    order, so every successor component's digest exists when a component is closed."""
    index, low, on, stack, comp_of, digest = {}, {}, set(), [], {}, {}
    counter = 0
    for root in sorted(nodes):
        if root in index:
            continue
        work = [(root, iter(nodes[root]["deps"]))]
        index[root] = low[root] = counter
        counter += 1
        stack.append(root)
        on.add(root)
        while work:
            v, it = work[-1]
            advanced = False
            for w in it:
                if w not in nodes:
                    raise Malformed(f"closure edge {v} -> {w} leaves the graph")
                if w not in index:
                    index[w] = low[w] = counter
                    counter += 1
                    stack.append(w)
                    on.add(w)
                    work.append((w, iter(nodes[w]["deps"])))
                    advanced = True
                    break
                if w in on:
                    low[v] = min(low[v], index[w])
            if advanced:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                members = []
                while True:
                    w = stack.pop()
                    on.discard(w)
                    members.append(w)
                    if w == v:
                        break
                ms = set(members)
                succ = sorted({digest[comp_of[d]] for m in members for d in nodes[m]["deps"] if d not in ms})
                h = hashlib.sha256()
                for m in sorted(members):
                    h.update(f"{m} {nodes[m]['kind']} {nodes[m]['h']}\n".encode())
                h.update(b"--\n")
                for s in succ:
                    h.update(s.encode() + b"\n")
                d = h.hexdigest()
                for m in members:
                    comp_of[m] = v
                digest[v] = d
    return {n: digest[comp_of[n]] for n in nodes}


def closure_digests(data: dict) -> dict:
    comp = scc_digests(data["nodes"])
    out = {}
    for name, t in data["theorems"].items():
        h = hashlib.sha256()
        for d in sorted({comp[c] for c in t["stmt_consts"]}):
            h.update(d.encode() + b"\n")
        out[name] = h.hexdigest()
    return out


if __name__ == "__main__":
    d = parse(Path(sys.argv[1]))
    c = closure_digests(d)
    print(f"axioms {len(d['axioms'])}, theorems {len(d['theorems'])}, nodes {len(d['nodes'])}, digests {len(c)}")
