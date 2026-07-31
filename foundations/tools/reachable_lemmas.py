#!/usr/bin/env python3
"""Which lemmas are reachable from a given MachLib module — and what an import would cost.

## Why this exists

Four distinct missing-lemma discoveries across three sessions, each costing a build round:
`add_lt_add_right` (does not exist at all), `sub_le_sub_left` (not on the chain),
`div_lt_of_lt_mul` (exists, distant module), `log_le_log` (exists, `SignTactic`, unreachable).
Every one presented identically at the point of failure — `Unknown identifier` — while the right
response differed: re-derive locally, import, or use a differently-named neighbour.

MachLib is Mathlib-free by design, so the usual instinct ("it's in Mathlib somewhere") is wrong here
and the alternatives are not discoverable by guessing. This makes them discoverable by asking.

## The question it actually answers

Not "does X exist" — grep answers that. It answers **"is X reachable from where I am standing, and if
not, what would reaching it cost?"** That is the decision the codebase's own convention turns on:
re-derive locally when the chain is long (the `wgc_`/`ebc_` lemmas), import when it is short.

Usage:
  reachable_lemmas.py --from MachLib.EMLAsymptoticClass --find "log_le"
  reachable_lemmas.py --from MachLib.EMLAsymptoticClass --find "add_lt_add"
  reachable_lemmas.py --from MachLib.EMLAsymptoticClass --stats
"""
from __future__ import annotations

import argparse
import os
import re
import sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))   # foundations/
# `private` is captured, not stripped: a private declaration is usable ONLY inside its own module,
# so reporting one as "reachable" from elsewhere would send the reader after a name that will not
# resolve — the exact failure this tool exists to prevent, committed by the tool.
DECL = re.compile(r"^(private\s+)?(?:noncomputable\s+)?(theorem|def|abbrev)\s+([A-Za-z_][A-Za-z_0-9'.]*)", re.M)


def mod_path(m: str) -> str:
    return os.path.join(HERE, m.replace(".", "/") + ".lean")


def closure(root: str) -> set[str]:
    """Transitive import closure. A module that does not exist on disk is reported, not skipped."""
    seen, stack, missing = set(), [root], set()
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        p = mod_path(m)
        if not os.path.exists(p):
            missing.add(m)
            continue
        seen.add(m)
        for line in open(p, encoding="utf-8", errors="replace"):
            if line.startswith("import MachLib"):
                stack.append(line.split()[1])
    if missing:
        print(f"  note: {len(missing)} imported module(s) not found on disk: {sorted(missing)[:3]}",
              file=sys.stderr)
    return seen


def all_modules() -> list[str]:
    out = []
    for dirpath, dirnames, files in os.walk(os.path.join(HERE, "MachLib")):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for f in files:
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dirpath, f), HERE)
                out.append(rel[:-5].replace("/", "."))
    return sorted(out)


def decls(m: str) -> list[tuple[str, str]]:
    p = mod_path(m)
    if not os.path.exists(p):
        return []
    return [(k, n, bool(priv)) for priv, k, n in
            DECL.findall(open(p, encoding="utf-8", errors="replace").read())]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--from", dest="root", required=True, help="the module you are editing")
    ap.add_argument("--find", help="substring to search for")
    ap.add_argument("--stats", action="store_true")
    a = ap.parse_args()

    if not os.path.exists(mod_path(a.root)):
        print(f"[NO SUCH MODULE] {a.root}  ({mod_path(a.root)})")
        return 2

    reach = closure(a.root)
    every = all_modules()
    unreach = [m for m in every if m not in reach]

    if a.stats or not a.find:
        rn = sum(len(decls(m)) for m in reach)
        un = sum(len(decls(m)) for m in unreach)
        print(f"FROM {a.root}")
        print(f"  reachable   : {len(reach):>4} modules, {rn:>5} declarations")
        print(f"  UNreachable : {len(unreach):>4} modules, {un:>5} declarations")
        print(f"  the second number is the size of the trap: those names exist, and using one")
        print(f"  fails with the same 'Unknown identifier' as a name that does not exist at all.")
        return 0

    hit_r, hit_u = [], []
    for m in reach:
        for k, n, priv in decls(m):
            if a.find in n:
                # private is usable only in its OWN module
                (hit_r if (not priv or m == a.root) else hit_u).append((n, k, m, priv))
    for m in unreach:
        for k, n, priv in decls(m):
            if a.find in n:
                hit_u.append((n, k, m, priv))

    print(f"SEARCH {a.find!r}  FROM {a.root}\n")
    if hit_r:
        print(f"REACHABLE — use directly ({len(hit_r)})")
        for n, k, m, priv in sorted(hit_r):
            tag = "  [private — same module, so usable here]" if priv else ""
            print(f"  {n:<42} {k:<8} {m}{tag}")
    else:
        print("REACHABLE — none")
    print()

    if hit_u:
        print(f"EXISTS BUT NOT REACHABLE ({len(hit_u)}) — import, or re-derive locally")
        for n, k, m, priv in sorted(hit_u):
            if priv:
                print(f"  {n:<42} {k:<8} {m}")
                print(f"  {'':<42} PRIVATE — not usable outside its module at any import cost")
                continue
            cost = len(closure(m) - reach)
            verdict = "re-derive (convention)" if cost > 3 else "import is cheap"
            print(f"  {n:<42} {k:<8} {m}")
            print(f"  {'':<42} +{cost} new module(s) on the chain → {verdict}")
    elif not hit_r:
        print("EXISTS BUT NOT REACHABLE — none either.")
        print("  The name does not exist anywhere in MachLib. MachLib is Mathlib-free: if you are")
        print("  reaching for a Mathlib name, it is not here and will not be. Look for a")
        print("  differently-named neighbour, or prove it.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
