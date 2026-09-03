#!/usr/bin/env python3
"""Find conclusions the corpus PROVES and NEVER USES.

`Fbasis_root` obtained its root from `exists_unique_root_of_deriv_pos`, which also returns
UNIQUENESS, and destructured it as `⟨r, hr1, hr2, hr3, _⟩`. The fact was proved, discarded, and
invisible: no gate can see a `_`. It sat there until 2026-09-03, when stating it
(`Fbasis_zero_unique`) turned out to be the lever for a live obligation.

A single `_` is not a defect -- a caller need not use every component. The signal is a position
that is `_` at EVERY call site: a part of a lemma's conclusion that nothing in the corpus consumes.
Either it deserves its own name, or the lemma is over-strong and says so.

Advisory, not a gate: it reports, it does not fail. Use it to go looking.
"""
import re, pathlib, collections, sys

def calls(root: pathlib.Path):
    for f in sorted(root.glob('*.lean')):
        for i, ln in enumerate(f.read_text().split('\n'), 1):
            m = re.search(r'\b(?:obtain|rcases)\b.*?⟨([^⟩]*)⟩\s*(?::=|with)\s*(.*)', ln)
            if not m:
                continue
            parts = [p.strip() for p in m.group(1).split(',')]
            head = re.match(r'([A-Za-z_][\w.]*)', m.group(2).strip())
            if not head:
                continue
            name = head.group(1)
            if len(name) < 6 or not name[0].islower():
                continue
            yield f.name, i, name, parts

def main():
    root = pathlib.Path(__file__).resolve().parent.parent / "MachLib"
    sites = collections.defaultdict(list)
    for fn, i, name, parts in calls(root):
        sites[name].append((fn, i, parts))
    dead = []
    for name, ss in sites.items():
        width = {len(p) for _, _, p in ss}
        if len(width) != 1:
            continue                      # destructured at differing arities; skip rather than guess
        n = width.pop()
        for k in range(n):
            if all(p[k] == '_' for _, _, p in ss):
                dead.append((name, k, n, len(ss), ss[0][0], ss[0][1]))
    print(f"lemmas destructured somewhere: {len(sites)}")
    print(f"components discarded at EVERY call site: {len(dead)}\n")
    for name, k, n, c, fn, ln in sorted(dead, key=lambda d: -d[3]):
        print(f"  {name}  component {k+1}/{n} unused across all {c} call site(s)"
              f"   e.g. {fn}:{ln}")
    if not dead:
        print("  (none)")
    return 0

if __name__ == "__main__":
    sys.exit(main())
