#!/usr/bin/env python3
"""The EML instrument: grammar, ray, metric, controls, and the beam — over tower arithmetic.

Split out of `germ_tower_search.py` so that the INSTRUMENT and the EXPERIMENTS RUN ON IT are
separate files.  Everything here is machinery whose correctness the controls establish; everything
in the search file is a question asked of it.  Read `germ_tower_search.py`'s header first — it
carries the design, the four blind spots this run was built against, and what it still cannot find.
"""

from __future__ import annotations

import collections
import functools
import random
from dataclasses import dataclass
from typing import Optional, Sequence, Tuple

from mpmath import mp, mpf
from mpmath import exp as mexp
from mpmath import log as mlog
from mpmath import pi as mpi
from mpmath import euler as meuler

import germ_tower as G
from germ_tower import T, Unresolved

NEAR = None   # the scoring ray; set by germ_tower_search.main()
FAR = None    # the confirmation ray, reaching astronomically further


def set_rays(near, far):
    global NEAR, FAR
    NEAR, FAR = near, far


# ── the grammar ─────────────────────────────────────────────────────────────────────────────────


@dataclass(frozen=True)
class Tree:
    kind: str            # 'const' | 'var' | 'eml'
    c: object = None
    a: object = None
    b: object = None
    depth: int = 0

    def __str__(self) -> str:
        if self.kind == "const":
            return self.c[1]
        if self.kind == "var":
            return "x"
        return f"eml({self.a},{self.b})"

    def consts(self):
        if self.kind == "const":
            yield self
        elif self.kind == "eml":
            yield from self.a.consts()
            yield from self.b.consts()


def K(value, label) -> Tree:
    return Tree("const", c=(G.num(value), label))


VAR = Tree("var")


def E(a: Tree, b: Tree) -> Tree:
    return Tree("eml", a=a, b=b, depth=1 + max(a.depth, b.depth))


def eTree(a: Tree) -> Tree:
    """exp(a) — `eml a (const 1)`, since log₀ 1 = 0.  Costs one depth level."""
    return E(a, K(1, "1"))


def node_value(av: T, bv: T) -> T:
    """eval (eml A B) x = exp (A x) − log₀ (B x)."""
    return G.sub(G.mk_exp(av), G.log0(bv))


def eval_tree(t: Tree, x: T) -> Optional[T]:
    if t.kind == "const":
        return t.c[0]
    if t.kind == "var":
        return x
    av, bv = eval_tree(t.a, x), eval_tree(t.b, x)
    if av is None or bv is None:
        return None
    return node_value(av, bv)


# ── constants ───────────────────────────────────────────────────────────────────────────────────
#
# §6: "Its constants are a tiny fixed set.  A counterexample requiring a particular transcendental
# constant is invisible, and this corpus has a recorded instance of exactly that miss."
#
# The alphabet is chosen for what each constant BUYS in the grammar, not for variety:
#   log₀ c = 0  for c ≤ 0 and for c = 1 — the {0,1} alphabet can only ever ERASE the right child;
#   log₀ c = -M for c = e^-M          — the only way a leaf adds a positive offset to a germ, and
#                                        the mechanism that separates the two floor readings;
#   e, π, log 2, γ, e^π               — transcendentals, named in §6 as the recorded blind spot.
#
# MEASURED, not inferred: every sweep alphabet of the 2026-09-05 run is a subset of
# {0, 1, 5, 50, 1000} (`germ_approach_search.py` lines 503-519), so `log₀ c ≥ 0` at EVERY leaf of
# EVERY tree it examined and no leaf could ever add to a germ.  `e^-1` appears in that file exactly
# twice, at lines 334 and 337 — inside `controls()`.  The one leaf value able to move the reading
# was in the instrument's own controls and never in its search.

def constants(wide: bool) -> Sequence[Tree]:
    if not wide:
        return [K(0, "0"), K(1, "1"), VAR]
    mp.dps = max(mp.dps, 40)
    e = mexp(1)
    return [
        K(0, "0"), K(1, "1"), K(-1, "-1"), K(2, "2"), K(mpf(1) / 2, "1/2"),
        K(5, "5"), K(50, "50"), K(1000, "1000"),
        K(e, "e"), K(1 / e, "1/e"), K(mexp(-5), "e^-5"), K(mexp(-50), "e^-50"),
        K(mpi, "pi"), K(mlog(2), "log2"), K(meuler, "gamma"), K(mexp(mpi), "e^pi"),
        VAR,
    ]


# ── the ray ─────────────────────────────────────────────────────────────────────────────────────
#
# ITERATED-LOG COORDINATES, per §6's second recorded trap (a 400 001-point grid reported a finite
# sup for a germ that diverges): x = exp(exp(t)) with t uniform.  Reach no longer depends on depth,
# so ONE ray serves every depth and the far ray is not 3× longer but 1e300 against 1e64.

def ray(t_hi=5.0, n=10, t_lo=0.6) -> Tuple[T, ...]:
    return tuple(G.num(mexp(mexp(mpf(t_lo) + (mpf(t_hi) - mpf(t_lo)) * mpf(i) / (n - 1))))
                 for i in range(n))




def reach(xs) -> str:
    return f"x ∈ [{mp.nstr(xs[0].m, 3)}, {mp.nstr(xs[-1].m, 3)}]"


# ── the reading ─────────────────────────────────────────────────────────────────────────────────

TAIL = 3   # how many ray points at the far end are scored


@dataclass(frozen=True)
class Reading:
    verdict: str                 # 'ok' | 'not-positive' | 'unresolved' | 'zero-after-absorption'
    strict: Optional[int] = None    # exp(-tower_k x) ≤ t(x)                (EmlGermApproach)
    floor: Optional[int] = None     # t(x) ≥ exp(-(C + tower_k x))          (DecayFloor)
    note: str = ""


def read_decay(vals: Sequence[Optional[T]], xs: Sequence[T]) -> Reading:
    """Score ONE tree's germ.  The height is read in the TAIL, never maximised over the ray.

    §6 defect 1: a CONSTANT gap — `exp(0) − log(exp 50)` is the constant `exp(−49)` — sits below
    the floor at x = 2 and astronomically above it at x = 10^6.  The conjecture says `∃X₁ ≥ X₀`, so
    only the tail counts.

    `zero-after-absorption` is the instrument's own blind spot, given its own name rather than
    scored.  When a term falls below the working precision beside its neighbour it is ABSORBED, so
    a germ whose true value is `exp(E) − exp(E − exp(−E))`, i.e. 1, reads as an exact meeting.  No
    precision reaches that — `exp(−E)` beside `E` is not a precision question — so these are
    REFUSED, never read as germs that meet their target.  The bias is the safe way round
    (absorption over-states |t| and under-states the height), which is why a miss is possible here
    and an invented counterexample is not."""
    tail_idx = range(len(vals) - TAIL, len(vals))
    ks, excess = [], []
    for i in tail_idx:
        v, x = vals[i], xs[i]
        if v is None:
            return Reading("unresolved", note=f"no reading at x={mp.nstr(x.m, 3)}")
        if G.is_zero(v):
            return Reading("zero-after-absorption" if G.absorbed() else "not-positive",
                           note="germ meets zero exactly")
        if G.sign(v) <= 0:
            return Reading("not-positive", note=f"t ≤ 0 at x={mp.nstr(x.m, 3)}")
        k = G.required_height(v, x)
        ks.append(k)
        if k and k >= 1:
            try:
                excess.append(G.floor_excess(v, x, k - 1))
            except Unresolved:
                excess.append(None)
    strict = max(ks)
    fl = strict
    # DecayFloor allows one additive constant.  A germ fails the strict height-(k−1) test and still
    # satisfies the floor there iff the excess (−log t) − tower_{k−1}(x) stays BOUNDED along the
    # tail.  It can drop by at most one height: if it dropped two, the strict reading would too.
    if strict >= 1 and len(excess) >= 2 and all(e is not None for e in excess):
        try:
            if all(G.sign(e) > 0 for e in excess) and G.cmp_signed(excess[-1], excess[0]) <= 0:
                fl = strict - 1
        except Unresolved:
            pass
    return Reading("ok", strict, fl, f"tail={ks}")


def measure(tree: Tree, xs: Sequence[T]) -> Tuple[Reading, Tuple[Optional[T], ...]]:
    G.reset_absorbed()
    vals = []
    for x in xs:
        try:
            vals.append(eval_tree(tree, x))
        except (Unresolved, ValueError, OverflowError):
            vals.append(None)
    return read_decay(vals, xs), tuple(vals)


def confirm(tree: Tree) -> Reading:
    """Re-measure on a ray reaching astronomically further and require agreement.

    §6 defect 5: the depth-4 ray (x ≤ 2.8) was too short to decide EVENTUAL POSITIVITY, not merely
    too short to resolve a rate — `eml(x, eml(eml(x,0), x))` was read as a depth-4 counterexample
    and is a depth-3 tree that crosses zero at x ≈ 5.9.  The check is one-sided and this code says
    so: agreement does not prove a reading is asymptotic, disagreement proves it is not."""
    near, _ = measure(tree, NEAR)
    far, _ = measure(tree, FAR)
    if near.verdict != far.verdict or near.strict != far.strict or near.floor != far.floor:
        return Reading("unstable", note=f"near {near.verdict}/{near.strict}/{near.floor}  "
                                        f"far {far.verdict}/{far.strict}/{far.floor}")
    return far


# ── positive controls ───────────────────────────────────────────────────────────────────────────
#
# EVERY INSTRUMENT MUST BE SHOWN CAPABLE OF BOTH VERDICTS BEFORE EITHER IS READ.  §3's `deepDecay m`
# — `exp(1 − tower_{m+1}(x))` at depth exactly m + 4 — is the family that pins the height from
# below, so it is the natural control, and it is the one the 2026-09-05 instrument could not run
# past m = 1 (its depth-5 ray reached x ≈ 2.2).  Here it runs to m = 5, depth 9.

def tower_tree(n: int) -> Tree:
    t = VAR
    for _ in range(n):
        t = eTree(t)
    return t


def deep_decay(m: int) -> Tree:
    """eTree (eml (const 0) (eTree (towerTree (m+1)))) — depth m+4, germ exp(1 − tower_{m+1} x)."""
    return eTree(E(K(0, "0"), eTree(tower_tree(m + 1))))


def run_controls(verbose=True) -> bool:
    ok = True
    if verbose:
        print("\n=== POSITIVE CONTROLS — a nonzero height must be reported here ===")
    for m in range(0, 6):
        t = deep_decay(m)
        r = confirm(t)
        good = (r.verdict == "ok" and r.strict == m + 1 and r.floor == m + 1)
        ok &= good
        if verbose:
            print(f"  deepDecay {m}: depth {t.depth}  expect height {m+1}  "
                  f"got strict={r.strict} floor={r.floor}  "
                  f"{'FIRES' if good else 'SILENT — INSTRUMENT BROKEN'}")
    # NEGATIVE CONTROLS: germs whose height is 0 by hand must not be inflated.
    for label, t, want in [
        ("e/x  (recipTree var)", E(E(K(0, "0"), VAR), K(1, "1")), 0),
        ("exp(1-x)  (decayFast)", eTree(E(K(0, "0"), eTree(VAR))), 0),
        ("exp(x)   (diverges)", eTree(VAR), 0),
    ]:
        r = confirm(t)
        good = (r.verdict == "ok" and r.strict == want)
        ok &= good
        if verbose:
            print(f"  {label}: expect height {want}  got {r.verdict}/{r.strict}  "
                  f"{'OK' if good else 'INSTRUMENT BROKEN'}")
    if verbose:
        print("  CONTROLS " + ("PASS — both verdicts reachable."
                               if ok else "FAIL — no negative result may be read from this run."))
    return ok


# ── beam search ─────────────────────────────────────────────────────────────────────────────────
#
# §6 defect 6: enumerate-then-sample is not sampling (`trees_upto(4, {0,1})` reached 58 GB).  Nor,
# at depth 5, is uniform random construction: 8 000 uniform samples out of a class with more than
# 10^17 members says nothing about the extremes, and a counterexample IS an extreme.  So the pool
# at each level is selected FOR the extremes — the smallest positive germ (a counterexample is one),
# the most negative (its exp is the smallest positive one level up), the largest (its log₀ is the
# largest subtrahend) — with a random remainder for breadth, and deduplicated by GERM rather than
# by tree, which is what makes the coverage number mean anything.

@dataclass(frozen=True)
class Item:
    tree: Tree
    vals: Tuple[Optional[T], ...]
    reading: Reading


def signature(vals) -> tuple:
    out = []
    for v in vals:
        out.append(None if v is None else (v.signs, mp.nstr(v.m, 20)))
    return tuple(out)


def make_item(tree: Tree, xs) -> Optional[Item]:
    G.reset_absorbed()
    vals = []
    for x in xs:
        try:
            vals.append(eval_tree(tree, x))
        except (Unresolved, ValueError, OverflowError):
            vals.append(None)
    return Item(tree, tuple(vals), read_decay(vals, xs))


def _key_last(it: Item) -> Optional[T]:
    return it.vals[-1]


def select(items, per_class: int, rng) -> list:
    """Keep the extremes, then a random remainder.  Selection is the instrument here."""
    live = [it for it in items if _key_last(it) is not None and not G.is_zero(_key_last(it))]
    pos = [it for it in live if G.sign(_key_last(it)) > 0]
    negs = [it for it in live if G.sign(_key_last(it)) < 0]

    def srt(seq, rev):
        out = list(seq)
        out.sort(key=_CmpKey, reverse=rev)
        return out

    chosen = []
    chosen += srt(pos, False)[:per_class]              # smallest positive: the decay candidates
    chosen += srt(negs, False)[:per_class]             # most negative: exp of it is smallest
    chosen += srt(live, True)[:per_class]              # largest: log₀ of it is the biggest cut
    tall = [it for it in items if it.reading.verdict == "ok" and it.reading.strict]
    chosen += sorted(tall, key=lambda it: -it.reading.strict)[:per_class]
    rest = [it for it in items if it not in chosen]
    rng.shuffle(rest)
    chosen += rest[:per_class]
    seen, out = set(), []
    for it in chosen:
        s = signature(it.vals)
        if s not in seen:
            seen.add(s)
            out.append(it)
    return out


class _CmpKey:
    __slots__ = ("v",)

    def __init__(self, it: Item):
        self.v = it.vals[-1]

    def __lt__(self, other):
        return G.cmp_signed(self.v, other.v) < 0


def seed_trees(max_depth: int):
    """§3's adversarial families, handed to the search rather than left for it to rediscover.

    "All are in the corpus, all machine-checked.  Each was built to break something and is now a
    fixture."  Seeding them means the beam starts from the known extremes; the 2026-09-05 sweep
    rediscovered `deepDecay` at depth 4 by accident, which is reassuring about the sweep and
    wasteful as a method."""
    out = []
    for n in range(0, max_depth + 1):
        t = tower_tree(n)
        if t.depth <= max_depth:
            out.append(t)                                            # tower_n
    for n in range(0, max_depth):
        cap = E(K(0, "0"), tower_tree(n + 1))                        # capNode n: 1 − tower_n
        if cap.depth <= max_depth:
            out.append(cap)
        for m in range(0, max_depth):
            dd = deep_decay(m)
            if dd.depth <= max_depth and dd not in out:
                out.append(dd)
    for base in (VAR, eTree(VAR)):
        r = E(E(K(0, "0"), base), K(1, "1"))                         # recipTree: e / base
        if r.depth <= max_depth:
            out.append(r)
        p = E(K(0, "0"), eTree(E(K(0, "0"), eTree(base))))           # posEmbed: base, +4 depth
        if p.depth <= max_depth:
            out.append(p)
    for n in range(0, max_depth):
        for c in (0, 1, 5):
            g = E(tower_tree(n), K(mexp(c), f"e^{c}"))               # gapTarget n c
            if g.depth <= max_depth:
                out.append(g)
    out.append(eTree(eTree(VAR)))                                    # the exact-meeting shape
    return [t for t in out if t.depth <= max_depth]


def cut_height(lhs: T, v: T, x: T) -> int:
    """How many tower levels the node's own subtraction destroyed, on the SAME scale as the floor.

    `exp(A)/t` is the factor the subtraction cost; its height is the number of logs taking
    `log(exp(A)/t)` down to x.  A counterexample at depth d needs this to reach d−2."""
    if G.is_zero(v) or G.is_zero(lhs):
        return 0
    try:
        ratio = G.mk_exp(G.sub(G.logmag(v), G.logmag(lhs)))   # t / exp(A), in (0, 1] when cut
        return G.required_height(ratio, x) or 0
    except (Unresolved, ValueError):
        return 0


def beam(max_depth: int, consts, xs, per_class=60, budget=120000, seed=20260923, fame=12):
    """Build depth by depth, evaluating INCREMENTALLY: a node costs one tower op per ray point,
    because both children's germ vectors are already in hand.  Nothing is ever enumerated."""
    rng = random.Random(seed)
    pools = {0: [make_item(t, xs) for t in consts]}
    for t in seed_trees(max_depth):
        pools.setdefault(t.depth, [])
        it = make_item(t, xs)
        if it is not None:
            pools[t.depth].append(it)
    stats, hall, cancel = {}, {}, {}
    for d in range(1, max_depth + 1):
        lower = [it for k in range(d) for it in pools.get(k, [])]
        prev = pools.get(d - 1, [])
        pairs = [(a, b) for a in prev for b in lower] + [(a, b) for a in lower for b in prev]
        if len(pairs) > budget:
            pairs = rng.sample(pairs, budget)
        cand, counts = [], collections.Counter()
        top, cuts = [], collections.Counter()
        for a, b in pairs:
            vals, cut = [], 0
            for i in range(len(xs)):
                av, bv = a.vals[i], b.vals[i]
                if av is None or bv is None:
                    vals.append(None)
                    continue
                try:
                    lhs = G.mk_exp(av)
                    v = G.sub(lhs, G.log0(bv))
                    vals.append(v)
                    if i == len(xs) - 1:
                        cut = cut_height(lhs, v, xs[i])
                except (Unresolved, ValueError, OverflowError):
                    vals.append(None)
            r = read_decay(vals, xs)
            counts[r.verdict] += 1
            cuts[cut] += 1
            it = Item(E(a.tree, b.tree), tuple(vals), r)
            cand.append(it)
            if r.verdict == "ok" and r.strict:
                top.append(it)
                if cut >= 1:
                    cancel.setdefault(d, []).append((r.strict, cut, it.tree))
        germs = len({signature(it.vals) for it in cand})
        stats[d] = (len(pairs), germs, counts, cuts)
        top.sort(key=lambda z: -z.reading.strict)
        hall[d] = top[:fame]
        pools[d] = pools.get(d, []) + select(cand, per_class, rng)
    return pools, stats, hall, cancel

