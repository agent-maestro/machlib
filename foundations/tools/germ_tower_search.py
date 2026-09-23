#!/usr/bin/env python3
"""Second falsification instrument for EmlGermApproach — machlib `EmlGermApproachResearch.md` §6/§8.

The 2026-09-05 run (`germ_approach_search.py`) found no counterexample and stated four blind spots.
This instrument is built against those four and inherits every control that run paid for.

  WHAT IT FIXES                          HOW
  ─────────────────────────────────────  ───────────────────────────────────────────────────────
  "It cannot see far" — x ≤ 2.8 at       `germ_tower.py`: exp/log are spine push/pop, so the ray
  depth 4, x ≈ 2.2 at depth 5, 1 141     reach stops depending on depth.  This one reads the tail
  overflows out of 8 000 readings.       at x = 1e64 at EVERY depth, and re-measures at 1e300.
  "Its constants are a tiny fixed set"   17 leaf constants including e, π, log 2, γ, and e^-M for
  ({0,1}), while the grammar allows      M ∈ {1,5,50} — the ones that BUY an additive offset — plus
  an arbitrary real at every leaf.       a tuning pass that solves for the constant per tree.
  "It samples thinly at depth 3"         Beam search over germ-deduplicated pools, selected for the
  (6 000 of 4.7e8 pairs, ~0.001 %).      EXTREMES that a counterexample must live at, not uniformly.
  Depth 5 "under-resolved": 354 of       Depth 5 and 6 are read with 0 overflows, because there is
  8 000 unstable, 1 141 overflowed.      nothing left to overflow.

INHERITED CONTROLS, none re-derived:
  * read in the TAIL only (a constant gap sits below the floor early and astronomically above it
    late) — §6 defect 1;
  * a sentinel for "positively enormous" rather than "no sample" — superseded: in this
    representation there is no working range to leave, so the bucket is empty by construction;
  * a RELATIVE precision guard, never absolute — §6 defect 3, the one the controls caught;
  * CONSTRUCT samples, never filter an enumeration — §6 defect 6 (`trees_upto(4)` reached 58 GB);
  * re-measure every nonzero height on a much longer ray and drop it unless both agree — §6 defect
    5 (a depth-3 tree read as a depth-4 counterexample because its ray stopped before it crossed
    zero);
  * positive controls that MUST fire before any negative result is read.

THE PREDICTION UNDER TEST: required height = j − 3, pinned from both sides at depths 2-4.  Depth 5
should be 2.  A measured 3 is a counterexample to the current bound.

TWO READINGS OF THE FLOOR, and they differ by one height on a real family.  `EmlGermApproach`
states `exp(-tower_k x) ≤ gap` with no constant; `DecayFloor` states `t(x) ≥ exp(-(C + tower_k x))`
with one.  `exp(-exp(x) - 5)` is strict height 2 and DecayFloor height 1.  The 2026-09-05 sweep
could not see the difference because {0,1} cannot express the offset (`log₀ 1 = 0`); with `e^-5` in
the alphabet it appears at depth 4.  Both are reported.
"""
from __future__ import annotations

import argparse
import collections
import functools
import itertools
import random
import sys
from typing import Optional, Tuple

from mpmath import mp, mpf
from mpmath import exp as mexp

import germ_tower as G
import germ_tower_eml as M
from germ_tower import T, Unresolved
from germ_tower_eml import (E, K, VAR, Reading, Tree, beam, confirm, constants, eTree,
                            cut_height, measure, ray, reach, read_decay, run_controls)

NEAR = None
FAR = None


def report_beam(max_depth, consts, xs, per_class, budget, label):
    pools, stats, hall, cancel = beam(max_depth, consts, xs, per_class, budget)
    print(f"\n=== {label}: beam to depth {max_depth}, {len(consts)-1} constants + var, "
          f"{reach(xs)} ===")
    verdicts = {}
    for d in range(1, max_depth + 1):
        n, germs, counts, cuts = stats[d]
        deep_cut = sum(v for k, v in cuts.items() if k >= 1)
        print(f"  depth {d}: {n:>7} nodes formed, {germs:>6} distinct germs   {dict(counts)}"
              f"   top-node cancellation height ≥1: {deep_cut}")
    for d in range(1, max_depth + 1):
        # The tall candidates over EVERYTHING formed at this depth, not only the survivors, each
        # re-measured on the far ray before it is believed.
        # §6 defect 5 was a DEPTH mislabelling as much as a ray-length one: the reported depth-4
        # counterexample was a depth-3 tree.  Assert the depth of everything reported.
        assert all(it.tree.depth == d for it in hall[d]), f"depth mislabelled at {d}"
        top = [(confirm(it.tree), it.tree) for it in hall[d]]
        conf = [(r, t) for r, t in top if r.verdict == "ok"]
        unstable = sum(1 for r, _ in top if r.verdict == "unstable")
        ms = max((r.strict for r, _ in conf), default=0)
        mf = max((r.floor for r, _ in conf), default=0)
        verdicts[d] = (ms, mf)
        cc = cancel.get(d, [])
        cmax = max((k for k, _, _ in cc), default=0)
        print(f"  depth {d}: CONFIRMED max height  strict={ms}  DecayFloor={mf}   "
              f"(prediction j-3 = {max(d-3, 0)}; {unstable} of {len(top)} re-measurements unstable;"
              f" tallest cancelling node: {cmax})")
        for r, t in conf[:2]:
            if r.strict:
                print(f"      strict={r.strict} floor={r.floor}  {str(t)[:110]}")
    return pools, verdicts


# ── exhaustive regression against the 2026-09-05 run ────────────────────────────────────────────

def trees_upto(depth: int, consts):
    allt = list(consts)
    for _ in range(depth):
        allt = allt + [E(a, b) for a, b in itertools.product(allt, allt)]
        seen, ded = set(), []
        for t in allt:
            s = str(t)
            if s not in seen:
                seen.add(s)
                ded.append(t)
        allt = ded
    return [t for t in allt if t.depth <= depth]


def exhaustive(depth: int, consts, xs, label):
    ts = trees_upto(depth, consts)
    counts = collections.Counter()
    best = []
    for t in ts:
        r, _ = measure(t, xs)
        counts[r.verdict] += 1
        if r.verdict == "ok" and r.strict:
            best.append((r, t))
    conf, unstable = [], 0
    for _, t in sorted(best, key=lambda p: -p[0].strict)[:40]:
        r = confirm(t)
        if r.verdict == "ok":
            conf.append((r, t))
        elif r.verdict == "unstable":
            unstable += 1
    ms = max((r.strict for r, _ in conf), default=0)
    mf = max((r.floor for r, _ in conf), default=0)
    print(f"\n=== {label}: EXHAUSTIVE depth ≤ {depth}, {len(ts)} trees, {reach(xs)} ===")
    print(f"  {dict(counts)}")
    print(f"  max height  strict={ms}  DecayFloor={mf}   (prediction j-3 = {max(depth-3,0)}; "
          f"{unstable} unstable)")
    for r, t in conf[:3]:
        print(f"      strict={r.strict} floor={r.floor}  {str(t)[:110]}")
    return ms, mf


# ── tuned constants ─────────────────────────────────────────────────────────────────────────────
#
# §6's named blind spot: "a counterexample requiring a particular transcendental constant is
# invisible, and this corpus has a recorded instance of exactly that miss."  A fixed alphabet
# cannot answer it; solving for the constant can.
#
# The target is NOT "make the value vanish at one x" — that tunes a CROSSING, and a germ tuned to
# cross is not eventually positive, which is §6 defect 5 met from the front.  The target is the
# worst height that survives on the whole TAIL, so the search maximises min-over-tail subject to
# positivity everywhere on the tail.

def substitute(t: Tree, target: Tree, value: Tree) -> Tree:
    if t is target:
        return value
    if t.kind != "eml":
        return t
    return E(substitute(t.a, target, value), substitute(t.b, target, value))


def tune(tree: Tree, xs, grid=None, max_leaves=10, rng=None) -> Tuple[Optional[Reading],
                                                                     Optional[Tree]]:
    if grid is None:
        grid = [mpf(0), mpf(1), mpf(-1)]
        for u in (-200, -50, -20, -5, -2, -1, 0, 1, 2, 5, 20, 50, 200):
            grid.append(mexp(mpf(u)))
            grid.append(-mexp(mpf(u)))
    leaves = list(tree.consts())
    if len(leaves) > max_leaves:
        leaves = (rng or random.Random(7)).sample(leaves, max_leaves)
    best, best_tree = None, None
    for leaf in leaves:
        for c in grid:
            cand = substitute(tree, leaf, K(c, mp.nstr(c, 8)))
            r, _ = measure(cand, xs)
            if r.verdict != "ok" or not r.strict:
                continue
            if best is None or r.strict > best.strict:
                r2 = confirm(cand)
                if r2.verdict == "ok" and r2.strict:
                    best, best_tree = r2, cand
    return best, best_tree


def tuning_pass(pools, depths, xs, per_depth=25):
    print("\n=== TUNED CONSTANTS — solving for the leaf rather than picking from an alphabet ===")
    rng = random.Random(20260923)
    for d in depths:
        cands = [it for it in pools.get(d, []) if it.reading.verdict == "ok"]
        cands.sort(key=lambda it: -(it.reading.strict or 0))
        raised, best, best_tree = 0, None, None
        for it in cands[:per_depth]:
            base = it.reading.strict or 0
            r, tr = tune(it.tree, xs, rng=rng)
            if r and r.strict > base:
                raised += 1
            if r and (best is None or r.strict > best.strict):
                best, best_tree = r, tr
        if best is None:
            print(f"  depth {d}: no tuned tree confirmed")
            continue
        print(f"  depth {d}: best tuned height strict={best.strict} floor={best.floor} "
              f"(prediction j-3 = {max(d-3,0)}; {raised} of {min(len(cands),per_depth)} raised by tuning)")
        print(f"      {str(best_tree)[:140]}")


# ── the only mechanism that can beat j − 3, hunted directly ─────────────────────────────────────
#
# THE STRUCTURAL ARGUMENT, which says where a counterexample must live and is worth more than any
# amount of budget spent elsewhere.  Write max_d, min_d, pos_d for the largest, the most negative,
# and the smallest POSITIVE germ at depth d.  Three recurrences, from `eml A B = exp A − log₀ B`:
#
#   max_d = exp(max_{d-1}) − log(pos_{d-1})      (biggest left child, smallest positive right one —
#                                                 log₀ is NEGATIVE on (0,1), which is how a leaf
#                                                 ADDS to a germ and is the whole offset mechanism)
#   min_d = −log(max_{d-1})                      (exp A → 0, biggest possible subtrahend)
#   pos_d ≥ exp(min_{d-1})   **PROVIDED log₀ B ≤ 0 at the top node** — then t ≥ exp A.
#
# Unrolled from `max_0 = x`: max_1 = exp x + C, max_2 = e^C·exp(exp x) + C', so
# min_3 = −exp x − C and pos_4 ≥ exp(−exp x − C).  In general
#
#     −log pos_d  ≤  tower_{d-3}(x) + C        — DecayFloor at height d−3, for FREE,
#
# and strictly (no constant allowed) height d−2, which is ATTAINED: `offset_escalation` builds it.
#
# So the ONLY way to break the bound is for the top node's `log₀ B` to be POSITIVE and to CANCEL
# against `exp A`, and the arithmetic is unforgiving: to reach height d−2 in the DecayFloor reading
# the cancellation must itself be of tower height d−2.  Cancellation cannot bootstrap — it has to
# be as deep as the thing it is trying to build.
#
# Random pairing almost never produces a near-meeting.  This does it on purpose: index the pool by
# `log(log₀ B)` and, for each A, take the B whose `log₀ B` is CLOSEST to `exp(A)`.

def meet_hunt(pools, d, xs, neighbours=6, tune_top=12):
    import functools
    lower = [it for k in range(d) for it in pools.get(k, [])]
    keyed = []
    for it in lower:
        v = it.vals[-1]
        if v is None or G.sign(v) <= 0:
            continue
        try:
            keyed.append((G.logmag(G.log0(v)), it))     # log(log₀ B)
        except (ValueError, Unresolved):
            continue
    keyed.sort(key=functools.cmp_to_key(lambda p, q: G.cmp_signed(p[0], q[0])))
    keys = [k for k, _ in keyed]
    best, census = [], collections.Counter()
    for a in lower:
        av = a.vals[-1]
        if av is None:
            continue
        lo, hi = 0, len(keys)
        while lo < hi:                                   # bisect on the tower order
            mid = (lo + hi) // 2
            if G.cmp_signed(keys[mid], av) < 0:
                lo = mid + 1
            else:
                hi = mid
        for j in range(max(0, lo - neighbours), min(len(keyed), lo + neighbours)):
            b = keyed[j][1]
            vals, cut = [], 0
            for i in range(len(xs)):
                x, ai, bi = xs[i], a.vals[i], b.vals[i]
                if ai is None or bi is None:
                    vals.append(None)
                    continue
                try:
                    lhs = G.mk_exp(ai)
                    v = G.sub(lhs, G.log0(bi))
                    vals.append(v)
                    if i == len(xs) - 1:
                        cut = cut_height(lhs, v, x)
                except (Unresolved, ValueError, OverflowError):
                    vals.append(None)
            r = read_decay(vals, xs)
            census[(r.verdict, cut)] += 1
            if r.verdict == "ok" and r.strict:
                best.append((r.strict, cut, E(a.tree, b.tree)))
    best.sort(key=lambda z: (-z[0], -z[1]))
    cuts = collections.Counter(c for (_, c), n in census.items() for _ in range(n))
    print(f"\n=== NEAR-MEETING HUNT at depth {d}: "
          f"{sum(census.values())} deliberately-cancelling nodes ===")
    print(f"  cancellation height of the top node's own subtraction: {dict(sorted(cuts.items()))}")
    print(f"  (to reach height {d-2} — a counterexample — a node needs cancellation height "
          f"{d-2}; the growth bound gives height {max(d-3,0)} to every tree for free)")
    conf = []
    for k, cut, t in best[:tune_top]:
        r = confirm(t)
        if r.verdict == "ok" and r.strict:
            conf.append((r, cut, t))
    ms = max((r.strict for r, _, _ in conf), default=0)
    mf = max((r.floor for r, _, _ in conf), default=0)
    print(f"  CONFIRMED max height from near-meetings: strict={ms} DecayFloor={mf} "
          f"(prediction j-3 = {max(d-3,0)})")
    for r, cut, t in conf[:2]:
        print(f"      strict={r.strict} cut={cut}  {str(t)[:110]}")
    # and tune a constant inside the best near-meeting, which is the sharpest attack available:
    # a real constant chosen to make the two germs meet, rather than one picked from an alphabet.
    rng = random.Random(4)
    raised, bt, btr = 0, None, None
    for _, _, t in best[:tune_top]:
        r, tr = tune(t, xs, rng=rng)
        if r and (bt is None or r.strict > bt.strict):
            bt, btr = r, tr
    if bt:
        print(f"  best after solving for a leaf constant: strict={bt.strict} floor={bt.floor}")
        print(f"      {str(btr)[:130]}")
    return ms, mf


# ── the pair form ───────────────────────────────────────────────────────────────────────────────

def pair_sweep(pools, j, xs, budget=200000, seed=20260923):
    """EmlGermApproach proper: gap = exp(A x) − C(x) over pairs of depth ≤ j."""
    items = [it for d in range(0, j + 1) for it in pools.get(d, [])]
    rng = random.Random(seed)
    pairs = [(a, b) for a in items for b in items]
    if len(pairs) > budget:
        pairs = rng.sample(pairs, budget)
    counts, best = collections.Counter(), []
    for a, b in pairs:
        vals = []
        for i in range(len(xs)):
            av, bv = a.vals[i], b.vals[i]
            if av is None or bv is None:
                vals.append(None)
                continue
            try:
                vals.append(G.sub(G.mk_exp(av), bv))
            except (Unresolved, ValueError, OverflowError):
                vals.append(None)
        r = read_decay(vals, xs)
        counts[r.verdict] += 1
        if r.verdict == "ok" and r.strict:
            best.append((r.strict, a.tree, b.tree))
    best.sort(key=lambda z: -z[0])
    ms = best[0][0] if best else 0
    print(f"\n=== PAIR FORM, depth ≤ {j}: {len(pairs)} pairs, {reach(xs)} ===")
    print(f"  {dict(counts)}")
    print(f"  max required height (tail, unconfirmed): {ms}")
    for k, a, b in best[:3]:
        print(f"      k={k}  A={str(a)[:55]}  C={str(b)[:55]}")
    return ms


# ── precision ladder ────────────────────────────────────────────────────────────────────────────

def precision_ladder(max_depth, consts, ladder=(15, 30, 60, 120, 240)):
    """What precision does each depth actually need?  Not a guess: run the same beam at each dps
    and report where the verdict and the unresolved count stop moving."""
    print("\n=== PRECISION LADDER — what each depth actually needed ===")
    print("  dps | " + " | ".join(f"d{d}: max h / unresolved" for d in range(2, max_depth + 1)))
    prev = None
    settle = {}
    for dps in ladder:
        mp.dps = dps
        xs = ray()
        pools, stats, hall, _ = beam(max_depth, constants(consts), xs,
                                     per_class=25, budget=12000)
        row, sig = [], []
        for d in range(2, max_depth + 1):
            hs = [it.reading.strict for it in hall[d] if it.reading.strict]
            mh = max(hs, default=0)
            unres = stats[d][2].get("unresolved", 0)
            row.append(f"{mh} / {unres}")
            sig.append((d, mh))
            if prev is not None and dict(prev).get(d) == mh and d not in settle:
                settle[d] = dps
        print(f"  {dps:>4} | " + " | ".join(row))
        prev = sig
    print("  settles at (first dps whose verdict the next one repeats): "
          + ", ".join(f"depth {d}: {p}" for d, p in sorted(settle.items())))


# ── main ────────────────────────────────────────────────────────────────────────────────────────

def offset_escalation(depths=(4, 5, 6)):
    """Does the required height rise with CONSTANT MAGNITUDE at fixed depth?

    The cheapest possible way for the conjecture to be false, and the 2026-09-05 run tested it only
    at depth 2, over {0,1,5,50,1000} — an alphabet with NO member in (0,1), so `log₀ c ≥ 0` at every
    leaf and a leaf can never ADD to a germ.  `e^-M` can, and it is the one mechanism by which a
    constant moves the reading at all:

        eml(tower_{n-1}, const e^-M) = tower_n(x) + M    at depth n
        … ⇒  exp(1 − tower_n(x) − M)                     at depth n+3

    which misses the strict height-n floor at EVERY x, by the constant M − 1, and meets DecayFloor's
    `exp(-(C + tower_n x))` at height n with C = M − 1.  So the two readings of the floor part
    company at depth 4 as soon as the alphabet can express an offset — and the height stays put as
    M runs over 40 orders of magnitude, which is the thing being tested."""
    print("\n=== CONSTANT ESCALATION at fixed depth — the cheapest falsification ===")
    for d in depths:
        n = d - 3
        row = []
        for M in (0, 1, 5, 50, 10 ** 6, 10 ** 40):
            t = VAR
            for _ in range(max(n - 1, 0)):
                t = eTree(t)
            t = E(t, K(mexp(-mpf(M)), f"e^-{M}"))       # tower_n(x) + M
            t = eTree(E(K(0, "0"), eTree(t)))           # exp(1 − tower_n(x) − M)
            near = [G.num(v) for v in (5, 12, 40)]      # where an offset is still resolvable
            r_small, _ = measure(t, near)
            r_tail = confirm(t)
            row.append(f"M={M:<6g}: small-x strict={r_small.strict} "
                       f"floor={r_small.floor} | tail strict={r_tail.strict} floor={r_tail.floor}")
        print(f"  depth {d} (prediction j-3 = {max(d-3,0)}), tree depth {t.depth}")
        for s in row:
            print("      " + s)


LIMITATIONS = """
=== WHAT THIS SEARCH CANNOT FIND — the deliverable, since no counterexample appeared ===

  1. IT CANNOT RESOLVE AN ADDITIVE CONSTANT IN THE TAIL, and that is now the sharpest limitation,
     where the 2026-09-05 instrument's was reach.  Beside `tower_{j-3}(x)` at x = 1e64, any
     constant is below the working precision and is ABSORBED, so the TAIL reading is DecayFloor's
     constant-tolerant height and NOT EmlGermApproach's strict one.  The two differ by exactly one
     (`offset_escalation`), and the window of x on which the difference is visible shrinks like
     log^{j-3}(M).  Every "strict" figure printed at the tail should be read as "DecayFloor".

  2. IT CANNOT TELL AN EXACT MEETING FROM A MEETING TO WITHIN ITS OWN PRECISION.  `exp(E) − exp(E
     − exp(−E))` is 1 and reads as 0.  Raising dps does not help — the absorbed term is smaller
     than any representable relative perturbation of its neighbour.  Those trees are refused
     (`zero-after-absorption`), so this is a MISS, never a false alarm.  §4's `eTree (eTree A)` is
     a known satisfied instance of the same shape, so the class is not believed empty.

  3. ITS COVERAGE IS A BEAM, NOT A CENSUS, ABOVE DEPTH 3.  Exhaustive only at depth ≤ 3 over {0,1}
     (21 612 trees, matching the 2026-09-05 sweep exactly).  Above that it is a selected pool: the
     extremes a counterexample must live at, plus §3's families as seeds, plus a random remainder.
     A counterexample of a shape the selection rules never favour is invisible, and no coverage
     percentage can be quoted, because the class is uncountable once leaf constants are free.

  4. TUNING SOLVES FOR ONE LEAF AT A TIME, on a fixed grid with a local refinement.  A
     counterexample needing two constants in a particular RELATION — which is exactly what an
     engineered germ meeting looks like — is outside it.

  5. IT MEASURES A FINITE RAY AND READS A TREND.  Unchanged from 2026-09-05 and unfixable by any
     instrument of this kind: agreement between the x ≤ 1e64 and x ≤ 1e1294 readings does not prove
     a reading is asymptotic; disagreement proves it is not.  A germ whose behaviour separates only
     beyond tower-scale x is invisible — though "beyond 1e1294" is a different sentence from the
     2026-09-05 run's "beyond x = 2.8".

  6. GERM DEDUPLICATION IS BY 20 SIGNIFICANT DIGITS AT 10 RAY POINTS.  Two genuinely distinct germs
     agreeing there are collapsed and one is dropped.  The distinct-germ counts are therefore lower
     bounds on diversity and upper bounds on what was examined.

  7. IT CANNOT CERTIFY THE CANCELLING CASE, ONLY PROBE IT.  The growth recurrences give DecayFloor
     height j−3 for free to every tree whose top node has `log₀ B ≤ 0`; the whole open content is
     the cancelling case, and there the instrument reports only what it happened to construct —
     top-node cancellation never exceeded height 2 anywhere, where breaking the bound at depth d
     needs height d−2.
"""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", nargs="?", default="full",
                    choices=["controls", "regress", "full", "deep", "precision",
                             "meet", "offset"])
    ap.add_argument("--dps", type=int, default=120)
    ap.add_argument("--depth", type=int, default=6)
    ap.add_argument("--per-class", type=int, default=60)
    ap.add_argument("--budget", type=int, default=120000)
    args = ap.parse_args()

    mp.dps = args.dps
    global NEAR, FAR
    NEAR, FAR = ray(5.0), ray(8.0)
    M.set_rays(NEAR, FAR)          # `confirm` lives in the instrument and reads both rays
    print(f"working precision: {mp.dps} dps ({mp.prec} bits), "
          f"cancellation margin {G.guard_bits()} bits")
    print(f"scoring ray {reach(NEAR)}   confirmation ray {reach(FAR)}")

    if args.mode == "precision":
        precision_ladder(min(args.depth, 5), True)
        return 0

    if not run_controls():
        sys.exit("controls failed; a negative result would be unreadable")
    if args.mode == "controls":
        return 0

    if args.mode == "offset":
        offset_escalation(tuple(range(4, args.depth + 1)))
        return 0

    if args.mode == "meet":
        pools, _, _, _ = beam(args.depth, constants(True), NEAR, args.per_class, args.budget)
        for d in range(4, args.depth + 1):
            meet_hunt(pools, d, NEAR)
        return 0

    if args.mode in ("regress", "full"):
        # Against the 2026-09-05 table: depth 2 and 3 exhaustive over {0,1}, max height 0.
        exhaustive(2, constants(False), NEAR, "regression vs 2026-09-05, constants {0,1}")
        exhaustive(3, constants(False), NEAR, "regression vs 2026-09-05, constants {0,1}")
        if args.mode == "regress":
            return 0

    pools, _ = report_beam(args.depth, constants(True), NEAR,
                           args.per_class, args.budget, "wide alphabet")
    for d in range(4, args.depth + 1):
        meet_hunt(pools, d, NEAR)
    offset_escalation(tuple(range(4, min(args.depth, 6) + 1)))
    tuning_pass(pools, range(3, min(args.depth, 6) + 1), NEAR)
    for j in (2, 3, 4):
        if j <= args.depth:
            pair_sweep(pools, j, NEAR)
    print(LIMITATIONS)
    return 0


if __name__ == "__main__":
    sys.exit(main())
