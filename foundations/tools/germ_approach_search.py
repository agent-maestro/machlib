#!/usr/bin/env python3
"""Falsification search for EmlGermApproach (machlib EmlGermApproachResearch.md §6).

THE CONJECTURE. For every depth bound j there is ONE tower height k such that, for every pair of
EML trees (A, C) of depth ≤ j with C eventually strictly below exp∘A on a ray, the gap
exp(A x) − C(x) is eventually at least exp(−towerFn k x).  The whole open content is that ∃k sits
OUTSIDE the ∀(A,C): k may depend on the depth bound, not on the pair.

WHAT A COUNTEREXAMPLE LOOKS LIKE.  Not a single pair — for any one pair, k exists (that is
EmlGermApproachPerPair, already proved, a corollary of Hardy 1912).  A counterexample is a FAMILY
at FIXED depth whose required k is unbounded: increasing syntactic complexity (bigger constants,
different shapes — anything but depth) driving the gap below every tower floor.

THE METRIC.  For a pair, on a ray, let g(x) = exp(A x) − C(x) > 0 and h(x) = −log g(x).  The
required tower height at x is the least k with towerFn k x ≥ h(x), i.e. the number of times log
must be applied to h(x) before it drops to x.  Report the max over the sampled x.

THE TWO RECORDED TRAPS, both obeyed here.
  * Double precision cannot decide this question: a 528-configuration search reached machine
    epsilon (1.11e-16) and all ten sub-1e-6 candidates were refuted only at 80 digits.  So mpmath
    at dps=120, and any gap that lands within 10^-90 of zero is reported as UNDECIDED at this
    precision rather than as a small gap.
  * A grid steps over singularities: a 400 001-point grid reported sup|t| ≈ 15 for a germ that
    diverges.  So this does not grid a fixed window; it walks x in ITERATED-LOG coordinates
    (x = exp(exp(t)) style spacing) out to where the germ's behaviour is asymptotic, and it
    records the trend of the metric rather than a supremum over a box.

EML: eval(const c) = c, eval(var) = x, eval(eml A B) x = exp(A x) − log₀(B x), where log₀ is the
TOTALISED logarithm (log₀ y = 0 for y ≤ 0) — the convention that makes the grammar generate
anything, and the source of most of its surprises.
"""
from __future__ import annotations

import itertools
import sys
from dataclasses import dataclass

from mpmath import mp, mpf, exp as mexp, log as mlog, inf, isnan, isinf

mp.dps = 120

# The precision guard is about CANCELLATION, not magnitude.  A gap is untrustworthy when it is
# the difference of two nearly-equal large numbers — there the working precision is spent and
# what remains is noise, which is the recorded trap (a 528-configuration search that reached
# 1.11e-16 and mistook it for a finding).  A gap that arises WITHOUT cancellation is exact at any
# size: `exp(−exp x) − 0` is 1e-9566 at x = 10 and every digit of it is real.
#
# The first version of this guard was absolute (|gap| < 1e-90 ⇒ undecided).  It rejected both
# positive controls — the two pairs whose height is known BY CONSTRUCTION to be nonzero — and
# would have reported "height 0 everywhere, conjecture survives" from an instrument that was
# discarding precisely the interesting cases.  It was caught by the controls and by nothing else.
CANCEL_MARGIN = mpf(10) ** (-(120 - 20))   # dps − 20 digits of headroom
# Guard against overflow in the double-exponential regime; a value past this is treated as
# "diverges", which is a legitimate answer, not a failure.
BIG = mpf(10) ** (10**6)


# ── the grammar ──────────────────────────────────────────────────────────────

@dataclass(frozen=True)
class Tree:
    kind: str            # 'const' | 'var' | 'eml'
    c: object = None     # for const
    a: object = None     # for eml
    b: object = None

    def depth(self) -> int:
        if self.kind in ("const", "var"):
            return 0
        return 1 + max(self.a.depth(), self.b.depth())

    def __str__(self) -> str:
        if self.kind == "const":
            return f"{float(self.c):g}"
        if self.kind == "var":
            return "x"
        return f"eml({self.a},{self.b})"


def C(c) -> Tree:
    return Tree("const", c=mpf(c))


VAR = Tree("var")


def E(a: Tree, b: Tree) -> Tree:
    return Tree("eml", a=a, b=b)


def log0(y):
    """The totalised logarithm: 0 for y ≤ 0."""
    if y <= 0:
        return mpf(0)
    return mlog(y)


# Three-valued evaluation.  A value is either an mpf, or the sentinel HUGE ("positively
# enormous — beyond any representable float, but KNOWN to be positive and larger than anything
# finite"), or None ("could not be determined").  The distinction matters: the first pass of this
# search returned None for the doubly-exponential regime, so every pair whose left side outgrows
# the working range lost its TAIL samples and was scored on the FOOT of the ray alone — a
# truncation read as asymptotics, which is the second recorded trap wearing a new hat.  With
# HUGE, `enormous − finite` is correctly a diverging gap (height 0) rather than a missing sample.
HUGE = "HUGE"
EXP_CEIL = mpf(10) ** 6          # exp of anything past this is beyond the working range


def ev(t: Tree, x):
    """Evaluate to an mpf, or HUGE (positively enormous), or None (undetermined)."""
    try:
        if t.kind == "const":
            return t.c
        if t.kind == "var":
            return x
        av = ev(t.a, x)
        bv = ev(t.b, x)
        if av is None or bv is None:
            return None
        if av is HUGE:
            return HUGE              # exp(enormous) − log(anything finite-ish) is enormous
        if av > EXP_CEIL:
            return HUGE
        e = mexp(av)
        if bv is HUGE:
            return None              # e − log(enormous): both sides unbounded, undetermined
        return e - log0(bv)
    except (OverflowError, ValueError):
        return None


def exp_eval(t: Tree, x):
    """exp(t(x)), the left-hand side of the gap; HUGE / None as above."""
    v = ev(t, x)
    if v is None:
        return None
    if v is HUGE or v > EXP_CEIL:
        return HUGE
    try:
        return mexp(v)
    except (OverflowError, ValueError):
        return HUGE


# ── the metric ───────────────────────────────────────────────────────────────

def required_height(h, x, cap: int = 12):
    """Least k with towerFn k x ≥ h, i.e. how many logs take h down to x.  h = −log(gap)."""
    if h is None:
        return None
    if h <= x:
        return 0
    k = 0
    v = h
    while k < cap:
        if v <= x:
            return k
        if v <= 0:
            return k
        v = mlog(v)
        k += 1
    return cap  # saturated: beyond what this search can distinguish


def gap_profile(A: Tree, Cq: Tree, xs, tail_from=0.6):
    """Walk the ray; return (verdict, tail_height, detail).

    THE HEIGHT IS READ IN THE TAIL, not maximised over the ray.  The conjecture says
    `∃X₁ ≥ X₀, ∀x ≥ X₁, …` — it is free to start late, so a gap that is small only near the
    foot of the ray is not evidence of anything.  First pass of this search maximised over all
    sampled x and reported height 2 for pairs whose gap is a CONSTANT (`exp(0) − log(exp(50))`
    is the constant `exp(−49)`): at x = 2 that constant is below the floor, at x = 10^6 it is
    astronomically above it.  Constant gaps have tail height 0, and the corrected metric says so.

    verdict: 'ok' (gap positive and its required height is bounded),
             'not-below' (C is not eventually below exp∘A — the hypothesis fails, not a
                          counterexample), 'undecided' (gap within ZERO_FLOOR of 0 at dps=120),
             'overflow' (values beyond the working range on the whole tail)."""
    heights = []          # (x, k) over the whole ray
    seen_positive = 0
    seen_overflow = 0
    gaps = []
    tail_measured = False
    for i, x in enumerate(xs):
        lhs = exp_eval(A, x)
        rhs = ev(Cq, x)
        if lhs is None or rhs is None:
            seen_overflow += 1
            continue
        if lhs is HUGE and rhs is HUGE:
            seen_overflow += 1          # ∞ − ∞ at this working range: undetermined, not a gap
            continue
        if lhs is HUGE:
            # left side diverges, right side finite: the gap diverges, so every floor is met
            heights.append((x, 0))
            gaps.append((x, BIG))
            if i >= int(len(xs) * tail_from):
                tail_measured = True
            continue
        if rhs is HUGE:
            return ("not-below", None, f"C diverges above exp∘A at x={float(x):.3g}")
        g = lhs - rhs
        if isnan(g) or isinf(g):
            seen_overflow += 1
            continue
        if i >= int(len(xs) * tail_from):
            tail_measured = True
        if g <= 0:
            return ("not-below", None, f"gap ≤ 0 at x={float(x):.3g}")
        scale = max(abs(lhs), abs(rhs))
        if scale > 0 and g < scale * CANCEL_MARGIN:
            return ("undecided", None,
                    f"gap {mp.nstr(g, 5)} is {mp.nstr(g / scale, 3)} of the operands at "
                    f"x={float(x):.3g} — cancellation, not a measurement")
        seen_positive += 1
        gaps.append((x, g))
        h = -mlog(g)
        heights.append((x, required_height(h, x)))
    if not heights:
        return ("overflow", None, f"{seen_overflow} sample(s) beyond working range")
    if not tail_measured:
        # The far end of the ray produced nothing, so whatever was measured describes the FOOT.
        # Refusing to score it is the whole point: an unmeasured tail is not a small height.
        return ("tail-unmeasured", None,
                f"only {len(heights)} foot sample(s); {seen_overflow} beyond range")
    cut = int(len(heights) * tail_from)
    tail = heights[cut:] or heights[-1:]
    tail_k = max(k for _, k in tail)
    # is the gap decaying?  (a decaying gap is the only shape that can ever need k > 0 eventually)
    decaying = len(gaps) >= 2 and gaps[-1][1] < gaps[cut][1]
    tag = "decaying" if decaying else "non-decaying"
    return ("ok", tail_k, f"{tag} tail_k={[k for _, k in tail]} all={[k for _, k in heights]}")


# ── the ray, in iterated-log coordinates ─────────────────────────────────────

def ray_for_depth(depth: int, n=12):
    """The ray, chosen so the depth-`d` tower stays inside the working range.

    HOW FAR THE SEARCH CAN SEE IS A FUNCTION OF DEPTH, and saying so is part of the result.  A
    depth-2 tree reaches exp(exp x), fine out to x ~ 10^6.  A depth-3 tree reaches exp(exp(exp x)),
    which passes the working range at about x = 13; depth 4 at about x = 2.8.  Walking a fixed
    long ray at depth 3 does not probe the tail, it just loses every sample — which is what the
    first version of this search did, and the tail-unmeasured guard is what caught it.

    Spacing is geometric in the ITERATED LOG, per the note: a plain grid steps over singularities
    (a recorded 400 001-point grid reported a finite sup for a germ that diverges)."""
    top = {0: mpf(10) ** 6, 1: mpf(10) ** 6, 2: mpf(10) ** 5,
           3: mpf(13), 4: mpf("2.8")}.get(depth, mpf("2.2"))
    lo = mpf("1.5")
    if top <= lo:
        return [lo]
    # geometric in log-space between lo and top
    lt, tt = mlog(lo), mlog(top)
    return [mexp(lt + (tt - lt) * mpf(i) / (n - 1)) for i in range(n)]


def ray(n=14):
    """Back-compat wrapper: the depth-2 ray."""
    return ray_for_depth(2, n)


# ── the enumeration ──────────────────────────────────────────────────────────

def trees_upto(depth: int, consts):
    """All EML trees of depth ≤ `depth` over the given constant set."""
    level = [C(c) for c in consts] + [VAR]
    allt = list(level)
    for _ in range(depth):
        new = [E(a, b) for a, b in itertools.product(allt, allt)]
        allt = allt + new
        # dedupe by printed form
        seen, ded = set(), []
        for t in allt:
            s = str(t)
            if s not in seen:
                seen.add(s)
                ded.append(t)
        allt = ded
    return [t for t in allt if t.depth() <= depth]


def sweep(depth, consts, label, limit_pairs=None):
    xs = ray_for_depth(depth)
    ts = trees_upto(depth, consts)
    ts = [t for t in ts if t.depth() <= depth]
    print(f"\n=== {label}: depth ≤ {depth}, {len(consts)} constants, {len(ts)} trees ===")
    counts = {"ok": 0, "not-below": 0, "undecided": 0, "overflow": 0, "tail-unmeasured": 0}
    worst = []
    if limit_pairs and len(ts) * len(ts) > limit_pairs:
        # RANDOM, not strided.  Striding an ordered product varies the second component fast and
        # the first component barely at all, so a "6000-pair sample" can contain a handful of
        # distinct left-hand trees.  That is a census dressed as a sample, and this project has a
        # recorded instance of exactly that error.
        import random
        rng = random.Random(20260905)
        pairs = [(rng.choice(ts), rng.choice(ts)) for _ in range(limit_pairs)]
    else:
        pairs = list(itertools.product(ts, ts))
    for A, Cq in pairs:
        verdict, mh, detail = gap_profile(A, Cq, xs)
        counts[verdict] += 1
        if verdict == "ok" and mh is not None:
            worst.append((mh, str(A), str(Cq), detail))
    worst.sort(key=lambda r: -r[0])
    print(f"  pairs examined: {len(pairs)}   {counts}")
    if worst:
        hs = [w[0] for w in worst]
        import collections
        print(f"  required tower height, distribution: {dict(collections.Counter(hs))}")
        print(f"  MAX required height: {worst[0][0]}")
        for w in worst[:5]:
            print(f"    k={w[0]}  A={w[1][:60]}  C={w[2][:60]}")
    return counts, (worst[0][0] if worst else None)


# ── positive controls ────────────────────────────────────────────────────────
#
# An instrument must be shown capable of BOTH verdicts before either is read.  A search that
# reports "height 0 everywhere" is worthless until it is shown to report a nonzero height on a
# pair whose height is known by hand.  These are those pairs, built by construction:
#
#   D = eml(var, const e⁻¹)      = exp(x) − log(e⁻¹)      = exp(x) + 1        depth 1
#   B = eml(D, const 1)          = exp(exp x + 1) − 0     = e·exp(exp x)      depth 2
#   A₁ = eml(const 0, B)         = 1 − log(e·exp(exp x))  = −exp(x)           depth 3
#   gap(A₁, const 0) = exp(−exp x);  h = exp x;  one log takes it to x  ⇒  height 1
#
# and one level deeper, A₂ with value −exp(exp x), whose gap is exp(−exp(exp x)) ⇒ height 2.
# Both are legitimate members of the class: they show the required height rising with DEPTH,
# which the conjecture explicitly allows (k may depend on j).  What it forbids is the height
# rising at FIXED depth, and that is what the sweeps look for.

def controls():
    D = E(VAR, C(mexp(-1)))                 # exp(x) + 1
    B = E(D, C(1))                          # e·exp(exp x)
    A1 = E(C(0), B)                         # −exp(x)                        depth 3
    D2 = E(D, C(mexp(-1)))                  # exp(exp x + 1) + 1
    B2 = E(D2, C(1))                        # e·exp(exp(exp x + 1) + 1)
    A2 = E(C(0), B2)                        # −exp(exp x + 1)                depth 4
    return [("control-1 (expect height 1)", A1, C(0), 1),
            ("control-2 (expect height ≥ 2)", A2, C(0), 2)]


def run_controls():
    print("\n=== POSITIVE CONTROLS — the search must report a NONZERO height here ===")
    allgood = True
    for label, A, Cq, expect in controls():
        xs = ray_for_depth(A.depth())
        verdict, k, detail = gap_profile(A, Cq, xs)
        ok = (verdict == "ok" and k is not None and k >= expect)
        allgood &= ok
        print(f"  {label}: depth(A)={A.depth()}  verdict={verdict}  height={k}  "
              f"{'FIRES' if ok else 'SILENT — INSTRUMENT BROKEN'}")
        print(f"      {detail[:150]}")
    print("  CONTROLS " + ("PASS — the search can report a nonzero height."
                           if allgood else "FAIL — no negative result may be read from this run."))
    return allgood


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "small"
    if mode == "controls":
        sys.exit(0 if run_controls() else 1)
    if mode == "small":
        # Does the required height depend on the CONSTANTS at fixed depth?  Three constant sets
        # of growing magnitude, same shapes.  If the conjecture is false in the cheapest possible
        # way, the max height rises with the constants.
        for label, consts in [
            ("tiny constants", [0, 1]),
            ("mid constants", [0, 1, 5]),
            ("large constants", [0, 1, 50]),
            ("huge constants", [0, 1, 1000]),
        ]:
            sweep(2, consts, label)
    elif mode == "depth3":
        if not run_controls():
            sys.exit("controls failed; a negative result would be unreadable")
        sweep(3, [0, 1], "depth 3, minimal constants", limit_pairs=6000)


