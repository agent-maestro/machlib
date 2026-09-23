#!/usr/bin/env python3
"""Tower arithmetic — exact iterated-log coordinates for the EML germ search.

WHY THIS EXISTS.  `germ_approach_search.py` (2026-09-05) evaluates EML germs as mpmath floats at a
fixed 120 digits, and its own limits section names the consequence first: *"it cannot see far"* —
the ray reaches `x ≤ 10^5` at depth 2, `x ≤ 13` at depth 3, `x ≤ 2.8` at depth 4, `x ≈ 2.2` at
depth 5, where 354 of 8 000 readings were rejected as unstable and 1 141 overflowed.  The cause is
not the precision setting.  A VALUE representation must materialise the mantissa of
`exp(exp(exp(x)))`, and to know that mantissa to ONE digit you must know `exp(exp(x))` to one
ABSOLUTE digit, i.e. `exp(x)/ln 10` significant digits.  At `x = 20` that is 210 million digits.
No dps reaches depth 5; raising it buys about one unit of `x`.

THE FIX.  Do not represent the value.  Represent the ITERATED-LOG SPINE and keep a mantissa only at
the bottom:

    val((), m)          = m                        (m an ordinary mpf, any sign)
    val((s,) + rest, m) = s * exp(val(rest, m))    (s = ±1)

canonical iff a nonempty spine's inner value has |·| > LOGBIG, so every number has exactly one
form.  Then

    exp  is  PUSH a (+1) onto the spine        — exact, no arithmetic at all
    log  is  POP  a (+1) off  the spine        — exact, no arithmetic at all
    neg  is  FLIP the leading sign             — exact

and the ONLY operation that can cost a digit is `+`.  `exp(-exp(exp(x)))` at `x = 10^30` is the
three-symbol object `((+1,-1,+1), 1e30)`, compared and differenced exactly.  Ray reach stops
being a function of depth, which is the single limitation the 2026-09-05 run called sharpest.

WHAT `+` COSTS, AND WHERE THE GUARD GOES.  For `a = sa·exp(A)`, `b = sb·exp(B)` with |a| ≥ |b|,

    a + b = sa · exp(A) · (1 + (sa·sb)·exp(B - A)),      D := B - A ≤ 0

so a sum is a RECURSIVE difference of exponents plus one ordinary `expm1`, bottoming out on two
ordinary mpfs.  That bottom is the one place cancellation destroys digits, and the guard there is
RELATIVE — `|a+b| < max(|a|,|b|)·2^-(prec-guard)` raises `Unresolved` — never absolute.  §6 defect
3 of the research note is this exact mistake: the first instrument's absolute guard
(`|gap| < 1e-90 ⇒ undecided`) rejected BOTH positive controls, because `exp(-exp x) - 0` is
`1e-9566` at `x = 10` and every digit of it is real.  A tiny number is not a lost number; a number
that lost its leading digits to a near-equal neighbour is.

`1 - exp(D)` for an infinitesimal D is returned as `-D`, never computed as written: that is the one
place a naive implementation re-introduces the cancellation the spine exists to avoid.

THE ERROR BIAS, AND IT IS THE RIGHT WAY ROUND.  When `|b|` falls below the working precision beside
`|a|`, `a + b` returns `a` — the term is ABSORBED.  In a difference that makes the computed |value|
LARGER than the truth, hence the computed height SMALLER.  So this instrument can MISS a
counterexample and cannot INVENT one.  Every absorption is counted (`absorbed()`), so a result that
lands on exact zero after one can be reported in its own bucket instead of being read as a germ
that meets its target.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Tuple

from mpmath import exp as mexp
from mpmath import expm1 as mexpm1
from mpmath import log as mlog
from mpmath import mp, mpf

# A spine is extended rather than collapsed once the inner value passes this, so every mantissa
# stays an ordinary mpf of modest exponent (|v| ≤ exp(1000) ≈ 1e434, which mpmath handles in
# microseconds).  Nothing depends on the exact value; it only has to sit comfortably inside the
# working range and comfortably above every constant and every ray point's logarithm.
LOGBIG = mpf(1000)

ZERO_SPINE: Tuple[int, ...] = ()

_ABSORBED = 0


def absorbed() -> int:
    return _ABSORBED


def reset_absorbed() -> None:
    global _ABSORBED
    _ABSORBED = 0


class Unresolved(Exception):
    """A difference lost more relative precision than the working precision can vouch for.

    Never swallowed and never scored: a tree that raises this is counted in its own bucket and
    retried at higher precision.  Reading it as a small value would be the 2026-09-05 instrument's
    defect 2 — a truncation read as asymptotics — in a new costume."""


@dataclass(frozen=True)
class T:
    """`sign_chain · exp · … · exp(mant)`.  See the module docstring for the exact reading."""

    signs: Tuple[int, ...]
    m: object  # mpf

    def __str__(self) -> str:
        s = mp.nstr(self.m, 8)
        for sg in reversed(self.signs):
            s = ("exp(%s)" % s) if sg > 0 else ("-exp(%s)" % s)
        return s


def num(v) -> T:
    return T(ZERO_SPINE, mpf(v))


ZERO = T(ZERO_SPINE, mpf(0))
ONE = T(ZERO_SPINE, mpf(1))
TWO = T(ZERO_SPINE, mpf(2))


def guard_bits() -> int:
    """Bits of the working precision held back as the cancellation margin."""
    return max(24, mp.prec // 5)


def rel_eps():
    return mpf(2) ** (-(mp.prec - guard_bits()))


def is_ord(a: T) -> bool:
    return not a.signs


def is_zero(a: T) -> bool:
    return not a.signs and a.m == 0


def sign(a: T) -> int:
    if a.signs:
        return a.signs[0]
    return -1 if a.m < 0 else (1 if a.m > 0 else 0)


def neg(a: T) -> T:
    if not a.signs:
        return T(ZERO_SPINE, -a.m)
    return T((-a.signs[0],) + a.signs[1:], a.m)


def with_sign(s: int, a: T) -> T:
    return a if s > 0 else neg(a)


def logmag(a: T) -> T:
    """log |a|, EXACTLY — a spine pop when there is a spine, one mpmath log when there is not."""
    if a.signs:
        return T(a.signs[1:], a.m)
    if a.m == 0:
        raise ValueError("log 0")
    return T(ZERO_SPINE, mlog(abs(a.m)))


def mk_exp(a: T) -> T:
    """exp(a) — a spine push unless the argument is small enough to keep a real mantissa."""
    if not a.signs and abs(a.m) <= LOGBIG:
        return T(ZERO_SPINE, mexp(a.m))
    return T((1,) + a.signs, a.m)


def log0(a: T) -> T:
    """The TOTALISED logarithm of the EML semantics: log y for y > 0, and 0 for y ≤ 0."""
    return logmag(a) if sign(a) > 0 else ZERO


def cmp_signed(a: T, b: T) -> int:
    sa, sb = sign(a), sign(b)
    if sa != sb:
        return -1 if sa < sb else 1
    if sa == 0:
        return 0
    c = cmp_mag(a, b)
    return c if sa > 0 else -c


def cmp_mag(a: T, b: T) -> int:
    """Compare |a| and |b|, both nonzero.  Recurses on the spine; never forms a value."""
    if not a.signs and not b.signs:
        x, y = abs(a.m), abs(b.m)
        return -1 if x < y else (1 if x > y else 0)
    return cmp_signed(logmag(a), logmag(b))


def _blend(D: T, t: int) -> T:
    """`1 + t·exp(D)` for D ≤ 0 and t = ±1, as a nonnegative tower value.

    The `t = -1`, D infinitesimal branch is why this is a named function: `1 - exp(D)` computed as
    written subtracts two numbers agreeing in every digit the representation holds, which is the
    cancellation the spine exists to avoid.  For infinitesimal D it is `-D` to relative accuracy
    |D|/2, and in the spine representation that is exact."""
    global _ABSORBED
    if D.signs:
        # canonical spine ⇒ |D| is either > exp(LOGBIG) or < exp(-LOGBIG); D ≤ 0 here.
        _ABSORBED += 1
        if sign(logmag(D)) > 0:          # |D| enormous, D very negative: exp(D) is absorbed by 1
            return ONE
        return TWO if t > 0 else neg(D)  # |D| infinitesimal
    # SHORT-CIRCUIT, and it is a correctness-of-COST fix rather than a micro-optimisation.  `D.m`
    # is an ordinary mpf but can be -1e70685 on a far ray, and mpmath would then evaluate exp of
    # it — which needs ln 2 to seventy thousand digits just to place the exponent, minutes of work
    # for an answer that is 1 in every digit this precision holds.  Found by a specimen re-check
    # that hung; the far ray reached x = exp(exp(12)) and nothing else had ever gone that far.
    if D.m < -(mp.prec + 8) * mpf("0.6931471805599454"):
        _ABSORBED += 1
        return ONE
    u = mexp(D.m)
    c = (1 + u) if t > 0 else -mexpm1(D.m)
    if c == 1 and u != 0:
        _ABSORBED += 1                   # the smaller operand vanished into the larger
    return T(ZERO_SPINE, c)


def add(a: T, b: T) -> T:
    if is_zero(a):
        return b
    if is_zero(b):
        return a
    if not a.signs and not b.signs:
        s = a.m + b.m
        big = max(abs(a.m), abs(b.m))
        if s != 0 and abs(s) < big * rel_eps():
            raise Unresolved("relative cancellation past the working precision")
        return T(ZERO_SPINE, s)
    sa, sb = sign(a), sign(b)
    A, B = logmag(a), logmag(b)
    if cmp_signed(A, B) < 0:
        A, B, sa, sb = B, A, sb, sa
    D = sub(B, A)                        # ≤ 0
    c = _blend(D, sa * sb)
    if is_zero(c):
        return ZERO
    return with_sign(sa, mk_exp(add(A, logmag(c))))


def sub(a: T, b: T) -> T:
    return add(a, neg(b))


def tower(k: int, x: T) -> T:
    """tower_k(x) = exp^k(x)."""
    v = x
    for _ in range(k):
        v = mk_exp(v)
    return v


def to_float(a: T) -> Optional[float]:
    """A float, for display only.  `None` when the value has none — the normal case here, and not
    a failure: having no float is the whole reason this module exists."""
    if a.signs:
        return None
    try:
        return float(a.m)
    except (OverflowError, ValueError):
        return None


def required_height(v: T, x: T, cap: int = 24) -> Optional[int]:
    """Least k with tower_k(x) ≥ -log v, i.e. how many logs take -log v down to x.

    This is the STRICT reading of the conjecture's floor `exp(-tower_k x) ≤ gap`, with no constant.
    `None` when v ≤ 0 — the germ is not positive here, so no floor is claimed about it."""
    if sign(v) <= 0:
        return None
    h = neg(logmag(v))
    k = 0
    while k < cap:
        if cmp_signed(h, x) <= 0:
            return k
        h = logmag(h)
        k += 1
    return cap


def floor_excess(v: T, x: T, k: int) -> Optional[T]:
    """`(-log v) - tower_k(x)`, the amount by which the height-`k` floor is missed.

    DecayFloor is stated with a constant — `t(x) ≥ exp(-(C + tower_k x))` — so a germ can fail the
    STRICT height-`k` test and still satisfy the floor, if the excess stays BOUNDED as x grows.
    Two ray points decide that, and the two metrics differ by exactly one height on a family the
    strict test alone would have mis-scored.  Returns None if the germ is not positive."""
    if sign(v) <= 0:
        return None
    return sub(neg(logmag(v)), tower(k, x))


# ── self-test: the instrument must be shown capable of both verdicts ─────────────────────────────

def _selftest() -> bool:
    mp.dps = 60
    ok = True

    def chk(label, cond, extra=""):
        nonlocal ok
        ok &= bool(cond)
        print(f"  {'PASS' if cond else 'FAIL'}  {label} {extra}")

    x = num(mpf(10) ** 30)
    ex = mk_exp(x)
    chk("exp/log round trip at x=1e30", cmp_signed(logmag(ex), x) == 0)
    chk("exp^4(1e30) is representable", mk_exp(mk_exp(mk_exp(ex))).signs == (1, 1, 1, 1))
    tiny = mk_exp(neg(mk_exp(mk_exp(x))))           # exp(-exp(exp(x)))
    chk("height of exp(-exp(exp x)) is 2", required_height(tiny, x) == 2)
    chk("height of exp(-exp x) is 1", required_height(mk_exp(neg(mk_exp(x))), x) == 1)
    chk("height of exp(-x) is 0", required_height(mk_exp(neg(x)), x) == 0)
    chk("height of exp(-2x) is 1 (strict)", required_height(mk_exp(neg(add(x, x))), x) == 1)

    # The two readings of the floor, and the family that separates them.  `exp(-exp(x) - 5)` fails
    # the STRICT height-1 test — `-log v = exp(x) + 5 > exp(x)` at every x — and satisfies
    # DecayFloor's `exp(-(C + tower_k x))` at height 1 with C = 5.  floor_excess sees the constant.
    xs = num(10)
    off = mk_exp(neg(add(mk_exp(xs), num(5))))
    chk("exp(-exp x - 5) is strict height 2 at x=10", required_height(off, xs) == 2)
    e1 = floor_excess(off, xs, 1)
    chk("…and its height-1 excess is the constant 5", is_ord(e1) and abs(e1.m - 5) < 1e-20)
    off2 = mk_exp(neg(add(mk_exp(num(20)), num(5))))
    chk("…excess still 5 at x=20 (bounded ⇒ DecayFloor height 1)",
        abs(floor_excess(off2, num(20), 1).m - 5) < 1e-20)
    # A factor, unlike an offset, is NOT absorbed by the floor: exp(-2·exp x) is height 2 in both
    # readings, because the excess exp(x) grows.  The two controls bracket the distinction.
    two_e = mk_exp(neg(add(mk_exp(xs), mk_exp(xs))))
    chk("exp(-2 exp x) is height 2 in both readings",
        required_height(two_e, xs) == 2
        and cmp_signed(floor_excess(two_e, xs, 1), mk_exp(num(9))) > 0)
    # Far out on the ray an additive constant is BELOW the working precision beside exp(x), so the
    # tail reading is automatically the constant-tolerant one.  That is the metric DecayFloor
    # states, and reading at x ≤ 2.8 (2026-09-05, depth 4) is where the two part company.
    far = num(mpf(10) ** 30)
    chk("at x=1e30 the +5 offset is invisible, so the tail reads height 1",
        required_height(mk_exp(neg(add(mk_exp(far), num(5)))), far) == 1)

    chk("exact meeting reads as exactly 0", is_zero(sub(mk_exp(ex), mk_exp(ex))))

    # 1 - exp(tiny) must not be a catastrophic subtraction.
    eps = mk_exp(neg(ex))
    chk("1 - exp(exp(-exp x)) = -exp(-exp x)", cmp_signed(sub(ONE, mk_exp(eps)), neg(eps)) == 0)

    # KNOWN BLIND SPOT, asserted rather than hoped for: `E - exp(-E)` is E in any finite relative
    # precision, so `exp(E) - exp(E - exp(-E))`, whose true value is 1, reads as an exact meeting.
    # The absorption counter is what makes that visible instead of silent.
    reset_absorbed()
    z = sub(mk_exp(ex), mk_exp(sub(ex, eps)))
    chk("absorbed near-meeting reads 0 AND flags absorption", is_zero(z) and absorbed() > 0)

    chk("ordinary add", abs(add(num("1.25"), num("0.75")).m - mpf("2.0")) < mpf(10) ** -50)
    chk("log0 of a negative is 0", is_zero(log0(num(-3))))

    # NEGATIVE CONTROL: the guard must FIRE on a real cancellation, not pass it silently.
    fired = False
    try:
        sub(num(mpf(1)), num(1 + mpf(2) ** (-(mp.prec - 10))))
    except Unresolved:
        fired = True
    chk("relative cancellation guard FIRES", fired)
    quiet = True
    try:
        sub(num(mpf(1)), num("0.5"))
    except Unresolved:
        quiet = False
    chk("…and stays quiet on an honest difference", quiet)
    chk("exp(-exp x) is not rejected as underflow (the defect-3 regression)",
        sign(mk_exp(neg(mk_exp(x)))) > 0)
    return ok


if __name__ == "__main__":
    import sys

    print("=== tower arithmetic self-test ===")
    sys.exit(0 if _selftest() else 1)
