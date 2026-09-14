#!/usr/bin/env python3
"""tools/float_bridge/measure.py — MEASURE the float-bridge axioms against the floats they are about.

WHY THIS EXISTS (2026-09-14). AXIOM_MANIFEST.md classes 22 axioms "float-bridge": claims about IEEE floats
that no Mathlib witness can discharge, "validated by measurement". Nothing measured them. On 2026-09-13
`Certcom.real_tanh_rounds` — `|realToR (stdI1 leanPrims .tanh a) − tanh (realToR a)| ≤ u` with u = 2⁻⁵³ — was
checked against a 200-bit tanh on [-30, 30] and is FALSE: the runtime composite exceeds u at 2 318 of 60 001
points (max 1.48u). Two grounded certificates rested on it with every gate green. A disclosed axiom that nobody
measures is a claim, not trust.

WHAT IT DOES. For every float-bridge axiom in AXIOM_MANIFEST.md the registry (registry.json) says how the
harness can read it, and the harness enforces that the registry and the corpus agree:

  * `measured` — a bound on the value `leanPrims` computes. Each input `a` is a finite double, so
    `realToR a` is its exact value `x`. The float side is computed EXACTLY as `leanPrims` does: the same libm
    (glibc, called through ctypes — the functions `Float.exp` & co. link), IEEE double arithmetic, the
    runtime's composite bodies, and `floatCopySign`'s bit definition. The real side is mpmath at 256 bits.
    Where the statement has free parameters (`R`, `hi`, `lo`), the harness uses the instantiation that makes
    the bound TIGHTEST, because a ∀ over them is false if it fails at any one (`c` is the statement's
    constant: `u + u` is 2):
      exp:   c·u·exp hi, hi ≥ x                    → c·u·exp x
      log:   c·u·(|log lo| + |log hi|), lo ≤ x ≤ hi → c·u·|log x| (lo or hi at 1)     (log10 likewise)
      sqrt:  u·sqrt hi, hi ≥ x                     → u·sqrt x
      sinh, cosh:  c·u·cosh R, R ≥ |x|             → c·u·cosh x
      tan:   c·u·tan R, |x| ≤ R < π/2              → c·u·|tan x|, and only |x| < π/2 is in the domain
      asin, acos:  a constant, |x| ≤ R < 1         → only |x| < 1 is in the domain
    An input outside a statement's hypotheses is VACUOUS (not counted). Since 2026-09-14 some hypotheses are
    about the RESULT: `(stdI1 leanPrims .f a).isFinite = true` (sinh, cosh, exp) makes an input with a
    non-finite result vacuous, and exp's `dblMin ≤ exp (realToR a)` one whose exact result is below DBL_MIN.
    Where no hypothesis excludes it, a non-finite float result is UNMEASURABLE: `realToR` of a non-finite
    float has no real value, so nothing can be said, and the count is reported rather than hidden.
    Non-finite INPUTS are likewise outside what can be measured, whatever the statement quantifies over.
  * `existential-eps` — `|… − f x| ≤ real_f_eps` for an opaque constant: satisfiable iff the error is
    bounded; the harness reports the supremum it found.
  * `bridge` — `real_fpbridge : FPBridgeFinite realToR`: `+`, `−`, `×` round within `u` relatively (`RoundsW`)
    wherever the float result is finite and, for `×`, the exact product is 0 or at least DBL_MIN in magnitude;
    negation of a finite float is exact. `bridge-unconditional` is `FPBridge`, every pair, as `real_fpbridge`
    stated it until 2026-09-14: measured only as a control that must fail.
  * `rounding` — `real_round_bounds`: round-to-nearest of a real `x` with `x = 0` or `DBL_MIN ≤ |x|`, and
    `|x| ≤ DBL_MAX`, lands within `u·|x|` (floatOfR read as IEEE round-to-nearest-even, which is what its
    docstring says it models). `rounding-unconditional` is the statement before 2026-09-14, a control.
  * `finite-of-range` — `real_fpfinite : FPFiniteOfRange realToR` (added 2026-09-14): for finite doubles `a`, `b`, the
    float `a + b`, `a − b`, `a × b` is finite whenever the EXACT real result is at most DBL_MAX in magnitude, and `−a`
    is finite. An operation whose exact result is above DBL_MAX is vacuous. Round-to-nearest-even rounds the overflow
    tie DBL_MAX + 2^970 UP to infinity, so two controls must fail: `finite-of-range-tie-inclusive` (the range widened
    to `≤ DBL_MAX + 2^970`, which must fail at the tie and nowhere else) and `finite-of-range-unconditional` (no range).
  * `round-finite` — `real_round_finite` (added 2026-09-14): round-to-nearest-even of a real `x` with `|x| ≤ DBL_MAX` is
    finite. Controls `round-finite-tie-inclusive` (must fail at the tie and nowhere else) and
    `round-finite-unconditional`. A finiteness row pins the largest `|exact result| / DBL_MAX` it examined, so an input
    set that stopped reaching the boundary moves a pin. It may also carry `min_examined`, a floor above MIN_EXAMINED.
  * `declaration` — a function symbol or an opaque constant, not a proposition.

INPUTS, deterministic: a dense grid over each function's interesting range; log-spaced tiny |x| down to the
denormals; consecutive doubles on both sides of every branch threshold and edge (identity cut-offs, the
exp-overflow switch, the subnormal onset, ±1 for asin/acos, π/2 for tan); ±large magnitudes; random finite
bit patterns; then a local search around the 25 worst points found, two rounds. Since 2026-09-14 also the
adversarial sets that found the restated rows' failures: inputs whose result sits just above a power of two
(where a misrounding costs the most relative error: exp found 7 of them over u), exp's whole subnormal range,
sinh and cosh's large branch densely, log10 on [0.5, 2) and at 10^(±2^j), tan at atan(2^k) and geometrically
close to π/2; products straddling DBL_MIN (some rounding up to it, and the exact midpoint below it), sums
landing either side of DBL_MIN, sums and products near overflow, subnormal operands; reals straddling DBL_MIN
and DBL_MAX, zero, and ties on the subnormal grid.

VERDICTS. Every `measured` axiom has an `expect`: `holds` fails on any violation; `violated` is an
ACKNOWLEDGED failure whose numbers are pinned, and the run fails if they change or if a new failure appears.
Each measured axiom also pins its examined count, maximum error and where it occurs, so a change in the
libm, the runtime body or the input set cannot pass silently (`--record` re-pins, as a deliberate act).
The run also fails if:
  * a positive CONTROL — an axiom stated deliberately too tight — does not come out violated. Every statement
    restated on 2026-09-14 is kept as a control in its old form, so the run keeps showing the old one fails;
  * any measured axiom examined fewer than MIN_EXAMINED inputs (a harness that measured nothing passes), or fewer
    than its row's own `min_examined`;
  * a control marked `only_at_tie` fails anywhere other than at the overflow tie DBL_MAX + 2^970, which would mean
    something other than the range decides it;
  * the registry and AXIOM_MANIFEST.md's float-bridge rows are not the same set of names;
  * an axiom's statement in the Lean source is not the one registered, OR the registry's reading of it (kind,
    function, domain, bound, constant) is not what the statement's own text determines. `derive_reading`
    derives that reading mechanically from a closed table of statement shapes (`READINGS`); a statement no
    entry matches is UNREADABLE and fails, never guessed. `FPBridge`'s four fields and `RoundsW`, which the
    bridge row's reading depends on, are fingerprinted the same way;
  * a sample of the harness's float values differs from Lean's own `#eval` of `stdI1 leanPrims` and
    `Float` arithmetic, bit for bit — so the harness cannot be measuring a different function.
Exit 0 all green, 1 a failure, 2 UNAVAILABLE (mpmath or Lean missing, or a different platform) — never a pass.

LOCAL ONLY, NOT CI. The pinned numbers are properties of THIS libm (glibc 2.39, aarch64): another glibc or
architecture rounds differently at some points, and the acknowledged counts would move. The registry pins the
platform and the harness reports UNAVAILABLE elsewhere rather than failing or passing. machlib's CI runner is
ubuntu-latest on x86-64, and it has no mpmath. It runs in tools/check_all.sh.

USAGE (from foundations/):
    python3 tools/float_bridge/measure.py              # the gate
    python3 tools/float_bridge/measure.py --self-test  # the verdict logic on doctored data (no Lean)
    python3 tools/float_bridge/measure.py --explore [--only NAME]   # measure and print, verify nothing
    python3 tools/float_bridge/measure.py --record     # re-pin the measured numbers (then review the diff)
"""
from __future__ import annotations

import argparse
import ctypes
import functools
import ctypes.util
import json
import math
import multiprocessing
import os
import pathlib
import platform
import random
import re
import struct
import subprocess
import sys
import tempfile
from fractions import Fraction

HERE = pathlib.Path(__file__).resolve().parent
FOUNDATIONS = HERE.parent.parent
REGISTRY = HERE / "registry.json"
MANIFEST = FOUNDATIONS / "AXIOM_MANIFEST.md"
PREC = 256
MIN_EXAMINED = 10_000
TOP_K = 25

DBL_MAX = sys.float_info.max
DBL_MIN = sys.float_info.min
DBL_MIN_F = Fraction(DBL_MIN)
DBL_MAX_F = Fraction(DBL_MAX)
#: Domains whose hypotheses are about the result, checked after the float is computed.
RESULT_DOMAINS = ("finite_result", "finite_normal_exp")
DENORM_MIN = 5e-324
HALF_PI_DOUBLE = 1.5707963267948966
#: DBL_MAX + 2^970, the midpoint between DBL_MAX and 2^1024. Round-to-nearest-even rounds it UP, to infinity: it is the
#: smallest exact result that overflows, so a finiteness range that includes it is false there and nowhere else.
OVERFLOW_TIE_F = DBL_MAX_F + Fraction(2) ** 970
#: The finiteness kinds and the range each puts on the exact result (`None`: no range at all).
FINITE_RANGES = {"finite-of-range": DBL_MAX_F, "finite-of-range-tie-inclusive": OVERFLOW_TIE_F,
                 "finite-of-range-unconditional": None, "round-finite": DBL_MAX_F,
                 "round-finite-tie-inclusive": OVERFLOW_TIE_F, "round-finite-unconditional": None}


# ── floats, bit for bit ──────────────────────────────────────────────────────────────────────────

def bits(x: float) -> int:
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def from_bits(b: int) -> float:
    return struct.unpack("<d", struct.pack("<Q", b & 0xFFFFFFFFFFFFFFFF))[0]


def hex_bits(x: float) -> str:
    return f"{bits(x):016x}"


_LIBM = ctypes.CDLL(ctypes.util.find_library("m") or "libm.so.6")


def _c1(name: str):
    f = getattr(_LIBM, name)
    f.argtypes, f.restype = [ctypes.c_double], ctypes.c_double
    return f


EXP, LOG, LOG10, SIN, COS, TAN = (_c1(n) for n in ("exp", "log", "log10", "sin", "cos", "tan"))
ASIN, ACOS, ATAN, SQRT, FABS = (_c1(n) for n in ("asin", "acos", "atan", "sqrt", "fabs"))


def lean_copysign(x: float, y: float) -> float:
    """`floatCopySign` (EMLToCRuntime.lean): the bits of `x` with the sign bit of `y`."""
    return from_bits((bits(x) & 0x7FFFFFFFFFFFFFFF) | (bits(y) & 0x8000000000000000))


#: `stdI1 leanPrims .tanh`'s small-argument threshold. The Lean cross-check below holds this copy to Lean.
TANH_X_MAX = 1.3538603431225864e-8
#: `stdI1 leanPrims .sinh`'s (forge's `MG_SINH_X_MAX`, 2026-09-14), held to Lean the same way.
SINH_X_MAX = 2.149119332890821e-8


def lean_tanh(x: float) -> float:
    a = FABS(x)
    if a <= TANH_X_MAX:
        return x
    t = EXP(-2.0 * a)
    return lean_copysign((1.0 - t) / (1.0 + t), x)


def lean_sinh(x: float) -> float:
    a = FABS(x)
    if a <= SINH_X_MAX:
        return x
    if a > 709.78:
        w = EXP(0.5 * a)
        r = (0.5 * w) * w
    else:
        r = (EXP(a) - EXP(-a)) * 0.5
    return lean_copysign(r, x)


def lean_cosh(x: float) -> float:
    a = FABS(x)
    if a > 709.78:
        w = EXP(0.5 * a)
        return (0.5 * w) * w
    return (EXP(a) + EXP(-a)) * 0.5


#: `stdI1 leanPrims .<f>` in Python, keyed by the `Trans1` constructor.
FLOAT_FUNCS = {
    "tanh": lean_tanh, "sinh": lean_sinh, "cosh": lean_cosh, "exp": EXP, "ln": LOG, "log10": LOG10,
    "sin": SIN, "cos": COS, "tan": TAN, "asin": ASIN, "acos": ACOS, "atan": ATAN, "sqrt": SQRT, "abs": FABS,
}


def _mp():
    import mpmath
    mpmath.mp.prec = PREC
    return mpmath


def reference(name: str):
    mp = _mp()
    return {"tanh": mp.tanh, "sinh": mp.sinh, "cosh": mp.cosh, "exp": mp.exp, "ln": mp.log, "log10": mp.log10,
            "sin": mp.sin, "cos": mp.cos, "tan": mp.tan, "asin": mp.asin, "acos": mp.acos, "atan": mp.atan,
            "sqrt": mp.sqrt, "abs": abs}[name]


# ── domains and bounds (the tightest instantiation of each statement; see the module docstring) ──

def in_domain(domain: str, x: float) -> bool:
    if not math.isfinite(x):
        return False
    if domain in ("finite",) + RESULT_DOMAINS:
        return True
    if domain == "positive":
        return x > 0
    if domain == "nonneg":
        return x >= 0
    if domain == "open_unit":
        return abs(x) < 1
    if domain == "tan_open":
        mp = _mp()
        return mp.mpf(abs(x)) < mp.pi / 2
    raise ValueError(f"unknown domain {domain!r}")


def bound_of(spec: dict, X):
    """The bound at exact input X, or None for an existential eps."""
    mp = _mp()
    u = mp.mpf(2) ** -53
    kind = spec["bound"]
    if kind == "sup":
        return None
    if kind == "c_u":
        return mp.mpf(spec["c"]) * u
    if kind == "u_exp_x":
        return u * mp.exp(X)
    if kind == "u_abs_log_x":
        return u * abs(mp.log(X))
    if kind == "u_abs_log10_x":
        return u * abs(mp.log10(X))
    if kind == "u_sqrt_x":
        return u * mp.sqrt(X)
    if kind == "c_u_sqrt_x":
        return mp.mpf(spec["c"]) * u * mp.sqrt(X)
    if kind == "u_pi_half":
        return u * mp.pi / 2
    if kind == "u_pi":
        return u * mp.pi
    if kind == "u_abs_tan_x":
        return u * abs(mp.tan(X))
    if kind == "u_cosh_x":
        return u * mp.cosh(X)
    if kind == "c_u_cosh_x":
        return mp.mpf(spec["c"]) * u * mp.cosh(X)
    if kind == "c_u_exp_x":
        return mp.mpf(spec["c"]) * u * mp.exp(X)
    if kind == "c_u_abs_log10_x":
        return mp.mpf(spec["c"]) * u * abs(mp.log10(X))
    if kind == "c_u_abs_tan_x":
        return mp.mpf(spec["c"]) * u * abs(mp.tan(X))
    raise ValueError(f"unknown bound {kind!r}")


# ── inputs ───────────────────────────────────────────────────────────────────────────────────────

def steps(lo: float, hi: float, step: float) -> list[float]:
    n = int(round((hi - lo) / step))
    return [lo + i * step for i in range(n + 1)]


def around(x: float, k: int) -> list[float]:
    out, lo, hi = [x], x, x
    for _ in range(k):
        lo, hi = math.nextafter(lo, -math.inf), math.nextafter(hi, math.inf)
        out += [lo, hi]
    return out


def logspace(lo: float, hi: float, n: int, signed: bool) -> list[float]:
    a, b = math.log(lo), math.log(hi)
    mags = [math.exp(a + (b - a) * i / (n - 1)) for i in range(n)]
    mags = [min(max(m, lo), hi) for m in mags]
    return mags + ([-m for m in mags] if signed else [])


def random_bits(n: int, seed: int, positive: bool = False) -> list[float]:
    rng, out = random.Random(seed), []
    while len(out) < n:
        x = from_bits(rng.getrandbits(64))
        if math.isfinite(x):
            out.append(abs(x) if positive else x)
    return out


def uniform(lo: float, hi: float, n: int, seed: int) -> list[float]:
    rng = random.Random(seed)
    return [rng.uniform(lo, hi) for _ in range(n)]


def denormals(k: int) -> list[float]:
    return [from_bits(i) for i in range(1, k + 1)] + around(DBL_MIN, k)


SPECIALS = [0.0, -0.0, 1.0, -1.0, DBL_MIN, -DBL_MIN, DENORM_MIN, -DENORM_MIN, DBL_MAX, -DBL_MAX,
            math.inf, -math.inf, math.nan]


def inputs_for(function: str) -> list[float]:
    """The deterministic input set for a `measured`/`existential-eps` function."""
    return list(_inputs_for(function))


@functools.lru_cache(maxsize=None)
def _inputs_for(function: str) -> tuple:
    mp = _mp()
    if function == "tanh":
        xs = (steps(-30, 30, 1e-3) + steps(-1, 1, 1e-5) + logspace(DENORM_MIN, 1.0, 4000, True)
              + around(TANH_X_MAX, 2000) + around(-TANH_X_MAX, 2000) + around(18.715, 1000) + around(19.0615, 1000)
              + around(20.0, 500) + logspace(1.0, DBL_MAX, 2000, True) + denormals(1000)
              + random_bits(50_000, 11) + uniform(-40, 40, 100_000, 12))
    elif function in ("sinh", "cosh"):
        xs = (steps(-712, 712, 0.01) + steps(-30, 30, 1e-3) + logspace(DENORM_MIN, 1.0, 4000, True)
              + around(709.78, 2000) + around(-709.78, 2000) + around(SINH_X_MAX, 2000) + around(-SINH_X_MAX, 2000)
              + around(710.4758, 500) + around(-710.4758, 500)
              + random_bits(50_000, 21) + uniform(-711, 711, 100_000, 22) + denormals(500))
        # the large branch densely, and results just above a power of two
        xs += (uniform(709.78, 710.4758600739439, 100_000, 23) + logspace(SINH_X_MAX, 709.78, 100_000, True)
               + uniform(19, 21, 20_000, 24))
        for k in range(-25, 1024):
            xs += around(float(mp.asinh(mp.mpf(2) ** k)), 20)
        for k in range(1, 1024):
            xs += around(float(mp.acosh(mp.mpf(2) ** k)), 20)
    elif function == "exp":
        xs = (steps(-750, 710, 0.01) + around(709.782712893384, 1000) + around(-708.3964185322641, 2000)
              + around(-744.4400719213812, 1000) + around(-745.1332191019412, 1000) + around(0.0, 1000)
              + logspace(DENORM_MIN, 1.0, 4000, True) + random_bits(50_000, 31) + uniform(-750, 710, 100_000, 32))
        rng = random.Random(33)
        for k in range(-1074, 1024):   # results just above 2^k
            x0 = float(mp.log(mp.mpf(2) ** k))
            xs += around(x0, 40) + [x0 + rng.uniform(0, 0.02) for _ in range(60)]
        xs += uniform(-708.4, 709.78, 200_000, 34) + uniform(-745.2, -708.39, 100_000, 35)
    elif function in ("ln", "log10"):
        xs = (logspace(DENORM_MIN, DBL_MAX, 200_000, False) + around(1.0, 5000) + denormals(2000)
              + [y for k in range(-20, 23) for y in around(10.0 ** k, 50)]
              + [y for k in range(-1074, 1024, 7) for y in around(math.ldexp(1.0, k), 5)]
              + random_bits(50_000, 41, positive=True) + uniform(0.0, 10.0, 100_000, 42))
        if function == "log10":
            xs += uniform(0.5, 2.0, 200_000, 43) + around(1.0, 20_000)
            for j in range(-52, 9):    # results just above 2^j in magnitude
                for sgn in (1, -1):
                    x0 = float(mp.mpf(10) ** (sgn * mp.mpf(2) ** j))
                    if 0 < x0 < math.inf:
                        xs += around(x0, 100)
    elif function == "sqrt":
        xs = (logspace(DENORM_MIN, DBL_MAX, 200_000, False) + denormals(2000)
              + [y for k in range(-537, 512, 3) for y in around(math.ldexp(1.0, 2 * k), 20)]
              + random_bits(50_000, 51, positive=True) + uniform(0.0, 100.0, 100_000, 52))
    elif function in ("asin", "acos"):
        xs = (steps(-1, 1, 1e-5) + around(1.0, 5000) + around(-1.0, 5000) + logspace(DENORM_MIN, 1.0, 20_000, True)
              + uniform(-1, 1, 100_000, 61) + random_bits(20_000, 62))
    elif function == "tan":
        xs = (steps(-HALF_PI_DOUBLE, HALF_PI_DOUBLE, 1e-5) + around(HALF_PI_DOUBLE, 5000) + around(-HALF_PI_DOUBLE, 5000)
              + logspace(DENORM_MIN, 1.0, 20_000, True) + uniform(-1.5707, 1.5707, 100_000, 71)
              + around(math.pi / 4, 1000))
        rng = random.Random(72)
        for k in range(-30, 54):       # results just above 2^k
            x0 = float(mp.atan(mp.mpf(2) ** k))
            xs += around(x0, 100) + around(-x0, 20)
        xs += [HALF_PI_DOUBLE * (1 - 10.0 ** rng.uniform(-16, 0)) for _ in range(50_000)]
    elif function in ("sin", "cos", "atan"):
        xs = (steps(-100, 100, 1e-3) + logspace(DENORM_MIN, DBL_MAX, 20_000, True) + random_bits(50_000, 81)
              + uniform(-1e6, 1e6, 50_000, 82) + [y for k in range(1, 101) for y in around(k * math.pi, 50)])
    elif function == "abs":
        xs = random_bits(20_000, 91) + denormals(500)
    else:
        raise ValueError(function)
    xs += SPECIALS
    seen, out = set(), []
    for x in xs:
        b = bits(x)
        if b not in seen:
            seen.add(b)
            out.append(x)
    return tuple(out)


@functools.lru_cache(maxsize=None)
def _pairs_for_bridge() -> tuple:
    rng, out = random.Random(101), []
    rand = random_bits(100_000, 102)
    out += list(zip(rand[::2], rand[1::2]))
    for _ in range(20_000):  # products landing in the subnormal range
        ea = rng.randint(-600, -400)
        eb = rng.randint(-1130 - ea, -1000 - ea)
        out.append((math.ldexp(rng.uniform(0.5, 1.0), ea) * rng.choice((1, -1)), math.ldexp(rng.uniform(0.5, 1.0), eb)))
    for _ in range(10_000):  # near-cancelling sums
        a = math.ldexp(rng.uniform(0.5, 1.0), rng.randint(-1070, 1020))
        out.append((a, -math.nextafter(a, math.inf)))
        out.append((a, -a * (1 + rng.uniform(-1e-9, 1e-9))))
    for _ in range(5_000):  # exact small integers and halves
        out.append((rng.randint(-1000, 1000) / 2, rng.randint(-1000, 1000) / 4))
    for _ in range(40_000):  # exact products straddling DBL_MIN, some of which round UP to it
        a = math.ldexp(rng.uniform(1.0, 2.0), rng.randint(-1000, -30)) * rng.choice((1, -1))
        out += [(a, b) for b in around(float(DBL_MIN_F / Fraction(a)), 3)]
    for _ in range(20_000):  # sums and differences landing just below or above DBL_MIN
        a = math.ldexp(rng.uniform(1.0, 2.0), -1022)
        out.append((a, -math.ldexp(rng.random(), rng.randint(-1074, -1022))))
        out.append((a, math.ldexp(rng.random(), rng.randint(-1074, -1022))))
    for _ in range(40_000):  # sums and products near overflow
        a = DBL_MAX * (1 - rng.random() * 1e-15)
        out.append((a, a * rng.random() * 2e-15))
        out.append((a, -a * rng.random()))
        out.append((math.ldexp(rng.uniform(1.0, 2.0), rng.randint(500, 1023)),
                    math.ldexp(rng.uniform(1.0, 2.0), rng.randint(0, 523))))
        c = math.sqrt(DBL_MAX) * (1 + rng.uniform(-1e-15, 1e-15))
        out.append((c, c))
    for _ in range(20_000):  # subnormal operands, with normal and with subnormal partners
        out.append((math.ldexp(rng.random(), -1074 + rng.randint(0, 51)), math.ldexp(rng.uniform(1.0, 2.0), rng.randint(0, 1000))))
        out.append((math.ldexp(rng.random(), -1074 + rng.randint(0, 51)), math.ldexp(rng.random(), -1074 + rng.randint(0, 51))))
    m = (1 << 53) - 1  # (2^53 - 1)·2^-1075 exactly: the midpoint below DBL_MIN, which rounds UP to it
    out.append((math.ldexp(6361.0, -500), math.ldexp(float(m // 6361), -575)))
    return tuple(out)


def pairs_for_bridge() -> list[tuple[float, float]]:
    return list(_pairs_for_bridge())


@functools.lru_cache(maxsize=None)
def _pairs_for_finite() -> tuple:
    """The bridge's pairs, plus the pairs where a finiteness range decides the verdict: exact sums, differences and
    products AT the overflow tie (they round up to infinity), between DBL_MAX and the tie (they round down to DBL_MAX),
    and exactly at DBL_MAX. Every operand below is exactly representable, so each exact result is what its comment says."""
    out = list(_pairs_for_bridge())
    two969, two970, two971 = math.ldexp(1.0, 969), math.ldexp(1.0, 970), math.ldexp(1.0, 971)
    below_max = math.nextafter(DBL_MAX, 0.0)
    for s in (1.0, -1.0):
        for i in range(1000):
            step = math.ldexp(float(i), 971)
            out += [(s * (DBL_MAX - step), s * (two970 + step)),     # a + b is the tie
                    (s * (DBL_MAX - step), -s * (two970 + step)),    # a − b is the tie
                    (s * (DBL_MAX - step), s * (two969 + step)),     # a + b is DBL_MAX + 2^969, below the tie
                    (s * (below_max - step), s * (two971 + step))]   # a + b is DBL_MAX
        for k in range(-26, 997):      # (2^27 − 1)(2^27 + 1) = 2^54 − 1, so a · b is the tie
            out.append((s * math.ldexp(134217727.0, k), math.ldexp(134217729.0, 970 - k)))
        for k in range(0, 1000):       # 5 · 7205759403792793 = 2^55 − 3, so a · b is DBL_MAX + 2^969
            out.append((s * math.ldexp(5.0, k), math.ldexp(7205759403792793.0, 969 - k)))
        for j in range(-50, 972):      # (2^53 − 1) · 2^971 is DBL_MAX
            out.append((s * math.ldexp(float(2 ** 53 - 1), j), math.ldexp(1.0, 971 - j)))
    return tuple(out)


def reals_for_rounding() -> list[tuple[int, int]]:
    """(mantissa, exponent) pairs: x = m · 2^e, exact, 256-bit mantissas."""
    rng, out = random.Random(111), []
    for _ in range(100_000):
        out.append((rng.getrandbits(256) | 1 << 255, rng.randint(-1100 - 256, 1020 - 256)))
    for _ in range(20_000):  # the subnormal range
        out.append((rng.getrandbits(256) | 1 << 255, rng.randint(-1080 - 256, -1020 - 256)))
    for _ in range(20_000):  # a double plus a sub-ulp nudge
        d = rng.getrandbits(52) | 1 << 52
        e = rng.randint(-1074, 971)
        out.append((d << 204 | rng.getrandbits(204), e - 204))
    for _ in range(50_000):  # straddling DBL_MIN within 2^-40 relative
        out.append(((1 << 256) + rng.getrandbits(216) - (1 << 215), -1022 - 256))
    top = ((1 << 53) - 1) << 203
    for _ in range(50_000):  # straddling DBL_MAX: some round to it, some overflow
        out.append((top + rng.getrandbits(204) * rng.choice((1, -1)), 971 - 203))
    out += [(0, 0), ((1 << 53) - 1, -1075)]  # zero, and the midpoint below DBL_MIN
    for _ in range(20_000):  # exact ties on the subnormal grid
        out.append((2 * rng.randint(1, (1 << 52) - 1) + 1, -1075))
    return out


def reals_for_round_finite() -> list[tuple[int, int]]:
    """`reals_for_rounding` with both signs, plus reals AT the overflow tie, just below it (they round to DBL_MAX), just
    above it (they overflow), between DBL_MAX and the tie, and at and just below DBL_MAX."""
    out = reals_for_rounding()
    out += [(-m, e) for m, e in out]
    tie, top = (1 << 54) - 1, (1 << 53) - 1      # tie · 2^970 and top · 2^971 = DBL_MAX
    for s in (1, -1):
        out += [(s * tie, 970), (s * top, 971)]
        for i in range(1, 2001):
            out += [(s * ((tie << 100) - i), 870), (s * ((tie << 100) + i), 870),
                    (s * ((top << 100) + i), 871), (s * ((top << 100) - i), 871)]
    return out


# ── measuring ────────────────────────────────────────────────────────────────────────────────────

def _measure_chunk(args) -> dict:
    spec, xs = args
    mp = _mp()
    fn, ref, domain = FLOAT_FUNCS[spec["function"]], reference(spec["function"]), spec["domain"]
    res = {"examined": 0, "vacuous": 0, "unmeasurable": 0, "violations": 0, "worst": []}
    worst = []
    dbl_min = mp.mpf(2) ** -1022
    for x in xs:
        if not in_domain(domain, x):
            res["vacuous"] += 1
            continue
        y = fn(x)
        if domain in RESULT_DOMAINS and (not math.isfinite(y)
                                         or (domain == "finite_normal_exp" and mp.exp(mp.mpf(x)) < dbl_min)):
            res["vacuous"] += 1
            continue
        if not math.isfinite(y):
            res["unmeasurable"] += 1
            continue
        X = mp.mpf(x)
        err = abs(mp.mpf(y) - ref(X))
        b = bound_of(spec, X)
        res["examined"] += 1
        if b is None:
            score = float(err)
        else:
            if err > b:
                res["violations"] += 1
            score = math.inf if (b == 0 and err > 0) else (0.0 if b == 0 else float(err / b))
        worst.append((score, bits(x)))
        if len(worst) > 4 * TOP_K:
            worst.sort(key=lambda t: (-t[0], t[1]))
            del worst[TOP_K:]
    worst.sort(key=lambda t: (-t[0], t[1]))
    res["worst"] = worst[:TOP_K]
    return res


def _merge(a: dict, b: dict) -> dict:
    out = {k: a[k] + b[k] for k in ("examined", "vacuous", "unmeasurable", "violations")}
    w = sorted(a["worst"] + b["worst"], key=lambda t: (-t[0], t[1]))
    out["worst"] = w[:TOP_K]
    return out


def _neighbours(x: float) -> list[float]:
    out = around(x, 300)
    if x != 0 and math.isfinite(x):
        out += [x * (1 + i * 1e-12) for i in range(-150, 151)]
    return out


def measure_function_axiom(spec: dict, pool, xs: list[float] | None = None) -> dict:
    xs = inputs_for(spec["function"]) if xs is None else xs
    chunks = [xs[i:i + 20_000] for i in range(0, len(xs), 20_000)]
    total = {"examined": 0, "vacuous": 0, "unmeasurable": 0, "violations": 0, "worst": []}
    for part in pool.map(_measure_chunk, [(spec, c) for c in chunks]):
        total = _merge(total, part)
    measured = {bits(x) for x in xs}
    for _ in range(2):  # local search around the worst points
        extra = []
        for _, b in total["worst"]:
            for y in _neighbours(from_bits(b)):
                if bits(y) not in measured:
                    measured.add(bits(y))
                    extra.append(y)
        if not extra:
            break
        for part in pool.map(_measure_chunk, [(spec, extra[i:i + 20_000]) for i in range(0, len(extra), 20_000)]):
            total = _merge(total, part)
    total["inputs"] = len(measured)
    return total


SIGN_BIT = 0x8000000000000000


def ieee_neg(v: float) -> float:
    """Lean's `-x` on `Float`: IEEE negation, which flips the sign bit and nothing else."""
    return -v


def _bridge_chunk(ps, neg=ieee_neg, conditional=True) -> dict:
    """`FPBridgeFinite`'s fields over pairs (`conditional`), or `FPBridge`'s, every pair. `neg` is a parameter so
    --self-test can hand it a negation that is not IEEE's and require both negation checks to fire."""
    res = {"examined": 0, "vacuous": 0, "unmeasurable": 0, "violations": 0, "worst": [], "neg_inexact": 0,
           "neg_not_bitflip": 0}
    worst = []
    two53 = 1 << 53
    for a, b in ps:
        fa, fb = Fraction(a), Fraction(b)
        n = neg(a)
        if bits(n) != bits(a) ^ SIGN_BIT:
            res["neg_not_bitflip"] += 1   # the harness is not computing what Lean's `-x` computes
        if not math.isfinite(n) or Fraction(n) != -fa:
            res["neg_inexact"] += 1       # FPBridge.neg: toR (-a) = -(toR a)
        for op, y, e in (("add", a + b, fa + fb), ("sub", a - b, fa - fb), ("mul", a * b, fa * fb)):
            if not math.isfinite(y):
                res["vacuous" if conditional else "unmeasurable"] += 1
                continue
            if conditional and op == "mul" and not (e == 0 or abs(e) >= DBL_MIN_F):
                res["vacuous"] += 1
                continue
            res["examined"] += 1
            err = abs(Fraction(y) - e)
            bound = abs(e) / two53
            if err > bound:
                res["violations"] += 1
            score = math.inf if (bound == 0 and err > 0) else (0.0 if bound == 0 else float(err / bound))
            worst.append((score, f"{op} {hex_bits(a)} {hex_bits(b)}"))
        if len(worst) > 4 * TOP_K:
            worst.sort(key=lambda t: (-t[0], t[1]))
            del worst[TOP_K:]
    worst.sort(key=lambda t: (-t[0], t[1]))
    res["worst"] = worst[:TOP_K]
    return res


def _bridge_chunk_unconditional(ps) -> dict:
    return _bridge_chunk(ps, conditional=False)


def _rounding_chunk(items, conditional=True) -> dict:
    """`real_round_bounds` as restated 2026-09-14 (`conditional`: `x = 0 ∨ DBL_MIN ≤ |x|`, `|x| ≤ DBL_MAX`), or as
    stated before, every real."""
    res = {"examined": 0, "vacuous": 0, "unmeasurable": 0, "violations": 0, "worst": []}
    worst = []
    two53 = 1 << 53
    for m, e in items:
        x = Fraction(m) * (Fraction(2) ** e)
        if conditional and (abs(x) > DBL_MAX_F or (x != 0 and abs(x) < DBL_MIN_F)):
            res["vacuous"] += 1
            continue
        try:
            y = float(x)  # correctly rounded, ties to even, subnormals included
        except OverflowError:
            res["unmeasurable"] += 1
            continue
        if not math.isfinite(y):
            res["unmeasurable"] += 1
            continue
        res["examined"] += 1
        err = abs(Fraction(y) - x)
        bound = abs(x) / two53
        if err > bound:
            res["violations"] += 1
        score = (math.inf if err > 0 else 0.0) if bound == 0 else float(err / bound)
        worst.append((score, f"{m:x}p{e}"))
        if len(worst) > 4 * TOP_K:
            worst.sort(key=lambda t: (-t[0], t[1]))
            del worst[TOP_K:]
    worst.sort(key=lambda t: (-t[0], t[1]))
    res["worst"] = worst[:TOP_K]
    return res


def _rounding_chunk_unconditional(items) -> dict:
    return _rounding_chunk(items, conditional=False)


def _finite_score(e: Fraction) -> float:
    """`|e| / DBL_MAX`, capped at 2 so that a huge exact result cannot overflow the conversion."""
    return 2.0 if abs(e) > 2 * DBL_MAX_F else float(abs(e) / DBL_MAX_F)


def _finite_chunk(args) -> dict:
    """`FPFiniteOfRange`'s fields over pairs of finite doubles, with the range `bound` on the exact result (`None`: no
    range). An operation the range admits is examined, and a non-finite float result is a violation; `off_tie` counts
    violations whose exact result is not the overflow tie. `neg` has no range: its hypothesis is only a finite operand."""
    ps, bound = args
    res = {"examined": 0, "vacuous": 0, "unmeasurable": 0, "violations": 0, "worst": [], "off_tie": 0}
    worst = []
    for a, b in ps:
        if not (math.isfinite(a) and math.isfinite(b)):
            res["vacuous"] += 4
            continue
        fa, fb = Fraction(a), Fraction(b)
        for op, y, e in (("add", a + b, fa + fb), ("sub", a - b, fa - fb), ("mul", a * b, fa * fb), ("neg", -a, -fa)):
            if op != "neg" and bound is not None and abs(e) > bound:
                res["vacuous"] += 1
                continue
            res["examined"] += 1
            if not math.isfinite(y):
                res["violations"] += 1
                if abs(e) != OVERFLOW_TIE_F:
                    res["off_tie"] += 1
            worst.append((_finite_score(e), f"{op} {hex_bits(a)} {hex_bits(b)}"))
        if len(worst) > 4 * TOP_K:
            worst.sort(key=lambda t: (-t[0], t[1]))
            del worst[TOP_K:]
    worst.sort(key=lambda t: (-t[0], t[1]))
    res["worst"] = worst[:TOP_K]
    return res


def _round_finite_chunk(args) -> dict:
    """`real_round_finite` over reals `m · 2^e`, with the range `bound` (`None`: no range): round-to-nearest-even of an
    admitted real must be finite. `off_tie` as in `_finite_chunk`."""
    items, bound = args
    res = {"examined": 0, "vacuous": 0, "unmeasurable": 0, "violations": 0, "worst": [], "off_tie": 0}
    worst = []
    for m, e in items:
        x = Fraction(m) * (Fraction(2) ** e)
        if bound is not None and abs(x) > bound:
            res["vacuous"] += 1
            continue
        res["examined"] += 1
        try:
            finite = math.isfinite(float(x))  # correctly rounded, ties to even; OverflowError from the tie up
        except OverflowError:
            finite = False
        if not finite:
            res["violations"] += 1
            if abs(x) != OVERFLOW_TIE_F:
                res["off_tie"] += 1
        worst.append((_finite_score(x), f"{m:x}p{e}"))
        if len(worst) > 4 * TOP_K:
            worst.sort(key=lambda t: (-t[0], t[1]))
            del worst[TOP_K:]
    worst.sort(key=lambda t: (-t[0], t[1]))
    res["worst"] = worst[:TOP_K]
    return res


def measure_axiom(spec: dict, pool) -> dict:
    kind = spec["kind"]
    if kind in ("measured", "existential-eps"):
        return measure_function_axiom(spec, pool)
    if kind in ("bridge", "bridge-unconditional"):
        chunk = _bridge_chunk if kind == "bridge" else _bridge_chunk_unconditional
        ps = pairs_for_bridge()
        total = {"examined": 0, "vacuous": 0, "unmeasurable": 0, "violations": 0, "worst": [], "neg_inexact": 0,
                 "neg_not_bitflip": 0}
        for part in pool.map(chunk, [ps[i:i + 10_000] for i in range(0, len(ps), 10_000)]):
            neg = total["neg_inexact"] + part["neg_inexact"]
            flip = total["neg_not_bitflip"] + part["neg_not_bitflip"]
            total = _merge(total, part)
            total["neg_inexact"], total["neg_not_bitflip"] = neg, flip
        total["inputs"] = len(ps)
        if total["neg_inexact"]:
            total["violations"] += total["neg_inexact"]
        return total
    if kind in ("rounding", "rounding-unconditional"):
        chunk = _rounding_chunk if kind == "rounding" else _rounding_chunk_unconditional
        items = reals_for_rounding()
        total = {"examined": 0, "vacuous": 0, "unmeasurable": 0, "violations": 0, "worst": []}
        for part in pool.map(chunk, [items[i:i + 10_000] for i in range(0, len(items), 10_000)]):
            total = _merge(total, part)
        total["inputs"] = len(items)
        return total
    if kind in FINITE_RANGES:
        bound = FINITE_RANGES[kind]
        if kind.startswith("finite-of-range"):
            data, chunk = list(_pairs_for_finite()), _finite_chunk
        else:
            data, chunk = reals_for_round_finite(), _round_finite_chunk
        total = {"examined": 0, "vacuous": 0, "unmeasurable": 0, "violations": 0, "worst": [], "off_tie": 0}
        for part in pool.map(chunk, [(data[i:i + 10_000], bound) for i in range(0, len(data), 10_000)]):
            off = total["off_tie"] + part["off_tie"]
            total = _merge(total, part)
            total["off_tie"] = off
        total["inputs"] = len(data)
        return total
    raise ValueError(kind)


def summary(result: dict) -> dict:
    """The pinned form of a measurement: counts, the maximum (6 significant digits) and where it occurs."""
    top = result["worst"][0] if result["worst"] else (0.0, "")
    where = top[1] if isinstance(top[1], str) else hex_bits(from_bits(top[1]))
    return {"inputs": result["inputs"], "examined": result["examined"], "vacuous": result["vacuous"],
            "unmeasurable": result["unmeasurable"], "violations": result["violations"],
            "max": f"{top[0]:.6e}", "argmax": where}


def describe_argmax(s: dict) -> str:
    a = s["argmax"]
    if re.fullmatch(r"[0-9a-f]{16}", a):
        return f"x = {from_bits(int(a, 16))!r} ({a})"
    return a


# ── reading a statement: what its own text says the harness must measure ─────────────────────────

#: `Trans1` constructor -> the `MachLib.Real` function its axiom must compare with.
CTOR_REAL = {"tanh": "tanh", "sinh": "sinh", "cosh": "cosh", "exp": "exp", "ln": "log", "log10": "log10",
             "sin": "sin", "cos": "cos", "tan": "tan", "asin": "arcsin", "acos": "arccos", "atan": "atan",
             "sqrt": "sqrt", "abs": "abs"}

_H = frozenset
_POS = _H({"0 < lo", "lo ≤ realToR a", "realToR a ≤ hi"})
#: (hypotheses, bound) -> (domain, bound kind, constant, the one function it may be read for, or None), each
#: hypothesis and bound exactly as the normalised source spells it, with `stdI1 leanPrims .<fn> a` written
#: `stdI1 leanPrims .<f> a`. This IS the "tightest instantiation" argument of the module docstring, made closed: a
#: hypothesis set or bound not listed here is unreadable, and the run fails rather than guessing.
READINGS = {
    (_H({"a.isFinite = true"}), "u + u"): ("finite", "c_u", "2", None),
    (_H({"a.isFinite = true"}), "u"): ("finite", "c_u", "1", None),
    (_H({"abs (realToR a) ≤ R"}), "u"): ("finite", "c_u", "1", None),                       # R free: every finite a
    (_H({"realToR a ≤ hi"}), "u * exp hi"): ("finite", "u_exp_x", None, None),              # hi = x
    (_POS, "u * (abs (log lo) + abs (log hi))"): ("positive", "u_abs_log_x", None, None),   # lo or hi at 1
    (_POS, "u * (abs (log10 lo) + abs (log10 hi))"): ("positive", "u_abs_log10_x", None, None),
    (_H({"0 ≤ realToR a", "realToR a ≤ hi"}), "u * sqrt hi"): ("nonneg", "u_sqrt_x", None, None),
    (_H({"R < 1", "abs (realToR a) ≤ R"}), "u * (pi / (1 + 1))"): ("open_unit", "u_pi_half", None, None),
    (_H({"R < 1", "abs (realToR a) ≤ R"}), "u * pi"): ("open_unit", "u_pi", None, None),
    (_H({"0 ≤ R", "R < pi / (1 + 1)", "abs (realToR a) ≤ R"}), "u * tan R"): ("tan_open", "u_abs_tan_x", None, None),
    (_H({"abs (realToR a) ≤ R"}), "u * cosh R"): ("finite", "u_cosh_x", None, None),       # R = |x|
    # restated 2026-09-14
    (_H({"a.isFinite = true", "(stdI1 leanPrims .<f> a).isFinite = true", "dblMin ≤ exp (realToR a)", "realToR a ≤ hi"}),
     "(u + u) * exp hi"): ("finite_normal_exp", "c_u_exp_x", "2", "exp"),
    (_H({"(stdI1 leanPrims .<f> a).isFinite = true", "abs (realToR a) ≤ R"}), "(u + u + u + u) * cosh R"):
        ("finite_result", "c_u_cosh_x", "4", None),
    (_POS | {"a.isFinite = true"}, "(u + u + u) * (abs (log10 lo) + abs (log10 hi))"):
        ("positive", "c_u_abs_log10_x", "3", None),
    (_H({"a.isFinite = true", "0 ≤ R", "R < pi / (1 + 1)", "abs (realToR a) ≤ R"}), "(u + u) * tan R"):
        ("tan_open", "c_u_abs_tan_x", "2", None),
}

#: `real_round_bounds` as stated since 2026-09-14, and before.
ROUNDING_STATEMENT = (": ∀ M x : Real, 0 ≤ M → M ≤ dblMax → abs x ≤ M → (x = 0 ∨ dblMin ≤ abs x) → "
                      "abs (realToR (floatOfR x) - x) ≤ u * M")
ROUNDING_STATEMENT_UNTIL_2026_09_14 = ": ∀ M x : Real, 0 ≤ M → abs x ≤ M → abs (realToR (floatOfR x) - x) ≤ u * M"
#: `real_fpfinite` and `real_round_finite`, as stated when they were added (2026-09-14).
FINITE_OF_RANGE_STATEMENT = ": FPFiniteOfRange realToR"
ROUND_FINITE_STATEMENT = ": ∀ x : Real, abs x ≤ dblMax → (floatOfR x).isFinite = true"

READING_KEYS = ("kind", "function", "domain", "bound", "c", "eps")


def derive_reading(statement: str | None) -> dict | None:
    """The reading a statement's text determines, or None when the harness cannot read it."""
    if statement is None:
        return None
    s = " ".join(statement.split())
    if s in (": Float → MachLib.Real", ": Real → Float", ": MachLib.Real"):
        return {"kind": "declaration"}
    if s == ": FPBridgeFinite realToR":
        return {"kind": "bridge"}
    if s == ": FPBridge realToR":
        return {"kind": "bridge-unconditional"}
    if s == ROUNDING_STATEMENT:
        return {"kind": "rounding"}
    if s == ROUNDING_STATEMENT_UNTIL_2026_09_14:
        return {"kind": "rounding-unconditional"}
    if s == FINITE_OF_RANGE_STATEMENT:
        return {"kind": "finite-of-range"}
    if s == ROUND_FINITE_STATEMENT:
        return {"kind": "round-finite"}
    m = re.fullmatch(r": ∀ (?:\([^)]*\) )*(?:\(a : Float\)|a : Float), (.*)", s)
    if m is None:
        return None
    parts = m.group(1).split(" → ")
    concl = parts[-1]
    c = re.fullmatch(r"abs \(realToR \(stdI1 leanPrims \.(\w+) a\) - (\w+) \(realToR a\)\) ≤ (.+)", concl)
    if c is None or CTOR_REAL.get(c.group(1)) != c.group(2):
        return None
    fn, bound_text = c.group(1), c.group(3)
    hyps = _H(h.replace(f"stdI1 leanPrims .{fn} a", "stdI1 leanPrims .<f> a") for h in parts[:-1])
    eps = re.fullmatch(r"real_\w+_eps", bound_text)
    if eps and not hyps:
        return {"kind": "existential-eps", "function": fn, "domain": "finite", "bound": "sup",
                "eps": "Certcom." + bound_text}
    reading = READINGS.get((hyps, bound_text))
    if reading is None or reading[3] not in (None, fn):
        return None
    domain, bound, const, _only = reading
    out = {"kind": "measured", "function": fn, "domain": domain, "bound": bound}
    if const is not None:
        out["c"] = const
    return out


#: The definitions the bridge row's reading depends on, as the source spells them (whitespace-normalised).
EXPECTED_DEFINITIONS = {
    "FPBridge": ("add : ∀ a b : Float, RoundsW u (toR (a + b)) (toR a + toR b) | "
                 "sub : ∀ a b : Float, RoundsW u (toR (a - b)) (toR a - toR b) | "
                 "mul : ∀ a b : Float, RoundsW u (toR (a * b)) (toR a * toR b) | "
                 "neg : ∀ a : Float, toR (-a) = -(toR a)"),
    "FPBridgeFinite": ("add : ∀ a b : Float, (a + b).isFinite = true → RoundsW u (toR (a + b)) (toR a + toR b) | "
                       "sub : ∀ a b : Float, (a - b).isFinite = true → RoundsW u (toR (a - b)) (toR a - toR b) | "
                       "mul : ∀ a b : Float, (a * b).isFinite = true → (toR a * toR b = 0 ∨ dblMin ≤ abs (toR a * toR b)) "
                       "→ RoundsW u (toR (a * b)) (toR a * toR b) | "
                       "neg : ∀ a : Float, a.isFinite = true → toR (-a) = -(toR a)"),
    "FPFiniteOfRange": ("add : ∀ a b : Float, a.isFinite = true → b.isFinite = true → abs (toR a + toR b) ≤ dblMax → "
                        "(a + b).isFinite = true | "
                        "sub : ∀ a b : Float, a.isFinite = true → b.isFinite = true → abs (toR a - toR b) ≤ dblMax → "
                        "(a - b).isFinite = true | "
                        "mul : ∀ a b : Float, a.isFinite = true → b.isFinite = true → abs (toR a * toR b) ≤ dblMax → "
                        "(a * b).isFinite = true | "
                        "neg : ∀ a : Float, a.isFinite = true → (-a).isFinite = true"),
    "RoundsW": "(w fl e : Real) : Prop := ∃ δ : Real, -w ≤ δ ∧ δ ≤ w ∧ fl = e * (1 + δ)",
    "dblMin": ": MachLib.Real := 1 / natCast (2 ^ 1022)",
    "dblMax": ": MachLib.Real := natCast ((2 ^ 53 - 1) * 2 ^ 971)",
}


def _strip_lean_comments(text: str) -> str:
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            out.append("\n" if text[i] == "\n" else "")
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def _structure_fields(text: str, name: str) -> str | None:
    """A `structure <name> (toR …) : Prop where` block's fields, one per `|`, a field's continuation lines joined."""
    m = re.search(rf"^structure {name} \(toR : Float → MachLib\.Real\) : Prop where\n((?:[ \t]*\n|[ \t]+\S.*\n)+)",
                  text, re.MULTILINE)
    if m is None:
        return None
    fields, indent = [], None
    for line in m.group(1).splitlines():
        if not line.strip():
            continue
        depth = len(line) - len(line.lstrip())
        indent = depth if indent is None else indent
        if depth > indent and fields:
            fields[-1] += " " + " ".join(line.split())
        else:
            fields.append(" ".join(line.split()))
    return " | ".join(fields)


def source_definitions(foundations: pathlib.Path) -> dict[str, str | None]:
    out: dict[str, str | None] = {k: None for k in EXPECTED_DEFINITIONS}
    bridge = _strip_lean_comments((foundations / "MachLib" / "FloatRealBridge.lean").read_text(encoding="utf-8"))
    out["FPBridge"] = _structure_fields(bridge, "FPBridge")
    out["FPBridgeFinite"] = _structure_fields(bridge, "FPBridgeFinite")
    out["FPFiniteOfRange"] = _structure_fields(bridge, "FPFiniteOfRange")
    for name in ("dblMin", "dblMax"):
        m = re.search(rf"^noncomputable def {name} (.*?)(?=\n\s*\n|\Z)", bridge, re.MULTILINE | re.DOTALL)
        if m:
            out[name] = " ".join(m.group(1).split())
    model = _strip_lean_comments((foundations / "MachLib" / "FPModel.lean").read_text(encoding="utf-8"))
    m = re.search(r"^def RoundsW (.*?)(?=\n\s*\n|\Z)", model, re.MULTILINE | re.DOTALL)
    if m:
        out["RoundsW"] = " ".join(m.group(1).split())
    return out

# ── the corpus: manifest names, source statements ────────────────────────────────────────────────

def manifest_float_bridge(text: str) -> set[str]:
    return set(re.findall(r"^\|\s*`([^`]+)`\s*\|\s*float-bridge\s*\|", text, re.MULTILINE))


def source_statements(foundations: pathlib.Path) -> dict[str, str]:
    """`axiom <name> <statement>` for every axiom in MachLib/*.lean, whitespace-normalised."""
    out: dict[str, str] = {}
    stop = r"(?=\n\s*\n|\n/--|\n/-!|\n--|\ntheorem\b|\ndef\b|\nexample\b|\nnoncomputable\b|\naxiom\b|\nend\b|\Z)"
    for path in sorted((foundations / "MachLib").glob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for m in re.finditer(r"^axiom\s+([A-Za-z_][\w']*)\b(.*?)" + stop, text, re.MULTILINE | re.DOTALL):
            out.setdefault(m.group(1), " ".join(m.group(2).split()))
    return out


# ── the Lean cross-check ─────────────────────────────────────────────────────────────────────────

LEAN_TEMPLATE = """import MachLib.EMLToCRuntime
open Certcom

def fbHexVal (s : String) : UInt64 :=
  s.foldl (fun acc c => acc * 16 + (if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10).toUInt64) 0

def fbEval (f : String) (x y : Float) : Float :=
  match f with
  | "tanh" => stdI1 leanPrims .tanh x | "sinh" => stdI1 leanPrims .sinh x | "cosh" => stdI1 leanPrims .cosh x
  | "exp" => stdI1 leanPrims .exp x | "ln" => stdI1 leanPrims .ln x | "log10" => stdI1 leanPrims .log10 x
  | "sin" => stdI1 leanPrims .sin x | "cos" => stdI1 leanPrims .cos x | "tan" => stdI1 leanPrims .tan x
  | "asin" => stdI1 leanPrims .asin x | "acos" => stdI1 leanPrims .acos x | "atan" => stdI1 leanPrims .atan x
  | "sqrt" => stdI1 leanPrims .sqrt x | "abs" => stdI1 leanPrims .abs x
  | "add" => x + y | "sub" => x - y | "mul" => x * y | "neg" => -x
  | "addfin" => if (x + y).isFinite then 1.0 else 0.0 | "subfin" => if (x - y).isFinite then 1.0 else 0.0
  | "mulfin" => if (x * y).isFinite then 1.0 else 0.0 | "negfin" => if (-x).isFinite then 1.0 else 0.0
  | _ => 0.0 / 0.0

#eval show IO Unit from do
  let text ← IO.FS.readFile "@@INPUTS@@"
  for line in text.splitOn "\\n" do
    match line.splitOn " " with
    | [f, a, b] => IO.println s!"FB {f} {a} {b} {(fbEval f (Float.ofBits (fbHexVal a)) (Float.ofBits (fbHexVal b))).toBits}"
    | _ => pure ()
"""


def python_eval(f: str, x: float, y: float) -> float:
    if f in FLOAT_FUNCS:
        return FLOAT_FUNCS[f](x)
    finite_of = {"addfin": lambda: x + y, "subfin": lambda: x - y, "mulfin": lambda: x * y, "negfin": lambda: -x}
    if f in finite_of:
        return 1.0 if math.isfinite(finite_of[f]()) else 0.0
    return {"add": lambda: x + y, "sub": lambda: x - y, "mul": lambda: x * y, "neg": lambda: -x}[f]()


def lean_crosscheck(samples: list[tuple[str, float, float]]) -> tuple[list[str], int, str | None]:
    """(mismatches, values compared, reason Lean could not run)."""
    with tempfile.TemporaryDirectory(prefix="float_bridge_") as tmp:
        inputs = pathlib.Path(tmp) / "inputs.txt"
        inputs.write_text("".join(f"{f} {hex_bits(x)} {hex_bits(y)}\n" for f, x, y in samples))
        lean = pathlib.Path(tmp) / "crosscheck.lean"
        lean.write_text(LEAN_TEMPLATE.replace("@@INPUTS@@", str(inputs)))
        proc = subprocess.run(["bash", str(FOUNDATIONS / "tools" / "capped_lean.sh"), "lake", "env", "lean", str(lean)],
                              cwd=FOUNDATIONS, capture_output=True, text=True, timeout=900)
    rows = [line.split() for line in proc.stdout.splitlines() if line.startswith("FB ")]
    if proc.returncode != 0 or len(rows) != len(samples):
        return [], 0, (f"lake env lean exited {proc.returncode} with {len(rows)} of {len(samples)} values: "
                       + (proc.stderr.strip().splitlines() or proc.stdout.strip().splitlines() or ["no output"])[-1][:300])
    bad = []
    for (f, x, y), row in zip(samples, rows):
        lean_bits = int(row[4])
        mine = python_eval(f, x, y)
        lean_value = from_bits(lean_bits)
        if row[1] != f or row[2] != hex_bits(x):
            bad.append(f"row out of order: {row[:3]} for {f} {hex_bits(x)}")
        elif math.isnan(mine) or math.isnan(lean_value):
            if not (math.isnan(mine) and math.isnan(lean_value)):
                bad.append(f"{f}({x!r}): harness {mine!r}, Lean {lean_value!r}")
        elif bits(mine) != lean_bits:
            bad.append(f"{f}({x!r}, {y!r}): harness {hex_bits(mine)}, Lean {lean_bits:016x}")
    return bad, len(samples), None


def crosscheck_samples(registry: dict, results: dict) -> list[tuple[str, float, float]]:
    rng = random.Random(121)
    samples: list[tuple[str, float, float]] = []
    functions = sorted({spec["function"] for spec in registry["axioms"].values() if "function" in spec})
    for f in functions:
        xs = inputs_for(f)
        pick = rng.sample(xs, 200) + around(TANH_X_MAX, 5) + around(SINH_X_MAX, 5) + around(709.78, 5) + SPECIALS
        for name, spec in registry["axioms"].items():
            if spec.get("function") == f and name in results:
                pick += [from_bits(b) for _, b in results[name]["worst"][:10]]
        samples += [(f, x, 0.0) for x in pick]
    for a, b in rng.sample(pairs_for_bridge(), 300):
        samples += [("add", a, b), ("sub", a, b), ("mul", a, b), ("neg", a, 0.0)]
    # the finiteness rows: Lean's own `Float.isFinite` at the overflow boundary, including the tie
    boundary = list(_pairs_for_finite())[len(_pairs_for_bridge()):]
    for a, b in rng.sample(boundary, 200) + [(DBL_MAX, math.ldexp(1.0, 970))]:
        samples += [("add", a, b), ("sub", a, b), ("mul", a, b),
                    ("addfin", a, b), ("subfin", a, b), ("mulfin", a, b), ("negfin", a, 0.0)]
    return samples


# ── verdicts ─────────────────────────────────────────────────────────────────────────────────────

def platform_id() -> dict:
    return {"machine": platform.machine(), "libc": os.confstr("CS_GNU_LIBC_VERSION") if hasattr(os, "confstr") else "?"}


def verdicts(registry: dict, results: dict, control_results: dict, manifest: set[str],
             statements: dict[str, str], definitions: dict[str, str | None]) -> tuple[list[str], list[str]]:
    """(problems, report lines). Pure: --self-test feeds it doctored inputs."""
    problems, report = [], []
    axioms = registry["axioms"]
    for name, want in EXPECTED_DEFINITIONS.items():
        if definitions.get(name) != want:
            problems.append(f"{name} is now\n      {definitions.get(name)!r}\n    and the harness reads it as\n"
                            f"      {want!r}\n    The bridge row's measurement no longer matches its definition.")
    for name in sorted(manifest - set(axioms)):
        problems.append(f"{name} is a float-bridge axiom in AXIOM_MANIFEST.md and is not in the registry")
    for name in sorted(set(axioms) - manifest):
        problems.append(f"the registry lists {name}, which AXIOM_MANIFEST.md does not class float-bridge")
    for name, spec in sorted(axioms.items()):
        short = name.split(".")[-1]
        if statements.get(short) != spec["statement"]:
            problems.append(f"{name}: the Lean source states\n      {statements.get(short)!r}\n    and the registry "
                            f"measures\n      {spec['statement']!r}\n    Re-read the axiom and update its registry entry.")
        derived = derive_reading(statements.get(short))
        if derived is None:
            problems.append(f"{name}: the harness cannot read its statement {statements.get(short)!r} (no READINGS "
                            "entry), so it cannot say what to measure")
        else:
            wrong = {k: (spec.get(k), derived.get(k)) for k in READING_KEYS if spec.get(k) != derived.get(k)}
            if wrong:
                problems.append(f"{name}: the registry's reading disagrees with what its statement says "
                                f"(field: registry, statement): {wrong}")
        kind = spec["kind"]
        if kind == "declaration":
            report.append(f"  {name}: declaration, not a proposition ({spec['reason']})")
            continue
        res = results.get(name)
        if res is None:
            problems.append(f"{name}: not measured")
            continue
        s = summary(res)
        if res.get("neg_not_bitflip"):
            problems.append(f"{name}: the harness's negation is not IEEE's at {res['neg_not_bitflip']} input(s), so the "
                            "neg field was measured on the wrong function")
        if s["examined"] < MIN_EXAMINED:
            problems.append(f"{name}: examined {s['examined']} inputs, fewer than {MIN_EXAMINED}: it measured nothing")
        elif s["examined"] < int(spec.get("min_examined", 0)):
            problems.append(f"{name}: examined {s['examined']} inputs, fewer than its row's min_examined "
                            f"{spec['min_examined']}: the input set shrank")
        line = (f"  {name}: {s['examined']} examined of {s['inputs']} ({s['vacuous']} outside its hypotheses, "
                f"{s['unmeasurable']} with a non-finite result); ")
        if kind == "existential-eps":
            line += f"sup |error| = {s['max']} at {describe_argmax(s)}: bounded, so an eps exists"
        elif kind in FINITE_RANGES:
            line += (f"{s['violations']} violation(s) (a non-finite result its range admits); largest |exact result| "
                     f"/ DBL_MAX examined = {s['max']} at {describe_argmax(s)}; expected {spec['expect']}")
            if spec["expect"] == "holds" and s["violations"]:
                problems.append(f"{name} is VIOLATED at {s['violations']} input(s) and the registry says it holds")
        else:
            line += (f"{s['violations']} violation(s); max error/bound = {s['max']} at {describe_argmax(s)}; "
                     f"expected {spec['expect']}")
            if spec["expect"] == "holds" and s["violations"]:
                problems.append(f"{name} is VIOLATED at {s['violations']} input(s) (max {s['max']} times its bound, "
                                f"at {describe_argmax(s)}) and the registry says it holds")
            if spec["expect"] == "violated" and not s["violations"]:
                problems.append(f"{name} is registered as an acknowledged failure and was not violated")
        pinned = spec.get("pinned")
        if pinned != s:
            problems.append(f"{name}: measured {s}\n    pinned   {pinned}\n    The measurement changed. Find out why "
                            "before re-pinning with --record.")
        report.append(line)
    for name, spec in sorted(registry.get("controls", {}).items()):
        res = control_results.get(name)
        if res is None:
            problems.append(f"control {name}: not measured")
            continue
        s = summary(res)
        if not s["violations"]:
            problems.append(f"control {name} ({spec['why']}) was NOT violated: the harness cannot see a violation, "
                            "so no verdict above means anything")
        if spec.get("only_at_tie") and res.get("off_tie"):
            problems.append(f"control {name} ({spec['why']}) fails at {res['off_tie']} exact result(s) other than the "
                            "overflow tie DBL_MAX + 2^970: something other than the range decides it")
        report.append(f"  control {name}: {s['violations']} violation(s) of {s['examined']} (max {s['max']} at "
                      f"{describe_argmax(s)}) — must be violated")
    return problems, report


# ── modes ────────────────────────────────────────────────────────────────────────────────────────

def run_measurements(registry: dict, only: str | None = None) -> tuple[dict, dict]:
    results, controls = {}, {}
    with multiprocessing.get_context("fork").Pool(max(1, min(8, os.cpu_count() or 1))) as pool:
        for name, spec in sorted(registry["axioms"].items()):
            if spec["kind"] == "declaration" or (only and only not in name):
                continue
            results[name] = measure_axiom(spec, pool)
            print(f"  measured {name}: {summary(results[name])}", flush=True)
        for name, spec in sorted(registry.get("controls", {}).items()):
            if only and only not in name and only not in spec.get("inputs_of", ""):
                continue
            controls[name] = measure_axiom(spec, pool)
    return results, controls


def main_gate(record: bool) -> int:
    try:
        _mp()
    except ImportError:
        print("FLOAT-BRIDGE UNAVAILABLE: mpmath is not installed (pip install mpmath)")
        return 2
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    if platform_id() != registry["platform"]:
        print(f"FLOAT-BRIDGE UNAVAILABLE: pinned to {registry['platform']}, this is {platform_id()}. The measured "
              "numbers are properties of that libm; re-measure there, or record a registry for this platform.")
        return 2
    print("=== float-bridge axioms, measured ===")
    results, controls = run_measurements(registry)
    if record:
        for name, res in results.items():
            registry["axioms"][name]["pinned"] = summary(res)
        REGISTRY.write_text(json.dumps(registry, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(f"FLOAT-BRIDGE RECORDED: {len(results)} measurements pinned in {REGISTRY.name}; review the diff")
        return 0
    manifest = manifest_float_bridge(MANIFEST.read_text(encoding="utf-8"))
    problems, report = verdicts(registry, results, controls, manifest, source_statements(FOUNDATIONS),
                                source_definitions(FOUNDATIONS))
    print("\n".join(report))
    bad, compared, unavailable = lean_crosscheck(crosscheck_samples(registry, results))
    if unavailable:
        print(f"FLOAT-BRIDGE UNAVAILABLE: the Lean cross-check could not run: {unavailable}")
        return 2
    print(f"  Lean cross-check: {compared - len(bad)} of {compared} values bit-identical to Lean's own evaluation")
    if compared < 1000:
        problems.append(f"the Lean cross-check compared only {compared} values")
    problems += [f"Lean cross-check: {b}" for b in bad[:20]]
    measured = [n for n, s in registry["axioms"].items() if s["kind"] != "declaration"]
    violated = sorted(n for n, s in registry["axioms"].items() if s.get("expect") == "violated")
    if problems:
        print("FLOAT-BRIDGE FAIL:\n  - " + "\n  - ".join(problems))
        return 1
    print(f"FLOAT-BRIDGE PASS: {len(measured)} axioms measured ({len(violated)} ACKNOWLEDGED VIOLATED: "
          f"{', '.join(violated) or 'none'}); {len(controls)} controls fired; {compared} values match Lean")
    return 0


def self_test() -> int:
    """The verdict logic, on doctored data. Each canary must produce the problem it names, and the clean
    input must produce none."""
    fake = {"examined": 50_000, "inputs": 60_000, "vacuous": 0, "unmeasurable": 0, "violations": 0,
            "worst": [(1.5, bits(-5.581))]}
    bad = dict(fake, violations=7, worst=[(1.9, bits(3.0))])
    stmt = ": ∀ (a : Float), a.isFinite = true → abs (realToR (stdI1 leanPrims .tanh a) - tanh (realToR a)) ≤ u + u"
    base = {"platform": platform_id(), "axioms": {
        "Certcom.real_x_rounds": {"kind": "measured", "function": "tanh", "domain": "finite", "bound": "c_u", "c": "2",
                                  "expect": "holds", "statement": stmt, "pinned": summary(fake)},
        "Certcom.realToR": {"kind": "declaration", "reason": "a function symbol", "statement": ": Float → MachLib.Real"}},
        "controls": {"too-tight": {"kind": "measured", "function": "tanh", "domain": "finite", "bound": "c_u",
                                   "c": "1", "why": "specimen"}}}
    manifest = {"Certcom.real_x_rounds", "Certcom.realToR"}
    statements = {"real_x_rounds": stmt, "realToR": ": Float → MachLib.Real"}
    results, controls = {"Certcom.real_x_rounds": fake}, {"too-tight": bad}
    definitions = dict(EXPECTED_DEFINITIONS)

    def problems_of(reg=base, res=results, ctl=controls, man=manifest, st=statements, defs=definitions):
        return verdicts(reg, res, ctl, man, st, defs)[0]

    def with_row(**fields):
        row = {**base["axioms"]["Certcom.real_x_rounds"], **fields}
        return dict(base, axioms={**base["axioms"], "Certcom.real_x_rounds": row})

    failures = []
    if problems_of():
        failures.append(f"clean input produced problems: {problems_of()}")
    canaries = [
        ("an unexpected violation", dict(base, axioms={**base["axioms"], "Certcom.real_x_rounds": {
            **base["axioms"]["Certcom.real_x_rounds"], "pinned": summary(bad)}}),
         {"Certcom.real_x_rounds": bad}, controls, manifest, statements, "VIOLATED"),
        ("a pinned number that moved", base, {"Certcom.real_x_rounds": dict(fake, worst=[(1.51, bits(-5.581))])},
         controls, manifest, statements, "measurement changed"),
        ("an empty measurement", base, {"Certcom.real_x_rounds": dict(fake, examined=0)}, controls, manifest,
         statements, "measured nothing"),
        ("a control that did not fire", base, results, {"too-tight": fake}, manifest, statements, "NOT violated"),
        ("a statement that changed in Lean", base, results, controls, manifest,
         dict(statements, real_x_rounds=": ∀ (a : Float), P"), "Lean source states"),
        ("a float-bridge axiom the registry lacks", base, results, controls, manifest | {"Certcom.real_y_rounds"},
         statements, "not in the registry"),
        ("an unchanged statement read with the wrong constant", with_row(c="3"), results, controls, manifest,
         statements, "reading disagrees"),
        ("an unchanged statement read on the wrong domain", with_row(domain="positive"), results, controls, manifest,
         statements, "reading disagrees"),
        ("an unchanged statement read with the wrong bound kind", with_row(bound="u_cosh_x", c=None), results, controls,
         manifest, statements, "reading disagrees"),
        ("an unchanged statement read as the wrong function", with_row(function="sinh"), results, controls, manifest,
         statements, "reading disagrees"),
        ("a statement no READINGS entry covers", with_row(statement=stmt.replace("u + u", "u * u")), results, controls,
         manifest, dict(statements, real_x_rounds=stmt.replace("u + u", "u * u")), "cannot read"),
    ]
    for label, reg, res, ctl, man, st, needle in canaries:
        got = problems_of(reg, res, ctl, man, st)
        if not any(needle in p for p in got):
            failures.append(f"canary '{label}' did not produce '{needle}': {got}")
        else:
            print(f"  canary fires: {label}")
    changed = dict(definitions, RoundsW=definitions["RoundsW"].replace("-w ≤ δ", "0 ≤ δ"))
    if not any("RoundsW is now" in p for p in problems_of(defs=changed)):
        failures.append("canary 'a changed RoundsW definition' did not fire")
    else:
        print("  canary fires: a changed RoundsW definition")
    # the negation instrument: IEEE's negation passes both checks; one that is not a bit flip, and one that is
    # not exact, must each be caught
    pairs = [(0.0, 1.0), (1.5, 2.0), (-3.25, 0.5)]
    ieee = _bridge_chunk(pairs)
    not_flip = _bridge_chunk(pairs, neg=lambda v: 0.0 - v)          # +0.0 for +0.0: the value agrees, the bits do not
    not_exact = _bridge_chunk(pairs, neg=lambda v: v * -1.0000000000000002)
    if ieee["neg_not_bitflip"] or ieee["neg_inexact"]:
        failures.append(f"IEEE negation flagged: {ieee['neg_not_bitflip']} not-bit-flip, {ieee['neg_inexact']} inexact")
    if not not_flip["neg_not_bitflip"]:
        failures.append("canary 'a negation that is not a bit flip' did not fire")
    if not not_exact["neg_inexact"]:
        failures.append("canary 'a negation that is not exact' did not fire")
    if not failures:
        print("  canary fires: a negation that is not a bit flip, and one that is not exact")
    # the 2026-09-14 shapes read as their hypotheses say, and a dropped hypothesis is not read the same
    sinh_st = (": ∀ (R : MachLib.Real) (a : Float), (stdI1 leanPrims .sinh a).isFinite = true → abs (realToR a) ≤ R → "
               "abs (realToR (stdI1 leanPrims .sinh a) - sinh (realToR a)) ≤ (u + u + u + u) * cosh R")
    exp_st = (": ∀ (hi : MachLib.Real) (a : Float), a.isFinite = true → (stdI1 leanPrims .exp a).isFinite = true → "
              "dblMin ≤ exp (realToR a) → realToR a ≤ hi → abs (realToR (stdI1 leanPrims .exp a) - exp (realToR a)) "
              "≤ (u + u) * exp hi")
    got = [derive_reading(sinh_st), derive_reading(exp_st)]
    want = [("finite_result", "c_u_cosh_x", "4"), ("finite_normal_exp", "c_u_exp_x", "2")]
    for r, w in zip(got, want):
        if r is None or (r["domain"], r["bound"], r.get("c")) != w:
            failures.append(f"a 2026-09-14 statement read as {r}, not {w}")
    for label, bad in (("sinh without its finite-result hypothesis",
                        sinh_st.replace("(stdI1 leanPrims .sinh a).isFinite = true → ", "")),
                       ("exp's DBL_MIN hypothesis on log10",
                        exp_st.replace(".exp a", ".log10 a").replace("exp (realToR a)) ≤", "log10 (realToR a)) ≤"))):
        if derive_reading(bad) is not None:
            failures.append(f"canary '{label}' is readable: {derive_reading(bad)}")
        else:
            print(f"  canary fires: {label} is unreadable")
    if derive_reading(ROUNDING_STATEMENT) != {"kind": "rounding"}:
        failures.append("the restated real_round_bounds does not read as rounding")
    # the bridge's and rounding's hypotheses are load-bearing: excluded inputs are vacuous, and fail without them
    tiny = [(1e-200, 1e-200)]
    b1, b0 = _bridge_chunk(tiny), _bridge_chunk_unconditional(tiny)
    if not (b1["vacuous"] >= 1 and b1["violations"] == 0 and b0["violations"] >= 1):
        failures.append(f"a subnormal product: FPBridgeFinite {b1['vacuous']} vacuous/{b1['violations']} violated, "
                        f"FPBridge {b0['violations']} violated")
    else:
        print("  canary fires: a subnormal product is vacuous for FPBridgeFinite and violates FPBridge")
    sub = [(3, -1076)]  # 0.75·2^-1074 rounds to 2^-1074
    r1, r0 = _rounding_chunk(sub), _rounding_chunk_unconditional(sub)
    if not (r1["vacuous"] == 1 and r0["violations"] == 1):
        failures.append(f"a subnormal real: restated {r1}, old {r0}")
    else:
        print("  canary fires: a subnormal real is vacuous for the restated real_round_bounds and violates the old")
    spec = {"function": "exp", "domain": "finite_normal_exp", "bound": "c_u_exp_x", "c": "2"}
    ex = _measure_chunk((spec, [-745.0, 800.0, 1.0]))
    if not (ex["vacuous"] == 2 and ex["examined"] == 1):
        failures.append(f"exp's result hypotheses: {ex['vacuous']} vacuous, {ex['examined']} examined of 3")
    else:
        print("  canary fires: exp at -745 (subnormal result) and 800 (overflow) is vacuous on its new domain")
    # a real registry must be readable row by row, or the gate would fail on every run
    real = json.loads(REGISTRY.read_text(encoding="utf-8"))
    unreadable = [n for n, sp in real["axioms"].items() if derive_reading(sp["statement"]) is None]
    if unreadable:
        failures.append(f"registry rows the harness cannot read: {unreadable}")
    # the float functions themselves: the identity branch, the overflow branch, a sign
    specimens = [(lean_tanh(1e-300) == 1e-300, "tanh(1e-300) is 1e-300"),
                 (lean_tanh(1000.0) == 1.0, "tanh(1000) is 1"),
                 (bits(lean_tanh(-0.0)) == bits(-0.0), "tanh(-0.0) keeps its sign"),
                 (math.isfinite(lean_sinh(710.0)), "sinh(710) is finite"),
                 (lean_sinh(1e-300) == 1e-300, "sinh(1e-300) is 1e-300"),
                 (bits(lean_sinh(-0.0)) == bits(-0.0), "sinh(-0.0) keeps its sign"),
                 (EXP(1.0) == math.exp(1.0), "ctypes exp is libm exp")]
    failures += [f"specimen failed: {why}" for ok, why in specimens if not ok]
    # the finiteness rows (2026-09-14): both statements read, a changed range does not, and the tie decides
    if derive_reading(FINITE_OF_RANGE_STATEMENT) != {"kind": "finite-of-range"}:
        failures.append(f"real_fpfinite's statement reads as {derive_reading(FINITE_OF_RANGE_STATEMENT)}")
    if derive_reading(ROUND_FINITE_STATEMENT) != {"kind": "round-finite"}:
        failures.append(f"real_round_finite's statement reads as {derive_reading(ROUND_FINITE_STATEMENT)}")
    for label, bad_st in (("real_round_finite with a strict range", ROUND_FINITE_STATEMENT.replace("≤ dblMax", "< dblMax")),
                          ("real_round_finite with no range", ": ∀ x : Real, (floatOfR x).isFinite = true"),
                          ("real_fpfinite over another denotation", ": FPFiniteOfRange (fun _ => 0)")):
        if derive_reading(bad_st) is not None:
            failures.append(f"canary '{label}' is readable: {derive_reading(bad_st)}")
        else:
            print(f"  canary fires: {label} is unreadable")
    tie_pair, far_pair = [(DBL_MAX, math.ldexp(1.0, 970))], [(DBL_MAX, DBL_MAX)]
    in_range = _finite_chunk((tie_pair, DBL_MAX_F))
    tie_incl = _finite_chunk((tie_pair, OVERFLOW_TIE_F))
    tie_incl_far = _finite_chunk((far_pair, OVERFLOW_TIE_F))
    no_range = _finite_chunk((tie_pair + far_pair, None))
    if not (in_range["violations"] == 0 and in_range["vacuous"] == 2 and tie_incl["violations"] == 1
            and tie_incl["off_tie"] == 0 and tie_incl_far["violations"] == 0 and no_range["off_tie"] >= 2):
        failures.append(f"finiteness at the overflow tie: in range {in_range}, tie-inclusive {tie_incl} and "
                        f"{tie_incl_far}, no range {no_range}")
    else:
        print("  canary fires: DBL_MAX + 2^970 is outside real_fpfinite's range, violates the tie-inclusive range "
              "exactly there, and a far overflow violates only with no range")
    tie_real, below_tie = [((1 << 54) - 1, 970)], [((((1 << 54) - 1) << 100) - 1, 870)]
    r_in, r_tie = _round_finite_chunk((tie_real, DBL_MAX_F)), _round_finite_chunk((tie_real, OVERFLOW_TIE_F))
    r_below, r_none = _round_finite_chunk((below_tie, OVERFLOW_TIE_F)), _round_finite_chunk(([((1 << 55), 970)], None))
    if not (r_in["vacuous"] == 1 and r_tie["violations"] == 1 and r_tie["off_tie"] == 0 and r_below["examined"] == 1
            and r_below["violations"] == 0 and r_none["off_tie"] == 1):
        failures.append(f"round-finite at the overflow tie: {r_in}, {r_tie}, {r_below}, {r_none}")
    else:
        print("  canary fires: the real at the overflow tie overflows, one just below it does not, and one far above "
              "violates only with no range")
    if not any("min_examined" in pr for pr in problems_of(with_row(min_examined=60_000))):
        failures.append("canary 'a row that examined fewer than its min_examined' did not fire")
    else:
        print("  canary fires: a row that examined fewer than its min_examined")
    tie_ctl = dict(base, controls={"too-tight": {"kind": "finite-of-range-tie-inclusive", "only_at_tie": True,
                                                 "why": "specimen"}})
    if not any("other than the overflow tie" in pr
               for pr in problems_of(reg=tie_ctl, ctl={"too-tight": dict(fake, violations=7, off_tie=3)})):
        failures.append("canary 'a tie-inclusive control failing away from the tie' did not fire")
    else:
        print("  canary fires: a tie-inclusive control failing away from the tie")
    if failures:
        print("FLOAT-BRIDGE SELFTEST FAIL:\n  - " + "\n  - ".join(failures))
        return 1
    print(f"FLOAT-BRIDGE SELFTEST PASS: {len(canaries) + 3} canaries fire, the clean input passes, every registry "
          f"row is readable, {len(specimens)} float specimens hold")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--explore", action="store_true")
    ap.add_argument("--record", action="store_true")
    ap.add_argument("--only")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    if args.explore:
        registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
        run_measurements(registry, args.only)
        return 0
    return main_gate(args.record)


if __name__ == "__main__":
    sys.exit(main())
