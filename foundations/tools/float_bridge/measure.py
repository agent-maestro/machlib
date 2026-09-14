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
    the bound TIGHTEST, because a ∀ over them is false if it fails at any one:
      exp:   u·exp hi, hi ≥ x                    → u·exp x
      log:   u·(|log lo| + |log hi|), lo ≤ x ≤ hi → u·|log x| (lo or hi at 1)      (log10 likewise)
      sqrt:  u·sqrt hi, hi ≥ x                   → u·sqrt x
      sinh, cosh:  u·cosh R, R ≥ |x|             → u·cosh x
      tan:   u·tan R, |x| ≤ R < π/2              → u·|tan x|, and only |x| < π/2 is in the domain
      asin, acos:  a constant, |x| ≤ R < 1       → only |x| < 1 is in the domain
    An input outside a statement's hypotheses is VACUOUS (not counted). An input whose float result is
    ±inf or NaN is UNMEASURABLE: `realToR` of a non-finite float has no real value, so nothing can be said,
    and the count is reported rather than hidden. Non-finite INPUTS are likewise outside what can be
    measured, whatever the statement quantifies over.
  * `existential-eps` — `|… − f x| ≤ real_f_eps` for an opaque constant: satisfiable iff the error is
    bounded; the harness reports the supremum it found.
  * `bridge` — `real_fpbridge`: `+`, `−`, `×` round within `u` relatively (`RoundsW`), negation is exact.
  * `rounding` — `real_round_bounds`: round-to-nearest of a real `x` lands within `u·|x|` (floatOfR read as
    IEEE round-to-nearest-even, which is what its docstring says it models).
  * `declaration` — a function symbol or an opaque constant, not a proposition.

INPUTS, deterministic: a dense grid over each function's interesting range; log-spaced tiny |x| down to the
denormals; consecutive doubles on both sides of every branch threshold and edge (identity cut-offs, the
exp-overflow switch, the subnormal onset, ±1 for asin/acos, π/2 for tan); ±large magnitudes; random finite
bit patterns; then a local search around the 25 worst points found, two rounds.

VERDICTS. Every `measured` axiom has an `expect`: `holds` fails on any violation; `violated` is an
ACKNOWLEDGED failure whose numbers are pinned, and the run fails if they change or if a new failure appears.
Each measured axiom also pins its examined count, maximum error and where it occurs, so a change in the
libm, the runtime body or the input set cannot pass silently (`--record` re-pins, as a deliberate act).
The run also fails if:
  * a positive CONTROL — an axiom stated deliberately too tight — does not come out violated;
  * any measured axiom examined fewer than MIN_EXAMINED inputs (a harness that measured nothing passes);
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
DENORM_MIN = 5e-324
HALF_PI_DOUBLE = 1.5707963267948966


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
    if domain == "finite":
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
    if function == "tanh":
        xs = (steps(-30, 30, 1e-3) + steps(-1, 1, 1e-5) + logspace(DENORM_MIN, 1.0, 4000, True)
              + around(TANH_X_MAX, 2000) + around(-TANH_X_MAX, 2000) + around(18.715, 1000) + around(19.0615, 1000)
              + around(20.0, 500) + logspace(1.0, DBL_MAX, 2000, True) + denormals(1000)
              + random_bits(50_000, 11) + uniform(-40, 40, 100_000, 12))
    elif function in ("sinh", "cosh"):
        xs = (steps(-712, 712, 0.01) + steps(-30, 30, 1e-3) + logspace(DENORM_MIN, 1.0, 4000, True)
              + around(709.78, 2000) + around(-709.78, 2000) + around(SINH_X_MAX, 2000) + around(-SINH_X_MAX, 2000) + around(710.4758, 500) + around(-710.4758, 500)
              + random_bits(50_000, 21) + uniform(-711, 711, 100_000, 22) + denormals(500))
    elif function == "exp":
        xs = (steps(-750, 710, 0.01) + around(709.782712893384, 1000) + around(-708.3964185322641, 2000)
              + around(-744.4400719213812, 1000) + around(-745.1332191019412, 1000) + around(0.0, 1000)
              + logspace(DENORM_MIN, 1.0, 4000, True) + random_bits(50_000, 31) + uniform(-750, 710, 100_000, 32))
    elif function in ("ln", "log10"):
        xs = (logspace(DENORM_MIN, DBL_MAX, 200_000, False) + around(1.0, 5000) + denormals(2000)
              + [y for k in range(-20, 23) for y in around(10.0 ** k, 50)]
              + [y for k in range(-1074, 1024, 7) for y in around(math.ldexp(1.0, k), 5)]
              + random_bits(50_000, 41, positive=True) + uniform(0.0, 10.0, 100_000, 42))
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
    return out


def pairs_for_bridge() -> list[tuple[float, float]]:
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
    return out


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
    return out


# ── measuring ────────────────────────────────────────────────────────────────────────────────────

def _measure_chunk(args) -> dict:
    spec, xs = args
    mp = _mp()
    fn, ref, domain = FLOAT_FUNCS[spec["function"]], reference(spec["function"]), spec["domain"]
    res = {"examined": 0, "vacuous": 0, "unmeasurable": 0, "violations": 0, "worst": []}
    worst = []
    for x in xs:
        if not in_domain(domain, x):
            res["vacuous"] += 1
            continue
        y = fn(x)
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


def _bridge_chunk(ps, neg=ieee_neg) -> dict:
    """`FPBridge`'s fields over pairs. `neg` is a parameter so --self-test can hand it a negation that is not
    IEEE's and require both negation checks to fire."""
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
                res["unmeasurable"] += 1
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


def _rounding_chunk(items) -> dict:
    res = {"examined": 0, "vacuous": 0, "unmeasurable": 0, "violations": 0, "worst": []}
    worst = []
    two53 = 1 << 53
    for m, e in items:
        x = Fraction(m) * (Fraction(2) ** e)
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
        worst.append((float(err / bound), f"{m:x}p{e}"))
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
    if kind == "bridge":
        ps = pairs_for_bridge()
        total = {"examined": 0, "vacuous": 0, "unmeasurable": 0, "violations": 0, "worst": [], "neg_inexact": 0,
                 "neg_not_bitflip": 0}
        for part in pool.map(_bridge_chunk, [ps[i:i + 10_000] for i in range(0, len(ps), 10_000)]):
            neg = total["neg_inexact"] + part["neg_inexact"]
            flip = total["neg_not_bitflip"] + part["neg_not_bitflip"]
            total = _merge(total, part)
            total["neg_inexact"], total["neg_not_bitflip"] = neg, flip
        total["inputs"] = len(ps)
        if total["neg_inexact"]:
            total["violations"] += total["neg_inexact"]
        return total
    if kind == "rounding":
        items = reals_for_rounding()
        total = {"examined": 0, "vacuous": 0, "unmeasurable": 0, "violations": 0, "worst": []}
        for part in pool.map(_rounding_chunk, [items[i:i + 10_000] for i in range(0, len(items), 10_000)]):
            total = _merge(total, part)
        total["inputs"] = len(items)
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
#: (hypotheses, bound) -> (domain, bound kind, constant), each hypothesis and bound exactly as the normalised
#: source spells it. This IS the "tightest instantiation" argument of the module docstring, made closed: a
#: hypothesis set or bound not listed here is unreadable, and the run fails rather than guessing.
READINGS = {
    (_H({"a.isFinite = true"}), "u + u"): ("finite", "c_u", "2"),
    (_H({"a.isFinite = true"}), "u"): ("finite", "c_u", "1"),
    (_H({"abs (realToR a) ≤ R"}), "u"): ("finite", "c_u", "1"),                       # R free: every finite a
    (_H({"realToR a ≤ hi"}), "u * exp hi"): ("finite", "u_exp_x", None),              # hi = x
    (_POS, "u * (abs (log lo) + abs (log hi))"): ("positive", "u_abs_log_x", None),   # lo or hi at 1
    (_POS, "u * (abs (log10 lo) + abs (log10 hi))"): ("positive", "u_abs_log10_x", None),
    (_H({"0 ≤ realToR a", "realToR a ≤ hi"}), "u * sqrt hi"): ("nonneg", "u_sqrt_x", None),
    (_H({"R < 1", "abs (realToR a) ≤ R"}), "u * (pi / (1 + 1))"): ("open_unit", "u_pi_half", None),
    (_H({"R < 1", "abs (realToR a) ≤ R"}), "u * pi"): ("open_unit", "u_pi", None),
    (_H({"0 ≤ R", "R < pi / (1 + 1)", "abs (realToR a) ≤ R"}), "u * tan R"): ("tan_open", "u_abs_tan_x", None),
    (_H({"abs (realToR a) ≤ R"}), "u * cosh R"): ("finite", "u_cosh_x", None),       # R = |x|
}

READING_KEYS = ("kind", "function", "domain", "bound", "c", "eps")


def derive_reading(statement: str | None) -> dict | None:
    """The reading a statement's text determines, or None when the harness cannot read it."""
    if statement is None:
        return None
    s = " ".join(statement.split())
    if s in (": Float → MachLib.Real", ": Real → Float", ": MachLib.Real"):
        return {"kind": "declaration"}
    if s == ": FPBridge realToR":
        return {"kind": "bridge"}
    if s == ": ∀ M x : Real, 0 ≤ M → abs x ≤ M → abs (realToR (floatOfR x) - x) ≤ u * M":
        return {"kind": "rounding"}
    m = re.fullmatch(r": ∀ (?:\([^)]*\) )*(?:\(a : Float\)|a : Float), (.*)", s)
    if m is None:
        return None
    parts = m.group(1).split(" → ")
    concl, hyps = parts[-1], _H(parts[:-1])
    c = re.fullmatch(r"abs \(realToR \(stdI1 leanPrims \.(\w+) a\) - (\w+) \(realToR a\)\) ≤ (.+)", concl)
    if c is None or CTOR_REAL.get(c.group(1)) != c.group(2):
        return None
    fn, bound_text = c.group(1), c.group(3)
    eps = re.fullmatch(r"real_\w+_eps", bound_text)
    if eps and not hyps:
        return {"kind": "existential-eps", "function": fn, "domain": "finite", "bound": "sup",
                "eps": "Certcom." + bound_text}
    reading = READINGS.get((hyps, bound_text))
    if reading is None:
        return None
    domain, bound, const = reading
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
    "RoundsW": "(w fl e : Real) : Prop := ∃ δ : Real, -w ≤ δ ∧ δ ≤ w ∧ fl = e * (1 + δ)",
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


def source_definitions(foundations: pathlib.Path) -> dict[str, str | None]:
    out: dict[str, str | None] = {"FPBridge": None, "RoundsW": None}
    bridge = _strip_lean_comments((foundations / "MachLib" / "FloatRealBridge.lean").read_text(encoding="utf-8"))
    m = re.search(r"^structure FPBridge \(toR : Float → MachLib\.Real\) : Prop where\n((?:[ \t]*\n|[ \t]+\S.*\n)+)",
                  bridge, re.MULTILINE)
    if m:
        out["FPBridge"] = " | ".join(" ".join(line.split()) for line in m.group(1).splitlines() if line.strip())
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
        line = (f"  {name}: {s['examined']} examined of {s['inputs']} ({s['vacuous']} outside its hypotheses, "
                f"{s['unmeasurable']} with a non-finite result); ")
        if kind == "existential-eps":
            line += f"sup |error| = {s['max']} at {describe_argmax(s)}: bounded, so an eps exists"
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
