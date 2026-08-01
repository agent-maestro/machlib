"""Q16.16 models of the shipped RTL kernels, bit-exact to the Verilog.

A fixed-point golden is only worth something if it computes what the fabric computes. These are
transcriptions of the actual `.v` files, not idealised maths -- same normalisation, same truncation,
same iteration count -- so a golden built on them can be compared to hardware bit-for-bit rather
than "to within a tolerance".

Validated against the RTL itself in `test_qkernels_match_rtl.py`; if a kernel changes, that test
fails and these must be re-transcribed.

Two Verilog details that matter and are easy to get wrong in Python:

  * `>>>` on a signed value is an ARITHMETIC shift -- floor, toward negative infinity. Python's `>>`
    on ints does the same, so shifts transcribe directly.
  * `/` on signed values TRUNCATES toward zero, which Python's `//` does NOT (it floors). Hence
    `_tdiv`. Getting this wrong only shows up on negative operands, which is exactly where the
    range-folded atan lives.
"""
from __future__ import annotations

FRAC = 16
ONE = 1 << FRAC
MASK32 = (1 << 32) - 1


def s32(x: int) -> int:
    x &= MASK32
    return x - (1 << 32) if x & (1 << 31) else x


def d2q(v: float) -> int:
    return s32(int(round(v * (1 << FRAC))))


def q2d(q: int) -> float:
    return s32(q) / (1 << FRAC)


def _tdiv(a: int, b: int) -> int:
    """Verilog signed division: truncate toward zero (Python's // floors)."""
    if b == 0:
        return 0
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b >= 0) else -q


def qmul(a: int, b: int) -> int:
    return s32((s32(a) * s32(b)) >> FRAC)


def qdiv(a: int, b: int) -> int:
    """eml_sqrt/eml_sqrt_wide's qdiv: (a << FRAC) / b."""
    if b == 0:
        return 0
    return s32(_tdiv(s32(a) << FRAC, s32(b)))


def q_recip(b: int) -> int:
    """eml_reciprocal (Newton-Raphson), which eml_atan_wide now uses for its range fold.

    Imported lazily from test_ekf so there is ONE model of that kernel -- the one already validated
    against silicon by the polynomial EKF golden -- rather than a second transcription to keep in
    step. Loaded by PATH, not by name: this module is also imported from
    hardware/modules/transcendental/tests/, where `tests/` is not on sys.path.
    """
    global _RECIP
    if _RECIP is None:
        import importlib.util
        import pathlib
        spec = importlib.util.spec_from_file_location(
            "_qk_test_ekf", pathlib.Path(__file__).resolve().parent / "test_ekf.py")
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        _RECIP = mod._recip
    return _RECIP(s32(b))


_RECIP = None


# ── eml_sqrt / eml_sqrt_wide ─────────────────────────────────────────────────

def _sqrt_newton(u: int) -> int:
    """The shared 4-stage core: y0 = u/2 then 3 Newton steps."""
    y = u >> 1
    for _ in range(3):
        y = (y + qdiv(u, y)) >> 1
    return s32(y)


def q_sqrt(x: int) -> int:
    """eml_sqrt.v -- accurate only on [0.25, 4]."""
    return _sqrt_newton(s32(x))


def q_sqrt_wide(x: int, width: int = 32) -> int:
    """eml_sqrt_wide.v -- restoring (digit-by-digit) integer square root, EXACT.

    result = floor(sqrt(x * 2^FRAC)), so the error is below one ULP by construction. No Newton, no
    divide, no valid-input range: the RTL is a compare-subtract per result bit and this is the same
    recurrence in Python.
    """
    x = s32(x)
    if x <= 0:
        return 0
    rad = x << FRAC
    rem = 0
    root = 0
    nb = 2 * width
    for i in range(width):
        rem = ((rem << 2) | ((rad >> (nb - 2)) & 0b11)) & ((1 << nb) - 1)
        rad = (rad << 2) & ((1 << nb) - 1)
        trial = (root << 2) | 1
        if rem >= trial:
            rem -= trial
            root = (root << 1) | 1
        else:
            root <<= 1
    return s32(root)


# ── eml_atan / eml_atan_wide ─────────────────────────────────────────────────

_ONE_THIRD = ONE // 3
_ONE_FIFTH = ONE // 5
_ONE_SEVENTH = ONE // 7
HALF_PI = 102944          # round(pi/2 * 65536), as the RTL localparam


def _atan_taylor(u: int) -> int:
    """The shared 4-term series, staged exactly as the RTL stages it."""
    x1 = s32(u)
    x2 = qmul(x1, x1)
    x3 = qmul(x2, x1)
    x4 = qmul(x2, x2)
    x5 = qmul(x4, x1)
    x7 = qmul(x4, x3)
    return s32(x1 - qmul(x3, _ONE_THIRD) + qmul(x5, _ONE_FIFTH) - qmul(x7, _ONE_SEVENTH))


def q_atan(x: int) -> int:
    """eml_atan.v -- diverges outside |x| <= 1."""
    return _atan_taylor(s32(x))


def q_atan_wide(x: int) -> int:
    """eml_atan_wide.v -- atan(x) = sign(x)*pi/2 - atan(1/x) for |x| > 1.

    The 1/x is eml_reciprocal (NR), not a divide -- see q_recip.
    """
    x = s32(x)
    fold = x > ONE or x < -ONE
    u = q_recip(x) if fold else x
    acc = _atan_taylor(u)
    if not fold:
        return acc
    return s32((-HALF_PI if x < 0 else HALF_PI) - acc)
