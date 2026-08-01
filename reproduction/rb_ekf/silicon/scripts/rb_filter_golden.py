#!/usr/bin/env python3
"""Q16.16 golden for the RANGE-BEARING radar EKF -- the trajectory the silicon is judged against.

h(x) = (range, bearing) = (sqrt(x0^2 + x1^2), atan(x1/x0)), with H = dh/dx DERIVED BY THE COMPILER
(lang.optimizer.autodiff) and normalised to lowest terms before lowering, giving the textbook

    H = [[ x0/r,    x1/r  ],
         [ -x1/r^2, x0/r^2 ]]        r = sqrt(x0^2 + x1^2)

SELF-CONTAINED ON PURPOSE. This runs on the bench box, which has no forge checkout on its path (and
whose checkout has diverged before). Every kernel below is a transcription of the shipped `.v`,
proven bit-exact against it in forge `tests/test_qkernels_match_rtl.py`:

    q_sqrt_wide   eml_sqrt_wide.v    restoring digit-by-digit sqrt, error < 1 ULP by construction
    q_atan_wide   eml_atan_wide.v    4-term Taylor + range fold atan(x)=sign(x)*pi/2-atan(1/x)
    recip         eml_reciprocal.v   Newton-Raphson, the certified kernel the Kalman anchors use

TWO VERILOG DETAILS that are easy to get wrong in Python and are the reason this is a transcription
rather than a re-implementation:
  * `>>>` is an ARITHMETIC shift -- floor, toward -inf. Python's `>>` matches, so shifts transcribe.
  * `/` TRUNCATES toward zero; Python's `//` FLOORS. They differ only on negatives -- which is
    exactly where the range-folded atan spends its time. Hence `_tdiv`.

GEOMETRY. Truth (2, 5) from prior (3, 4), so |x1/x0| runs 1.33 -> 2.07: the bearing argument is
ABOVE 1 for the whole track, which means this anchor exercises eml_atan_wide's RANGE FOLD on real
fabric -- the path that does not exist in the polynomial anchors and the reason the wide kernel was
written. It deliberately stays clear of |x1/x0| ~ 1, where the 4-term series is at its worst
(3.5 deg); that band-edge behaviour is characterised by exhaustive enumeration in
test_eml_atan_wide_certificate.py, which is stronger evidence than a single silicon point would be.

Run `python rb_filter_golden.py` to print the trajectory + the z ROM to paste into the anchor top.
"""
from __future__ import annotations

import math

FRAC = 16
WIDTH = 32
ONE_Q = 1 << FRAC
TWO_Q = 2 << FRAC
MASK32 = (1 << 32) - 1
HALF_PI_Q = 102944                      # round(pi/2 * 65536), as eml_atan_wide's localparam

# eml_reciprocal's linear-seed constants -- taken from the RTL, NOT recalled. Getting these wrong
# is silent: the filter still converges, just to slightly different words, so only a bit-exact
# comparison catches it. (First cut of this file had them 2x too large and the whole trajectory
# drifted; the end-to-end UART sim is what refused it.)
LIN_C1 = 0x00016969
LIN_C2 = 0x00007878


def s32(x):
    x &= MASK32
    return x - (1 << 32) if x & (1 << 31) else x


def d2q(d):
    return s32(int(round(d * (1 << FRAC))))


def q2d(x):
    return s32(x) / (1 << FRAC)


def qmul(a, b):
    return s32((s32(a) * s32(b)) >> FRAC)


def _tdiv(a, b):
    """Verilog signed division: truncate toward zero (Python's // floors)."""
    if b == 0:
        return 0
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b >= 0) else -q


# ── eml_reciprocal.v ─────────────────────────────────────────────────────────

def _init_est(xin):
    """Seed for eml_reciprocal, MIRRORING the 2026-07-27 defect fix in eml_reciprocal.v.

    The seed scale is 2^(2F-lb-1) -- HALF the old 2^(2F-lb) -- and the two multiplies by it
    truncate by FRAC-1 instead of FRAC. The product is identical; what changes is that the
    constant can no longer reach bit WIDTH-1. The old form gave `1 << 31` at lb = 1, i.e. a
    NEGATIVE seed, so recip(3 LSB) came out -1310718717 instead of 1431655765.

    |b| <= 2 LSB saturates: 1/|b| would need 2^31 or 2^32 and is not representable.
    Verified against the RTL in Verilator: 6 inputs change (b = +/-1, +/-2, +/-3), and
    ZERO of 57155 swept inputs at |b| >= 4 change.
    """
    xin = s32(xin)
    sign = 1 if (xin & (1 << 31)) else 0
    absv = ((~xin) + 1) & MASK32 if sign else (xin & MASK32)
    floor_av = 1 << (2 * FRAC - WIDTH + 1)          # = 2 for Q16.16/32-bit
    if absv <= floor_av:
        return s32(-(1 << (WIDTH - 1))) if sign else s32(~(1 << (WIDTH - 1)) & MASK32)
    lb = 0
    for i in range(WIDTH):
        if (absv >> i) & 1:
            lb = i
    y0e = s32(1 << (2 * FRAC - lb - 1))             # <= 2^30, never the sign bit
    m   = s32((absv * y0e) >> (FRAC - 1))
    y0  = s32((y0e * s32(LIN_C1 - qmul(LIN_C2, m))) >> (FRAC - 1))
    return s32(-y0) if sign else y0


def _recip_saturates(b):
    """True when eml_reciprocal saturates instead of computing -- |b| <= 2 LSB."""
    av = abs(s32(b))
    return av <= (1 << (2 * FRAC - WIDTH + 1))


def recip(b):
    y0 = _init_est(b)
    if _recip_saturates(b):
        return y0                    # saturation BYPASSES the NR (see eml_reciprocal.v)
    y = y0
    for _ in range(2):
        y = qmul(y, s32(TWO_Q - qmul(b, y)))
    return y


# ── eml_sqrt_wide.v (restoring, exact to < 1 ULP) ────────────────────────────

def q_sqrt_wide(x):
    x = s32(x)
    if x <= 0:
        return 0
    rad, rem, root, nb = x << FRAC, 0, 0, 2 * WIDTH
    for _ in range(WIDTH):
        rem = ((rem << 2) | ((rad >> (nb - 2)) & 0b11)) & ((1 << nb) - 1)
        rad = (rad << 2) & ((1 << nb) - 1)
        trial = (root << 2) | 1
        if rem >= trial:
            rem -= trial
            root = (root << 1) | 1
        else:
            root <<= 1
    return s32(root)


# ── eml_atan_wide.v (4-term Taylor + range fold) ─────────────────────────────

_ONE_THIRD, _ONE_FIFTH, _ONE_SEVENTH = ONE_Q // 3, ONE_Q // 5, ONE_Q // 7


def _atan_taylor(u):
    x1 = s32(u)
    x2 = qmul(x1, x1)
    x3 = qmul(x2, x1)
    x4 = qmul(x2, x2)
    x5 = qmul(x4, x1)
    x7 = qmul(x4, x3)
    return s32(x1 - qmul(x3, _ONE_THIRD) + qmul(x5, _ONE_FIFTH) - qmul(x7, _ONE_SEVENTH))


def q_atan_wide(x):
    x = s32(x)
    fold = x > ONE_Q or x < -ONE_Q
    acc = _atan_taylor(recip(x) if fold else x)
    if not fold:
        return acc
    return s32((-HALF_PI_Q if x < 0 else HALF_PI_Q) - acc)


# ── h and the compiler-derived H, in the emitter's lowering order ────────────

def _h(x0, x1):
    """(range, bearing) -- GENERATED from the compiler's AST, not hand-derived.

    See the module note on why: a hand-written reference drifts from the emitter, and the drift is
    invisible until a bit-exact comparison. The first cut of this file wrote H's negation as
    `-qmul(x1, inv_r2)` where the compiler emits `qmul(-x1, inv_r2)` -- identical in the reals,
    1 ULP apart under truncation, and the whole trajectory diverged from step 0.
    """
    r2 = s32(qmul(x0, x0) + qmul(x1, x1))
    return [q_sqrt_wide(r2), q_atan_wide(qmul(x1, recip(x0)))]


def _H(x0, x1):
    """H = dh/dx, in the emitter's exact lowering order.

    Mathematically [[x0/r, x1/r], [-x1/r^2, x0/r^2]]; structurally each entry is
    `qmul(num, qmul(1.0, recip(den)))` because `cancel` leaves x0*(r^2)^(-1/2) and the constant-pow
    lowering turns the negative power into 1.0/den. The `qmul(1.0, .)` is exact (65536*r >> 16 == r)
    and kept so this mirrors the emitted datapath rather than an algebraically tidied version of it.
    """
    r2 = s32(qmul(x0, x0) + qmul(x1, x1))
    inv_r = qmul(d2q(1.0), recip(q_sqrt_wide(r2)))
    inv_r2 = qmul(d2q(1.0), recip(r2))
    return [[qmul(x0, inv_r), qmul(x1, inv_r)],
            [qmul(s32(-x1), inv_r2), qmul(x0, inv_r2)]]


# ── 2x2 helpers + the EKF step ───────────────────────────────────────────────

def _mm(X, Y):
    return [[s32(qmul(X[i][0], Y[0][j]) + qmul(X[i][1], Y[1][j])) for j in range(2)]
            for i in range(2)]


def _T(M):
    return [[M[0][0], M[1][0]], [M[0][1], M[1][1]]]


def _add(X, Y):
    return [[s32(X[i][j] + Y[i][j]) for j in range(2)] for i in range(2)]


def _mv(X, v):
    return [s32(qmul(X[0][0], v[0]) + qmul(X[0][1], v[1])),
            s32(qmul(X[1][0], v[0]) + qmul(X[1][1], v[1]))]


def _inv(S):
    r = recip(s32(qmul(S[0][0], S[1][1]) - qmul(S[0][1], S[1][0])))
    return [[qmul(S[1][1], r), qmul(s32(-S[0][1]), r)],
            [qmul(s32(-S[1][0]), r), qmul(S[0][0], r)]]


def step(x, P, z, Q, R):
    """One EKF step: predict -> compiler-linearize -> measurement update -> Joseph -> commit."""
    Pm = _add(P, Q)
    H = _H(x[0], x[1])
    hx = _h(x[0], x[1])
    y = [s32(z[0] - hx[0]), s32(z[1] - hx[1])]
    S = _add(_mm(_mm(H, Pm), _T(H)), R)
    K = _mm(_mm(Pm, _T(H)), _inv(S))
    Ky = _mv(K, y)
    xn = [s32(x[0] + Ky[0]), s32(x[1] + Ky[1])]
    KH = _mm(K, H)
    A = [[s32(ONE_Q - KH[0][0]), s32(-KH[0][1])],
         [s32(-KH[1][0]), s32(ONE_Q - KH[1][1])]]
    Pn = _add(_mm(_mm(A, Pm), _T(A)), _mm(_mm(K, R), _T(K)))
    return xn, Pn


# ── the anchor's scenario ────────────────────────────────────────────────────

TRUTH = (2.0, 5.0)          # target; |x1/x0| = 2.5, so the bearing argument FOLDS
X0 = [3.0, 4.0]             # prior estimate (|x1/x0| = 1.33, also folded)
P0 = [[0.5, 0.1], [0.1, 0.5]]      # NON-diagonal, as in the sibling anchors
Q = [[0.001, 0.0], [0.0, 0.001]]
# Measurement noise: range sigma 0.141 (var 0.02), bearing sigma 0.045 rad = 2.6 deg (var 0.002).
#
# The two entries DIFFER because the two components of h have different units -- a property of the
# range-bearing model that the polynomial anchors never had (there both outputs are lengths, so a
# single variance is fine). Using one variance for both here would model a ~13 deg bearing sensor;
# the filter rightly distrusts it and barely moves.
#
# Chosen for a VISIBLE convergence curve rather than the smallest final error. Much tighter R
# (var 0.0025/0.0001) converges in ONE step and then plateaus for seven -- and worse, P collapses
# so fast that the Kalman gain drops below the point where the remaining innovation can move the
# estimate, freezing it at a biased (2.13, 5.13). Eight nearly-identical steps is a weak acceptance
# signal; a monotone curve over all eight is a strong one, and it exercises the kernels at eight
# genuinely different linearisation points.
R = [[0.02, 0.0], [0.0, 0.002]]
N_STEPS = 8

# READ THIS BEFORE CALLING STEP 7 A REGRESSION.
# The track converges -- err 0.306 -> 0.003 over 24 steps -- but trace(P) carries a PERIODIC
# QUANTISATION WOBBLE (steps 7, 14, 19: P roughly doubles for one step, err ticks up, then both
# resume falling). It is a fixed-point artifact of the covariance recursion as P gets small, not
# divergence, and the anchor's eighth step lands exactly on one.
#
# Kept rather than tuned away, for two reasons. It is real behaviour of this arithmetic and hiding
# it by shifting the geometry would be dishonest. And it makes the anchor a STRONGER test: the
# fabric has to reproduce a quantisation artifact bit-for-bit, which is a sharper check than
# reproducing a smooth curve -- a design that were subtly wrong would smooth it or move it.
#
# The acceptance criterion is bit-exactness to this golden, NOT monotone error.


def z_rom():
    """The measurement stream: h(truth) held constant, one (z0, z1) per step."""
    z = [d2q(math.hypot(*TRUTH)), d2q(math.atan(TRUTH[1] / TRUTH[0]))]
    return [tuple(z) for _ in range(N_STEPS)]


def trajectory():
    """[(step, x0, x1, p0, p1, p2, p3)] as MASKED 32-bit words -- the state after each measurement.

    Masked, not signed, because that is what the analyzer and the UART decoder compare against: the
    telemetry carries raw hex words. Returning signed ints here makes every NEGATIVE covariance
    off-diagonal miscompare while the positive entries pass -- which reads as "the filter is
    subtly wrong" rather than "the golden's return convention is wrong". Same convention as the
    sibling anchors' goldens.
    """
    x = [d2q(X0[0]), d2q(X0[1])]
    P = [[d2q(v) for v in row] for row in P0]
    Qq = [[d2q(v) for v in row] for row in Q]
    Rq = [[d2q(v) for v in row] for row in R]
    out = []
    for m, z in enumerate(z_rom()):
        x, P = step(x, P, list(z), Qq, Rq)
        out.append((m, x[0] & MASK32, x[1] & MASK32,
                    P[0][0] & MASK32, P[0][1] & MASK32, P[1][0] & MASK32, P[1][1] & MASK32))
    return out


def _main():
    zs = z_rom()
    print("# range-bearing EKF trajectory (Q16.16) -- h(x) = (sqrt(x0^2+x1^2), atan(x1/x0))")
    # R is printed IN FULL, not as "R[0][0] I". It is 10:1 asymmetric (range var vs bearing var)
    # -- the very property this anchor exists to exercise, since h's two components have different
    # units -- and an "R = 0.02 I" label in the shipped golden_trajectory.txt asserted the opposite
    # of what the filter computes. Caught by the bench reading the artifact against the source.
    print(f"# truth {TRUTH}  prior x={X0}  P0(row-major)={[v for r in P0 for v in r]}"
          f"  Q(row-major)={[v for r in Q for v in r]}"
          f"  R(row-major)={[v for r in R for v in r]}  <- R ASYMMETRIC: range var"
          f" {R[0][0]}, bearing var {R[1][1]} (different units)")
    print(f"# z = ({q2d(zs[0][0]):.6f}, {q2d(zs[0][1]):.6f})  "
          f"= (range, bearing) of the truth; bearing arg |x1/x0| = {TRUTH[1]/TRUTH[0]:.3f} -> FOLDS")
    for m, x0, x1, p0, p1, p2, p3 in trajectory():
        err = math.hypot(q2d(x0) - TRUTH[0], q2d(x1) - TRUTH[1])
        print(f"  step {m}: x=({q2d(x0):7.4f},{q2d(x1):7.4f})  err={err:.5f}  "
              f"trace(P)={q2d(p0) + q2d(p3):.5f}  |x1/x0|={q2d(x1) / q2d(x0):.3f}  "
              f"[P={p0 & MASK32:08x} {p1 & MASK32:08x} {p2 & MASK32:08x} {p3 & MASK32:08x}]")
    print("\n# --- z ROM (paste into rb_ekf_anchor_top.v; 2 words/step) ---")
    for m, (z0, z1) in enumerate(zs):
        print(f"            4'd{m}: begin z0=32'h{z0 & MASK32:08X}; z1=32'h{z1 & MASK32:08X}; end")
    print(f"            default: begin z0=32'h{zs[0][0] & MASK32:08X}; "
          f"z1=32'h{zs[0][1] & MASK32:08X}; end")
    print(f"\n# X0 = {[f'{d2q(v) & MASK32:08x}' for v in X0]}  "
          f"P0 = {[f'{d2q(v) & MASK32:08x}' for r in P0 for v in r]}  "
          f"Q = {[f'{d2q(v) & MASK32:08x}' for r in Q for v in r]}  "
          f"R = {[f'{d2q(v) & MASK32:08x}' for r in R for v in r]}")


if __name__ == "__main__":
    _main()
