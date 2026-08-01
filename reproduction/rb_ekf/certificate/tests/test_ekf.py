"""EKF step assembled from the COMPILER-derived Jacobian + the shared-MAC linear-Kalman math.

Chunk 2 of the EKF frontier (docs/ekf_compiler_jacobian.md): a Q16.16 EKF for the nonlinear
measurement h(x) = z^2 = [x0^2 - x1^2, 2 x0 x1]. The measurement Jacobian H is NOT hand-coded —
it is produced by the compiler (lang.optimizer.autodiff.jacobian_matrix) and evaluated in Q16.16
here. Tests: (a) the compiler H equals the analytic Jacobian in fixed-point at sample states;
(b) the EKF, assembled on that Jacobian + the certified 2x2 inverse / matmul / Joseph, TRACKS a
nonlinear-measurement trajectory (estimate converges, trace(P) shrinks).
"""
from __future__ import annotations

from lang.optimizer.autodiff import jacobian_matrix
from lang.parser import parse_source
from lang.parser.ast_nodes import NodeKind

# ── Q16.16 fixed-point ──
FRAC = 16
ONE_Q = 1 << FRAC
TWO_Q = 2 << FRAC
MASK32 = (1 << 32) - 1
LIN_C1 = (24 << FRAC) // 17
LIN_C2 = (8 << FRAC) // 17


def s32(x):
    x &= MASK32
    return x - (1 << 32) if x & (1 << 31) else x


def d2q(d):
    return s32(int(round(d * 65536.0)))


def q2d(x):
    return s32(x) / 65536.0


def qmul(a, b):
    return s32((s32(a) * s32(b)) >> FRAC)


def _recip(b):
    def ie(xin):
        xin = s32(xin); sign = 1 if (xin & (1 << 31)) else 0
        absv = ((~xin) + 1) & MASK32 if sign else (xin & MASK32)
        lb = 0
        for i in range(32):
            if (absv >> i) & 1:
                lb = i
        tf = 2 * FRAC
        # DEFECT FIX 2026-07-27 (eml_reciprocal.v): seed scale HALVED so the shift can never
        # reach the sign bit; the two multiplies by it truncate by FRAC-1 to compensate
        # (algebraically identical). |b| <= 2 LSB saturates: 1/|b| needs 2^31 or 2^32.
        if absv <= (1 << (tf - 32 + 1)):
            return s32(-(1 << (32 - 1))) if sign else s32(~(1 << (32 - 1)) & MASK32)
        if (tf > lb) and (tf - lb) < 32:
            y0e = s32(1 << (tf - lb - 1))
            y0 = s32((y0e * s32(LIN_C1 - qmul(LIN_C2, s32((absv * y0e) >> (FRAC - 1))))) >> (FRAC - 1))
            return s32(-y0) if sign else y0
        return s32(1 << 31) if (tf > lb and sign) else (s32(~(1 << 31) & MASK32) if tf > lb else 1)
    y = ie(b)
    for _ in range(2):
        y = qmul(y, s32(TWO_Q - qmul(b, y)))
    return y


# ── 2x2 matrix ops (per-product Q16.16) ──
def mm(X, Y):
    return [[s32(qmul(X[i][0], Y[0][j]) + qmul(X[i][1], Y[1][j])) for j in range(2)] for i in range(2)]


def mv(X, v):
    return [s32(qmul(X[0][0], v[0]) + qmul(X[0][1], v[1])),
            s32(qmul(X[1][0], v[0]) + qmul(X[1][1], v[1]))]


def T(M):
    return [[M[0][0], M[1][0]], [M[0][1], M[1][1]]]


def add(X, Y):
    return [[s32(X[i][j] + Y[i][j]) for j in range(2)] for i in range(2)]


def inv(S):
    r = _recip(s32(qmul(S[0][0], S[1][1]) - qmul(S[0][1], S[1][0])))
    return [[qmul(S[1][1], r), qmul(s32(-S[0][1]), r)], [qmul(s32(-S[1][0]), r), qmul(S[0][0], r)]]


# ── a tiny Q16.16 evaluator for the compiler-derived Jacobian AST ──
def eval_q16(node, env):
    k = node.kind
    if k == NodeKind.LITERAL:
        return d2q(float(node.value))
    if k == NodeKind.VAR:
        return env[node.value]
    if k == NodeKind.UNARYOP and node.value == "-":
        return s32(-eval_q16(node.children[0], env))
    if k == NodeKind.BINOP:
        a, b = eval_q16(node.children[0], env), eval_q16(node.children[1], env)
        if node.value == "+":
            return s32(a + b)
        if node.value == "-":
            return s32(a - b)
        if node.value == "*":
            return qmul(a, b)
        if node.value == "/":
            return qmul(a, _recip(b))
    raise AssertionError(f"eval_q16: unsupported node {k}/{node.value}")


# ── the nonlinear measurement + its compiler Jacobian ──
_H_SRC = ("fn h(x0: Real, x1: Real) -> (Real, Real) "
          "{ (x0*x0 - x1*x1, 2.0*x0*x1) }")
_H_FN = parse_source(f"module t;\n{_H_SRC}", "<t>").functions[0]
_H_JAC = jacobian_matrix(_H_FN)                      # compiler-derived H, as AST


def _H_at(x0q, x1q):
    """Evaluate the COMPILER Jacobian in Q16.16 at state (x0,x1)."""
    env = {"x0": x0q, "x1": x1q}
    return [[eval_q16(_H_JAC[i][j], env) for j in range(2)] for i in range(2)]


def _h_at(x0q, x1q):
    return [s32(qmul(x0q, x0q) - qmul(x1q, x1q)), s32(2 * qmul(x0q, x1q))]


def test_compiler_jacobian_matches_analytic_fixedpoint():
    """The compiler-derived H, evaluated in Q16.16, equals the analytic [[2x0,-2x1],[2x1,2x0]]."""
    for x0, x1 in [(2.0, 3.0), (1.5, -0.5), (0.25, 1.75), (-1.0, 2.0)]:
        x0q, x1q = d2q(x0), d2q(x1)
        got = _H_at(x0q, x1q)
        want = [[d2q(2 * x0), d2q(-2 * x1)], [d2q(2 * x1), d2q(2 * x0)]]
        assert got == want, (x0, x1, got, want)


def _ekf_step(x, P, z, Q, R):
    """One EKF step for h(x)=z^2, F=I. H is the compiler Jacobian (evaluated in Q16.16)."""
    Pm = add(P, Q)                                   # predict: x-=x (F=I), P- = P+Q
    H = _H_at(x[0], x[1])                            # linearize (compiler Jacobian)
    hx = _h_at(x[0], x[1])
    y = [s32(z[0] - hx[0]), s32(z[1] - hx[1])]       # innovation
    S = add(mm(mm(H, Pm), T(H)), R)                  # S = H P- H^T + R
    K = mm(mm(Pm, T(H)), inv(S))                     # K = P- H^T S^-1
    xn = [s32(x[0] + mv(K, y)[0]), s32(x[1] + mv(K, y)[1])]
    KH = mm(K, H)
    A = [[s32(ONE_Q - KH[0][0]), s32(-KH[0][1])], [s32(-KH[1][0]), s32(ONE_Q - KH[1][1])]]
    Pn = add(mm(mm(A, Pm), T(A)), mm(mm(K, R), T(K)))   # Joseph with KH
    return xn, Pn


def test_ekf_tracks_nonlinear_measurement():
    """The EKF (compiler Jacobian + shared math) tracks a target seen through h(x)=z^2: the
    estimate converges to the truth and the covariance trace shrinks."""
    truth = (2.0, 3.0)
    zt = [d2q(truth[0] ** 2 - truth[1] ** 2), d2q(2 * truth[0] * truth[1])]   # h(truth) = (-5, 12)
    Q = [[d2q(0.001), 0], [0, d2q(0.001)]]
    R = [[d2q(0.05), 0], [0, d2q(0.05)]]
    x = [d2q(1.6), d2q(2.6)]                          # initial estimate near the truth (EKF is local)
    P = [[d2q(0.5), 0], [0, d2q(0.5)]]
    tr0 = q2d(P[0][0]) + q2d(P[1][1])
    for _ in range(25):
        x, P = _ekf_step(x, P, zt, Q, R)
    err = ((q2d(x[0]) - truth[0]) ** 2 + (q2d(x[1]) - truth[1]) ** 2) ** 0.5
    tr = q2d(P[0][0]) + q2d(P[1][1])
    assert err < 0.05, (q2d(x[0]), q2d(x[1]), err)
    assert tr < 0.5 * tr0, (tr, tr0)
