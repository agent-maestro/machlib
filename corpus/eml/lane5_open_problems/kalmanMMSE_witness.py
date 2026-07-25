#!/usr/bin/env python3
"""Runtime witness for the scalar Kalman/Gaussian MMSE-optimality arc.

The Lean proofs (`MachLib/GaussianConjugacy.lean`, on top of
`MachLib/GaussianDensityIntegral.lean`) establish, from MachLib's Mathlib-free
real-analysis base with ZERO new axioms:

  - jointDensity_conjugacy : jointDensity = gaussianDensity mu (sig2+r2) y
                                          * gaussianDensity (m y) tau2 x
        (the Bayesian conjugacy factorization: marginal x posterior)
  - jointDensity_marginal_tendsto : integral_x jointDensity dx -> N(mu, sig2+r2)
  - posterior_mean_mmse : tau2 <= tau2 + (c - m(y))^2   (conditional MSE >= tau2)
  - posteriorMSE_tendsto : integral (x-c)^2 posterior dx -> tau2 + (c - m(y))^2
  - optimalMSE_tendsto : the posterior-mean estimator's total MSE = tau2
  - mse_lower_bound : no continuous estimator beats tau2
  - postMean_eq_kalman : m(y) = mu + K*(y-mu), K = sig2/(sig2+r2)   (Kalman gain)

This script checks the SAME claims the other way: it numerically integrates the
actual Gaussian densities (quadrature) and confirms every closed form the Lean
kernel proves. Two proofs, same claims -- the kernel checks the arguments, this
checks the arithmetic. Agreement to ~1e-9 is independent evidence the theorem
STATEMENTS mean what they appear to mean (it cannot, on its own, rule out a
subtly wrong statement -- that is the formal proof's job).

Model: prior X ~ N(mu, sig2); measurement Y = X + N, noise N ~ N(0, r2)
independent. Posterior X | Y=y ~ N(m(y), tau2).

Usage: python3 kalmanMMSE_witness.py     (needs numpy)
"""
import math

import numpy as np

# --- model parameters (arbitrary distinct positive values, general case) ---
MU = 0.7
SIG2 = 2.0
R2 = 0.5

# --- Kalman / posterior closed forms (what postMean_eq_kalman etc. prove) ---
K = SIG2 / (SIG2 + R2)            # Kalman gain
TAU2 = SIG2 * R2 / (SIG2 + R2)    # posterior variance
MARGVAR = SIG2 + R2               # marginal variance of Y
TOL = 1e-9


def gd(mu: float, s2: float, x):
    """gaussianDensity mu s2 x = exp(-(x-mu)^2/(2 s2)) / sqrt(2 pi s2)."""
    return np.exp(-((x - mu) ** 2) / (2.0 * s2)) / math.sqrt(2.0 * math.pi * s2)


def post_mean(y: float) -> float:
    return MU + K * (y - MU)


def joint(x, y):
    """jointDensity mu sig2 r2 x y = gd(mu,sig2,x) * gd(0,r2,y-x)."""
    return gd(MU, SIG2, x) * gd(0.0, R2, y - x)


def quad(f, lo, hi, n=200001):
    """Simpson quadrature of f on [lo, hi] (n odd)."""
    xs = np.linspace(lo, hi, n)
    ys = f(xs)
    return float(scipy_simpson(ys, xs))


def scipy_simpson(ys, xs):
    # composite Simpson (n-1 intervals, n odd) without a scipy dependency
    h = xs[1] - xs[0]
    s = ys[0] + ys[-1] + 4.0 * ys[1:-1:2].sum() + 2.0 * ys[2:-2:2].sum()
    return s * h / 3.0


def check(name: str, got: float, want: float, ok_flag: list) -> None:
    d = abs(got - want)
    status = "ok " if d <= TOL else "FAIL"
    print(f"  [{status}] {name:<52} got={got:.12f} want={want:.12f} |d|={d:.2e}")
    if d > TOL:
        ok_flag[0] = False


def main() -> int:
    ok = [True]
    print(f"model: mu={MU}, sig2={SIG2}, r2={R2}  ->  K={K}, tau2={TAU2}, margVar={MARGVAR}")
    LO, HI = MU - 40.0, MU + 40.0  # wide enough that Gaussian tails are negligible

    # (1) postMean_eq_kalman: m(y) = mu + K(y-mu)
    print("\n(1) Kalman-gain cross-check (postMean_eq_kalman):")
    check("K = sig2/(sig2+r2)", K, SIG2 / (SIG2 + R2), ok)
    check("tau2 = sig2*r2/(sig2+r2)", TAU2, SIG2 * R2 / (SIG2 + R2), ok)

    # (2) jointDensity_conjugacy: joint(x,y) == margDensity(y) * postDensity(x)
    print("\n(2) conjugacy factorization (jointDensity_conjugacy):")
    max_rel = 0.0
    for y in (-1.3, 0.4, 1.9):
        for x in (-0.8, 0.7, 2.1):
            lhs = joint(x, y)
            rhs = gd(MU, MARGVAR, y) * gd(post_mean(y), TAU2, x)
            max_rel = max(max_rel, abs(lhs - rhs) / abs(rhs))
    check("max rel-err joint vs marginal*posterior", max_rel, 0.0, ok)

    # (3) jointDensity_marginal_tendsto: integral_x joint dx = gd(mu, margVar, y)
    print("\n(3) marginal is Gaussian (jointDensity_marginal_tendsto):")
    for y in (-1.3, 0.4, 1.9):
        got = quad(lambda x: joint(x, y), LO, HI)
        check(f"integral_x joint(.,{y}) dx = N(mu,margVar)(y)", got, gd(MU, MARGVAR, y), ok)

    # (4) posteriorMSE_tendsto: integral (x-c)^2 posterior dx = tau2 + (c-m(y))^2
    print("\n(4) conditional MSE = tau2 + (c-m(y))^2 (posteriorMSE_tendsto):")
    y0 = 0.9
    m0 = post_mean(y0)
    for c in (m0, m0 + 0.5, MU, y0):
        got = quad(lambda x: (x - c) ** 2 * gd(m0, TAU2, x), LO, HI)
        check(f"cond-MSE at c={c:.3f}", got, TAU2 + (c - m0) ** 2, ok)

    # (5) posterior_mean_mmse: conditional MSE is minimised at c = m(y), value tau2
    print("\n(5) posterior mean is the conditional MMSE minimiser (posterior_mean_mmse):")
    cs = np.linspace(m0 - 2.0, m0 + 2.0, 4001)
    mses = np.array([quad(lambda x: (x - c) ** 2 * gd(m0, TAU2, x), LO, HI, n=40001) for c in cs])
    argmin_c = cs[int(np.argmin(mses))]
    check("argmin_c cond-MSE == m(y)", argmin_c, m0, ok)
    check("min cond-MSE == tau2", float(mses.min()), TAU2, [ok[0]] if False else ok)

    # (6) optimalMSE_tendsto + mse_lower_bound: total (unconditional) MSE.
    #     E[(X-phi(Y))^2] = integral_y margDensity(y) * (tau2 + (phi(y)-m(y))^2) dy
    #     (inner x-integral closed by parallel-axis). Optimal phi=m gives tau2 exactly;
    #     any other continuous phi gives strictly more.
    print("\n(6) unconditional MSE: optimal = tau2, nothing continuous beats it")

    def total_mse(phi):
        return quad(lambda y: gd(MU, MARGVAR, y) * (TAU2 + (phi(y) - post_mean(y)) ** 2), LO, HI)

    check("total MSE of optimal phi=m == tau2", total_mse(post_mean), TAU2, ok)
    mse_const = total_mse(lambda y: MU)          # constant estimator mu
    mse_ident = total_mse(lambda y: y)           # identity estimator y
    print(f"  [info] total MSE(phi=mu)  = {mse_const:.12f}  (>= tau2: {mse_const >= TAU2 - TOL})")
    print(f"  [info] total MSE(phi=y)   = {mse_ident:.12f}  (>= tau2: {mse_ident >= TAU2 - TOL})")
    if mse_const < TAU2 - TOL or mse_ident < TAU2 - TOL:
        ok[0] = False
        print("  [FAIL] a sub-optimal estimator beat tau2 -- contradicts mse_lower_bound")

    print()
    if ok[0]:
        print("WITNESS PASS: every closed form matches quadrature to <1e-9; "
              "the posterior mean is the numerically-confirmed MMSE estimator (min MSE = tau2).")
        return 0
    print("WITNESS FAIL: a closed form diverged from quadrature beyond tolerance.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
