#!/usr/bin/env python3
"""Runtime witness for `MachLib.Real.gaussianImproperIntegral_eq_sqrt_pi_div_two`.

The Lean proof (`MachLib/GaussianLaplaceRoute.lean`) establishes
`gaussianImproperIntegral = sqrt pi / 2` via a from-scratch Laplace/Feynman
parameter-differentiation argument, with zero new axioms. This script checks
the SAME claim the other way: numerically integrate exp(-t^2) over [0, T] for
T large enough that the tail is negligible, via Simpson's rule, and compare
against sqrt(pi)/2 computed independently.

Two proofs, same claim -- the Lean kernel checks the argument; this checks
the arithmetic. Agreement to machine precision is not a substitute for the
formal proof (it can't rule out a subtly wrong theorem STATEMENT), but it is
independent evidence that the statement means what it appears to mean.

Usage: python3 gaussianImproperIntegral_witness.py
"""
import math


def gaussian_integral_quadrature(t_max: float, n: int) -> float:
    """Simpson's rule for integral_0^t_max exp(-t^2) dt, n even."""
    h = t_max / n
    total = math.exp(0.0) + math.exp(-t_max * t_max)
    for i in range(1, n):
        t = i * h
        coeff = 4 if i % 2 == 1 else 2
        total += coeff * math.exp(-t * t)
    return total * h / 3.0


def main() -> int:
    target = math.sqrt(math.pi) / 2
    print(f"target (sqrt(pi)/2)          = {target:.15f}")
    ok = True
    for t_max, n in [(6, 6000), (8, 8000), (10, 10000), (12, 12000)]:
        val = gaussian_integral_quadrature(t_max, n)
        diff = abs(val - target)
        print(f"T={t_max:>3}  n={n:>6}  quadrature={val:.15f}  |diff|={diff:.3e}")
        if diff > 1e-12:
            ok = False
    if ok:
        print("WITNESS PASS: quadrature agrees with sqrt(pi)/2 to <1e-12 across all T,n.")
        return 0
    print("WITNESS FAIL: quadrature diverged from sqrt(pi)/2 beyond tolerance.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
