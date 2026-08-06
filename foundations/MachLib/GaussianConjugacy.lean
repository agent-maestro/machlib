import MachLib.GaussianDensityIntegral

/-!
# Scalar Gaussian-Bayesian conjugacy and MMSE-optimality (Kalman S8–S13)

The Bayesian-conjugacy half of the scalar MMSE-optimality arc, on top of the second-moment theory
in `GaussianDensityIntegral.lean`. Model: prior `X ~ N(μ, σ²)`, measurement `Y = X + N` with noise
`N ~ N(0, r²)` independent of `X`. The joint density is a bare product of two 1-D densities
(no bivariate Gaussian, no covariance matrix). Completing the square factors it as

  jointDensity = gaussianDensity μ (σ²+r²) y · gaussianDensity (m y) τ² x

i.e. the marginal `Y ~ N(μ, σ²+r²)` times the posterior `X | Y=y ~ N(m(y), τ²)`, where
`m(y) = μ + K(y-μ)`, `K = σ²/(σ²+r²)` (the Kalman gain), `τ² = σ²r²/(σ²+r²)` (posterior variance).
The MMSE-optimality of the posterior mean is then the parallel-axis theorem (S7) applied to the
posterior.

Honest scope: SCALAR state and measurement only (not the matrix Kalman filter); noise-independence
is baked into the joint density as a product by construction; `m/τ²/K` are DEFINED by the
completing-the-square algebra, and shown to be the Bayesian posterior via the factorization.

`sorryAx`-free, no new axioms.
-/

namespace MachLib
namespace Real

/-! ## §1 — the Kalman quantities and the standard-form density -/

/-- Kalman gain `K = σ²/(σ²+r²)`.

**CANONICAL.** `KalmanEstimateRecursion.kalmanGainMap r P` is an **alias** of this
(arguments swapped for the recursion layer's reading order); `kalmanGainMap_eq_kGain` closes by
`rfl`. Merged 2026-08-06 — see `MachLib/AliasDecisions.lean`.
**Do not add a third name: bridge to this one.** -/
noncomputable def kGain (sig2 r2 : Real) : Real := sig2 / (sig2 + r2)

/-- Posterior mean `m(y) = μ + K·(y-μ)`. -/
noncomputable def postMean (mu sig2 r2 y : Real) : Real := mu + kGain sig2 r2 * (y - mu)

/-- Posterior variance `τ² = σ²r²/(σ²+r²)`.

**CANONICAL.** `KalmanVarianceRecursion.kalmanVarMap r P` is an **alias** of this
(arguments swapped for the recursion layer's reading order); `kalmanVarMap_eq_postVar` closes by
`rfl`. Merged 2026-08-06 — see `MachLib/AliasDecisions.lean`.
**Do not add a third name: bridge to this one.** -/
noncomputable def postVar (sig2 r2 : Real) : Real := sig2 * r2 / (sig2 + r2)

/-- Marginal variance of `Y`: `σ²+r²`. -/
noncomputable def margVar (sig2 r2 : Real) : Real := sig2 + r2

/-- The joint density of `(X, Y)` — a bare product of two 1-D densities (independence by
construction). -/
noncomputable def jointDensity (mu sig2 r2 x y : Real) : Real :=
  gaussianDensity mu sig2 x * gaussianDensity 0 r2 (y - x)

/-- **`gaussianDensity` in standard form**: `exp(-(x-μ)²/(2σ²)) / √(2πσ²)`. Bridges the scaled-kernel
definition to the sqrt-free-exponent form the conjugacy algebra needs. -/
theorem gaussianDensity_eq_standard (mu sig2 : Real) (hsig2 : 0 < sig2) (x : Real) :
    gaussianDensity mu sig2 x
      = Real.exp (-((x - mu) * (x - mu) / ((1 + 1) * sig2))) / sqrt ((1 + 1) * (pi * sig2)) := by
  have hc : 0 < sqrt ((1 + 1) * sig2) := sqrt_pos (mul_pos two_pos hsig2)
  rw [gaussianDensity]
  -- exponent: ((x-μ)·k)·((x-μ)·k) = (x-μ)²/(2σ²)
  rw [show (x - mu) * (1 / sqrt ((1 + 1) * sig2)) * ((x - mu) * (1 / sqrt ((1 + 1) * sig2)))
      = (x - mu) * (x - mu) * (1 / sqrt ((1 + 1) * sig2) * (1 / sqrt ((1 + 1) * sig2))) from by
    mach_mpoly [x, mu, (1 / sqrt ((1 + 1) * sig2) : Real)]]
  rw [one_div_mul_one_div hc, sqrt_sq_nonneg _ (le_of_lt (mul_pos two_pos hsig2)),
    ← div_def ((x - mu) * (x - mu)) ((1 + 1) * sig2) (ne_of_gt (mul_pos two_pos hsig2))]
  -- normalizer: √π·√(2σ²) = √(2·(π·σ²))
  rw [show (1 + 1) * (pi * sig2) = pi * ((1 + 1) * sig2) from by mach_mpoly [pi, sig2],
    sqrt_mul (le_of_lt pi_pos) (le_of_lt (mul_pos two_pos hsig2))]

/-! ## §2 — completing the square (S9)

The polynomial heart of the conjugacy (verified by hand, then machine): with `p = x-μ`, `q = y-μ`,
`s = σ²`, `t = r²`, and `x - m(y) = (p(s+t) - sq)/(s+t)`, `τ² = st/(s+t)`, clearing `st(s+t)` from
`p²/s + (q-p)²/t = q²/(s+t) + (x-m)²/τ²` gives exactly: -/
private theorem conjugacy_poly (p q s t : Real) :
    p * p * (t * (s + t)) + (q - p) * (q - p) * (s * (s + t))
      = q * q * (s * t) + (p * (s + t) - s * q) * (p * (s + t) - s * q) := by
  mach_mpoly [p, q, s, t]

/-- Abstract ring step for `postMean_diff` (fully abstract atoms `K`, `D` — no overlap). -/
private theorem postMean_diff_ring (x mu y K D : Real) :
    (x - (mu + K * (y - mu))) * D = (x - mu) * D - K * D * (y - mu) := by
  mach_mpoly [x, mu, y, K, D]

/-- `x - postMean μ σ² r² y = ((x-μ)(σ²+r²) - σ²(y-μ))/(σ²+r²)` — the numerator that clears the
posterior mean's denominator. -/
private theorem postMean_diff (mu sig2 r2 x y : Real) (hst : 0 < sig2 + r2) :
    x - postMean mu sig2 r2 y = ((x - mu) * (sig2 + r2) - sig2 * (y - mu)) / (sig2 + r2) := by
  apply mul_right_cancel' (ne_of_gt hst)
  rw [div_mul_cancel (ne_of_gt hst), postMean, kGain, postMean_diff_ring,
    div_mul_cancel (ne_of_gt hst)]

/-- `(Z/d)·(d·e) = Z·e` — clear a denominator that divides the multiplier. -/
private theorem div_mul_clear (Z d e : Real) (hd : d ≠ 0) : Z / d * (d * e) = Z * e := by
  rw [← mul_assoc, div_mul_cancel hd]

-- Abstract ring rearrangements (proved on fresh variables, then applied to real terms — this
-- sidesteps `mach_mpoly`'s overlapping-atom failure when a divisor also appears standalone).
private theorem rearr_ACbd (A C b d : Real) : A * C * (b * d) = A * b * (C * d) := by
  mach_mpoly [A, C, b, d]
private theorem rearr_Acb (A b c : Real) : A * (b * c) = A * c * b := by mach_mpoly [A, b, c]
private theorem rearr_DDtwoF (two D F : Real) : D * D * (two * F) = two * D * (F * D) := by
  mach_mpoly [two, D, F]
private theorem add_mul_l (a b c : Real) : (a + b) * c = a * c + b * c := by mach_mpoly [a, b, c]

/-- `(a/b)·(c/d) = (a·c)/(b·d)`. -/
private theorem div_mul_div (a b c d : Real) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b * (c / d) = a * c / (b * d) := by
  apply mul_right_cancel' (mul_ne_zero hb hd)
  rw [div_mul_cancel (mul_ne_zero hb hd), rearr_ACbd (a / b) (c / d) b d, div_mul_cancel hb,
    div_mul_cancel hd]

/-- `a/b/c = a/(b·c)`. -/
private theorem div_div (a b c : Real) (hb : b ≠ 0) (hc : c ≠ 0) : a / b / c = a / (b * c) := by
  apply mul_right_cancel' (mul_ne_zero hb hc)
  rw [div_mul_cancel (mul_ne_zero hb hc), rearr_Acb (a / b / c) b c, div_mul_cancel hc,
    div_mul_cancel hb]

/-- `postVar σ² r² ≠ 0`. -/
private theorem postVar_ne_zero (sig2 r2 : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2) :
    postVar sig2 r2 ≠ 0 := by
  rw [postVar]; intro h
  have hc := mul_div_cancel' (t := sig2 * r2) (ne_of_gt (add_pos hsig2 hr2))
  rw [h, mul_zero] at hc
  exact mul_ne_zero (ne_of_gt hsig2) (ne_of_gt hr2) hc.symm

/-- `0 < postVar σ² r²` — the posterior variance is a genuine positive variance. -/
theorem postVar_pos (sig2 r2 : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2) : 0 < postVar sig2 r2 := by
  have hst : 0 < sig2 + r2 := add_pos hsig2 hr2
  have hle : 0 ≤ postVar sig2 r2 := by
    rw [postVar]; exact div_nonneg (mul_nonneg (le_of_lt hsig2) (le_of_lt hr2)) (le_of_lt hst)
  rcases (le_iff_lt_or_eq 0 (postVar sig2 r2)).mp hle with h | h
  · exact h
  · exact absurd h.symm (postVar_ne_zero sig2 r2 hsig2 hr2)

/-- Denominator step for `postTerm_eq`: `(σ+r)²·((1+1)·τ²) = (1+1)·(σ²r²)·(σ²+r²)`. -/
private theorem postTerm_den (sig2 r2 : Real) (hst : sig2 + r2 ≠ 0) :
    (sig2 + r2) * (sig2 + r2) * ((1 + 1) * postVar sig2 r2)
      = (1 + 1) * (sig2 * r2) * (sig2 + r2) := by
  rw [postVar, rearr_DDtwoF (1 + 1) (sig2 + r2) (sig2 * r2 / (sig2 + r2)), div_mul_cancel hst]
  mach_mpoly [sig2, r2]

/-- The posterior term with its nested division cleared: `(x-m)²/((1+1)τ²) = NUM²/((1+1)σ²r²(σ²+r²))`
where `NUM = (x-μ)(σ²+r²) - σ²(y-μ)`. -/
private theorem postTerm_eq (mu sig2 r2 x y : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2) :
    (x - postMean mu sig2 r2 y) * (x - postMean mu sig2 r2 y) / ((1 + 1) * postVar sig2 r2)
      = ((x - mu) * (sig2 + r2) - sig2 * (y - mu)) * ((x - mu) * (sig2 + r2) - sig2 * (y - mu))
        / ((1 + 1) * (sig2 * r2) * (sig2 + r2)) := by
  have hst : sig2 + r2 ≠ 0 := ne_of_gt (add_pos hsig2 hr2)
  rw [postMean_diff mu sig2 r2 x y (add_pos hsig2 hr2),
    div_mul_div _ _ _ _ hst hst, div_div _ _ _ (mul_ne_zero hst hst)
      (mul_ne_zero (ne_of_gt two_pos) (postVar_ne_zero sig2 r2 hsig2 hr2)),
    show (sig2 + r2) * (sig2 + r2) * ((1 + 1) * postVar sig2 r2)
        = (1 + 1) * (sig2 * r2) * (sig2 + r2) from postTerm_den sig2 r2 hst]

/-- Cleared-denominator polynomial form of the completing-the-square identity. Reduced to
`conjugacy_poly` (the `p,q,s,t`-abstract form, which normalises cleanly) by shifting `y-x` to
`(y-μ)-(x-μ)` — direct `mach_mpoly` on the `x,mu,y`-form leaves spurious `-0` coefficient leaves. -/
private theorem conjugacy_expArg_poly (x mu y sig2 r2 : Real) :
    (x - mu) * (x - mu) * (r2 * (sig2 + r2)) + (y - x) * (y - x) * (sig2 * (sig2 + r2))
      = (y - mu) * (y - mu) * (sig2 * r2)
        + ((x - mu) * (sig2 + r2) - sig2 * (y - mu))
          * ((x - mu) * (sig2 + r2) - sig2 * (y - mu)) := by
  rw [show y - x = (y - mu) - (x - mu) from by mach_mpoly [x, y, mu]]
  exact conjugacy_poly (x - mu) (y - mu) sig2 r2

/-- **The completing-the-square exponent identity (S9 crux)**: the two joint-density exponents sum
to the marginal + posterior exponents. Positive form (the actual exponents are the negatives). -/
private theorem conjugacy_expArg (mu sig2 r2 x y : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2) :
    (x - mu) * (x - mu) / ((1 + 1) * sig2) + (y - x) * (y - x) / ((1 + 1) * r2)
      = (y - mu) * (y - mu) / ((1 + 1) * (sig2 + r2))
        + (x - postMean mu sig2 r2 y) * (x - postMean mu sig2 r2 y)
          / ((1 + 1) * postVar sig2 r2) := by
  have hst : sig2 + r2 ≠ 0 := ne_of_gt (add_pos hsig2 hr2)
  have h2 : (1 + 1 : Real) ≠ 0 := ne_of_gt two_pos
  have hD : (1 + 1) * (sig2 * r2) * (sig2 + r2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero h2 (mul_ne_zero (ne_of_gt hsig2) (ne_of_gt hr2))) hst
  rw [postTerm_eq mu sig2 r2 x y hsig2 hr2]
  apply mul_right_cancel' hD
  rw [add_mul_l ((x - mu) * (x - mu) / ((1 + 1) * sig2)) ((y - x) * (y - x) / ((1 + 1) * r2))
        ((1 + 1) * (sig2 * r2) * (sig2 + r2)),
    add_mul_l ((y - mu) * (y - mu) / ((1 + 1) * (sig2 + r2)))
        (((x - mu) * (sig2 + r2) - sig2 * (y - mu)) * ((x - mu) * (sig2 + r2) - sig2 * (y - mu))
          / ((1 + 1) * (sig2 * r2) * (sig2 + r2)))
        ((1 + 1) * (sig2 * r2) * (sig2 + r2))]
  -- clear each fraction against the common denominator
  rw [show (x - mu) * (x - mu) / ((1 + 1) * sig2) * ((1 + 1) * (sig2 * r2) * (sig2 + r2))
      = (x - mu) * (x - mu) * (r2 * (sig2 + r2)) from by
        rw [show (1 + 1) * (sig2 * r2) * (sig2 + r2) = ((1 + 1) * sig2) * (r2 * (sig2 + r2)) from by
          mach_mpoly [sig2, r2]]
        exact div_mul_clear _ _ _ (mul_ne_zero h2 (ne_of_gt hsig2))]
  rw [show (y - x) * (y - x) / ((1 + 1) * r2) * ((1 + 1) * (sig2 * r2) * (sig2 + r2))
      = (y - x) * (y - x) * (sig2 * (sig2 + r2)) from by
        rw [show (1 + 1) * (sig2 * r2) * (sig2 + r2) = ((1 + 1) * r2) * (sig2 * (sig2 + r2)) from by
          mach_mpoly [sig2, r2]]
        exact div_mul_clear _ _ _ (mul_ne_zero h2 (ne_of_gt hr2))]
  rw [show (y - mu) * (y - mu) / ((1 + 1) * (sig2 + r2)) * ((1 + 1) * (sig2 * r2) * (sig2 + r2))
      = (y - mu) * (y - mu) * (sig2 * r2) from by
        rw [show (1 + 1) * (sig2 * r2) * (sig2 + r2) = ((1 + 1) * (sig2 + r2)) * (sig2 * r2) from by
          mach_mpoly [sig2, r2]]
        exact div_mul_clear _ _ _ (mul_ne_zero h2 hst)]
  rw [div_mul_cancel hD]
  exact conjugacy_expArg_poly x mu y sig2 r2

/-! ## §3 — the normalizer identity (S9) -/

/-- Radicand equality behind the normalizer match: both `2πσ²·2πr²` and `2π(σ²+r²)·2πτ²` are
`(2π)²σ²r²` once `(σ²+r²)·τ² = σ²r²`. -/
private theorem normalizer_radicand (two P s t W : Real) (hW : (s + t) * W = s * t) :
    two * (P * s) * (two * (P * t)) = two * (P * (s + t)) * (two * (P * W)) := by
  rw [show two * (P * (s + t)) * (two * (P * W)) = two * two * (P * P) * ((s + t) * W) from by
      mach_mpoly [two, P, s, t, W], hW]
  mach_mpoly [two, P, s, t]

/-- **The normalizer identity (S9)**: the joint density's normalizer factors match the marginal ×
posterior normalizers — `√(2πσ²)·√(2πr²) = √(2π(σ²+r²))·√(2πτ²)`. -/
private theorem conjugacy_normalizer (sig2 r2 : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2) :
    sqrt ((1 + 1) * (pi * sig2)) * sqrt ((1 + 1) * (pi * r2))
      = sqrt ((1 + 1) * (pi * (sig2 + r2))) * sqrt ((1 + 1) * (pi * postVar sig2 r2)) := by
  have hst : 0 < sig2 + r2 := add_pos hsig2 hr2
  have hpv : 0 ≤ postVar sig2 r2 := by
    rw [postVar]; exact div_nonneg (mul_nonneg (le_of_lt hsig2) (le_of_lt hr2)) (le_of_lt hst)
  have nn : ∀ z : Real, 0 ≤ z → 0 ≤ (1 + 1) * (pi * z) := fun z hz =>
    mul_nonneg (le_of_lt two_pos) (mul_nonneg (le_of_lt pi_pos) hz)
  rw [← sqrt_mul (nn sig2 (le_of_lt hsig2)) (nn r2 (le_of_lt hr2)),
    ← sqrt_mul (nn (sig2 + r2) (le_of_lt hst)) (nn (postVar sig2 r2) hpv),
    normalizer_radicand (1 + 1) pi sig2 r2 (postVar sig2 r2)
      (by rw [postVar]; exact mul_div_cancel' (ne_of_gt hst))]

/-! ## §4 — the conjugacy factorization (S9/S10) -/

/-- `exp A / N₁ · (exp B / N₂) = exp(A+B) / (N₁N₂)`. -/
private theorem expdiv_mul (A B N1 N2 : Real) (hN1 : N1 ≠ 0) (hN2 : N2 ≠ 0) :
    Real.exp A / N1 * (Real.exp B / N2) = Real.exp (A + B) / (N1 * N2) := by
  rw [div_mul_div _ _ _ _ hN1 hN2, ← exp_add]

/-- **Gaussian-Bayesian conjugacy (S9/S10)**: the joint density factors as the marginal `Y ~
N(μ, σ²+r²)` times the posterior `X | Y=y ~ N(m(y), τ²)`. This is the completing-the-square identity
at the density level, and hands S10 the marginal (integrate `x` out, `∫posterior = 1` by S3) and the
posterior density for free. -/
theorem jointDensity_conjugacy (mu sig2 r2 x y : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2) :
    jointDensity mu sig2 r2 x y
      = gaussianDensity mu (margVar sig2 r2) y
        * gaussianDensity (postMean mu sig2 r2 y) (postVar sig2 r2) x := by
  have hst : 0 < sig2 + r2 := add_pos hsig2 hr2
  have hmarg : 0 < margVar sig2 r2 := by rw [margVar]; exact hst
  have hpv : 0 < postVar sig2 r2 := postVar_pos sig2 r2 hsig2 hr2
  rw [jointDensity, gaussianDensity_eq_standard mu sig2 hsig2 x,
    gaussianDensity_eq_standard 0 r2 hr2 (y - x),
    gaussianDensity_eq_standard mu (margVar sig2 r2) hmarg y,
    gaussianDensity_eq_standard (postMean mu sig2 r2 y) (postVar sig2 r2) hpv x, sub_zero, margVar,
    expdiv_mul _ _ _ _ (ne_of_gt (sqrt_pos (mul_pos two_pos (mul_pos pi_pos hsig2))))
      (ne_of_gt (sqrt_pos (mul_pos two_pos (mul_pos pi_pos hr2)))),
    expdiv_mul _ _ _ _ (ne_of_gt (sqrt_pos (mul_pos two_pos (mul_pos pi_pos hst))))
      (ne_of_gt (sqrt_pos (mul_pos two_pos (mul_pos pi_pos hpv)))),
    ← neg_add, conjugacy_expArg mu sig2 r2 x y hsig2 hr2, neg_add,
    conjugacy_normalizer sig2 r2 hsig2 hr2]

/-! ## §5 — MMSE-optimality of the posterior mean (S13/S14) -/

/-- **Posterior (conditional) MSE**: for any point estimate `c`, the mean-squared error against the
posterior `X | Y=y ~ N(m(y), τ²)` converges to `τ² + (c - m(y))²` — the parallel-axis theorem (S7)
at the posterior identified by the conjugacy factorization. -/
theorem posteriorMSE_tendsto (mu sig2 r2 y c : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2) :
    ∀ ε : Real, 0 < ε → ∃ R₀ : Real, 0 < R₀ ∧ ∀ R : Real, R₀ ≤ R →
      abs (gaussianVarCSymInt (postMean mu sig2 r2 y) (postVar sig2 r2)
              (postVar_pos sig2 r2 hsig2 hr2) c R
            - (postVar sig2 r2 + (c - postMean mu sig2 r2 y) * (c - postMean mu sig2 r2 y))) < ε :=
  gaussianVarCSymInt_tendsto (postMean mu sig2 r2 y) (postVar sig2 r2) c
    (postVar_pos sig2 r2 hsig2 hr2)

/-- **The posterior mean is MMSE-optimal (S13)**: among all point estimates `c` of `X` given
`Y=y`, the posterior/Kalman mean `m(y) = μ + K(y-μ)` minimizes the conditional MSE `τ² + (c-m(y))²`,
achieving the minimum posterior variance `τ²`. Every estimate is at least as bad as the posterior
mean. -/
theorem posterior_mean_mmse (mu sig2 r2 y c : Real) :
    postVar sig2 r2
      ≤ postVar sig2 r2 + (c - postMean mu sig2 r2 y) * (c - postMean mu sig2 r2 y) :=
  le_add_of_nonneg_right (mul_self_nonneg _)

/-- **Strict sub-optimality of any other estimate (S13)**: any estimate off the posterior mean
(`c - m(y) ≠ 0`) has strictly larger conditional MSE — the posterior mean is the unique minimizer. -/
theorem posterior_mean_mmse_strict (mu sig2 r2 y c : Real)
    (hc : c - postMean mu sig2 r2 y ≠ 0) :
    postVar sig2 r2
      < postVar sig2 r2 + (c - postMean mu sig2 r2 y) * (c - postMean mu sig2 r2 y) := by
  have h := add_lt_add_left (mul_self_pos hc) (postVar sig2 r2)
  rw [add_zero] at h
  exact h

/-- **S14 cross-check**: the optimal update's gain is the Kalman gain `K = σ²/(σ²+r²)` and the
optimal mean is `m(y) = μ + K(y-μ)`, matching the algebraic Kalman formulas. -/
theorem postMean_eq_kalman (mu sig2 r2 y : Real) :
    postMean mu sig2 r2 y = mu + sig2 / (sig2 + r2) * (y - mu) := by
  rw [postMean, kGain]

/-! ## §6 — the marginal is Gaussian (S10-proper) -/

/-- Local copy of the integrand-congruence for `Classical.choose` (private upstream). -/
private theorem cri_congr {f g : Real → Real} (hfg : f = g) {a b : Real} (hab : a ≤ b)
    (hcontf : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hcontg : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt g z) :
    Classical.choose (continuous_riemann_integrable f a b hab hcontf)
      = Classical.choose (continuous_riemann_integrable g a b hab hcontg) := by
  subst hfg; rfl

/-- As a function of `x` (fixed `y`), the joint density is a constant times the posterior density —
so it is continuous, hence Riemann-integrable. -/
theorem continuousAt_jointDensity_x (mu sig2 r2 y : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2)
    (z : Real) : ContinuousAt (fun x => jointDensity mu sig2 r2 x y) z := by
  have hfun : (fun x => jointDensity mu sig2 r2 x y)
      = (fun x => gaussianDensity (postMean mu sig2 r2 y) (postVar sig2 r2) x
          * gaussianDensity mu (margVar sig2 r2) y) := by
    funext x; rw [jointDensity_conjugacy mu sig2 r2 x y hsig2 hr2, mul_comm]
  rw [hfun]
  exact continuousAt_mul_const (continuousAt_gaussianDensity (postMean mu sig2 r2 y)
    (postVar sig2 r2) (postVar_pos sig2 r2 hsig2 hr2) z) _

/-- `∫_{-R}^R jointDensity μ σ² r² x y dx` — the marginal integral over `x` at `Y=y`. -/
noncomputable def jointDensitySymInt (mu sig2 r2 y : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2)
    (R : Real) : Real :=
  if h : 0 < R then
    Classical.choose (continuous_riemann_integrable (fun x => jointDensity mu sig2 r2 x y) (-R) R
      (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun z _ _ => continuousAt_jointDensity_x mu sig2 r2 y hsig2 hr2 z))
  else 0

/-- The marginal integral factors: `∫jointDensity dx = (∫posterior dx)·(marginal density)` — the
posterior (a genuine density) is pulled through `riemann_integral_mul_const`, the marginal density
is constant in `x`. -/
private theorem jointDensitySymInt_eq (mu sig2 r2 y : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2)
    {R : Real} (hR : 0 < R) :
    jointDensitySymInt mu sig2 r2 y hsig2 hr2 R
      = gaussianDensitySymInt (postMean mu sig2 r2 y) (postVar sig2 r2)
          (postVar_pos sig2 r2 hsig2 hr2) R
        * gaussianDensity mu (margVar sig2 r2) y := by
  have hpv := postVar_pos sig2 r2 hsig2 hr2
  have hab : -R < R := lt_trans_ax (neg_neg_of_pos hR) hR
  have hcg : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (gaussianDensity (postMean mu sig2 r2 y) (postVar sig2 r2)) z :=
    fun z _ _ => continuousAt_gaussianDensity (postMean mu sig2 r2 y) (postVar sig2 r2) hpv z
  have hcp : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun x => gaussianDensity (postMean mu sig2 r2 y) (postVar sig2 r2) x
        * gaussianDensity mu (margVar sig2 r2) y) z :=
    fun z hz0 hz1 => continuousAt_mul_const (hcg z hz0 hz1) _
  have hfun : (fun x => jointDensity mu sig2 r2 x y)
      = (fun x => gaussianDensity (postMean mu sig2 r2 y) (postVar sig2 r2) x
          * gaussianDensity mu (margVar sig2 r2) y) := by
    funext x; rw [jointDensity_conjugacy mu sig2 r2 x y hsig2 hr2, mul_comm]
  show (if h : 0 < R then Classical.choose (continuous_riemann_integrable
      (fun x => jointDensity mu sig2 r2 x y) (-R) R _ _) else 0) = _
  rw [dif_pos hR,
    cri_congr hfun (le_of_lt hab)
      (fun z _ _ => continuousAt_jointDensity_x mu sig2 r2 y hsig2 hr2 z) hcp,
    riemann_integral_mul_const (le_of_lt hab) hcg hcp]
  show _ * _ = gaussianDensitySymInt (postMean mu sig2 r2 y) (postVar sig2 r2) hpv R * _
  rw [gaussianDensitySymInt, dif_pos hR]

/-- Coefficient-scaling closer: `|S-1| < ε/(|m|+1)` ⇒ `|S·m - m| < ε`. -/
private theorem marg_final_bound (S m ε : Real) (hS : abs (S - 1) < ε / (abs m + 1)) :
    abs (S * m - m) < ε := by
  have hcoef : 0 < abs m + 1 := add_pos_of_nonneg_pos (abs_nonneg m) one_pos
  rw [show S * m - m = (S - 1) * m from by mach_mpoly [S, m], abs_mul]
  have h1 : abs (S - 1) * (abs m + 1) < ε := by
    have h := mul_lt_mul_of_pos_right hS hcoef
    rwa [div_mul_cancel (ne_of_gt hcoef)] at h
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (le_of_lt one_pos)) (abs_nonneg _)) h1

/-- **The marginal is Gaussian (S10)**: integrating `x` out of the joint density leaves the marginal
`Y ~ N(μ, σ²+r²)` — `∫_{-R}^R jointDensity μ σ² r² x y dx → gaussianDensity μ (σ²+r²) y`. No new
Gaussian-integral identity is needed: the conjugacy factorization plus `∫posterior = 1` (S3) suffice.
-/
theorem jointDensity_marginal_tendsto (mu sig2 r2 y : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2) :
    ∀ ε : Real, 0 < ε → ∃ R₀ : Real, 0 < R₀ ∧ ∀ R : Real, R₀ ≤ R →
      abs (jointDensitySymInt mu sig2 r2 y hsig2 hr2 R
            - gaussianDensity mu (margVar sig2 r2) y) < ε := by
  intro ε hε
  have hpv := postVar_pos sig2 r2 hsig2 hr2
  have hm : 0 < abs (gaussianDensity mu (margVar sig2 r2) y) + 1 :=
    add_pos_of_nonneg_pos (abs_nonneg _) one_pos
  obtain ⟨R0, hR0p, hR0⟩ := gaussianDensity_symInt_tendsto_one (postMean mu sig2 r2 y)
    (postVar sig2 r2) hpv (ε / (abs (gaussianDensity mu (margVar sig2 r2) y) + 1))
    (div_pos_of_pos_pos hε hm)
  refine ⟨max R0 1, lt_of_lt_of_le one_pos (le_max_right R0 1), ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_trans (le_max_right R0 1) hR)
  rw [jointDensitySymInt_eq mu sig2 r2 y hsig2 hr2 hRpos]
  exact marg_final_bound (gaussianDensitySymInt (postMean mu sig2 r2 y) (postVar sig2 r2) hpv R)
    (gaussianDensity mu (margVar sig2 r2) y) ε (hR0 R (le_trans (le_max_left R0 1) hR))

/-! ## §7 — the optimal estimator's total MSE is τ² (unconditional value, S13)

For the posterior-mean (Kalman) estimator `m(·)`, the conditional MSE at each `y` is exactly `τ²`
(parallel-axis with `c = m(y)`, so the `(c-m(y))²` term vanishes). Hence the total-MSE integrand is
`margDensity(y)·τ²`, and the total MSE — the outer `y`-integral — is `τ²·∫margDensity = τ²`. Every
other estimate is at least as bad at every `y` (`posterior_mean_mmse`), so `τ²` is the minimum
achievable mean-squared error. -/

/-- `0 < margVar σ² r²`. -/
theorem margVar_pos (sig2 r2 : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2) : 0 < margVar sig2 r2 := by
  rw [margVar]; exact add_pos hsig2 hr2

/-- `∫_{-R}^R margDensity(y)·τ² dy` — the outer integral of the optimal estimator's (constant-`τ²`)
conditional MSE. -/
noncomputable def optimalMSESymInt (mu sig2 r2 : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2)
    (R : Real) : Real :=
  if h : 0 < R then
    Classical.choose (continuous_riemann_integrable
      (fun y => gaussianDensity mu (margVar sig2 r2) y * postVar sig2 r2) (-R) R
      (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun z _ _ => continuousAt_mul_const
        (continuousAt_gaussianDensity mu (margVar sig2 r2) (margVar_pos sig2 r2 hsig2 hr2) z) _))
  else 0

/-- The optimal total-MSE integral factors as `(∫margDensity)·τ²`. -/
private theorem optimalMSESymInt_eq (mu sig2 r2 : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2)
    {R : Real} (hR : 0 < R) :
    optimalMSESymInt mu sig2 r2 hsig2 hr2 R
      = gaussianDensitySymInt mu (margVar sig2 r2) (margVar_pos sig2 r2 hsig2 hr2) R
        * postVar sig2 r2 := by
  have hmarg := margVar_pos sig2 r2 hsig2 hr2
  have hab : -R < R := lt_trans_ax (neg_neg_of_pos hR) hR
  have hcg : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (gaussianDensity mu (margVar sig2 r2)) z :=
    fun z _ _ => continuousAt_gaussianDensity mu (margVar sig2 r2) hmarg z
  have hcp : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => gaussianDensity mu (margVar sig2 r2) y * postVar sig2 r2) z :=
    fun z hz0 hz1 => continuousAt_mul_const (hcg z hz0 hz1) _
  show (if h : 0 < R then Classical.choose (continuous_riemann_integrable
      (fun y => gaussianDensity mu (margVar sig2 r2) y * postVar sig2 r2) (-R) R _ _) else 0) = _
  rw [dif_pos hR, riemann_integral_mul_const (le_of_lt hab) hcg hcp]
  show _ * _ = gaussianDensitySymInt mu (margVar sig2 r2) hmarg R * _
  rw [gaussianDensitySymInt, dif_pos hR]

/-- **The optimal (posterior-mean/Kalman) estimator achieves total MSE `τ²` (S13, unconditional
value)**: `∫_{-R}^R margDensity(y)·τ² dy → τ²`. This is the minimum mean-squared error —
`posterior_mean_mmse` shows every other estimate is at least as bad at every `y`. -/
theorem optimalMSE_tendsto (mu sig2 r2 : Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2) :
    ∀ ε : Real, 0 < ε → ∃ R₀ : Real, 0 < R₀ ∧ ∀ R : Real, R₀ ≤ R →
      abs (optimalMSESymInt mu sig2 r2 hsig2 hr2 R - postVar sig2 r2) < ε := by
  intro ε hε
  have hmarg := margVar_pos sig2 r2 hsig2 hr2
  have hm : 0 < abs (postVar sig2 r2) + 1 := add_pos_of_nonneg_pos (abs_nonneg _) one_pos
  obtain ⟨R0, hR0p, hR0⟩ := gaussianDensity_symInt_tendsto_one mu (margVar sig2 r2) hmarg
    (ε / (abs (postVar sig2 r2) + 1)) (div_pos_of_pos_pos hε hm)
  refine ⟨max R0 1, lt_of_lt_of_le one_pos (le_max_right R0 1), ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_trans (le_max_right R0 1) hR)
  rw [optimalMSESymInt_eq mu sig2 r2 hsig2 hr2 hRpos]
  exact marg_final_bound (gaussianDensitySymInt mu (margVar sig2 r2) hmarg R) (postVar sig2 r2) ε
    (hR0 R (le_trans (le_max_left R0 1) hR))

/-! ## §8 — no continuous estimator beats τ² (unconditional lower bound, S13) -/

private theorem sub_eq_add_neg_l (a b : Real) : a - b = a + -b := by mach_mpoly [a, b]

/-- Continuity of a difference of continuous functions (`sub = add ∘ neg`). -/
private theorem continuousAt_sub {f g : Real → Real} {z : Real} (hf : ContinuousAt f z)
    (hg : ContinuousAt g z) : ContinuousAt (fun y => f y - g y) z := by
  have h : (fun y => f y - g y) = (fun y => f y + -(g y)) := by
    funext y; exact sub_eq_add_neg_l (f y) (g y)
  rw [h]; exact continuousAt_add hf (continuousAt_neg hg)

/-- `y ↦ postMean μ σ² r² y` is continuous (it is affine in `y`). -/
private theorem continuousAt_postMean (mu sig2 r2 z : Real) :
    ContinuousAt (fun y => postMean mu sig2 r2 y) z := by
  have h : (fun y => postMean mu sig2 r2 y) = (fun y => mu + kGain sig2 r2 * (y - mu)) := by
    funext y; rw [postMean]
  rw [h]
  exact continuousAt_add (continuousAt_const mu z)
    (continuousAt_mul (continuousAt_const (kGain sig2 r2) z)
      (continuousAt_sub (hasDerivAt_continuousAt (HasDerivAt_id z)) (continuousAt_const mu z)))

/-- Continuity of the total-MSE integrand `margDensity(y)·(τ²+(φy-m y)²)` for continuous `φ`. -/
private theorem continuousAt_mseIntegrand (mu sig2 r2 : Real) (phi : Real → Real) (hsig2 : 0 < sig2)
    (hr2 : 0 < r2) (hphi : ∀ z, ContinuousAt phi z) (z : Real) :
    ContinuousAt (fun y => gaussianDensity mu (margVar sig2 r2) y
      * (postVar sig2 r2 + (phi y - postMean mu sig2 r2 y) * (phi y - postMean mu sig2 r2 y))) z := by
  have hsub : ContinuousAt (fun y => phi y - postMean mu sig2 r2 y) z :=
    continuousAt_sub (hphi z) (continuousAt_postMean mu sig2 r2 z)
  exact continuousAt_mul
    (continuousAt_gaussianDensity mu (margVar sig2 r2) (margVar_pos sig2 r2 hsig2 hr2) z)
    (continuousAt_add (continuousAt_const _ z) (continuousAt_mul hsub hsub))

/-- `∫_{-R}^R margDensity(y)·(τ²+(φy-m y)²) dy` — the total MSE of a continuous estimator `φ`, as the
outer `y`-integral of its conditional MSE `τ²+(φy-m y)²` (the inner `x`-integral, `posteriorMSE`). -/
noncomputable def mseSymInt (mu sig2 r2 : Real) (phi : Real → Real) (hphi : ∀ z, ContinuousAt phi z)
    (hsig2 : 0 < sig2) (hr2 : 0 < r2) (R : Real) : Real :=
  if h : 0 < R then
    Classical.choose (continuous_riemann_integrable
      (fun y => gaussianDensity mu (margVar sig2 r2) y
        * (postVar sig2 r2 + (phi y - postMean mu sig2 r2 y) * (phi y - postMean mu sig2 r2 y)))
      (-R) R (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun z _ _ => continuousAt_mseIntegrand mu sig2 r2 phi hsig2 hr2 hphi z))
  else 0

/-- **The optimal estimator dominates at every window (S13)**: for any continuous estimator `φ` and
any `R`, `optimalMSESymInt ≤ mseSymInt φ` — pointwise the conditional MSE `τ²+(φy-m y)²` is `≥ τ²`,
so Riemann-integral monotonicity gives it window by window. -/
theorem optimalMSESymInt_le_mseSymInt (mu sig2 r2 : Real) (phi : Real → Real) (hsig2 : 0 < sig2)
    (hr2 : 0 < r2) (hphi : ∀ z, ContinuousAt phi z) {R : Real} (hR : 0 < R) :
    optimalMSESymInt mu sig2 r2 hsig2 hr2 R ≤ mseSymInt mu sig2 r2 phi hphi hsig2 hr2 R := by
  have hmarg := margVar_pos sig2 r2 hsig2 hr2
  have hab : -R < R := lt_trans_ax (neg_neg_of_pos hR) hR
  have hcg : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => gaussianDensity mu (margVar sig2 r2) y * postVar sig2 r2) z :=
    fun z _ _ => continuousAt_mul_const (continuousAt_gaussianDensity mu (margVar sig2 r2) hmarg z) _
  have hch : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => gaussianDensity mu (margVar sig2 r2) y
        * (postVar sig2 r2 + (phi y - postMean mu sig2 r2 y)
          * (phi y - postMean mu sig2 r2 y))) z :=
    fun z _ _ => continuousAt_mseIntegrand mu sig2 r2 phi hsig2 hr2 hphi z
  have hpt : ∀ t : Real, -R ≤ t → t ≤ R →
      gaussianDensity mu (margVar sig2 r2) t * postVar sig2 r2
        ≤ gaussianDensity mu (margVar sig2 r2) t
          * (postVar sig2 r2
            + (phi t - postMean mu sig2 r2 t) * (phi t - postMean mu sig2 r2 t)) :=
    fun t _ _ => mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_self_nonneg _))
      (le_of_lt (gaussianDensity_pos mu (margVar sig2 r2) hmarg t))
  have hgspec := Classical.choose_spec (continuous_riemann_integrable
    (fun y => gaussianDensity mu (margVar sig2 r2) y * postVar sig2 r2) (-R) R (le_of_lt hab) hcg)
  have hhspec := Classical.choose_spec (continuous_riemann_integrable
    (fun y => gaussianDensity mu (margVar sig2 r2) y
      * (postVar sig2 r2 + (phi y - postMean mu sig2 r2 y) * (phi y - postMean mu sig2 r2 y)))
    (-R) R (le_of_lt hab) hch)
  rw [optimalMSESymInt, dif_pos hR, mseSymInt, dif_pos hR]
  exact riemann_integral_mono _ _ (-R) R (le_of_lt hab) hcg hch hpt _ _
    (fun k => (hgspec.1 k).2) (fun k => (hhspec.1 k).1) hhspec.2

/-- From `|a - b| < ε`, the lower bound `b - ε < a`. -/
private theorem lower_of_abs_lt {a b ε : Real} (h : abs (a - b) < ε) : b - ε < a := by
  have hba : abs (b - a) < ε := by rw [abs_sub_comm b a]; exact h
  have h3 := add_lt_add_left (lt_of_abs_lt hba) (a - ε)
  rwa [show a - ε + (b - a) = b - ε from by mach_mpoly [a, b, ε],
    show a - ε + ε = a from by mach_mpoly [a, ε]] at h3

/-- **No continuous estimator beats τ² (S13, unconditional MMSE lower bound)**: for every continuous
`φ` and every ε, its total-MSE window integral is eventually `> τ² - ε`. Together with
`optimalMSE_tendsto` (the posterior-mean estimator *achieves* `τ²`), this is the unconditional
statement that the scalar Kalman update is the minimum-mean-squared-error estimator. -/
theorem mse_lower_bound (mu sig2 r2 : Real) (phi : Real → Real) (hsig2 : 0 < sig2) (hr2 : 0 < r2)
    (hphi : ∀ z, ContinuousAt phi z) :
    ∀ ε : Real, 0 < ε → ∃ R₀ : Real, 0 < R₀ ∧ ∀ R : Real, R₀ ≤ R →
      postVar sig2 r2 - ε < mseSymInt mu sig2 r2 phi hphi hsig2 hr2 R := by
  intro ε hε
  obtain ⟨R0, hR0p, hR0⟩ := optimalMSE_tendsto mu sig2 r2 hsig2 hr2 ε hε
  refine ⟨max R0 1, lt_of_lt_of_le one_pos (le_max_right R0 1), ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_trans (le_max_right R0 1) hR)
  exact lt_of_lt_of_le (lower_of_abs_lt (hR0 R (le_trans (le_max_left R0 1) hR)))
    (optimalMSESymInt_le_mseSymInt mu sig2 r2 phi hsig2 hr2 hphi hRpos)

end Real
end MachLib
