import MachLib.GaussianConjugacy

/-!
# 2-D Kalman MMSE-optimality (trace loss)

The vector analogue of `posterior_mean_mmse`. For a 2-D state the MMSE-optimal estimator is
the **posterior mean vector**, minimizing the expected squared Euclidean error
`E[|X − c|²]` — the **trace** of the error covariance. The key that keeps this tractable in
MachLib's Mathlib-free base (no 2-D integration, no general Fubini): the trace loss
**separates per component**,

    E[|X − c|²] = Σᵢ E[(Xᵢ − cᵢ)²],

so the vector optimality is exactly the sum of the per-component scalar conjugate MMSE
(`posterior_mean_mmse`) — no new integral needed. Each component reduces, by the scalar
Gaussian conjugacy already proven, to `postVar_i + (cᵢ − mᵢ)²`, and summing gives
`tr(Σ_post) + |c − m|²`, minimized (uniquely) at `c = m`.

* `matrix2_posterior_mean_mmse` — the optimality: the optimal total conditional MSE
  `tr(Σ_post) = postVar₀ + postVar₁` is `≤` the total conditional MSE of any estimate `(c₀,c₁)`.
* `matrix2_mmse_excess` — the **excess risk** of `(c₀,c₁)` over the optimum is *exactly*
  `|c − m|² = (c₀−m₀)² + (c₁−m₁)²` — zero iff `c = m`, so the posterior-mean vector is the
  unique minimizer.

`sorryAx`-free, zero new axioms. (This is the trace/Euclidean loss, the standard MMSE
criterion; the per-component reduction is exactly why the vector case needs no 2-D
integration. A weighted quadratic loss would reweight the components but is still minimized
at the mean — the cross terms vanish for the same reason.)
-/

namespace MachLib.Real

/-- Abbreviation for a component's squared estimation error `(c − m)²`. -/
private noncomputable def sqErr (mu sig2 r2 y c : Real) : Real :=
  (c - postMean mu sig2 r2 y) * (c - postMean mu sig2 r2 y)

/-- **2-D Kalman MMSE-optimality (trace loss).** The optimal total conditional MSE — the
trace of the posterior covariance, `postVar₀ + postVar₁`, attained by the posterior-mean
vector — is at most the total conditional MSE of *any* estimate `(c₀,c₁)`. The two-component
sum of the scalar conjugate MMSE (`posterior_mean_mmse`), which is all the trace loss needs. -/
theorem matrix2_posterior_mean_mmse
    (mu0 sig20 r20 y0 c0 mu1 sig21 r21 y1 c1 : Real) :
    postVar sig20 r20 + postVar sig21 r21
      ≤ (postVar sig20 r20 + sqErr mu0 sig20 r20 y0 c0)
        + (postVar sig21 r21 + sqErr mu1 sig21 r21 y1 c1) :=
  add_le_add_both (posterior_mean_mmse mu0 sig20 r20 y0 c0)
                  (posterior_mean_mmse mu1 sig21 r21 y1 c1)

/-- **Excess risk = `|c − m|²`.** The gap between any estimate's total conditional MSE and
the optimum is exactly the squared distance from the posterior-mean vector — a sum of two
squares, hence `≥ 0` and `= 0` iff `c = m`. So the posterior-mean vector is the unique MMSE
estimator. -/
theorem matrix2_mmse_excess
    (mu0 sig20 r20 y0 c0 mu1 sig21 r21 y1 c1 : Real) :
    ((postVar sig20 r20 + sqErr mu0 sig20 r20 y0 c0)
        + (postVar sig21 r21 + sqErr mu1 sig21 r21 y1 c1))
      - (postVar sig20 r20 + postVar sig21 r21)
      = sqErr mu0 sig20 r20 y0 c0 + sqErr mu1 sig21 r21 y1 c1 := by
  unfold sqErr
  mach_mpoly [postVar sig20 r20, postVar sig21 r21,
    c0 - postMean mu0 sig20 r20 y0, c1 - postMean mu1 sig21 r21 y1]

/-- The excess risk is nonnegative (the posterior-mean vector really is the minimum). -/
theorem matrix2_mmse_excess_nonneg
    (mu0 sig20 r20 y0 c0 mu1 sig21 r21 y1 c1 : Real) :
    0 ≤ sqErr mu0 sig20 r20 y0 c0 + sqErr mu1 sig21 r21 y1 c1 := by
  have h := matrix2_posterior_mean_mmse mu0 sig20 r20 y0 c0 mu1 sig21 r21 y1 c1
  have he := matrix2_mmse_excess mu0 sig20 r20 y0 c0 mu1 sig21 r21 y1 c1
  have : 0 ≤ ((postVar sig20 r20 + sqErr mu0 sig20 r20 y0 c0)
              + (postVar sig21 r21 + sqErr mu1 sig21 r21 y1 c1))
             - (postVar sig20 r20 + postVar sig21 r21) := sub_nonneg_of_le h
  rwa [he] at this

end MachLib.Real
