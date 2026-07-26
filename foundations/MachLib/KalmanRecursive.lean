import MachLib.GaussianConjugacy

/-!
# Recursive (multi-step) Kalman filter (probability frontier)

The single-measurement result (`jointDensity_conjugacy`, `posterior_mean_mmse`) turns into the
*time-recursive* Kalman filter by iterating it: after measurement `y₁` the posterior `N(m₁, P₁)`
becomes the prior for the next measurement `y₂`. Because the conjugacy update maps a Gaussian prior to
a Gaussian posterior, the recursion stays inside the Gaussian family forever, and the recursive
estimate is MMSE-optimal at every step.

This file records the recursion's correctness from the single-step theorems:

* **precisions add** (`postVar_precision`): `1/P' = 1/P + 1/r²` — each measurement adds its precision
  `1/r²` to the posterior precision. This is the recursion's engine; the k-step posterior precision is
  just `1/σ² + Σ 1/rᵢ²`.
* **well-defined** (`kalman_recursive_var_pos`): the recursed posterior variance stays positive.
* **self-composing** (`kalman_recursive_step`): the second measurement's joint density factors by the
  *same* conjugacy, with the first posterior as prior — `jointDensity_conjugacy` at `(m₁, P₁, r₂²)`.
* **optimal at each step** (`kalman_recursive_mmse`): the recursive posterior mean minimizes the
  conditional MSE — `posterior_mean_mmse` at the recursed posterior.

`sorryAx`-free, zero new axioms.
-/

namespace MachLib
namespace Real

private theorem reorder_mul3 (A B C : Real) : A * B * C = A * C * B := by mach_mpoly [A, B, C]
private theorem distrib_precision (s r i j : Real) :
    s * r * (i + j) = r * (s * i) + s * (r * j) := by mach_mpoly [s, r, i, j]

/-- **Precisions add**: `1/(postVar σ² r²) = 1/σ² + 1/r²`. The reciprocal posterior variance
(precision) is the sum of the prior precision and the measurement precision — the engine of the
recursion (the k-step precision is `1/σ² + Σ 1/rᵢ²`). -/
theorem postVar_precision (s r : Real) (hs : 0 < s) (hr : 0 < r) :
    1 / postVar s r = 1 / s + 1 / r := by
  have hpv : 0 < postVar s r := postVar_pos s r hs hr
  have hst : 0 < s + r := add_pos hs hr
  have h1 : postVar s r * (1 / s + 1 / r) = 1 := by
    rw [postVar]
    apply mul_right_cancel' (ne_of_gt hst)
    rw [reorder_mul3 (s * r / (s + r)) (1 / s + 1 / r) (s + r), div_mul_cancel (ne_of_gt hst),
      distrib_precision s r (1 / s) (1 / r), mul_inv s (ne_of_gt hs), mul_inv r (ne_of_gt hr),
      mul_one_ax, mul_one_ax]
    mach_mpoly [s, r]
  exact mul_left_cancel₀ (ne_of_gt hpv) ((mul_inv (postVar s r) (ne_of_gt hpv)).trans h1.symm)

/-- **The recursion is well-defined**: after two updates the posterior variance is still positive. -/
theorem kalman_recursive_var_pos (sig2 r1 r2 : Real) (hsig2 : 0 < sig2) (hr1 : 0 < r1)
    (hr2 : 0 < r2) : 0 < postVar (postVar sig2 r1) r2 :=
  postVar_pos (postVar sig2 r1) r2 (postVar_pos sig2 r1 hsig2 hr1) hr2

/-- **The two-step precision** is the sum of all three precisions — `1/P₂ = 1/σ² + 1/r₁² + 1/r₂²`. -/
theorem kalman_recursive_precision (sig2 r1 r2 : Real) (hsig2 : 0 < sig2) (hr1 : 0 < r1)
    (hr2 : 0 < r2) :
    1 / postVar (postVar sig2 r1) r2 = 1 / sig2 + 1 / r1 + 1 / r2 := by
  rw [postVar_precision (postVar sig2 r1) r2 (postVar_pos sig2 r1 hsig2 hr1) hr2,
    postVar_precision sig2 r1 hsig2 hr1]

/-- **The filter self-composes**: the second measurement's joint density factors by the *same*
conjugacy update, with the first posterior `N(m₁, P₁)` as the prior — `jointDensity_conjugacy`
instantiated at the posterior. This is what makes the filter recursive. -/
theorem kalman_recursive_step (mu sig2 r1 r2 y1 x2 y2 : Real) (hsig2 : 0 < sig2) (hr1 : 0 < r1)
    (hr2 : 0 < r2) :
    jointDensity (postMean mu sig2 r1 y1) (postVar sig2 r1) r2 x2 y2
      = gaussianDensity (postMean mu sig2 r1 y1) (margVar (postVar sig2 r1) r2) y2
        * gaussianDensity
            (postMean (postMean mu sig2 r1 y1) (postVar sig2 r1) r2 y2)
            (postVar (postVar sig2 r1) r2) x2 :=
  jointDensity_conjugacy (postMean mu sig2 r1 y1) (postVar sig2 r1) r2 x2 y2
    (postVar_pos sig2 r1 hsig2 hr1) hr2

/-- **Optimal at each step**: the recursive posterior mean (after two updates) minimizes the
conditional MSE, achieving the recursed posterior variance — `posterior_mean_mmse` at the recursed
posterior. -/
theorem kalman_recursive_mmse (mu sig2 r1 r2 y1 y2 c : Real) :
    postVar (postVar sig2 r1) r2
      ≤ postVar (postVar sig2 r1) r2
        + (c - postMean (postMean mu sig2 r1 y1) (postVar sig2 r1) r2 y2)
          * (c - postMean (postMean mu sig2 r1 y1) (postVar sig2 r1) r2 y2) :=
  posterior_mean_mmse (postMean mu sig2 r1 y1) (postVar sig2 r1) r2 y2 c

end Real
end MachLib
