-- MonogateEML/EMLDuality.lean
-- Formalizes PROP 02-B (Blind Session 02):
-- The exp–log multiplier product at any fixed point of exp equals 1.
-- I.e. if Complex.exp z = z then exp'(z) · log'(z) = 1.
--
-- This is the structural duality observed empirically for the Lambert
-- fixed points z_k* = -W_k(-1) in Blind Session 02/03.
--
-- Session 28 — post-blind research; T_EXP_LOG_DUALITY

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Complex

/-- Any fixed point of `Complex.exp` is non-zero (since `Complex.exp` has no zeros). -/
lemma exp_fixed_point_ne_zero {z : ℂ} (hz : Complex.exp z = z) : z ≠ 0 := by
  intro hz0
  have : Complex.exp z = 0 := by rw [hz]; exact hz0
  exact Complex.exp_ne_zero z this

/-- Pointwise form of `Complex.deriv_exp`. -/
lemma deriv_exp_at (z : ℂ) : deriv Complex.exp z = Complex.exp z :=
  (Complex.hasDerivAt_exp z).deriv

/-- Pointwise form of the complex-log derivative (slit-plane). -/
lemma deriv_log_at {z : ℂ} (hdom : z ∈ Complex.slitPlane) :
    deriv Complex.log z = z⁻¹ :=
  (Complex.hasDerivAt_log hdom).deriv

/-- Corollary: the fixed-point multiplier of `Complex.exp` at `z*` is exactly
    `z*` itself, so `|mult_exp| = |z*|`. -/
theorem exp_fixed_point_multiplier_equals_z
    {z : ℂ} (hz : Complex.exp z = z) :
    deriv Complex.exp z = z := by
  rw [deriv_exp_at, hz]

/-- The log-multiplier at any slit-plane point is the reciprocal. -/
theorem log_multiplier_at_exp_fixed_point
    {z : ℂ} (_hz : Complex.exp z = z) (hdom : z ∈ Complex.slitPlane) :
    deriv Complex.log z = z⁻¹ :=
  deriv_log_at hdom

/-- **PROP 02-B**: The multiplier product `(exp)'(z) · (log)'(z)` equals 1
    at any fixed point of `exp` lying in the slit plane (where `log` is
    differentiable).

    Empirically verified in Blind Session 02 for the Lambert fixed points
    `z_k* = -W_k(-1)`: they are all repelling under exp (|mult| = |z_k*| > 1)
    and attracting under log (|mult| = 1/|z_k*| < 1), with product exactly 1. -/
theorem exp_log_multiplier_product_at_fixed_point
    {z : ℂ} (hz : Complex.exp z = z) (hdom : z ∈ Complex.slitPlane) :
    deriv Complex.exp z * deriv Complex.log z = 1 := by
  have hne : z ≠ 0 := exp_fixed_point_ne_zero hz
  rw [deriv_exp_at, deriv_log_at hdom, hz]
  field_simp

-- ===================================================================
-- Core complex exp/log identities (named aliases over Mathlib)
-- ===================================================================

/-- Complex exp is never zero. -/
theorem complex_exp_ne_zero (z : ℂ) : Complex.exp z ≠ 0 := Complex.exp_ne_zero z

/-- exp(0) = 1 in ℂ. -/
theorem complex_exp_zero_eq_one : Complex.exp 0 = 1 := Complex.exp_zero

/-- Complex exp distributes over addition: exp(z + w) = exp z · exp w. -/
theorem complex_exp_add (z w : ℂ) :
    Complex.exp (z + w) = Complex.exp z * Complex.exp w := Complex.exp_add z w

/-- Complex exp of negation: exp(−z) = 1 / exp z. -/
theorem complex_exp_neg (z : ℂ) : Complex.exp (-z) = (Complex.exp z)⁻¹ :=
  Complex.exp_neg z

/-- Complex exp of subtraction: exp(z − w) = exp z / exp w. -/
theorem complex_exp_sub (z w : ℂ) :
    Complex.exp (z - w) = Complex.exp z / Complex.exp w := Complex.exp_sub z w

/-- Log of complex exp on a range that makes the round-trip valid
    (Mathlib convention; equality holds modulo 2πi for the imaginary part).
    For the round-trip at 0: `log 1 = 0`. -/
theorem complex_log_one : Complex.log 1 = 0 := Complex.log_one

-- ===================================================================
-- Euler-style identities
-- ===================================================================

/-- Euler: exp(π · i) = −1. -/
theorem complex_exp_pi_I : Complex.exp (↑Real.pi * Complex.I) = -1 :=
  Complex.exp_pi_mul_I

/-- Euler: exp(0 · i) = 1 (trivial; base atom). -/
theorem complex_exp_zero_I : Complex.exp ((0 : ℝ) * Complex.I) = 1 := by
  simp [Complex.exp_zero]

-- ===================================================================
-- Fixed-point corollaries (restatements of the main theorem)
-- ===================================================================

/-- At any fixed point `z* ∈ slitPlane` of `Complex.exp`, the exp-multiplier
    is `z*` itself (restatement of `exp_fixed_point_multiplier_equals_z`). -/
theorem mult_exp_at_fp_eq_z
    {z : ℂ} (hz : Complex.exp z = z) :
    deriv Complex.exp z = z :=
  exp_fixed_point_multiplier_equals_z hz

/-- At any fixed point `z* ∈ slitPlane`, the log-multiplier is `1/z*`. -/
theorem mult_log_at_fp_eq_inv_z
    {z : ℂ} (_hz : Complex.exp z = z) (hdom : z ∈ Complex.slitPlane) :
    deriv Complex.log z = z⁻¹ :=
  deriv_log_at hdom

/-- The Blind-Session-02 duality restated as `mult_log = (mult_exp)⁻¹`
    at any slit-plane fixed point. -/
theorem mult_log_is_inv_mult_exp
    {z : ℂ} (hz : Complex.exp z = z) (hdom : z ∈ Complex.slitPlane) :
    deriv Complex.log z = (deriv Complex.exp z)⁻¹ := by
  have hne : z ≠ 0 := exp_fixed_point_ne_zero hz
  rw [mult_exp_at_fp_eq_z hz, mult_log_at_fp_eq_inv_z hz hdom]

-- ===================================================================
-- exp_pos for the complex derivative at any point
-- ===================================================================

/-- `(exp)'(z) = exp(z) ≠ 0` — the exp-derivative is nonvanishing everywhere. -/
theorem deriv_exp_ne_zero (z : ℂ) : deriv Complex.exp z ≠ 0 := by
  rw [deriv_exp_at]; exact Complex.exp_ne_zero z
