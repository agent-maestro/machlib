import MachLib.EML
import MachLib.Forge
import MachLib.HyperbolicPreservation
import MachLib.Lemmas

/-!
MachLib.ProofSpine — small checked obligations for the EML / Forge /
CapCard evidence bridge.

This module is intentionally narrow. It is not a broad theorem-library
claim; it gives product surfaces a compact set of named Lean artifacts
that can be referenced as evidence when explaining what MachLib checks.
-/

namespace MachLib
namespace ProofSpine

open MachLib.Real

/-! ## EML primitive obligations -/

/-- EML recovers the exp branch when the log argument is one. -/
theorem eml_exp_branch_checked (x : Real) :
    eml x 1 = exp x :=
  eml_arg2_one x

/-- EML exposes the log branch as `1 - log y` at first argument zero. -/
theorem eml_log_branch_checked (y : Real) :
    eml 0 y = 1 - log y :=
  eml_arg1_zero y

/-! ## Exponential rewrite obligations -/

/-- `exp 0 = 1`, the normalization point for exp rewrites. -/
theorem exp_zero_checked : exp 0 = 1 :=
  exp_zero

/-- Subtraction lowers through exp as division. -/
theorem exp_sub_checked (x y : Real) :
    exp (x - y) = exp x / exp y :=
  exp_sub x y

/-! ## Trig / hyperbolic identity obligations -/

/-- Sine/cosine Pythagorean identity in MachLib product form. -/
theorem sin_cos_pythagorean_checked (x : Real) :
    sin x * sin x + cos x * cos x = 1 :=
  sin_sq_add_cos_sq x

/-- Swapped cosine/sine Pythagorean identity for Forge matrix witnesses. -/
theorem cos_sin_pythagorean_swapped_checked (x : Real) :
    cos x * cos x + sin x * sin x = 1 :=
  cos_sq_add_sin_sq x

/-- Hyperbolic Pythagorean identity in MachLib product form. -/
theorem cosh_sinh_pythagorean_checked (x : Real) :
    cosh x * cosh x - sinh x * sinh x = 1 :=
  HyperbolicPreservation.cosh_sq_sub_sinh_sq x

/-- Cosh decomposes to exp-arithmetic, which is the EML-facing bridge. -/
theorem cosh_exp_decomposition_checked (x : Real) :
    cosh x = (exp x + exp (-x)) / (1 + 1) :=
  HyperbolicPreservation.cosh_as_exp_arithmetic x

/-! ## Forge guard obligations -/

/-- Product of nonnegative values remains nonnegative. -/
theorem nonneg_product_guard_checked (a b : Real)
    (ha : (0 : Real) ≤ a) (hb : (0 : Real) ≤ b) :
    (0 : Real) ≤ a * b :=
  mul_nonneg ha hb

/-- `max 0 (min x 1)` has a nonnegative lower guard. -/
theorem saturate_lower_guard_checked (x : Real) :
    (0 : Real) ≤ max 0 (min x 1) :=
  max_nonneg_left (le_refl 0)

end ProofSpine
end MachLib
