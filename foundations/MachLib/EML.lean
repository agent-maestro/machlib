import MachLib.Exp
import MachLib.Log

/-
MachLib.EML — the Exp-Minus-Log primitive.

The core EML primitive is the two-argument operation

  eml(x, y) := exp(x) - log(y)

EML's universality theorem says that every elementary function
on the reals (every closed-form expression in `+`, `-`, `*`, `/`,
`exp`, `log`, polynomial, …) can be rewritten as a finite tree
of `eml`, `+`, `*`, and constants. That is, `eml` together with
ring arithmetic generates the elementary closure.

This file:

  * defines `eml`,
  * proves the two specialisations that recover `exp` and `log`
    individually,
  * proves the lightweight algebraic rearrangements MachLib's
    downstream theorems use.

The full universality theorem is structural — every elementary
function rewrites to an `eml` tree — and is the subject of
`MachLib.Universality` (forthcoming, requires the EML AST type
which we do not yet have in MachLib).
-/

namespace MachLib
namespace Real

/-- The core EML primitive: `eml(x, y) = exp(x) - log(y)`. -/
noncomputable def eml (x y : Real) : Real := exp x - log y

/-! ### Helper: `-0 = 0` -/

theorem neg_zero : -(0 : Real) = 0 := by
  have h1 : -(0 : Real) + 0 = 0 := by
    rw [add_comm]; exact add_neg 0
  have h2 : -(0 : Real) + 0 = -(0 : Real) := add_zero _
  rw [h2] at h1
  exact h1

theorem sub_zero (x : Real) : x - 0 = x := by
  rw [sub_def, neg_zero, add_zero]

/-! ### Specialisations -/

/-- `eml(x, 1) = exp(x)`. The "exp branch" of EML. -/
theorem eml_arg2_one (x : Real) : eml x 1 = exp x := by
  unfold eml
  rw [log_one, sub_zero]

/-- `eml(0, y) = 1 - log(y)`. The "log branch" of EML. -/
theorem eml_arg1_zero (y : Real) : eml 0 y = 1 - log y := by
  unfold eml
  rw [exp_zero]

/-! ### Basic algebraic rearrangements -/

theorem eml_def_unfold (x y : Real) : eml x y = exp x - log y := rfl

/-! ### Atlas / Advantage Lab witnesses -/

/-- Subtraction boundary witness for the EML Atlas gate and Advantage Lab.
For positive `v`, feeding inverse-shaped arguments into EML recovers flat
subtraction: `eml(log v, exp u) = v - u`. -/
theorem eml_log_exp_subtraction_boundary (v u : Real) (hv : 0 < v) :
    eml (log v) (exp u) = v - u := by
  unfold eml
  rw [exp_log hv, log_exp]

/-! ### Constant boundary witnesses -/

/-- Constant boundary witness: `eml(0, exp(1)) = 0`.
This is the local MachLib spelling of the Atlas shorthand `eml(0,e)=0`. -/
theorem eml_zero_exp_one_zero : eml 0 (exp 1) = 0 := by
  unfold eml
  rw [exp_zero, log_exp, sub_def, add_neg]

/-- Constant boundary witness: `eml(0, 1) = 1`. -/
theorem eml_zero_one_one : eml 0 1 = 1 := by
  rw [eml_arg1_zero, log_one, sub_zero]

/-- Constant boundary witness: `eml(1, 1) = exp(1)`. -/
theorem eml_one_one_exp_one : eml 1 1 = exp 1 := by
  exact eml_arg2_one 1

end Real
end MachLib
