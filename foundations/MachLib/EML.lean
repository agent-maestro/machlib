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
namespace R

/-- The core EML primitive: `eml(x, y) = exp(x) - log(y)`. -/
noncomputable def eml (x y : R) : R := exp x - log y

/-! ### Helper: `-0 = 0` -/

theorem neg_zero : -(0 : R) = 0 := by
  have h1 : -(0 : R) + 0 = 0 := by
    rw [add_comm]; exact add_neg 0
  have h2 : -(0 : R) + 0 = -(0 : R) := add_zero _
  rw [h2] at h1
  exact h1

theorem sub_zero (x : R) : x - 0 = x := by
  rw [sub_def, neg_zero, add_zero]

/-! ### Specialisations -/

/-- `eml(x, 1) = exp(x)`. The "exp branch" of EML. -/
theorem eml_arg2_one (x : R) : eml x 1 = exp x := by
  unfold eml
  rw [log_one, sub_zero]

/-- `eml(0, y) = 1 - log(y)`. The "log branch" of EML. -/
theorem eml_arg1_zero (y : R) : eml 0 y = 1 - log y := by
  unfold eml
  rw [exp_zero]

/-! ### Basic algebraic rearrangements -/

theorem eml_def_unfold (x y : R) : eml x y = exp x - log y := rfl

end R
end MachLib
