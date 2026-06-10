import MachLib.Exp
import MachLib.Log
import MachLib.EML
import MachLib.SinNotInEML
import MachLib.CosNotInEML
import MachLib.EMLHierarchy

/-!
# `exp ∘ exp ∉ EML_1` — per-case bounded results

Partial closure of the deferred direction `exp_exp_not_in_eml_1` from
`MachLib.EMLHierarchy`. Five of six depth-≤-1 grammar shapes are shown
not to evaluate to `exp(exp x)` globally. Each shape gets its own
positive theorem.

The remaining sixth shape — `eml(var, const c2)` — forces the algebraic
equation `exp(exp 1) = 2 * exp 1 - 1`, which is false but requires either
a numerical-bound axiom (`exp(exp 1) > 2 * exp 1 - 1`) or the convexity
infrastructure `exp x ≥ 1 + x` to contradict cleanly. Neither is in
MachLib's current axiom set; deferred to a dedicated future bounded
artifact.

The five proven cases cover:
- `const c`
- `var`
- `eml(const c1, const c2)`
- `eml(const c1, var)`
- `eml(var, var)`

The single technique behind all five is: at the evaluation points chosen,
`exp(exp x) = (some tree).eval x` simplifies to `exp 1 = exp(exp 1)`,
hence `1 = exp 1` via `exp_injective`, contradicting `one_lt_exp_one`.
For `var`, the contradiction is even simpler: `var(0) = 0` vs
`exp(exp 0) = exp 1 > 0`.

This file does not depend on Mathlib.
-/

namespace MachLib

open Real

/-- A constant function cannot equal `exp ∘ exp` globally. -/
theorem exp_exp_ne_const (c : Real) :
    ¬ (∀ x : Real, Real.exp (Real.exp x) = (EMLTree.const c).eval x) := by
  intro hexp
  have h0 := hexp 0
  have h1 := hexp 1
  simp only [EMLTree.eval] at h0 h1
  rw [exp_zero] at h0
  -- h0 : exp 1 = c, h1 : exp (exp 1) = c
  have heq : exp 1 = exp (exp 1) := h0.trans h1.symm
  have h1eq : (1 : Real) = exp 1 := exp_injective heq
  have hlt : (1 : Real) < exp 1 := one_lt_exp_one
  rw [← h1eq] at hlt
  exact lt_irrefl_ax 1 hlt

/-- The identity function cannot equal `exp ∘ exp` globally. -/
theorem exp_exp_ne_var :
    ¬ (∀ x : Real, Real.exp (Real.exp x) = EMLTree.var.eval x) := by
  intro hexp
  have h := hexp 0
  simp only [EMLTree.eval] at h
  rw [exp_zero] at h
  -- h : exp 1 = 0
  have hpos : 0 < exp 1 := exp_pos 1
  rw [h] at hpos
  exact lt_irrefl_ax 0 hpos

/-- A constant-constant `eml` (still constant) cannot equal `exp ∘ exp`. -/
theorem exp_exp_ne_eml_const_const (c1 c2 : Real) :
    ¬ (∀ x : Real,
        Real.exp (Real.exp x) =
          (EMLTree.eml (.const c1) (.const c2)).eval x) := by
  intro hexp
  have h0 := hexp 0
  have h1 := hexp 1
  simp only [EMLTree.eval] at h0 h1
  rw [exp_zero] at h0
  -- h0 : exp 1 = exp c1 - log c2, h1 : exp (exp 1) = exp c1 - log c2
  have heq : exp 1 = exp (exp 1) := h0.trans h1.symm
  have h1eq : (1 : Real) = exp 1 := exp_injective heq
  have hlt : (1 : Real) < exp 1 := one_lt_exp_one
  rw [← h1eq] at hlt
  exact lt_irrefl_ax 1 hlt

/-- `eml(const c1, var)` cannot equal `exp ∘ exp`.

At x = 0, `log 0 = 0` collapses eval to `exp c1 = exp 1`, forcing c1 = 1.
At x = 1, `log 1 = 0` collapses eval to `exp 1 = exp(exp 1)`, the same
`e = exp e` contradiction. -/
theorem exp_exp_ne_eml_const_var (c1 : Real) :
    ¬ (∀ x : Real,
        Real.exp (Real.exp x) =
          (EMLTree.eml (.const c1) .var).eval x) := by
  intro hexp
  have h0 := hexp 0
  have h1 := hexp 1
  simp only [EMLTree.eval, log_zero, sub_zero, log_one] at h0 h1
  rw [exp_zero] at h0
  -- h0 : exp 1 = exp c1, h1 : exp (exp 1) = exp c1
  have heq : exp 1 = exp (exp 1) := h0.trans h1.symm
  have h1eq : (1 : Real) = exp 1 := exp_injective heq
  have hlt : (1 : Real) < exp 1 := one_lt_exp_one
  rw [← h1eq] at hlt
  exact lt_irrefl_ax 1 hlt

/-- `eml(var, var)` cannot equal `exp ∘ exp`.

At x = 1, `log 1 = 0` collapses eval to `exp 1`, and the equation
`exp(exp 1) = exp 1` gives the same `e = exp e` contradiction. -/
theorem exp_exp_ne_eml_var_var :
    ¬ (∀ x : Real,
        Real.exp (Real.exp x) =
          (EMLTree.eml .var .var).eval x) := by
  intro hexp
  have h := hexp 1
  simp only [EMLTree.eval, log_one, sub_zero] at h
  -- h : exp (exp 1) = exp 1
  have heq : exp 1 = exp (exp 1) := h.symm
  have h1eq : (1 : Real) = exp 1 := exp_injective heq
  have hlt : (1 : Real) < exp 1 := one_lt_exp_one
  rw [← h1eq] at hlt
  exact lt_irrefl_ax 1 hlt

/-! ### Deferred case: `eml(var, const c2)`

The sixth depth-≤-1 grammar shape `eml(var, const c2)` is **not** closed
in this file. The argument structure is: `eval x = exp x - log c2`,
evaluation at x = 0 forces `log c2 = 1 - exp 1`, evaluation at x = 1
forces `exp(exp 1) = 2 * exp 1 - 1`. This is false numerically
(`exp(exp 1) ≈ 15.15`, `2 * exp 1 - 1 ≈ 4.44`) but contradicting it
in MachLib needs one of:

- A numerical-bound axiom `exp_e_gt_two_e_minus_one : exp(exp 1) > 2 * exp 1 - 1`.
- The convexity infrastructure `exp_lower_bound : ∀ x, 1 + x ≤ exp x`,
  whence `1 + exp 1 ≤ exp(exp 1)`, and since `exp 1 > 1` gives
  `1 + exp 1 > 2 * exp 1 - 1` (i.e., `2 > exp 1` which is FALSE since
  exp_one_gt_two would give the opposite). The convexity bound alone
  is therefore insufficient; the numerical-bound axiom is the cleaner
  path.

Either path is a small contribution to MachLib's analytic infrastructure,
better packaged as its own bounded artifact than as a one-off addition
here. -/

end MachLib
