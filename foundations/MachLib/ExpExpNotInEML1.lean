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
namespace Real

/-- `exp(exp x) - exp x` is strictly increasing in `x`. Used to close the
`eml(var, const c2)` case of `exp(exp x) ∉ EML_1` (where the hypothesis
forces `exp(exp x) - exp x = constant`, contradicting strict
monotonicity).

This is a natural analytic property of `f(x) = exp(exp x) - exp x`: its
derivative is `exp x · exp(exp x) - exp x = exp x · (exp(exp x) - 1)`,
which is positive for all real `x` because `exp(exp x) > 1` (since
`exp x > 0`). Added as a direct axiom in MachLib until the convexity /
monotonicity infrastructure is fully formalized; replaces a more
specific numerical-bound axiom. -/
axiom exp_exp_minus_exp_strictly_increasing :
    ∀ x y : Real, x < y → exp (exp x) - exp x < exp (exp y) - exp y

end Real
end MachLib

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

/-- `eml(var, const c2)` cannot equal `exp ∘ exp`.

The hypothesis `exp(exp x) = exp x - log c2` for all `x` forces
`exp(exp x) - exp x = -log c2`, a constant. But by
`exp_exp_minus_exp_strictly_increasing`, the function
`x ↦ exp(exp x) - exp x` is strictly increasing, so it cannot be
constant. Concretely, the values at `x = 0` and `x = 1` must differ
strictly. -/
theorem exp_exp_ne_eml_var_const (c2 : Real) :
    ¬ (∀ x : Real,
        Real.exp (Real.exp x) =
          (EMLTree.eml .var (.const c2)).eval x) := by
  intro hexp
  have h0 := hexp 0
  have h1 := hexp 1
  simp only [EMLTree.eval, exp_zero] at h0 h1
  -- h0 : exp 1 = 1 - log c2
  -- h1 : exp (exp 1) = exp 1 - log c2
  -- Derive -log c2 = exp 1 - 1 from h0:
  have hneg_log : -log c2 = exp 1 - 1 := by
    rw [sub_def] at h0
    -- h0 : exp 1 = 1 + -log c2
    have step : (-1 : Real) + (1 + -log c2) = (-1) + exp 1 := by rw [h0]
    rw [← add_assoc, neg_add_self, zero_add] at step
    -- step : -log c2 = -1 + exp 1
    rw [add_comm (-1 : Real) (exp 1), ← sub_def] at step
    exact step
  -- Compute exp(exp 1) - exp 1 = -log c2 from h1:
  have hexp_diff : exp (exp 1) - exp 1 = -log c2 := by
    rw [h1, sub_def, sub_def, add_assoc, add_comm (-log c2) (-exp 1),
        ← add_assoc, add_neg, zero_add]
  -- Combine: exp(exp 1) - exp 1 = exp 1 - 1.
  have key : exp (exp 1) - exp 1 = exp 1 - 1 := hexp_diff.trans hneg_log
  -- Strict monotonicity gives the opposite strict inequality:
  -- exp(exp 0) - exp 0 < exp(exp 1) - exp 1
  have hlt : exp (exp 0) - exp 0 < exp (exp 1) - exp 1 :=
    exp_exp_minus_exp_strictly_increasing 0 1 zero_lt_one_ax
  rw [exp_zero] at hlt
  -- hlt : exp 1 - 1 < exp (exp 1) - exp 1
  rw [key] at hlt
  -- hlt : exp 1 - 1 < exp 1 - 1
  exact lt_irrefl_ax _ hlt

/-- **Master theorem:** `exp ∘ exp ∉ EML_1`.

Combines the six per-case theorems via the EMLTree case analysis.
This closes the deferred direction of `EML_1 ⊊ EML_2` from
`MachLib.EMLHierarchy`. -/
theorem exp_exp_not_in_eml_1 :
    ¬ InEMLDepth (fun x : Real => Real.exp (Real.exp x)) 1 := by
  intro ⟨t, htd, hexp⟩
  match t, htd with
  | .const c, _ =>
    exact exp_exp_ne_const c (fun x => hexp x)
  | .var, _ =>
    exact exp_exp_ne_var (fun x => hexp x)
  | .eml t1 t2, htd =>
    have ht1 : t1.depth = 0 := by
      simp only [EMLTree.depth] at htd
      have h := Nat.le_max_left t1.depth t2.depth
      omega
    have ht2 : t2.depth = 0 := by
      simp only [EMLTree.depth] at htd
      have h := Nat.le_max_right t1.depth t2.depth
      omega
    match t1, ht1, t2, ht2 with
    | .eml _ _, ht1, _, _ =>
      simp only [EMLTree.depth] at ht1; omega
    | _, _, .eml _ _, ht2 =>
      simp only [EMLTree.depth] at ht2; omega
    | .const c1, _, .const c2, _ =>
      exact exp_exp_ne_eml_const_const c1 c2 (fun x => hexp x)
    | .const c1, _, .var, _ =>
      exact exp_exp_ne_eml_const_var c1 (fun x => hexp x)
    | .var, _, .const c2, _ =>
      exact exp_exp_ne_eml_var_const c2 (fun x => hexp x)
    | .var, _, .var, _ =>
      exact exp_exp_ne_eml_var_var (fun x => hexp x)

/-- **`EML_1 ⊊ EML_2`** as a strict containment, witnessed by `exp ∘ exp`. -/
theorem strict_eml_one_subset_eml_two :
    (∀ f : Real → Real, InEMLDepth f 1 → InEMLDepth f 2) ∧
    (∃ f : Real → Real, InEMLDepth f 2 ∧ ¬ InEMLDepth f 1) :=
  ⟨eml_one_subset_eml_two,
   ⟨fun x => Real.exp (Real.exp x), exp_exp_in_eml_2, exp_exp_not_in_eml_1⟩⟩

end MachLib
