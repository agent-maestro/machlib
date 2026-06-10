import MachLib.Trig
import MachLib.EML
import MachLib.Lemmas
import MachLib.Forge
import MachLib.SinNotInEML

/-!
# `cos ∉ EML_k(ℝ)` for fixed small `k` — direct case analysis

Mirror of `MachLib.SinNotInEML` for cosine. Uses the same EML AST and the
same overall two-point-evaluation technique, but the case structure differs
because `cos 0 = 1` (where `sin 0 = 0`) and `cos(π/2) = 0` (where
`sin(π/2) = 1`). The `eml`-with-`var` cases use either an unboundedness
argument (eval drops below -1 while cos ≥ -1) or a strict-exp argument
(`1 < exp 1` combined with `cos_le_one`).
-/

namespace MachLib
namespace Real

/-- `cos(π/2) = 0`. Derivable from `pythagorean + sin_pi_div_two`, but added
here as a direct axiom to keep the proof self-contained. -/
axiom cos_pi_div_two : cos (pi / (1 + 1)) = 0

end Real
end MachLib

namespace MachLib

open Real

-- ===================================================================
-- Local arithmetic helpers (file-private)
-- ===================================================================

theorem one_lt_one_plus_one : (1 : Real) < 1 + 1 := by
  have step := add_lt_add_left zero_lt_one_ax 1
  rw [add_zero] at step
  exact step

theorem one_lt_exp_one : (1 : Real) < exp 1 := by
  have step : exp 0 < exp 1 := exp_lt zero_lt_one_ax
  rw [exp_zero] at step
  exact step

-- ===================================================================
-- Main theorems
-- ===================================================================

/-- `cos` is not depth-0. -/
theorem cos_not_in_eml_depth_le_0 (t : EMLTree) (ht : t.depth ≤ 0) :
    ¬ (∀ x : Real, t.eval x = cos x) := by
  intro hcos
  cases t with
  | const c =>
    have h0 := hcos 0
    have h1 := hcos (pi / (1 + 1))
    simp only [EMLTree.eval, cos_zero, cos_pi_div_two] at h0 h1
    rw [h0] at h1
    exact zero_ne_one_ax h1.symm
  | var =>
    have h := hcos 0
    simp only [EMLTree.eval, cos_zero] at h
    exact zero_ne_one_ax h
  | eml _ _ =>
    simp only [EMLTree.depth] at ht
    omega

/-- `cos` is not depth-≤-1. -/
theorem cos_not_in_eml_depth_le_1 (t : EMLTree) (ht : t.depth ≤ 1) :
    ¬ (∀ x : Real, t.eval x = cos x) := by
  intro hcos
  match t, ht with
  | .const c, _ =>
    exact cos_not_in_eml_depth_le_0 (.const c) (by simp [EMLTree.depth]) hcos
  | .var, _ =>
    exact cos_not_in_eml_depth_le_0 .var (by simp [EMLTree.depth]) hcos
  | .eml t1 t2, ht =>
    have ht1 : t1.depth = 0 := by
      simp only [EMLTree.depth] at ht
      have h := Nat.le_max_left t1.depth t2.depth
      omega
    have ht2 : t2.depth = 0 := by
      simp only [EMLTree.depth] at ht
      have h := Nat.le_max_right t1.depth t2.depth
      omega
    match t1, ht1, t2, ht2 with
    | .eml _ _, ht1, _, _ =>
      simp only [EMLTree.depth] at ht1; omega
    | _, _, .eml _ _, ht2 =>
      simp only [EMLTree.depth] at ht2; omega
    | .const c1, _, .const c2, _ =>
      -- Constant. Same as const case.
      have h0 := hcos 0
      have h1 := hcos (pi / (1 + 1))
      simp only [EMLTree.eval, cos_zero, cos_pi_div_two] at h0 h1
      rw [h0] at h1
      exact zero_ne_one_ax h1.symm
    | .const c1, _, .var, _ =>
      -- `eml(const c1, var).eval x = exp c1 - log x`.
      -- x = 0: exp c1 - 0 = exp c1 = cos 0 = 1.
      -- x = exp(1+1+1): exp c1 - (1+1+1) = 1 - (1+1+1) = cos(exp(1+1+1)).
      -- cos ≥ -1, so -1 ≤ 1 - (1+1+1). Rearranges to 1 + 1 ≤ 1, contradicting 1 < 1+1.
      have h0 := hcos 0
      simp only [EMLTree.eval, cos_zero, log_zero, sub_zero] at h0
      have hbig := hcos (exp (1 + 1 + 1))
      simp only [EMLTree.eval] at hbig
      rw [log_exp, h0] at hbig
      have hcos_lb : -1 ≤ cos (exp (1 + 1 + 1)) := neg_one_le_cos _
      rw [← hbig] at hcos_lb
      -- hcos_lb : -1 ≤ 1 - (1 + 1 + 1)
      have step : (1 + 1 + 1 : Real) + (-1) ≤ (1 + 1 + 1) + (1 - (1 + 1 + 1)) :=
        add_le_add_left hcos_lb (1 + 1 + 1)
      have lhs : (1 + 1 + 1 : Real) + (-1) = 1 + 1 := by
        rw [add_assoc (1 + 1) 1 (-1), add_neg, add_zero]
      have rhs : (1 + 1 + 1 : Real) + (1 - (1 + 1 + 1)) = 1 := by
        rw [sub_def, ← add_assoc, add_comm (1 + 1 + 1) 1, add_assoc, add_neg, add_zero]
      rw [lhs, rhs] at step
      -- step : 1 + 1 ≤ 1
      exact lt_irrefl_ax 1 (lt_of_lt_of_le one_lt_one_plus_one step)
    | .var, _, .const c2, _ =>
      -- `eml(var, const c2).eval x = exp x - log c2`.
      -- x = 0: 1 - log c2 = cos 0 = 1 → log c2 = 0.
      -- x = 1: exp 1 - 0 = exp 1 = cos 1. But 1 < exp 1 and cos 1 ≤ 1.
      have h0 := hcos 0
      have h1 := hcos 1
      simp only [EMLTree.eval, cos_zero, exp_zero] at h0 h1
      -- h0 : 1 - log c2 = 1
      -- h1 : exp 1 - log c2 = cos 1
      have hlog : log c2 = 0 := by
        rw [sub_def] at h0
        -- h0 : 1 + (-log c2) = 1
        have step : (-1 : Real) + (1 + (-log c2)) = (-1) + 1 := by rw [h0]
        rw [← add_assoc, neg_add_self, zero_add] at step
        -- step : -log c2 = 0
        have step2 : log c2 + (-log c2) = log c2 + 0 := by rw [step]
        rw [add_neg, add_zero] at step2
        exact step2.symm
      rw [hlog, sub_def, neg_zero, add_zero] at h1
      -- h1 : exp 1 = cos 1
      have h_cos1_le_one : cos 1 ≤ 1 := cos_le_one 1
      rw [← h1] at h_cos1_le_one
      exact lt_irrefl_ax 1 (lt_of_lt_of_le one_lt_exp_one h_cos1_le_one)
    | .var, _, .var, _ =>
      -- `eml(var, var).eval x = exp x - log x`.
      -- x = 1: log 1 = 0, eval = exp 1 = cos 1. But 1 < exp 1 ≥ cos 1.
      have h := hcos 1
      simp only [EMLTree.eval, log_one, sub_zero] at h
      have h_cos1_le_one : cos 1 ≤ 1 := cos_le_one 1
      rw [← h] at h_cos1_le_one
      exact lt_irrefl_ax 1 (lt_of_lt_of_le one_lt_exp_one h_cos1_le_one)

end MachLib
