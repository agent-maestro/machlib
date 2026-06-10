import MachLib.Trig
import MachLib.EML
import MachLib.Lemmas

/-!
# `sin ∉ EML_k(ℝ)` for fixed small `k` — direct case analysis

This file ports monogate-lean's `MonogateEML.SinNotInEMLDepthBounds`
(which depended on Mathlib) onto MachLib's zero-Mathlib foundations.

The statement: `Real.sin` cannot equal `t.eval` globally for any EML
tree of depth ≤ k, for fixed small k. Closed here for k = 0 and k = 1
by explicit case analysis at chosen evaluation points; the technique
generalizes mechanically to fixed K (depth_le_2, ...).

Strategically: this is what the trig barrier theorem looks like in
MachLib's Real-valued, Mathlib-free setting. The Complex-valued
formulation in monogate-lean's legacy file stays as a private reference
during the migration but is not the long-lived artifact.

Strategic context:
`monogate-research/exploration/alpha_sin_not_in_eml_depth_2_feasibility_scoping_2026_06_10/FINDINGS.md`.
-/

namespace MachLib
namespace Real

-- ===================================================================
-- One small new MachLib axiom needed for this proof
-- ===================================================================

/-- `sin(π/2) = 1`. The sign of `sin(π/2)` is the one piece of
information that does not drop out of `pythagorean + sin_add + cos_add
+ sin_pi + cos_pi`; the standing axiom set determines `sin(π/2) = ±1`
but not the sign. We pin it here at `+1` to match the standard
convention. -/
axiom sin_pi_div_two : sin (pi / (1 + 1)) = 1

-- ===================================================================
-- Small helper: log 0 = 0 (follows from log's definition)
-- ===================================================================

theorem log_zero : log 0 = 0 := by
  unfold log
  exact dif_neg (lt_irrefl_ax 0)

end Real
end MachLib

-- ===================================================================
-- EML tree AST (Real-valued, MachLib-native)
-- ===================================================================

namespace MachLib

/-- AST of EML expressions over ℝ.

Mirrors monogate-lean's `MonogateEML.EMLTree` but with `Real`-valued
constants instead of `Complex`-valued constants. The third
constructor is named `eml` to match the underlying operation
`MachLib.Real.eml`, but lives at the `EMLTree.` namespace so there
is no collision with the `Real` operation. -/
inductive EMLTree : Type where
  | const : Real → EMLTree
  | var   : EMLTree
  | eml   : EMLTree → EMLTree → EMLTree

namespace EMLTree

/-- Depth of an EML tree. `eml` nodes contribute one level of nesting;
constants and the variable are depth 0. -/
def depth : EMLTree → Nat
  | const _   => 0
  | var       => 0
  | eml t1 t2 => 1 + max t1.depth t2.depth

/-- Real evaluation of an EML tree at `x : Real`. Uses MachLib's
`Real.exp` and `Real.log` — no Mathlib, no Complex. -/
noncomputable def eval (t : EMLTree) (x : Real) : Real :=
  match t with
  | const c   => c
  | var       => x
  | eml t1 t2 => Real.exp (t1.eval x) - Real.log (t2.eval x)

end EMLTree

end MachLib

-- ===================================================================
-- Main theorems
-- ===================================================================

namespace MachLib

open Real

/-- `sin` is not depth-0. The depth-0 grammar is `const c | var`. -/
theorem sin_not_in_eml_depth_le_0 (t : EMLTree) (ht : t.depth ≤ 0) :
    ¬ (∀ x : Real, t.eval x = sin x) := by
  intro hsin
  cases t with
  | const c =>
    -- Constant-function argument: c = sin 0 = 0 AND c = sin(π/2) = 1.
    have h0 := hsin 0
    have h1 := hsin (pi / (1 + 1))
    simp only [EMLTree.eval, sin_zero, sin_pi_div_two] at h0 h1
    -- h0 : c = 0, h1 : c = 1
    rw [h0] at h1
    exact zero_ne_one_ax h1
  | var =>
    -- Identity-function argument: var.eval π = π, but sin π = 0, and π ≠ 0.
    have h := hsin pi
    simp only [EMLTree.eval, sin_pi] at h
    -- h : pi = 0; but pi_pos says 0 < pi, contradiction.
    have hpos : (0 : Real) < pi := pi_pos
    rw [h] at hpos
    exact lt_irrefl_ax 0 hpos
  | eml _ _ =>
    -- An `eml` node has depth ≥ 1, contradicting ht : depth ≤ 0.
    simp only [EMLTree.depth] at ht
    omega

/-- `sin` is not depth-≤-1.

Proof: two-point evaluation at carefully chosen `x` values. The
depth-1 grammar has six shapes — `const c`, `var`, and the four
leaf-pair `eml`-nodes (`eml(const, const)`, `eml(const, var)`,
`eml(var, const)`, `eml(var, var)`); each forces a contradiction
on the assumed equation `t.eval = sin`. -/
theorem sin_not_in_eml_depth_le_1 (t : EMLTree) (ht : t.depth ≤ 1) :
    ¬ (∀ x : Real, t.eval x = sin x) := by
  intro hsin
  match t, ht with
  | .const c, _ =>
    exact sin_not_in_eml_depth_le_0 (.const c) (by simp [EMLTree.depth]) hsin
  | .var, _ =>
    exact sin_not_in_eml_depth_le_0 .var (by simp [EMLTree.depth]) hsin
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
      -- `eml(const c1, const c2).eval x = exp c1 - log c2`, constant.
      -- Same argument as the `const c` case.
      have h0 := hsin 0
      have h1 := hsin (pi / (1 + 1))
      simp only [EMLTree.eval, sin_zero, sin_pi_div_two] at h0 h1
      rw [h0] at h1
      exact zero_ne_one_ax h1
    | .const c1, _, .var, _ =>
      -- `eml(const c1, var).eval 0 = exp c1 - log 0 = exp c1`.
      -- sin 0 = 0 forces exp c1 = 0; but exp_pos says exp c1 > 0.
      have h0 := hsin 0
      simp only [EMLTree.eval, sin_zero, log_zero, sub_zero] at h0
      -- h0 : exp c1 = 0
      have hpos : 0 < exp c1 := exp_pos c1
      rw [h0] at hpos
      exact lt_irrefl_ax 0 hpos
    | .var, _, .const c2, _ =>
      -- `eml(var, const c2).eval 0 = 1 - log c2`, .eval π = exp π - log c2.
      -- sin 0 = 0 forces log c2 = 1; sin π = 0 forces exp π = log c2 = 1.
      -- exp π = 1 = exp 0 forces π = 0 (by exp_injective), contradicting pi_pos.
      have h0 := hsin 0
      have hπ := hsin pi
      simp only [EMLTree.eval, sin_zero, sin_pi, exp_zero] at h0 hπ
      -- h0 : 1 - log c2 = 0
      -- hπ : exp pi - log c2 = 0
      -- Derive log c2 = 1 from h0:
      have hlog : log c2 = 1 := by
        have : 1 - log c2 + log c2 = 0 + log c2 := by rw [h0]
        rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at this
        exact this.symm
      -- Substitute into hπ:
      rw [hlog] at hπ
      -- hπ : exp pi - 1 = 0, i.e., exp pi = 1.
      have hexp_pi : exp pi = 1 := by
        have : exp pi - 1 + 1 = 0 + 1 := by rw [hπ]
        rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at this
        exact this
      -- exp pi = 1 = exp 0, so by exp_injective, pi = 0.
      have heq : exp pi = exp 0 := by rw [hexp_pi, exp_zero]
      have hpi_zero : pi = 0 := exp_injective heq
      -- But pi_pos says 0 < pi, contradiction.
      have hpos : (0 : Real) < pi := pi_pos
      rw [hpi_zero] at hpos
      exact lt_irrefl_ax 0 hpos
    | .var, _, .var, _ =>
      -- `eml(var, var).eval 0 = exp 0 - log 0 = 1 - 0 = 1`. But sin 0 = 0.
      have h := hsin 0
      simp only [EMLTree.eval, sin_zero, exp_zero, log_zero, sub_zero] at h
      -- h : 1 = 0
      exact zero_ne_one_ax h.symm

end MachLib
