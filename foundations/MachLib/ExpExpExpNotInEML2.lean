import MachLib.Exp
import MachLib.Log
import MachLib.EML
import MachLib.EMLHierarchy
import MachLib.ExpExpNotInEML1
import MachLib.SinNotInEMLDepth2Sweep

/-!
# `exp ∘ exp ∘ exp ∉ EML_2` — staging file for `EML_2 ⊊ EML_3`

The strict containment `EML_2 ⊊ EML_3` is witnessed by
`exp ∘ exp ∘ exp` (triple-exp). This file establishes:

1. **Membership** `exp_exp_exp_in_eml_3`: triple-exp = eml(eml(eml(var,
   const 1), const 1), const 1).eval. Depth 3.

2. **Forward inclusion** `eml_two_subset_eml_three`: `EML_2 ⊆ EML_3`
   (trivial Nat-monotonicity).

3. **Non-membership** `exp_exp_exp_not_in_eml_1` (this session): for
   any depth-≤1 EML tree `t`, `t.eval ≠ exp(exp(exp x))` globally.
   This is the analog of `exp_exp_not_in_eml_1` but with one more
   exp on the target side.

4. **`EML_1 ⊊ EML_3`** (this session): combines #1 + #2 + #3 via
   `in_eml_depth_mono` chains. NOT the same as `EML_2 ⊊ EML_3` —
   that requires the depth-2 enumeration (32+ cases analogous to the
   depth-2 sin barrier).

Per-case theorems follow the `exp_exp_ne_*` pattern: evaluate at
specific x, equate, apply `exp_injective` repeatedly, contradict via
`one_lt_exp_one` or a numerical bound axiom.

The harder direction `exp_exp_exp_not_in_eml_2` (depth-≤2 enumeration,
32 depth-2 sub-cases) is deferred as a focused follow-up artifact.
The depth-2 sin barrier closure (32/32) in `SinNotInEMLDepth2Sweep`
and `SinNotInEMLDepth2FinalVcVc` provides the template.

No Mathlib dependency. Zero-Mathlib gate stays PASS.
-/

namespace MachLib
open Real

-- ===================================================================
-- Membership in EML_3.
-- ===================================================================

/-- `exp(exp(exp x)) = eml(eml(eml(var, const 1), const 1), const 1).eval x`. Depth 3.
Uses `eml(t, const 1) = exp(t.eval x) - log 1 = exp(t.eval x)` thrice. -/
theorem exp_exp_exp_in_eml_3 :
    InEMLDepth (fun x : Real => Real.exp (Real.exp (Real.exp x))) 3 := by
  refine ⟨EMLTree.eml (EMLTree.eml (EMLTree.eml .var (.const 1)) (.const 1)) (.const 1),
          ?_, ?_⟩
  · simp [EMLTree.depth]
  · intro x
    simp [EMLTree.eval, log_one, sub_zero]

/-- Forward inclusion `EML_2 ⊆ EML_3`. -/
theorem eml_two_subset_eml_three :
    ∀ f : Real → Real, InEMLDepth f 2 → InEMLDepth f 3 := by
  intro f hf
  exact in_eml_depth_mono hf (by omega)

-- ===================================================================
-- Per-case theorems: no depth-≤1 EMLTree evaluates to exp(exp(exp x)).
--
-- Strategy: evaluate at x = 0 and x = 1.
--   exp(exp(exp 0)) = exp(exp 1)        (target value at x = 0)
--   exp(exp(exp 1)) = exp(exp(exp 1))  (target value at x = 1)
-- Equate to t.eval at these points, derive 1 = exp 1 or analogous
-- contradiction via exp_injective + one_lt_exp_one.
-- ===================================================================

/-- A constant function cannot equal `exp ∘ exp ∘ exp` globally. -/
theorem exp_exp_exp_ne_const (c : Real) :
    ¬ (∀ x : Real, Real.exp (Real.exp (Real.exp x)) = (EMLTree.const c).eval x) := by
  intro hexp
  have h0 := hexp 0
  have h1 := hexp 1
  simp only [EMLTree.eval] at h0 h1
  rw [exp_zero] at h0
  -- h0 : exp(exp 1) = c, h1 : exp(exp(exp 1)) = c
  have heq : exp (exp 1) = exp (exp (exp 1)) := h0.trans h1.symm
  have h_inner : exp 1 = exp (exp 1) := exp_injective heq
  have h_inner2 : (1 : Real) = exp 1 := exp_injective h_inner
  have hlt : (1 : Real) < exp 1 := one_lt_exp_one
  rw [← h_inner2] at hlt
  exact lt_irrefl_ax 1 hlt

/-- The identity function cannot equal `exp ∘ exp ∘ exp` globally. -/
theorem exp_exp_exp_ne_var :
    ¬ (∀ x : Real, Real.exp (Real.exp (Real.exp x)) = EMLTree.var.eval x) := by
  intro hexp
  have h := hexp 0
  simp only [EMLTree.eval] at h
  rw [exp_zero] at h
  -- h : exp(exp 1) = 0
  have hpos : 0 < exp (exp 1) := exp_pos _
  rw [h] at hpos
  exact lt_irrefl_ax 0 hpos

/-- `eml(const c1, const c2)` (constant) cannot equal `exp ∘ exp ∘ exp`. -/
theorem exp_exp_exp_ne_eml_const_const (c1 c2 : Real) :
    ¬ (∀ x : Real,
        Real.exp (Real.exp (Real.exp x)) =
          (EMLTree.eml (.const c1) (.const c2)).eval x) := by
  intro hexp
  have h0 := hexp 0
  have h1 := hexp 1
  simp only [EMLTree.eval] at h0 h1
  rw [exp_zero] at h0
  -- h0 : exp(exp 1) = exp c1 - log c2
  -- h1 : exp(exp(exp 1)) = exp c1 - log c2
  have heq : exp (exp 1) = exp (exp (exp 1)) := h0.trans h1.symm
  have h_inner : exp 1 = exp (exp 1) := exp_injective heq
  have h_inner2 : (1 : Real) = exp 1 := exp_injective h_inner
  have hlt : (1 : Real) < exp 1 := one_lt_exp_one
  rw [← h_inner2] at hlt
  exact lt_irrefl_ax 1 hlt

/-- `eml(const c1, var)`: at x = 0, log 0 = 0 collapses to exp c1; at x = 1,
log 1 = 0 also collapses to exp c1. Same constant contradiction. -/
theorem exp_exp_exp_ne_eml_const_var (c1 : Real) :
    ¬ (∀ x : Real,
        Real.exp (Real.exp (Real.exp x)) =
          (EMLTree.eml (.const c1) .var).eval x) := by
  intro hexp
  have h0 := hexp 0
  have h1 := hexp 1
  simp only [EMLTree.eval, log_zero, sub_zero, log_one] at h0 h1
  rw [exp_zero] at h0
  -- h0 : exp(exp 1) = exp c1
  -- h1 : exp(exp(exp 1)) = exp c1
  have heq : exp (exp 1) = exp (exp (exp 1)) := h0.trans h1.symm
  have h_inner : exp 1 = exp (exp 1) := exp_injective heq
  have h_inner2 : (1 : Real) = exp 1 := exp_injective h_inner
  have hlt : (1 : Real) < exp 1 := one_lt_exp_one
  rw [← h_inner2] at hlt
  exact lt_irrefl_ax 1 hlt

/-- `eml(var, var)`: at x = 1, log 1 = 0 collapses to exp 1. So target at
x = 1 is exp 1, but exp(exp(exp 1)) ≠ exp 1 (since exp(exp 1) > 1). -/
theorem exp_exp_exp_ne_eml_var_var :
    ¬ (∀ x : Real,
        Real.exp (Real.exp (Real.exp x)) =
          (EMLTree.eml .var .var).eval x) := by
  intro hexp
  have h1 := hexp 1
  simp only [EMLTree.eval, log_one, sub_zero] at h1
  -- h1 : exp(exp(exp 1)) = exp 1
  -- So exp(exp 1) = 1 via exp_injective. But exp(exp 1) > 1.
  have h_inner : exp (exp 1) = 1 := exp_injective h1
  have hlt : (1 : Real) < exp (exp 1) := by
    have step : exp 0 < exp (exp 1) := exp_lt (exp_pos _)
    rw [exp_zero] at step
    exact step
  rw [h_inner] at hlt
  exact lt_irrefl_ax 1 hlt

/-- `eml(var, const c2)`: at x = 0 and x = 1, we get
`(exp 0, exp 1) - log c2 = (exp(exp 1), exp(exp(exp 1)))`.
Cancelling `log c2`: `exp 1 - 1 = exp(exp(exp 1)) - exp(exp 1)`.
Contradict via `exp_gt_two_x` at `exp(exp 1)`:
`2 * exp(exp 1) < exp(exp(exp 1))`, so RHS > exp(exp 1) > 2 > exp 1 = LHS + 1 > LHS. -/
theorem exp_exp_exp_ne_eml_var_const (c2 : Real) :
    ¬ (∀ x : Real,
        Real.exp (Real.exp (Real.exp x)) =
          (EMLTree.eml .var (.const c2)).eval x) := by
  intro hexp
  have h0 := hexp 0
  have h1 := hexp 1
  simp only [EMLTree.eval] at h0 h1
  rw [exp_zero] at h0
  -- h0 : exp(exp 1) = 1 - log c2
  -- h1 : exp(exp(exp 1)) = exp 1 - log c2
  -- Subtract: h1 - h0 gives: exp(exp(exp 1)) - exp(exp 1) = exp 1 - 1.
  have hkey : exp (exp (exp 1)) - exp (exp 1) = exp 1 - 1 := by
    have step1 : exp (exp (exp 1)) - exp (exp 1) =
                 (exp 1 - log c2) - (1 - log c2) := by rw [h1, h0]
    have step2 : (exp 1 - log c2) - (1 - log c2) = exp 1 - 1 := by
      rw [sub_def, sub_def, sub_def, neg_add, neg_neg_helper,
          add_assoc, ← add_assoc (-log c2) (-1) (log c2),
          add_comm (-log c2) (-1),
          add_assoc (-1) (-log c2) (log c2), neg_add_self, add_zero,
          ← sub_def]
    exact step1.trans step2
  -- Contradict via exp_gt_two_x at exp(exp 1):
  -- 2 * exp(exp 1) < exp(exp(exp 1)).
  -- So exp(exp(exp 1)) - exp(exp 1) > exp(exp 1).
  -- And exp(exp 1) > exp 1 (from exp_lt + 1 < exp 1).
  -- And exp 1 > exp 1 - 1 (from -1 < 0).
  -- So exp(exp(exp 1)) - exp(exp 1) > exp(exp 1) > exp 1 > exp 1 - 1.
  -- Contradicts hkey: LHS = exp 1 - 1.
  have h2_exp_exp_one : (1 + 1) * exp (exp 1) < exp (exp (exp 1)) :=
    exp_gt_two_x (exp (exp 1))
  -- (1 + 1) * exp(exp 1) = exp(exp 1) + exp(exp 1).
  have h2_eq : (1 + 1) * exp (exp 1) = exp (exp 1) + exp (exp 1) := by
    rw [mul_distrib_right, one_mul_thm]
  rw [h2_eq] at h2_exp_exp_one
  -- h2_exp_exp_one : exp(exp 1) + exp(exp 1) < exp(exp(exp 1)).
  -- So exp(exp 1) < exp(exp(exp 1)) - exp(exp 1).
  have hsub_gt : exp (exp 1) < exp (exp (exp 1)) - exp (exp 1) := by
    have step := add_lt_add_left h2_exp_exp_one (-exp (exp 1))
    rw [← add_assoc, neg_add_self, zero_add,
        add_comm (-exp (exp 1)) (exp (exp (exp 1))), ← sub_def] at step
    exact step
  -- exp(exp 1) > exp 1 (from 1 < exp 1).
  have hone_lt_exp_one : (1 : Real) < exp 1 := one_lt_exp_one
  have hexp_one_lt_exp_exp_one : exp 1 < exp (exp 1) := by
    have step : exp 1 < exp (exp 1) := exp_lt hone_lt_exp_one
    exact step
  -- exp 1 > exp 1 - 1 (from -1 < 0).
  have hexp_one_minus_1_lt : exp 1 - 1 < exp 1 := by
    have hneg : (-1 : Real) < 0 := by
      have step := add_lt_add_left zero_lt_one_ax (-1)
      rw [add_zero, neg_add_self] at step
      exact step
    have step := add_lt_add_left hneg (exp 1)
    rw [add_zero, ← sub_def] at step
    exact step
  -- Chain: exp 1 - 1 < exp 1 < exp(exp 1) < exp(exp(exp 1)) - exp(exp 1).
  have hchain : exp 1 - 1 < exp (exp (exp 1)) - exp (exp 1) :=
    lt_trans_ax hexp_one_minus_1_lt (lt_trans_ax hexp_one_lt_exp_exp_one hsub_gt)
  -- Contradicts hkey: exp(exp(exp 1)) - exp(exp 1) = exp 1 - 1.
  rw [hkey] at hchain
  exact lt_irrefl_ax _ hchain

-- ===================================================================
-- Master theorem: exp(exp(exp x)) ∉ EML_1.
-- ===================================================================

/-- **Master theorem:** `exp ∘ exp ∘ exp ∉ EML_1`. Closes via depth-≤1
case-analysis on the EMLTree. -/
theorem exp_exp_exp_not_in_eml_1 :
    ¬ InEMLDepth (fun x : Real => Real.exp (Real.exp (Real.exp x))) 1 := by
  intro ⟨t, htd, hexp⟩
  match t, htd with
  | .const c, _ =>
    exact exp_exp_exp_ne_const c (fun x => hexp x)
  | .var, _ =>
    exact exp_exp_exp_ne_var (fun x => hexp x)
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
      exact exp_exp_exp_ne_eml_const_const c1 c2 (fun x => hexp x)
    | .const c1, _, .var, _ =>
      exact exp_exp_exp_ne_eml_const_var c1 (fun x => hexp x)
    | .var, _, .const c2, _ =>
      exact exp_exp_exp_ne_eml_var_const c2 (fun x => hexp x)
    | .var, _, .var, _ =>
      exact exp_exp_exp_ne_eml_var_var (fun x => hexp x)

/-- **`EML_1 ⊊ EML_3`** as a strict containment, witnessed by `exp ∘ exp ∘
exp`. This is a CHAIN-skip result: combines `EML_1 ⊆ EML_3` (via two
applications of forward inclusion) with the witness `exp(exp(exp x))`
which is in EML_3 but not in EML_1.

NOT the same as `EML_2 ⊊ EML_3`. The latter requires
`exp_exp_exp_not_in_eml_2` (depth-≤2 enumeration, 32+ sub-cases) which
is deferred as a focused follow-up artifact. The depth-2 sin barrier
closure in SinNotInEMLDepth2Sweep + SinNotInEMLDepth2FinalVcVc
provides the template (~250-350 lines per "hard" depth-2 case). -/
theorem strict_eml_one_subset_eml_three :
    (∀ f : Real → Real, InEMLDepth f 1 → InEMLDepth f 3) ∧
    (∃ f : Real → Real, InEMLDepth f 3 ∧ ¬ InEMLDepth f 1) :=
  ⟨fun f hf => in_eml_depth_mono hf (by omega),
   ⟨fun x => Real.exp (Real.exp (Real.exp x)), exp_exp_exp_in_eml_3,
    exp_exp_exp_not_in_eml_1⟩⟩

end MachLib
