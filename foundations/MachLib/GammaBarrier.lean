import MachLib.Exp
import MachLib.Log
import MachLib.SinNotInEML
import MachLib.EMLHierarchy
import MachLib.Ring

/-!
# MachLib.GammaBarrier — Γ ∉ EML at depths 0 and 1

Mirrors `LambertW.lean` for the gamma function. Axiomatic foundation
+ constructive depth-0/1 EML barriers.

## Axioms (+4)

  - `gamma : Real → Real`
  - `gamma_one : gamma 1 = 1`
  - `gamma_func_eq : 0 < x → gamma (x + 1) = x * gamma x`
  - `gamma_pos_on_pos : 0 < x → 0 < gamma x`

## What's CLOSED

  - `gamma_not_in_eml_0`: Γ ∉ EML_0
  - `gamma_not_in_eml_1`: Γ ∉ EML_1

## What's STILL OPEN

Gamma any-depth barrier (Γ ∉ EML at ANY depth). Three paths in the
2026-06-13 scoping doc; all require multi-week infrastructure.
-/

namespace MachLib

open Real

/-! ## Axiomatic gamma -/

axiom gamma : Real → Real

axiom gamma_one : gamma 1 = 1

axiom gamma_func_eq (x : Real) (hx : 0 < x) : gamma (x + 1) = x * gamma x

axiom gamma_pos_on_pos (x : Real) (hx : 0 < x) : 0 < gamma x

/-! ## Specific values

`1 + 1` is the literal `2`; `1 + 1 + 1` is `3` (MachLib.Real
doesn't ship OfNat instances for numerals > 1). -/

theorem gamma_one_plus_one : gamma (1 + 1) = 1 := by
  have h : gamma (1 + 1) = 1 * gamma 1 := gamma_func_eq 1 zero_lt_one_ax
  rw [h, gamma_one, mul_one_ax 1]

theorem gamma_one_plus_one_plus_one : gamma (1 + 1 + 1) = 1 + 1 := by
  have h_two_pos : (0 : Real) < 1 + 1 :=
    lt_trans_ax zero_lt_one_ax
      (by have := add_lt_add_left zero_lt_one_ax 1; rwa [add_zero] at this)
  have h : gamma (1 + 1 + 1) = (1 + 1) * gamma (1 + 1) :=
    gamma_func_eq (1 + 1) h_two_pos
  rw [h, gamma_one_plus_one, mul_one_ax]

/-! ## Depth-0 barrier -/

theorem gamma_not_in_eml_0 (t : EMLTree) (ht : t.depth ≤ 0) :
    ¬ (∀ x : Real, t.eval x = gamma x) := by
  intro hG
  have h_one_lt : (1 : Real) < 1 + 1 := by
    have := add_lt_add_left zero_lt_one_ax 1
    rwa [add_zero] at this
  cases t with
  | const c =>
    -- c = Γ(1) = 1, AND c = Γ(1+1+1) = 1+1.
    have h1 := hG 1
    have h3 := hG (1 + 1 + 1)
    simp only [EMLTree.eval] at h1 h3
    rw [gamma_one] at h1
    rw [gamma_one_plus_one_plus_one] at h3
    rw [h1] at h3
    -- h3 : 1 = 1 + 1
    rw [← h3] at h_one_lt
    exact lt_irrefl_ax 1 h_one_lt
  | var =>
    have h2 := hG (1 + 1)
    simp only [EMLTree.eval] at h2
    rw [gamma_one_plus_one] at h2
    -- h2 : 1 + 1 = 1
    rw [h2] at h_one_lt
    exact lt_irrefl_ax 1 h_one_lt
  | eml a b =>
    have h_one_le_zero : (1 : Nat) ≤ 0 := by
      have hd : (EMLTree.eml a b).depth ≤ 0 := ht
      simp [EMLTree.depth] at hd
    omega

/-! ## Depth-1 barrier -/

theorem gamma_not_in_eml_1 (t : EMLTree) (ht : t.depth ≤ 1) :
    ¬ (∀ x : Real, t.eval x = gamma x) := by
  intro hG
  have h_one_lt : (1 : Real) < 1 + 1 := by
    have := add_lt_add_left zero_lt_one_ax 1
    rwa [add_zero] at this
  have h_two_pos : (0 : Real) < 1 + 1 :=
    lt_trans_ax zero_lt_one_ax h_one_lt
  cases t with
  | const c =>
    exact gamma_not_in_eml_0 (.const c) (by simp [EMLTree.depth]) hG
  | var =>
    exact gamma_not_in_eml_0 .var (by simp [EMLTree.depth]) hG
  | eml t1 t2 =>
    have htd : t1.depth = 0 ∧ t2.depth = 0 := by
      have hd : (EMLTree.eml t1 t2).depth ≤ 1 := ht
      simp [EMLTree.depth] at hd
      -- hd : t1.depth.max t2.depth ≤ 0 (after simp normalization).
      -- Both depths Nat-valued. Show both ≤ 0 via max bounds.
      refine ⟨?_, ?_⟩
      · have : t1.depth ≤ Nat.max t1.depth t2.depth := Nat.le_max_left _ _
        omega
      · have : t2.depth ≤ Nat.max t1.depth t2.depth := Nat.le_max_right _ _
        omega
    cases t1 with
    | const c1 =>
      cases t2 with
      | const c2 =>
        -- eml(const c1, const c2): constant.
        have h1 := hG 1
        have h3 := hG (1 + 1 + 1)
        simp only [EMLTree.eval] at h1 h3
        rw [gamma_one] at h1
        rw [gamma_one_plus_one_plus_one] at h3
        have heq : (1 : Real) = 1 + 1 := h1.symm.trans h3
        rw [← heq] at h_one_lt
        exact lt_irrefl_ax 1 h_one_lt
      | var =>
        -- eml(const c1, var). At x=1: exp c1 = 1. At x=1+1: 1 - log(1+1) = 1.
        -- So log(1+1) = 0 = log 1, so 1+1 = 1 by injectivity.
        have h1 := hG 1
        have h2 := hG (1 + 1)
        simp only [EMLTree.eval] at h1 h2
        rw [gamma_one, log_one, sub_zero] at h1
        rw [gamma_one_plus_one] at h2
        rw [h1] at h2
        -- h2 : 1 - log (1 + 1) = 1
        -- Want: log (1 + 1) = 0.
        have h_neg_log_zero : -log (1 + 1) = (0 : Real) := by
          have step : (-1 : Real) + (1 - log (1 + 1)) = (-1 : Real) + 1 := by rw [h2]
          -- Simplify both sides. LHS: -1 + (1 + -log(1+1)) = (-1+1) + -log(1+1) = -log(1+1).
          -- RHS: -1 + 1 = 0. Both via neg_add_self + zero_add + sub_def + add_assoc.
          rw [sub_def, ← add_assoc, neg_add_self, zero_add] at step
          exact step
        have h_log_zero : log (1 + 1) = (0 : Real) := by
          have h_sum : -log (1 + 1) + log (1 + 1) = (0 : Real) :=
            neg_add_self (log (1 + 1))
          rw [h_neg_log_zero, zero_add] at h_sum
          exact h_sum
        -- log(1+1) = log 1 → 1+1 = 1 via exp_log on both sides.
        have h_eq : log (1 + 1) = log 1 := by rw [h_log_zero, log_one]
        have h_two_eq_one : (1 + 1 : Real) = 1 := by
          have h_exp_log1 : exp (log (1 + 1)) = 1 + 1 := exp_log h_two_pos
          have h_exp_log2 : exp (log 1) = 1 := exp_log zero_lt_one_ax
          rw [h_eq] at h_exp_log1
          -- h_exp_log1 : exp (log 1) = 1 + 1
          -- h_exp_log2 : exp (log 1) = 1
          -- So 1 + 1 = 1.
          exact h_exp_log1.symm.trans h_exp_log2
        rw [h_two_eq_one] at h_one_lt
        exact lt_irrefl_ax 1 h_one_lt
      | eml _ _ =>
        have h_one_le_zero : (1 : Nat) ≤ 0 := by
          have hd' : (EMLTree.eml _ _).depth = 0 := htd.2
          simp [EMLTree.depth] at hd'
        omega
    | var =>
      cases t2 with
      | const c2 =>
        -- eml(var, const c2). At x=1: exp 1 - log c2 = 1.
        -- At x=1+1: exp(1+1) - log c2 = 1. Subtract → exp 1 = exp(1+1).
        -- But exp_lt: exp 1 < exp(1+1).
        have h1 := hG 1
        have h2 := hG (1 + 1)
        simp only [EMLTree.eval] at h1 h2
        rw [gamma_one] at h1
        rw [gamma_one_plus_one] at h2
        have h_exp_eq : Real.exp 1 = Real.exp (1 + 1) := by
          have heq : Real.exp 1 - log c2 = Real.exp (1 + 1) - log c2 := by
            rw [h1, h2]
          have : Real.exp 1 - log c2 + log c2 = Real.exp (1 + 1) - log c2 + log c2 := by
            rw [heq]
          rw [sub_def, add_assoc, add_comm (-log c2) (log c2), add_neg, add_zero,
              sub_def (Real.exp (1 + 1)) (log c2), add_assoc,
              add_comm (-log c2) (log c2), add_neg, add_zero] at this
          exact this
        have h_exp_lt : Real.exp 1 < Real.exp (1 + 1) := exp_lt h_one_lt
        rw [h_exp_eq] at h_exp_lt
        exact lt_irrefl_ax _ h_exp_lt
      | var =>
        -- eml(var, var). At x=1: exp 1 - log 1 = exp 1 = 1.
        -- exp_gt_one_plus_self 1 gives 1+1 < exp 1; contradiction.
        have h1 := hG 1
        simp only [EMLTree.eval] at h1
        rw [gamma_one, log_one, sub_zero] at h1
        have h_two_lt_exp_one : (1 : Real) + 1 < Real.exp 1 :=
          exp_gt_one_plus_self 1 zero_lt_one_ax
        rw [h1] at h_two_lt_exp_one
        -- h_two_lt_exp_one : 1 + 1 < 1
        exact lt_irrefl_ax 1 (lt_trans_ax h_one_lt h_two_lt_exp_one)
      | eml _ _ =>
        have h_one_le_zero : (1 : Nat) ≤ 0 := by
          have hd' : (EMLTree.eml _ _).depth = 0 := htd.2
          simp [EMLTree.depth] at hd'
        omega
    | eml _ _ =>
      have h_one_le_zero : (1 : Nat) ≤ 0 := by
        have hd' : (EMLTree.eml _ _).depth = 0 := htd.1
        simp [EMLTree.depth] at hd'
      omega

/-! ## Closing notes

Γ joins sin, cos, Lambert-W as functions provably outside EML at
small depths. Any-depth still open (multi-week per the scoping doc).

## Axiom audit

+4 axioms: `gamma`, `gamma_one`, `gamma_func_eq`, `gamma_pos_on_pos`.
0 in the SingleExp Khovanskii footprint.
-/

end MachLib
