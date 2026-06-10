import MachLib.SinNotInEMLDepth2Sweep
import MachLib.IteratedExpBounds

/-!
# Sin Not In EML Depth 2 — Final Closure of Row 3 vc-vc

Closes `sin_not_in_eml_t1_vc_t2_eml_vc` (Row 3 vc-vc), the last
remaining depth-2 sin barrier case. Combines three sub-cases via
`by_cases` on `0 < d` and (within the d > 0 branch) `1 < log d1`:

1. d ≤ 0 sub-case: handled by `sin_not_in_eml_t1_vc_t2_eml_vc_dnonpos`
   (from SinNotInEMLDepth2Sweep). log d = 0 by convention forces
   exp(1 - log d1) = 0 at x = 0, contradicting exp_pos.

2. d > 0 ∧ 1 < log d1 (log_mul chain): this file's
   `sin_not_in_eml_t1_vc_t2_eml_vc_dpos_Lgt1`. From (Eπ):
   log(exp π - log d) = exp(exp π - log d1). Bound:
   log(exp π - log d) < log(2 exp π) = log 2 + π < 1 + π
     (via log_lt_log + log_mul + log_two_lt_one_helper).
   Hence exp(exp π - log d1) < 1 + π. Apply log + log_lt_sub_one_helper:
   exp π - log d1 < π. So log d1 > exp π - π > π > exp 1
     (via exp_gt_two_x + exp_one_lt_pi).
   From (E1) + log d < 0 + sin_one_pos: contradiction.

3. d > 0 ∧ log d1 ≤ 1 (mean-value): this file's
   `sin_not_in_eml_t1_vc_t2_eml_vc_dpos_Lle1`. From (E0) and (Eπ):
   exp π - 1 = exp(exp(exp π - log d1)) - exp(exp(1 - log d1)).
   Apply exp_sub_exp_gt_helper twice + mul_lt_mul_left_helper:
   LHS > exp(exp(1 - log d1)) * exp(1 - log d1) * (exp π - 1).
   For log d1 ≤ 1: factor ≥ exp 1 > 2, so LHS > 2(exp π - 1) >
   exp π - 1. Contradiction.

Coverage: **32/32** complete depth-2 sin barrier. Sorry count
unchanged at 5. Zero-Mathlib gate stays PASS.
-/

namespace MachLib
open Real

/-- Row 3 vc-vc, d > 0 ∧ 1 < log d1 sub-case (log_mul chain). -/
theorem sin_not_in_eml_t1_vc_t2_eml_vc_dpos_Lgt1 (d1 d : Real)
    (hd : (0 : Real) < d) (hL : (1 : Real) < log d1) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml .var (.const d1)) (.eml .var (.const d))).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have h1 := hsin 1
  have hπ := hsin pi
  simp only [EMLTree.eval, sin_zero, sin_pi, exp_zero] at h0 h1 hπ
  -- From h0: log(1 - log d) = exp(1 - log d1).
  have hlog_eq_0 : log (1 - log d) = exp (1 - log d1) := by
    have step : exp (1 - log d1) - log (1 - log d) + log (1 - log d) =
                  0 + log (1 - log d) := by rw [h0]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  have h1sub_pos : (0 : Real) < 1 - log d := by
    apply log_pos_arg_pos
    rw [hlog_eq_0]; exact exp_pos _
  have h1sub_eq : 1 - log d = exp (exp (1 - log d1)) := by
    have step : exp (log (1 - log d)) = exp (exp (1 - log d1)) := by rw [hlog_eq_0]
    rw [exp_log h1sub_pos] at step
    exact step
  -- log d < 0.
  have hM_neg : log d < 0 := by
    have hone_lt : (1 : Real) < exp (exp (1 - log d1)) := by
      have step : exp 0 < exp (exp (1 - log d1)) := exp_lt (exp_pos _)
      rw [exp_zero] at step
      exact step
    rw [← h1sub_eq] at hone_lt
    have step1 : (0 : Real) < -log d := by
      have step := add_lt_add_left hone_lt (-1)
      rw [neg_add_self, sub_def, ← add_assoc, neg_add_self, zero_add] at step
      exact step
    have step := add_lt_add_left step1 (log d)
    rw [add_zero, add_neg] at step
    exact step
  -- From hπ: log(exp π - log d) = exp(exp π - log d1).
  have hlog_eq_pi : log (exp pi - log d) = exp (exp pi - log d1) := by
    have step : exp (exp pi - log d1) - log (exp pi - log d) + log (exp pi - log d) =
                  0 + log (exp pi - log d) := by rw [hπ]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  have hpi_sub_pos : (0 : Real) < exp pi - log d := by
    apply log_pos_arg_pos
    rw [hlog_eq_pi]; exact exp_pos _
  -- (a) 1 - log d1 < 0.
  have ha : 1 - log d1 < 0 := by
    have step := add_lt_add_left hL (-log d1)
    rw [neg_add_self, add_comm (-log d1) 1, ← sub_def] at step
    exact step
  -- (b) exp(1 - log d1) < 1.
  have hb : exp (1 - log d1) < 1 := by
    have step : exp (1 - log d1) < exp 0 := exp_lt ha
    rw [exp_zero] at step
    exact step
  -- (c) exp(exp(1 - log d1)) < exp 1.
  have hc : exp (exp (1 - log d1)) < exp 1 := exp_lt hb
  -- (d) exp 1 < exp π.
  have hd_chain : exp 1 < exp pi := exp_lt pi_gt_one
  -- (e) 1 - log d < exp π.
  have he : 1 - log d < exp pi := by
    rw [h1sub_eq]; exact lt_trans_ax hc hd_chain
  -- (f) -log d < exp π.
  have hf : -log d < exp pi := by
    have step := add_lt_add_left he (-1)
    rw [sub_def, ← add_assoc, neg_add_self, zero_add,
        add_comm (-1) (exp pi), ← sub_def] at step
    -- step : -log d < exp pi - 1
    have hexp_pi_minus_1_lt : exp pi - 1 < exp pi := by
      have hneg : (-1 : Real) < 0 := by
        have step := add_lt_add_left zero_lt_one_ax (-1)
        rw [add_zero, neg_add_self] at step
        exact step
      have step := add_lt_add_left hneg (exp pi)
      rw [add_zero, ← sub_def] at step
      exact step
    exact lt_trans_ax step hexp_pi_minus_1_lt
  -- (g) exp π - log d < 2 * exp π.
  have hg : exp pi - log d < (1 + 1) * exp pi := by
    have step := add_lt_add_left hf (exp pi)
    rw [← sub_def] at step
    have h2pi_eq : (1 + 1) * exp pi = exp pi + exp pi := by
      rw [mul_distrib_right, one_mul_thm]
    rw [← h2pi_eq] at step
    exact step
  -- (h) log(exp π - log d) < log(2 * exp π).
  have hh : log (exp pi - log d) < log ((1 + 1) * exp pi) :=
    log_lt_log hpi_sub_pos hg
  -- (i) log(2 * exp π) = log 2 + π.
  have h2_pos : (0 : Real) < 1 + 1 := by
    have step := add_lt_add_left zero_lt_one_ax 1
    rw [add_zero] at step
    exact lt_trans_ax zero_lt_one_ax step
  have hi : log ((1 + 1) * exp pi) = log (1 + 1) + pi := by
    rw [log_mul h2_pos (exp_pos pi), log_exp]
  -- (j) log 2 + π < 1 + π.
  have hj : log ((1 : Real) + 1) + pi < 1 + pi := by
    have step := add_lt_add_left log_two_lt_one_helper pi
    rw [add_comm pi (log (1 + 1)), add_comm pi 1] at step
    exact step
  -- (k) log(exp π - log d) < 1 + π.
  have hk : log (exp pi - log d) < 1 + pi := by
    rw [hi] at hh
    exact lt_trans_ax hh hj
  -- (l) exp(exp π - log d1) < 1 + π.
  have hl_chain : exp (exp pi - log d1) < 1 + pi := by
    rw [hlog_eq_pi] at hk; exact hk
  -- (m) exp π - log d1 < log(1 + π).
  have hm : exp pi - log d1 < log (1 + pi) := by
    have step : log (exp (exp pi - log d1)) < log (1 + pi) :=
      log_lt_log (exp_pos _) hl_chain
    rw [log_exp] at step
    exact step
  -- (n) log(1 + π) < π.
  have hn : log (1 + pi) < pi := by
    have h1pi_gt_1 : (1 : Real) < 1 + pi := by
      have step := add_lt_add_left pi_pos 1
      rw [add_zero] at step
      exact step
    have hlemma : log (1 + pi) < (1 + pi) - 1 := log_lt_sub_one_helper h1pi_gt_1
    have hsub_eq : ((1 : Real) + pi) - 1 = pi := by
      rw [sub_def, add_comm 1 pi, add_assoc, add_neg, add_zero]
    rw [hsub_eq] at hlemma
    exact hlemma
  -- (o) exp π - log d1 < π.
  have ho : exp pi - log d1 < pi := lt_trans_ax hm hn
  -- (p) π < exp π - π.
  have hp_chain : pi < exp pi - pi := by
    have h2pi_lt : (1 + 1) * pi < exp pi := exp_gt_two_x pi
    have h2pi_eq : (1 + 1) * pi = pi + pi := by
      rw [mul_distrib_right, one_mul_thm]
    rw [h2pi_eq] at h2pi_lt
    have step := add_lt_add_left h2pi_lt (-pi)
    rw [← add_assoc, neg_add_self, zero_add,
        add_comm (-pi) (exp pi), ← sub_def] at step
    exact step
  -- (q) exp π - π < log d1.
  have hq : exp pi - pi < log d1 := by
    have step := add_lt_add_left ho (-pi + log d1)
    have hlhs : (-pi + log d1) + (exp pi - log d1) = exp pi - pi := by
      rw [sub_def, sub_def, add_assoc, ← add_assoc (log d1) (exp pi) (-log d1),
          add_comm (log d1) (exp pi), add_assoc (exp pi) (log d1) (-log d1),
          add_neg, add_zero, add_comm (-pi) (exp pi)]
    have hrhs : (-pi + log d1) + pi = log d1 := by
      rw [add_assoc, add_comm (log d1) pi, ← add_assoc, neg_add_self, zero_add]
    rw [hlhs, hrhs] at step
    exact step
  -- (r) π < log d1.
  have hr : pi < log d1 := lt_trans_ax hp_chain hq
  -- (s) exp 1 < log d1.
  have hs : exp 1 < log d1 := lt_trans_ax exp_one_lt_pi hr
  -- (t) exp 1 - log d1 < 0.
  have ht : exp 1 - log d1 < 0 := by
    have step := add_lt_add_left hs (-log d1)
    rw [neg_add_self, add_comm (-log d1) (exp 1), ← sub_def] at step
    exact step
  -- (u) exp(exp 1 - log d1) < 1.
  have hu : exp (exp 1 - log d1) < 1 := by
    have step : exp (exp 1 - log d1) < exp 0 := exp_lt ht
    rw [exp_zero] at step
    exact step
  -- (v) exp 1 < exp 1 - log d.
  have hv : exp 1 < exp 1 - log d := by
    have step := add_lt_add_left hM_neg (-log d + exp 1)
    have hlhs : (-log d + exp 1) + log d = exp 1 := by
      rw [add_assoc, add_comm (exp 1) (log d), ← add_assoc, neg_add_self, zero_add]
    have hrhs : (-log d + exp 1) + 0 = exp 1 - log d := by
      rw [add_zero, add_comm (-log d) (exp 1), ← sub_def]
    rw [hlhs, hrhs] at step
    exact step
  -- (w) 1 < log(exp 1 - log d).
  have hw : (1 : Real) < log (exp 1 - log d) := by
    have step : log (exp 1) < log (exp 1 - log d) := log_lt_log (exp_pos _) hv
    rw [log_exp] at step
    exact step
  -- (final) sin 1 < 0, contradiction.
  have hsin1_lt_zero : Real.sin 1 < 0 := by
    rw [← h1]
    have step1 : exp (exp 1 - log d1) - log (exp 1 - log d) < 1 - log (exp 1 - log d) := by
      have step := add_lt_add_left hu (-log (exp 1 - log d))
      rw [add_comm (-log (exp 1 - log d)) (exp (exp 1 - log d1)),
          add_comm (-log (exp 1 - log d)) 1,
          ← sub_def, ← sub_def] at step
      exact step
    have step2 : (1 : Real) - log (exp 1 - log d) < 0 := by
      have step := add_lt_add_left hw (-log (exp 1 - log d))
      rw [neg_add_self, add_comm (-log (exp 1 - log d)) 1, ← sub_def] at step
      exact step
    exact lt_trans_ax step1 step2
  exact lt_irrefl_ax _ (lt_trans_ax sin_one_pos hsin1_lt_zero)

/-- Row 3 vc-vc, d > 0 ∧ log d1 ≤ 1 sub-case (mean-value chain).
LHS = exp(exp(exp π - log d1)) - exp(exp(1 - log d1)) > exp(exp(1 - log d1))
* exp(1 - log d1) * (exp π - 1) via mean-value twice. For log d1 ≤ 1:
exp(1 - log d1) ≥ 1 and exp(exp(1 - log d1)) ≥ exp 1 > 2. So LHS > 2(exp π
- 1) > exp π - 1, contradicting hkey: LHS = exp π - 1. -/
theorem sin_not_in_eml_t1_vc_t2_eml_vc_dpos_Lle1 (d1 d : Real)
    (hd : (0 : Real) < d) (hL : ¬ ((1 : Real) < log d1)) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml .var (.const d1)) (.eml .var (.const d))).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have hπ := hsin pi
  simp only [EMLTree.eval, sin_zero, sin_pi, exp_zero] at h0 hπ
  have hlog_eq_0 : log (1 - log d) = exp (1 - log d1) := by
    have step : exp (1 - log d1) - log (1 - log d) + log (1 - log d) =
                  0 + log (1 - log d) := by rw [h0]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  have h1sub_pos : (0 : Real) < 1 - log d := by
    apply log_pos_arg_pos
    rw [hlog_eq_0]; exact exp_pos _
  have h1sub_eq : 1 - log d = exp (exp (1 - log d1)) := by
    have step : exp (log (1 - log d)) = exp (exp (1 - log d1)) := by rw [hlog_eq_0]
    rw [exp_log h1sub_pos] at step
    exact step
  have hlog_eq_pi : log (exp pi - log d) = exp (exp pi - log d1) := by
    have step : exp (exp pi - log d1) - log (exp pi - log d) + log (exp pi - log d) =
                  0 + log (exp pi - log d) := by rw [hπ]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  have hpi_sub_pos : (0 : Real) < exp pi - log d := by
    apply log_pos_arg_pos
    rw [hlog_eq_pi]; exact exp_pos _
  have hpi_sub_eq : exp pi - log d = exp (exp (exp pi - log d1)) := by
    have step : exp (log (exp pi - log d)) = exp (exp (exp pi - log d1)) := by rw [hlog_eq_pi]
    rw [exp_log hpi_sub_pos] at step
    exact step
  -- hkey: exp π - 1 = exp(exp(exp π - log d1)) - exp(exp(1 - log d1)).
  have hkey : exp pi - 1 = exp (exp (exp pi - log d1)) - exp (exp (1 - log d1)) := by
    have step1 : (exp pi - log d) - (1 - log d) = exp pi - 1 := by
      rw [sub_def, sub_def, sub_def, neg_add, neg_neg_helper,
          add_assoc, ← add_assoc (-log d) (-1) (log d),
          add_comm (-log d) (-1),
          add_assoc (-1) (-log d) (log d), neg_add_self, add_zero,
          ← sub_def]
    have step2 : (exp pi - log d) - (1 - log d) =
                  exp (exp (exp pi - log d1)) - exp (exp (1 - log d1)) := by
      rw [h1sub_eq, hpi_sub_eq]
    rw [← step1, step2]
  -- Convert ¬(1 < log d1) → log d1 ≤ 1.
  have hL_le : log d1 ≤ 1 := by
    cases lt_total 1 (log d1) with
    | inl h => exact absurd h hL
    | inr h => cases h with
      | inl heq => rw [← heq]; exact le_refl _
      | inr h => exact le_of_lt h
  -- 0 ≤ 1 - log d1.
  have hone_sub_nonneg : (0 : Real) ≤ 1 - log d1 := by
    have step := add_le_add_left hL_le (-log d1)
    rw [neg_add_self, add_comm (-log d1) 1, ← sub_def] at step
    exact step
  -- 1 ≤ exp(1 - log d1).
  have hexp_inner_ge_one : (1 : Real) ≤ exp (1 - log d1) := by
    have step : exp 0 ≤ exp (1 - log d1) := exp_monotone hone_sub_nonneg
    rw [exp_zero] at step
    exact step
  -- exp 1 ≤ exp(exp(1 - log d1)).
  have hexp_outer_ge_e : exp 1 ≤ exp (exp (1 - log d1)) :=
    exp_monotone hexp_inner_ge_one
  -- Mean-value setup.
  have hexp_pi_gt_one : (1 : Real) < exp pi := by
    have step : exp 0 < exp pi := exp_lt pi_pos
    rw [exp_zero] at step
    exact step
  -- hA: 1 - log d1 < exp π - log d1.
  have hA : 1 - log d1 < exp pi - log d1 := by
    have step := add_lt_add_left hexp_pi_gt_one (-log d1)
    rw [add_comm (-log d1) 1, add_comm (-log d1) (exp pi), ← sub_def, ← sub_def] at step
    exact step
  have hmv_a := exp_sub_exp_gt_helper hA
  have hsub_simp : (exp pi - log d1) - (1 - log d1) = exp pi - 1 := by
    rw [sub_def, sub_def, sub_def, neg_add, neg_neg_helper,
        add_assoc, ← add_assoc (-log d1) (-1) (log d1),
        add_comm (-log d1) (-1),
        add_assoc (-1) (-log d1) (log d1), neg_add_self, add_zero,
        ← sub_def]
  rw [hsub_simp] at hmv_a
  -- hmv_a : exp(1 - log d1) * (exp π - 1) < exp(exp π - log d1) - exp(1 - log d1).
  have hB : exp (1 - log d1) < exp (exp pi - log d1) := exp_lt hA
  have hmv_b := exp_sub_exp_gt_helper hB
  -- hmv_b : exp(exp(1 - log d1)) * (exp(exp π - log d1) - exp(1 - log d1)) < exp(exp(exp π - log d1)) - exp(exp(1 - log d1)).
  have hexp_outer_pos : (0 : Real) < exp (exp (1 - log d1)) := exp_pos _
  -- Multiply hmv_a by exp(exp(1 - log d1)).
  have hmv_combined1 : exp (exp (1 - log d1)) * (exp (1 - log d1) * (exp pi - 1)) <
                       exp (exp (1 - log d1)) * (exp (exp pi - log d1) - exp (1 - log d1)) :=
    mul_lt_mul_left_helper hexp_outer_pos hmv_a
  -- Chain with hmv_b.
  have hmv_chain : exp (exp (1 - log d1)) * (exp (1 - log d1) * (exp pi - 1)) <
                    exp (exp (exp pi - log d1)) - exp (exp (1 - log d1)) :=
    lt_trans_ax hmv_combined1 hmv_b
  -- Substitute via hkey.
  rw [← hkey] at hmv_chain
  -- hmv_chain : exp(exp(1 - log d1)) * (exp(1 - log d1) * (exp pi - 1)) < exp pi - 1.
  -- Lower-bound the LHS.
  have hexp_pi_minus_1_pos : (0 : Real) < exp pi - 1 := by
    have step := add_lt_add_left hexp_pi_gt_one (-1)
    rw [neg_add_self, add_comm (-1) (exp pi), ← sub_def] at step
    exact step
  -- 1 * (exp π - 1) ≤ exp(1 - log d1) * (exp π - 1).
  have hprod_a : (1 : Real) * (exp pi - 1) ≤ exp (1 - log d1) * (exp pi - 1) :=
    mul_le_mul_of_nonneg_right hexp_inner_ge_one (le_of_lt hexp_pi_minus_1_pos)
  have hone_mul : (1 : Real) * (exp pi - 1) = exp pi - 1 := one_mul_thm _
  rw [hone_mul] at hprod_a
  -- hprod_a : exp pi - 1 ≤ exp(1 - log d1) * (exp pi - 1).
  -- exp(exp(1 - log d1)) * (exp π - 1) ≤ exp(exp(1 - log d1)) * (exp(1 - log d1) * (exp π - 1)).
  have hexp_outer_nonneg : (0 : Real) ≤ exp (exp (1 - log d1)) := le_of_lt hexp_outer_pos
  have hprod_b : exp (exp (1 - log d1)) * (exp pi - 1) ≤
                  exp (exp (1 - log d1)) * (exp (1 - log d1) * (exp pi - 1)) :=
    mul_le_mul_of_nonneg_left hprod_a hexp_outer_nonneg
  -- exp 1 * (exp π - 1) ≤ exp(exp(1 - log d1)) * (exp π - 1).
  have hprod_c : exp 1 * (exp pi - 1) ≤ exp (exp (1 - log d1)) * (exp pi - 1) :=
    mul_le_mul_of_nonneg_right hexp_outer_ge_e (le_of_lt hexp_pi_minus_1_pos)
  -- Chain: exp 1 * (exp π - 1) ≤ exp(exp(1 - log d1)) * (exp π - 1) ≤ exp(exp(1 - log d1)) * (exp(1 - log d1) * (exp π - 1)).
  have hprod_chain : exp 1 * (exp pi - 1) ≤
                      exp (exp (1 - log d1)) * (exp (1 - log d1) * (exp pi - 1)) :=
    le_trans hprod_c hprod_b
  -- 2 * (exp π - 1) < exp 1 * (exp π - 1) (from exp_one_gt_two).
  have h2_lt_exp1_mul : (1 + 1) * (exp pi - 1) < exp 1 * (exp pi - 1) :=
    mul_lt_mul_of_pos_right exp_one_gt_two hexp_pi_minus_1_pos
  -- 1 * (exp π - 1) < 2 * (exp π - 1).
  have h1_lt_2 : (1 : Real) < 1 + 1 := by
    have step := add_lt_add_left zero_lt_one_ax 1
    rw [add_zero] at step
    exact step
  have hpi_minus_1_lt_2pi_minus_2 : (1 : Real) * (exp pi - 1) < (1 + 1) * (exp pi - 1) :=
    mul_lt_mul_of_pos_right h1_lt_2 hexp_pi_minus_1_pos
  rw [hone_mul] at hpi_minus_1_lt_2pi_minus_2
  -- Chain to derive contradiction.
  have hfinal : exp pi - 1 < exp pi - 1 := by
    have step1 : exp pi - 1 < exp 1 * (exp pi - 1) :=
      lt_trans_ax hpi_minus_1_lt_2pi_minus_2 h2_lt_exp1_mul
    have step2 : exp pi - 1 < exp (exp (1 - log d1)) * (exp (1 - log d1) * (exp pi - 1)) :=
      lt_of_lt_of_le step1 hprod_chain
    exact lt_trans_ax step2 hmv_chain
  exact lt_irrefl_ax _ hfinal

/-- **Row 3 vc-vc closure** — the final depth-2 sin barrier case.
Combines the d ≤ 0 case (log convention), d > 0 ∧ log d1 > 1 case
(log_mul chain), and d > 0 ∧ log d1 ≤ 1 case (mean-value) into the
master theorem. With this, the depth-2 sin barrier is **32/32**
fully machine-checked under the zero-Mathlib gate. -/
theorem sin_not_in_eml_t1_vc_t2_eml_vc (d1 d : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml .var (.const d1)) (.eml .var (.const d))).eval x =
          Real.sin x) := by
  by_cases hd : (0 : Real) < d
  · by_cases hL : (1 : Real) < log d1
    · exact sin_not_in_eml_t1_vc_t2_eml_vc_dpos_Lgt1 d1 d hd hL
    · exact sin_not_in_eml_t1_vc_t2_eml_vc_dpos_Lle1 d1 d hd hL
  · exact sin_not_in_eml_t1_vc_t2_eml_vc_dnonpos d1 d hd

end MachLib
