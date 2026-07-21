import MachLib.WitnessResidualGrowthCompetitionNumeric
import MachLib.MonotoneFromDeriv

/-! # Non-monotonicity, FULLY CLOSED — `growthCompetitionWitness 2.2 2.7`

This is the final assembly. `WitnessResidualGrowthCompetitionDeriv.lean` connected the tree's real
derivative to an algebraic quadratic's sign; `WitnessResidualGrowthCompetitionNumeric.lean` pinned
that sign at four concrete `E`-witnesses for `c1=2.2, c2=2.7`. This file does the remaining,
mechanical (if lengthy) work: translate the `E`-witnesses into `x`-values, get `HasDerivAt`
existence and sign across the two intervals `[x1,x2]` and `[x3,x4]`, feed both into
`strictMono_of_deriv_pos`/`strictAnti_of_deriv_neg`, and assemble the final non-monotonicity
theorem — closing the whole `growthCompetitionWitness` arc.

**The `E`-to-`x` translation.** `E := exp(exp x)` is a strictly increasing bijection from `ℝ` onto
`(1,∞)`, with inverse `x = log(log E)` (valid whenever `E > 1`, since then `log E > 0` puts the
OUTER `log` in its analytic — non-clamped — branch too). `exp_exp_log_log` is this inversion;
`log_log_mono`/`exp_exp_mono` are the two monotonicity directions needed to move interval
membership back and forth between `E`-space and `x`-space.

**Witnesses chosen**: `x1 := log(log 1.02)`, `x2 := log(log 1.05)` (the increasing interval,
`E∈[1.02,1.05]`, both below the quadratic's vertex `≈1.912`), `x3 := log(log 1.3)`, `x4 :=
log(log 2.3)` (the decreasing interval, `E∈[1.3,2.3]`, both between the quadratic's roots
`≈1.112` and `≈2.712`). `E=1.02`'s only OTHER job is anchoring `hApos`/`hBpos` (`0 < exp(exp x) -
log cᵢ`) across the WHOLE positive interval via monotonicity — `1.02 > log(2.7) > log(2.2)` with
comfortable margin, so is `1.3` for the negative interval.

**A syntactic wrinkle, worth flagging.** `quadratic_neg_between`/`quadratic_pos_below_vertex` are
stated in `k·X·X+m·X+n` (addition) form; the numeric facts here are stated in `k·X·X - p·q·X + n`
(subtraction) form — mathematically identical (`m := -(p·q)`) but syntactically DIFFERENT terms,
since `sub_def` is an axiom, not a `rfl`-unfolding, in this Mathlib-free codebase. `quad_forms_eq`
is the one small bridge lemma needed to move between the two forms at both ends of the
`quadratic_neg_between`/`_pos_below_vertex` calls.

**Two `apply`-unification gotchas, both new this round.** (1) Stating a theorem's conclusion as
`(fun w => BODY) x` gets silently BETA-REDUCED by the elaborator into the substituted `BODY[w:=x]`
directly — so `apply strictAnti_of_deriv_neg _ a b hab` (with the function left as `_`) fails to
higher-order-unify against the now-non-application-shaped goal. Fixed by supplying the lambda
EXPLICITLY (not as a metavariable) in the `apply` call; Lean then checks the substituted instances
by defeq (which includes beta), not by syntactic pattern matching. (2) `mach_decimal` cannot prove
goals like `(1:Real) < 1.3` directly — `1` is the raw `oneR`, not a `realOfScientific` literal, so
none of `mach_decimal`'s normalization lemmas fire on it. Fixed via the pre-existing ad-hoc bridge
`realOfScientific_one_dot_zero : realOfScientific 10 true 1 = 1` (i.e. `1.0 = 1`), rewritten in
first to put both sides in decimal-literal form. -/

namespace MachLib
namespace Real

theorem exp_exp_log_log {E : Real} (hE : 1 < E) :
    Real.exp (Real.exp (Real.log (Real.log E))) = E := by
  have hlogE : 0 < Real.log E := log_pos_of_gt_one hE
  have hEpos : 0 < E := lt_trans_ax zero_lt_one_ax hE
  rw [Real.exp_log hlogE, Real.exp_log hEpos]

theorem log_log_mono {E1 E2 : Real} (hE1 : 1 < E1) (h : E1 < E2) :
    Real.log (Real.log E1) < Real.log (Real.log E2) :=
  log_lt_log (log_pos_of_gt_one hE1) (log_lt_log (lt_trans_ax zero_lt_one_ax hE1) h)

theorem exp_exp_mono {x y : Real} (h : x ≤ y) :
    Real.exp (Real.exp x) ≤ Real.exp (Real.exp y) :=
  exp_monotone (exp_monotone h)

theorem quad_forms_eq {k p q n X : Real} :
    k * X * X + (-(p * q)) * X + n = k * X * X - p * q * X + n := by
  rw [neg_mul, sub_def]

theorem one_lt_1_02 : (1 : Real) < 1.02 := by rw [← realOfScientific_one_dot_zero]; mach_decimal
theorem one_lt_1_05 : (1 : Real) < 1.05 := by rw [← realOfScientific_one_dot_zero]; mach_decimal
theorem one_lt_1_3 : (1 : Real) < 1.3 := by rw [← realOfScientific_one_dot_zero]; mach_decimal
theorem one_lt_2_3 : (1 : Real) < 2.3 := by rw [← realOfScientific_one_dot_zero]; mach_decimal
theorem one_lt_2_2 : (1 : Real) < 2.2 := by rw [← realOfScientific_one_dot_zero]; mach_decimal
theorem one_lt_2_7 : (1 : Real) < 2.7 := by rw [← realOfScientific_one_dot_zero]; mach_decimal

theorem hx12 : Real.log (Real.log 1.02) < Real.log (Real.log 1.05) :=
  log_log_mono one_lt_1_02 (by mach_decimal)

theorem hx34 : Real.log (Real.log 1.3) < Real.log (Real.log 2.3) :=
  log_log_mono one_lt_1_3 (by mach_decimal)

theorem growthCompetition_hApos_posside {w : Real}
    (hEw_ge : (1.02:Real) ≤ Real.exp (Real.exp w)) :
    0 < Real.exp (Real.exp w) - Real.log 2.2 := by
  have h1 : Real.log 2.2 < (0.7890:Real) := (log_2_2_bounds).2
  have h2 : (0.7890:Real) < 1.02 := by mach_decimal
  exact sub_pos_of_lt (lt_of_lt_of_le (lt_trans_ax h1 h2) hEw_ge)

theorem growthCompetition_hBpos_posside {w : Real}
    (hEw_ge : (1.02:Real) ≤ Real.exp (Real.exp w)) :
    0 < Real.exp (Real.exp w) - Real.log 2.7 := by
  have h1 : Real.log 2.7 < (0.9940:Real) := (log_2_7_bounds).2
  have h2 : (0.9940:Real) < 1.02 := by mach_decimal
  exact sub_pos_of_lt (lt_of_lt_of_le (lt_trans_ax h1 h2) hEw_ge)

theorem growthCompetition_hApos_negside {w : Real}
    (hEw_ge : (1.3:Real) ≤ Real.exp (Real.exp w)) :
    0 < Real.exp (Real.exp w) - Real.log 2.2 := by
  have h1 : Real.log 2.2 < (0.7890:Real) := (log_2_2_bounds).2
  have h2 : (0.7890:Real) < 1.3 := by mach_decimal
  exact sub_pos_of_lt (lt_of_lt_of_le (lt_trans_ax h1 h2) hEw_ge)

theorem growthCompetition_hBpos_negside {w : Real}
    (hEw_ge : (1.3:Real) ≤ Real.exp (Real.exp w)) :
    0 < Real.exp (Real.exp w) - Real.log 2.7 := by
  have h1 : Real.log 2.7 < (0.9940:Real) := (log_2_7_bounds).2
  have h2 : (0.9940:Real) < 1.3 := by mach_decimal
  exact sub_pos_of_lt (lt_of_lt_of_le (lt_trans_ax h1 h2) hEw_ge)

theorem hk_pos : (0:Real) < Real.log 2.7 - Real.log 2.2 := by
  have h1 : Real.log 2.2 < (0.7890:Real) := (log_2_2_bounds).2
  have h2 : (0.7890:Real) < 0.9930 := by mach_decimal
  have h3 : (0.9930:Real) < Real.log 2.7 := (log_2_7_bounds).1
  exact sub_pos_of_lt (lt_trans_ax (lt_trans_ax h1 h2) h3)

/-- **`T` is strictly INCREASING on `[x1,x2]`** (`E∈[1.02,1.05]`, below the quadratic's vertex). -/
theorem growthCompetition_increasing_on_positive_interval :
    (fun w => Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.2))
        - (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.7)))
      (Real.log (Real.log 1.02))
    < (fun w => Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.2))
        - (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.7)))
      (Real.log (Real.log 1.05)) := by
  apply strictMono_of_deriv_pos
    (fun w => Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.2))
        - (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.7)))
    (Real.log (Real.log 1.02)) (Real.log (Real.log 1.05)) hx12
  · intro w hw1 _
    have hEw_ge : (1.02:Real) ≤ Real.exp (Real.exp w) := by
      have h1 : Real.exp (Real.exp (Real.log (Real.log 1.02))) ≤ Real.exp (Real.exp w) :=
        exp_exp_mono hw1
      rwa [exp_exp_log_log one_lt_1_02] at h1
    exact ⟨_, growthCompetitionWitness_hasDerivAt 2.2 2.7 w
      (growthCompetition_hApos_posside hEw_ge) (growthCompetition_hBpos_posside hEw_ge)⟩
  · intro w f' hw1 hw2 hderiv
    have hEw_ge : (1.02:Real) ≤ Real.exp (Real.exp w) := by
      have h1 : Real.exp (Real.exp (Real.log (Real.log 1.02))) ≤ Real.exp (Real.exp w) :=
        exp_exp_mono hw1
      rwa [exp_exp_log_log one_lt_1_02] at h1
    have hEw_le : Real.exp (Real.exp w) ≤ (1.05:Real) := by
      have h1 : Real.exp (Real.exp w) ≤ Real.exp (Real.exp (Real.log (Real.log 1.05))) :=
        exp_exp_mono hw2
      rwa [exp_exp_log_log one_lt_1_05] at h1
    have hApos := growthCompetition_hApos_posside hEw_ge
    have hBpos := growthCompetition_hBpos_posside hEw_ge
    rw [HasDerivAt_unique _ _ _ w hderiv (growthCompetitionWitness_hasDerivAt 2.2 2.7 w hApos hBpos)]
    have hvertex : (Real.log 2.7 - Real.log 2.2) * (1.05 + 1.05) + -(Real.log 2.2 * Real.log 2.7) ≤ 0 :=
      growthCompetition_vertex_cond_1_05
    have hqb : 0 < (Real.log 2.7 - Real.log 2.2) * (1.05:Real) * 1.05
        + (-(Real.log 2.2 * Real.log 2.7)) * 1.05 + Real.log 2.2 * Real.log 2.2 * Real.log 2.7 := by
      rw [quad_forms_eq]; exact growthCompetition_quad_pos_1_05
    have hquad_add := quadratic_pos_below_vertex (k := Real.log 2.7 - Real.log 2.2)
      (m := -(Real.log 2.2 * Real.log 2.7)) (n := Real.log 2.2 * Real.log 2.2 * Real.log 2.7)
      (b := (1.05:Real)) (E := Real.exp (Real.exp w))
      hk_pos hEw_le hvertex hqb
    have hquad : 0 < (Real.log 2.7 - Real.log 2.2) * Real.exp (Real.exp w) * Real.exp (Real.exp w)
        - Real.log 2.2 * Real.log 2.7 * Real.exp (Real.exp w)
        + Real.log 2.2 * Real.log 2.2 * Real.log 2.7 := by
      rw [← quad_forms_eq]; exact hquad_add
    exact growthCompetitionWitness_deriv_pos_of_quad_pos 2.2 2.7 w hApos hBpos hquad

/-- **`T` is strictly DECREASING on `[x3,x4]`** (`E∈[1.3,2.3]`, between the quadratic's roots). -/
theorem growthCompetition_decreasing_on_negative_interval :
    (fun w => Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.2))
        - (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.7)))
      (Real.log (Real.log 2.3))
    < (fun w => Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.2))
        - (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.7)))
      (Real.log (Real.log 1.3)) := by
  apply strictAnti_of_deriv_neg
    (fun w => Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.2))
        - (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.7)))
    (Real.log (Real.log 1.3)) (Real.log (Real.log 2.3)) hx34
  · intro w hw3 _
    have hEw_ge : (1.3:Real) ≤ Real.exp (Real.exp w) := by
      have h1 : Real.exp (Real.exp (Real.log (Real.log 1.3))) ≤ Real.exp (Real.exp w) :=
        exp_exp_mono hw3
      rwa [exp_exp_log_log one_lt_1_3] at h1
    exact ⟨_, growthCompetitionWitness_hasDerivAt 2.2 2.7 w
      (growthCompetition_hApos_negside hEw_ge) (growthCompetition_hBpos_negside hEw_ge)⟩
  · intro w f' hw3 hw4 hderiv
    have hEw_ge : (1.3:Real) ≤ Real.exp (Real.exp w) := by
      have h1 : Real.exp (Real.exp (Real.log (Real.log 1.3))) ≤ Real.exp (Real.exp w) :=
        exp_exp_mono hw3
      rwa [exp_exp_log_log one_lt_1_3] at h1
    have hEw_le : Real.exp (Real.exp w) ≤ (2.3:Real) := by
      have h1 : Real.exp (Real.exp w) ≤ Real.exp (Real.exp (Real.log (Real.log 2.3))) :=
        exp_exp_mono hw4
      rwa [exp_exp_log_log one_lt_2_3] at h1
    have hApos := growthCompetition_hApos_negside hEw_ge
    have hBpos := growthCompetition_hBpos_negside hEw_ge
    rw [HasDerivAt_unique _ _ _ w hderiv (growthCompetitionWitness_hasDerivAt 2.2 2.7 w hApos hBpos)]
    have hqa : (Real.log 2.7 - Real.log 2.2) * (1.3:Real) * 1.3
        + (-(Real.log 2.2 * Real.log 2.7)) * 1.3 + Real.log 2.2 * Real.log 2.2 * Real.log 2.7 < 0 := by
      rw [quad_forms_eq]; exact growthCompetition_quad_neg_1_3
    have hqb : (Real.log 2.7 - Real.log 2.2) * (2.3:Real) * 2.3
        + (-(Real.log 2.2 * Real.log 2.7)) * 2.3 + Real.log 2.2 * Real.log 2.2 * Real.log 2.7 < 0 := by
      rw [quad_forms_eq]; exact growthCompetition_quad_neg_2_3
    have hquad_add := quadratic_neg_between (k := Real.log 2.7 - Real.log 2.2)
      (m := -(Real.log 2.2 * Real.log 2.7)) (n := Real.log 2.2 * Real.log 2.2 * Real.log 2.7)
      (a := (1.3:Real)) (b := (2.3:Real)) (E := Real.exp (Real.exp w))
      hk_pos (by mach_decimal) hEw_ge hEw_le hqa hqb
    have hquad : (Real.log 2.7 - Real.log 2.2) * Real.exp (Real.exp w) * Real.exp (Real.exp w)
        - Real.log 2.2 * Real.log 2.7 * Real.exp (Real.exp w)
        + Real.log 2.2 * Real.log 2.2 * Real.log 2.7 < 0 := by
      rw [← quad_forms_eq]; exact hquad_add
    exact growthCompetitionWitness_deriv_neg_of_quad_neg 2.2 2.7 w hApos hBpos hquad

theorem growthCompetitionWitness_2_2_2_7_eval_eq (x : Real) :
    (growthCompetitionWitness 2.2 2.7).eval x
      = Real.exp (Real.exp x - Real.log (Real.exp (Real.exp x) - Real.log 2.2))
        - (Real.exp x - Real.log (Real.exp (Real.exp x) - Real.log 2.7)) := by
  rw [growthCompetitionWitness_eval, boundedNonConstantWitness_eval, boundedNonConstantWitness_eval]

/-- **Non-monotonicity, both directions, fully proven.** `T` decreases somewhere (refuting
"monotone increasing everywhere") AND increases somewhere (refuting "monotone decreasing
everywhere") — using two DISJOINT point-pairs, not a shared 3-point pivot (simpler: the
negation of "monotone" only needs ONE counterexample pair per direction, and the two intervals
built above already give one each). -/
theorem growthCompetitionWitness_2_2_2_7_not_monotone :
    ¬ (∀ x y : Real, x < y → (growthCompetitionWitness 2.2 2.7).eval x
        ≤ (growthCompetitionWitness 2.2 2.7).eval y) ∧
    ¬ (∀ x y : Real, x < y → (growthCompetitionWitness 2.2 2.7).eval y
        ≤ (growthCompetitionWitness 2.2 2.7).eval x) := by
  constructor
  · intro hmono
    have h := hmono (Real.log (Real.log 1.3)) (Real.log (Real.log 2.3)) hx34
    rw [growthCompetitionWitness_2_2_2_7_eval_eq, growthCompetitionWitness_2_2_2_7_eval_eq] at h
    exact lt_irrefl_ax _ (lt_of_le_of_lt h growthCompetition_decreasing_on_negative_interval)
  · intro hanti
    have h := hanti (Real.log (Real.log 1.02)) (Real.log (Real.log 1.05)) hx12
    rw [growthCompetitionWitness_2_2_2_7_eval_eq, growthCompetitionWitness_2_2_2_7_eval_eq] at h
    exact lt_irrefl_ax _ (lt_of_le_of_lt h growthCompetition_increasing_on_positive_interval)

theorem log_2_2_lt_one : Real.log 2.2 < 1 := by
  have h1 : Real.log 2.2 < (0.7890:Real) := (log_2_2_bounds).2
  have h2 : (0.7890:Real) < 1 := by rw [← realOfScientific_one_dot_zero]; mach_decimal
  exact lt_trans_ax h1 h2

theorem log_2_7_lt_one : Real.log 2.7 < 1 := by
  have h1 : Real.log 2.7 < (0.9940:Real) := (log_2_7_bounds).2
  have h2 : (0.9940:Real) < 1 := by rw [← realOfScientific_one_dot_zero]; mach_decimal
  exact lt_trans_ax h1 h2

/-- **The fully closed witness.** `growthCompetitionWitness 2.2 2.7` is bounded (both directions),
non-`RightChildrenSimplePositive`, and non-monotonic (both directions) — a genuine, FULLY VERIFIED
member of the witness-finding residual's open classification, escaping every closure mechanism
built earlier in this arc (no `log`-clamp anywhere in the tree; the non-monotonicity here comes
from pure growth-rate competition between two smooth, never-clamping sub-expressions). Closes the
`growthCompetitionWitness` line of investigation end to end. -/
theorem growthCompetitionWitness_2_2_2_7_exists :
    (∀ x, 1 - (-Real.log (1 - Real.log 2.7)) < (growthCompetitionWitness 2.2 2.7).eval x) ∧
    (∀ x, (growthCompetitionWitness 2.2 2.7).eval x < Real.exp (-Real.log (1 - Real.log 2.2))) ∧
    ¬ RightChildrenSimplePositive (growthCompetitionWitness 2.2 2.7) ∧
    ¬ (∀ x y : Real, x < y → (growthCompetitionWitness 2.2 2.7).eval x
        ≤ (growthCompetitionWitness 2.2 2.7).eval y) ∧
    ¬ (∀ x y : Real, x < y → (growthCompetitionWitness 2.2 2.7).eval y
        ≤ (growthCompetitionWitness 2.2 2.7).eval x) :=
  ⟨fun x => growthCompetitionWitness_lower_bound one_lt_2_2 log_2_2_lt_one one_lt_2_7 log_2_7_lt_one x,
   fun x => growthCompetitionWitness_upper_bound one_lt_2_2 log_2_2_lt_one one_lt_2_7 log_2_7_lt_one x,
   growthCompetitionWitness_not_RightChildrenSimplePositive 2.2 2.7,
   growthCompetitionWitness_2_2_2_7_not_monotone.1,
   growthCompetitionWitness_2_2_2_7_not_monotone.2⟩

end Real
end MachLib
