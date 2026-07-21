import MachLib.WitnessResidualDeepNumeric
import MachLib.WitnessResidualGrowthCompetitionAssembly
import MachLib.DivisionError
import MachLib.SturmNonOscillation

/-! # Non-monotonicity, FULLY CLOSED — `growthCompetitionWitnessDeep 1.5 2.0`

Closes the SECOND, structurally distinct member of the witness-finding residual's open
classification (`growthCompetitionWitness` closed the first). Mirrors
`WitnessResidualGrowthCompetitionAssembly.lean`'s role exactly — translate `E`-witnesses to
`x`-values, get `HasDerivAt` sign across two intervals, feed both into
`strictMono_of_deriv_pos`/`strictAnti_of_deriv_neg`, assemble the final theorem — but with one
extra piece the first tree never needed: `growthCompetitionWitnessDeep`'s `g` is genuinely
transcendental (retains `exp(E/(E-p))`), so its cleared-numerator `hquad` form can't be reached by
`quadratic_neg_between`/`quadratic_pos_below_vertex`'s convexity argument. Instead:

**`g_to_hquad_pos`/`g_to_hquad_neg`**: the missing algebraic bridge. `g(E) := q/(E-q)² -
U·(p/(E-p)²)` combined over a common denominator (`div_sub_div`) is `(q·(E-p)² - U·p·(E-q)²) /
((E-q)²·(E-p)²)` — exactly `hquad`'s numerator over a POSITIVE denominator. Sign of a quotient
with positive denominator matches sign of its numerator (`mul_pos`/`mul_neg_of_neg_of_pos` +
`div_mul_cancel`, no case split needed since the denominator's positivity is known unconditionally
here). This is the one piece with no analogue in the first tree's own assembly file — there, `g`'s
role was played by an actual quadratic already sitting in cleared form.

**`deep_g_pos_on_interval`/`deep_g_neg_on_interval`**: extend `WitnessResidualDeepNumeric.lean`'s
corner-point facts (`deep_g_pos_witness`, `deep_g_neg_witness`, true only AT the specific corner
values `E=1.02/1.03` and `E=1.48/1.52`) to the WHOLE interval, via
`WitnessResidualDeepGSignControl.lean`'s `g_lower_bound_on_interval`/`g_upper_bound_on_interval`
(`g(E) ≥ [corner value]` throughout `[E_lo,E_hi]`, so `0 <` corner `≤ g(E)` gives `0 < g(E)`
everywhere in the interval, and symmetrically for the negative side).

**Everything past this point is a direct structural mirror of
`WitnessResidualGrowthCompetitionAssembly.lean`**: `E`-to-`x` translation via `log(log E)`
(`exp_exp_log_log`/`log_log_mono`/`exp_exp_mono`, reused UNCHANGED from the first tree's own
file — these are generic to any `exp(exp x)`-parameterized family, not specific to which tree),
`strictMono_of_deriv_pos`/`strictAnti_of_deriv_neg` applications using
`growthCompetitionWitnessDeep_hasDerivAt` for existence and the sign-bridge theorems
(`growthCompetitionWitnessDeep_deriv_pos_of_quad_pos`/`_neg_of_quad_neg`) for the derivative sign,
then the same "two disjoint witness-point pairs" non-monotonicity argument.

**Witnesses**: positive/increasing region `E∈[1.02,1.03]` (`x∈[loglog 1.02,loglog 1.03]`),
negative/decreasing region `E∈[1.48,1.52]` (`x∈[loglog 1.48,loglog 1.52]`) — the same two corners
`WitnessResidualDeepNumeric.lean` pinned `g`'s sign at.

**Final theorem** `growthCompetitionWitnessDeep_1_5_2_0_exists`: six conjuncts — bounded both
directions, non-`RightChildrenSimplePositive`, `RightChildrenEverywherePositive` (the first four
already established in `WitnessResidualGrowthCompetitionDeepWitness.lean`'s
`growthCompetitionWitnessDeep_partial_exists`), plus the two non-monotonicity directions closed
here. `sorryAx`-free; depends only on the foundational `HasDerivAt`/`exp`/`log` axiom calculus,
Rolle's theorem, and the four numeric axioms from `WitnessResidualDeepNumeric.lean`
(`log_1_5_bounds`, `log_2_0_bounds`, `exp_1_7_upper`, `exp_1_35_lower`) — verified via a
genuinely fresh rebuild, not a stale-cache read. -/

namespace MachLib
namespace Real

/-- `a*(b/c) = (a*b)/c`, for `c≠0`. -/
theorem mul_div_assoc' {a b c : Real} (hc : c ≠ 0) : a * (b / c) = (a * b) / c := by
  rw [div_def b c hc, ← mul_assoc]
  exact (div_def (a * b) c hc).symm

/-- Clears `g`'s fractional form to the `hquad` numerator form, positive side. -/
theorem g_to_hquad_pos {p q E U : Real} (hDp : (0:Real) < (E - p) * (E - p))
    (hDq : (0:Real) < (E - q) * (E - q))
    (hg : 0 < q / ((E - q) * (E - q)) - U * (p / ((E - p) * (E - p)))) :
    0 < q * (E - p) * (E - p) - U * p * (E - q) * (E - q) := by
  have hDpne : (E - p) * (E - p) ≠ 0 := ne_of_gt hDp
  have hDqne : (E - q) * (E - q) ≠ 0 := ne_of_gt hDq
  have hUp : U * (p / ((E - p) * (E - p))) = (U * p) / ((E - p) * (E - p)) := mul_div_assoc' hDpne
  rw [hUp] at hg
  have hcomb : q / ((E - q) * (E - q)) - (U * p) / ((E - p) * (E - p))
      = (q * ((E - p) * (E - p)) - (U * p) * ((E - q) * (E - q)))
        / (((E - q) * (E - q)) * ((E - p) * (E - p))) :=
    div_sub_div hDqne hDpne
  rw [hcomb] at hg
  have hDenomPos : (0:Real) < ((E - q) * (E - q)) * ((E - p) * (E - p)) := mul_pos hDq hDp
  have hnum_pos : 0 < q * ((E - p) * (E - p)) - (U * p) * ((E - q) * (E - q)) := by
    have hmul := mul_pos hg hDenomPos
    rwa [div_mul_cancel (ne_of_gt hDenomPos)] at hmul
  have hre : q * ((E - p) * (E - p)) - (U * p) * ((E - q) * (E - q))
      = q * (E - p) * (E - p) - U * p * (E - q) * (E - q) := by mach_mpoly [q, p, E, U]
  rwa [hre] at hnum_pos

/-- Mirror, negative side. -/
theorem g_to_hquad_neg {p q E U : Real} (hDp : (0:Real) < (E - p) * (E - p))
    (hDq : (0:Real) < (E - q) * (E - q))
    (hg : q / ((E - q) * (E - q)) - U * (p / ((E - p) * (E - p))) < 0) :
    q * (E - p) * (E - p) - U * p * (E - q) * (E - q) < 0 := by
  have hDpne : (E - p) * (E - p) ≠ 0 := ne_of_gt hDp
  have hDqne : (E - q) * (E - q) ≠ 0 := ne_of_gt hDq
  have hUp : U * (p / ((E - p) * (E - p))) = (U * p) / ((E - p) * (E - p)) := mul_div_assoc' hDpne
  rw [hUp] at hg
  have hcomb : q / ((E - q) * (E - q)) - (U * p) / ((E - p) * (E - p))
      = (q * ((E - p) * (E - p)) - (U * p) * ((E - q) * (E - q)))
        / (((E - q) * (E - q)) * ((E - p) * (E - p))) :=
    div_sub_div hDqne hDpne
  rw [hcomb] at hg
  have hDenomPos : (0:Real) < ((E - q) * (E - q)) * ((E - p) * (E - p)) := mul_pos hDq hDp
  have hnum_neg : q * ((E - p) * (E - p)) - (U * p) * ((E - q) * (E - q)) < 0 := by
    have hmul := mul_neg_of_neg_of_pos hg hDenomPos
    rwa [div_mul_cancel (ne_of_gt hDenomPos)] at hmul
  have hre : q * ((E - p) * (E - p)) - (U * p) * ((E - q) * (E - q))
      = q * (E - p) * (E - p) - U * p * (E - q) * (E - q) := by mach_mpoly [q, p, E, U]
  rwa [hre] at hnum_neg

theorem log_1_5_pos : (0:Real) < Real.log 1.5 :=
  lt_trans_ax (by mach_decimal : (0:Real) < 0.4050) (log_1_5_bounds).1

theorem log_2_0_pos : (0:Real) < Real.log 2.0 :=
  lt_trans_ax (by mach_decimal : (0:Real) < 0.6925) (log_2_0_bounds).1

theorem log_1_5_lt_1_02 : Real.log 1.5 < 1.02 :=
  lt_trans_ax (log_1_5_bounds).2 (by mach_decimal)

theorem log_2_0_lt_1_02 : Real.log 2.0 < 1.02 :=
  lt_trans_ax (log_2_0_bounds).2 (by mach_decimal)

theorem log_1_5_lt_1_48 : Real.log 1.5 < 1.48 := lt_trans_ax log_1_5_lt_1_02 (by mach_decimal)
theorem log_2_0_lt_1_48 : Real.log 2.0 < 1.48 := lt_trans_ax log_2_0_lt_1_02 (by mach_decimal)

/-- `g`'s corner witness extended to the WHOLE interval `E∈[1.02,1.03]`, via
`g_lower_bound_on_interval`. -/
theorem deep_g_pos_on_interval {E : Real} (hlo : (1.02:Real) ≤ E) (hhi : E ≤ 1.03) :
    0 < Real.log 2.0 / ((E - Real.log 2.0) * (E - Real.log 2.0))
      - Real.exp (E / (E - Real.log 1.5)) * (Real.log 1.5 / ((E - Real.log 1.5) * (E - Real.log 1.5))) := by
  have hbound := g_lower_bound_on_interval (p := Real.log 1.5) (q := Real.log 2.0)
      (E_lo := 1.02) (E_hi := 1.03) (E := E) log_1_5_pos log_2_0_pos
      log_1_5_lt_1_02 log_2_0_lt_1_02 hlo hhi
  exact lt_of_lt_of_le deep_g_pos_witness hbound

/-- Mirror, `E∈[1.48,1.52]`, via `g_upper_bound_on_interval`. -/
theorem deep_g_neg_on_interval {E : Real} (hlo : (1.48:Real) ≤ E) (hhi : E ≤ 1.52) :
    Real.log 2.0 / ((E - Real.log 2.0) * (E - Real.log 2.0))
      - Real.exp (E / (E - Real.log 1.5)) * (Real.log 1.5 / ((E - Real.log 1.5) * (E - Real.log 1.5))) < 0 := by
  have hbound := g_upper_bound_on_interval (p := Real.log 1.5) (q := Real.log 2.0)
      (E_lo := 1.48) (E_hi := 1.52) (E := E) log_1_5_pos log_2_0_pos
      log_1_5_lt_1_48 log_2_0_lt_1_48 hlo hhi
  exact lt_of_le_of_lt hbound deep_g_neg_witness

/-- `hquad`'s cleared form, positive side, for `E∈[1.02,1.03]`. -/
theorem deep_hquad_pos_on_interval {E : Real} (hlo : (1.02:Real) ≤ E) (hhi : E ≤ 1.03) :
    0 < Real.log 2.0 * (E - Real.log 1.5) * (E - Real.log 1.5)
      - Real.exp (E / (E - Real.log 1.5)) * Real.log 1.5 * (E - Real.log 2.0) * (E - Real.log 2.0) := by
  have hEp : Real.log 1.5 < E := lt_of_lt_of_le log_1_5_lt_1_02 hlo
  have hEq : Real.log 2.0 < E := lt_of_lt_of_le log_2_0_lt_1_02 hlo
  have hDp : (0:Real) < (E - Real.log 1.5) * (E - Real.log 1.5) :=
    mul_pos (sub_pos_of_lt hEp) (sub_pos_of_lt hEp)
  have hDq : (0:Real) < (E - Real.log 2.0) * (E - Real.log 2.0) :=
    mul_pos (sub_pos_of_lt hEq) (sub_pos_of_lt hEq)
  exact g_to_hquad_pos hDp hDq (deep_g_pos_on_interval hlo hhi)

/-- Mirror, negative side, for `E∈[1.48,1.52]`. -/
theorem deep_hquad_neg_on_interval {E : Real} (hlo : (1.48:Real) ≤ E) (hhi : E ≤ 1.52) :
    Real.log 2.0 * (E - Real.log 1.5) * (E - Real.log 1.5)
      - Real.exp (E / (E - Real.log 1.5)) * Real.log 1.5 * (E - Real.log 2.0) * (E - Real.log 2.0) < 0 := by
  have hEp : Real.log 1.5 < E := lt_of_lt_of_le log_1_5_lt_1_48 hlo
  have hEq : Real.log 2.0 < E := lt_of_lt_of_le log_2_0_lt_1_48 hlo
  have hDp : (0:Real) < (E - Real.log 1.5) * (E - Real.log 1.5) :=
    mul_pos (sub_pos_of_lt hEp) (sub_pos_of_lt hEp)
  have hDq : (0:Real) < (E - Real.log 2.0) * (E - Real.log 2.0) :=
    mul_pos (sub_pos_of_lt hEq) (sub_pos_of_lt hEq)
  exact g_to_hquad_neg hDp hDq (deep_g_neg_on_interval hlo hhi)

theorem deep_hApos_posside {w : Real} (hEw_ge : (1.02:Real) ≤ Real.exp (Real.exp w)) :
    0 < Real.exp (Real.exp w) - Real.log 1.5 :=
  sub_pos_of_lt (lt_of_lt_of_le log_1_5_lt_1_02 hEw_ge)

theorem deep_hBpos_posside {w : Real} (hEw_ge : (1.02:Real) ≤ Real.exp (Real.exp w)) :
    0 < Real.exp (Real.exp w) - Real.log 2.0 :=
  sub_pos_of_lt (lt_of_lt_of_le log_2_0_lt_1_02 hEw_ge)

theorem deep_hApos_negside {w : Real} (hEw_ge : (1.48:Real) ≤ Real.exp (Real.exp w)) :
    0 < Real.exp (Real.exp w) - Real.log 1.5 :=
  sub_pos_of_lt (lt_of_lt_of_le log_1_5_lt_1_48 hEw_ge)

theorem deep_hBpos_negside {w : Real} (hEw_ge : (1.48:Real) ≤ Real.exp (Real.exp w)) :
    0 < Real.exp (Real.exp w) - Real.log 2.0 :=
  sub_pos_of_lt (lt_of_lt_of_le log_2_0_lt_1_48 hEw_ge)

theorem one_lt_1_03_local : (1:Real) < 1.03 := by rw [← realOfScientific_one_dot_zero]; mach_decimal
theorem one_lt_1_48_local : (1:Real) < 1.48 := by rw [← realOfScientific_one_dot_zero]; mach_decimal
theorem one_lt_1_52_local : (1:Real) < 1.52 := by rw [← realOfScientific_one_dot_zero]; mach_decimal

theorem deep_hx12 : Real.log (Real.log 1.02) < Real.log (Real.log 1.03) :=
  log_log_mono one_lt_1_02 (by mach_decimal)

theorem deep_hx34 : Real.log (Real.log 1.48) < Real.log (Real.log 1.52) :=
  log_log_mono one_lt_1_48_local (by mach_decimal)

/-- **`growthCompetitionWitnessDeep 1.5 2.0` is strictly INCREASING on `[loglog 1.02,loglog 1.03]`**
(`E∈[1.02,1.03]`). -/
theorem deep_increasing_on_positive_interval :
    (fun w => Real.exp (Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 1.5)))
        - Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.0)))
      (Real.log (Real.log 1.02))
    < (fun w => Real.exp (Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 1.5)))
        - Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.0)))
      (Real.log (Real.log 1.03)) := by
  apply strictMono_of_deriv_pos
    (fun w => Real.exp (Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 1.5)))
        - Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.0)))
    (Real.log (Real.log 1.02)) (Real.log (Real.log 1.03)) deep_hx12
  · intro w hw1 _
    have hEw_ge : (1.02:Real) ≤ Real.exp (Real.exp w) := by
      have h1 : Real.exp (Real.exp (Real.log (Real.log 1.02))) ≤ Real.exp (Real.exp w) :=
        exp_exp_mono hw1
      rwa [exp_exp_log_log one_lt_1_02] at h1
    exact ⟨_, growthCompetitionWitnessDeep_hasDerivAt 1.5 2.0 w
      (deep_hApos_posside hEw_ge) (deep_hBpos_posside hEw_ge)⟩
  · intro w f' hw1 hw2 hderiv
    have hEw_ge : (1.02:Real) ≤ Real.exp (Real.exp w) := by
      have h1 : Real.exp (Real.exp (Real.log (Real.log 1.02))) ≤ Real.exp (Real.exp w) :=
        exp_exp_mono hw1
      rwa [exp_exp_log_log one_lt_1_02] at h1
    have hEw_le : Real.exp (Real.exp w) ≤ (1.03:Real) := by
      have h1 : Real.exp (Real.exp w) ≤ Real.exp (Real.exp (Real.log (Real.log 1.03))) :=
        exp_exp_mono hw2
      rwa [exp_exp_log_log one_lt_1_03_local] at h1
    have hApos := deep_hApos_posside hEw_ge
    have hBpos := deep_hBpos_posside hEw_ge
    rw [HasDerivAt_unique _ _ _ w hderiv (growthCompetitionWitnessDeep_hasDerivAt 1.5 2.0 w hApos hBpos)]
    exact growthCompetitionWitnessDeep_deriv_pos_of_quad_pos 1.5 2.0 w hApos hBpos
      (deep_hquad_pos_on_interval hEw_ge hEw_le)

/-- **`growthCompetitionWitnessDeep 1.5 2.0` is strictly DECREASING on `[loglog 1.48,loglog 1.52]`**
(`E∈[1.48,1.52]`). -/
theorem deep_decreasing_on_negative_interval :
    (fun w => Real.exp (Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 1.5)))
        - Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.0)))
      (Real.log (Real.log 1.52))
    < (fun w => Real.exp (Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 1.5)))
        - Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.0)))
      (Real.log (Real.log 1.48)) := by
  apply strictAnti_of_deriv_neg
    (fun w => Real.exp (Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 1.5)))
        - Real.exp (Real.exp w - Real.log (Real.exp (Real.exp w) - Real.log 2.0)))
    (Real.log (Real.log 1.48)) (Real.log (Real.log 1.52)) deep_hx34
  · intro w hw3 _
    have hEw_ge : (1.48:Real) ≤ Real.exp (Real.exp w) := by
      have h1 : Real.exp (Real.exp (Real.log (Real.log 1.48))) ≤ Real.exp (Real.exp w) :=
        exp_exp_mono hw3
      rwa [exp_exp_log_log one_lt_1_48_local] at h1
    exact ⟨_, growthCompetitionWitnessDeep_hasDerivAt 1.5 2.0 w
      (deep_hApos_negside hEw_ge) (deep_hBpos_negside hEw_ge)⟩
  · intro w f' hw3 hw4 hderiv
    have hEw_ge : (1.48:Real) ≤ Real.exp (Real.exp w) := by
      have h1 : Real.exp (Real.exp (Real.log (Real.log 1.48))) ≤ Real.exp (Real.exp w) :=
        exp_exp_mono hw3
      rwa [exp_exp_log_log one_lt_1_48_local] at h1
    have hEw_le : Real.exp (Real.exp w) ≤ (1.52:Real) := by
      have h1 : Real.exp (Real.exp w) ≤ Real.exp (Real.exp (Real.log (Real.log 1.52))) :=
        exp_exp_mono hw4
      rwa [exp_exp_log_log one_lt_1_52_local] at h1
    have hApos := deep_hApos_negside hEw_ge
    have hBpos := deep_hBpos_negside hEw_ge
    rw [HasDerivAt_unique _ _ _ w hderiv (growthCompetitionWitnessDeep_hasDerivAt 1.5 2.0 w hApos hBpos)]
    exact growthCompetitionWitnessDeep_deriv_neg_of_quad_neg 1.5 2.0 w hApos hBpos
      (deep_hquad_neg_on_interval hEw_ge hEw_le)

theorem growthCompetitionWitnessDeep_1_5_2_0_eval_eq (x : Real) :
    (growthCompetitionWitnessDeep 1.5 2.0).eval x
      = Real.exp (Real.exp (Real.exp x - Real.log (Real.exp (Real.exp x) - Real.log 1.5)))
        - Real.exp (Real.exp x - Real.log (Real.exp (Real.exp x) - Real.log 2.0)) := by
  rw [growthCompetitionWitnessDeep_eval, boundedNonConstantWitness_eval, boundedNonConstantWitness_eval]

/-- **Non-monotonicity, both directions, fully proven**, mirroring
`growthCompetitionWitness_2_2_2_7_not_monotone`'s structure exactly: two disjoint witness-point
pairs, one per direction. -/
theorem growthCompetitionWitnessDeep_1_5_2_0_not_monotone :
    ¬ (∀ x y : Real, x < y → (growthCompetitionWitnessDeep 1.5 2.0).eval x
        ≤ (growthCompetitionWitnessDeep 1.5 2.0).eval y) ∧
    ¬ (∀ x y : Real, x < y → (growthCompetitionWitnessDeep 1.5 2.0).eval y
        ≤ (growthCompetitionWitnessDeep 1.5 2.0).eval x) := by
  constructor
  · intro hmono
    have h := hmono (Real.log (Real.log 1.48)) (Real.log (Real.log 1.52)) deep_hx34
    rw [growthCompetitionWitnessDeep_1_5_2_0_eval_eq, growthCompetitionWitnessDeep_1_5_2_0_eval_eq] at h
    exact lt_irrefl_ax _ (lt_of_le_of_lt h deep_decreasing_on_negative_interval)
  · intro hanti
    have h := hanti (Real.log (Real.log 1.02)) (Real.log (Real.log 1.03)) deep_hx12
    rw [growthCompetitionWitnessDeep_1_5_2_0_eval_eq, growthCompetitionWitnessDeep_1_5_2_0_eval_eq] at h
    exact lt_irrefl_ax _ (lt_of_le_of_lt h deep_increasing_on_positive_interval)

theorem one_lt_1_5 : (1:Real) < 1.5 := by rw [← realOfScientific_one_dot_zero]; mach_decimal
theorem one_lt_2_0 : (1:Real) < 2.0 := by rw [← realOfScientific_one_dot_zero]; mach_decimal

theorem log_1_5_lt_one : Real.log 1.5 < 1 := by
  have h2 : (0.4060:Real) < 1 := by rw [← realOfScientific_one_dot_zero]; mach_decimal
  exact lt_trans_ax (log_1_5_bounds).2 h2

theorem log_2_0_lt_one : Real.log 2.0 < 1 := by
  have h2 : (0.6935:Real) < 1 := by rw [← realOfScientific_one_dot_zero]; mach_decimal
  exact lt_trans_ax (log_2_0_bounds).2 h2

/-- **The fully closed second witness.** `growthCompetitionWitnessDeep 1.5 2.0` is bounded (both
directions), non-`RightChildrenSimplePositive`, satisfies `RightChildrenEverywherePositive`, AND
is non-monotonic (both directions) — closing the SECOND, structurally distinct member of the
witness-finding residual's open classification, with a genuinely transcendental (non-algebraic)
derivative sign argument. -/
theorem growthCompetitionWitnessDeep_1_5_2_0_exists :
    (∀ x, Real.exp 1 - Real.exp (-Real.log (1 - Real.log 2.0))
        < (growthCompetitionWitnessDeep 1.5 2.0).eval x) ∧
    (∀ x, (growthCompetitionWitnessDeep 1.5 2.0).eval x
        < Real.exp (Real.exp (-Real.log (1 - Real.log 1.5))) - 1) ∧
    ¬ RightChildrenSimplePositive (growthCompetitionWitnessDeep 1.5 2.0) ∧
    RightChildrenEverywherePositive (growthCompetitionWitnessDeep 1.5 2.0) ∧
    ¬ (∀ x y : Real, x < y → (growthCompetitionWitnessDeep 1.5 2.0).eval x
        ≤ (growthCompetitionWitnessDeep 1.5 2.0).eval y) ∧
    ¬ (∀ x y : Real, x < y → (growthCompetitionWitnessDeep 1.5 2.0).eval y
        ≤ (growthCompetitionWitnessDeep 1.5 2.0).eval x) :=
  ⟨fun x => growthCompetitionWitnessDeep_lower_bound one_lt_1_5 log_1_5_lt_one one_lt_2_0 log_2_0_lt_one x,
   fun x => growthCompetitionWitnessDeep_upper_bound one_lt_1_5 log_1_5_lt_one one_lt_2_0 log_2_0_lt_one x,
   growthCompetitionWitnessDeep_not_RightChildrenSimplePositive 1.5 2.0,
   growthCompetitionWitnessDeep_RightChildrenEverywherePositive one_lt_1_5 log_1_5_lt_one one_lt_2_0 log_2_0_lt_one,
   growthCompetitionWitnessDeep_1_5_2_0_not_monotone.1,
   growthCompetitionWitnessDeep_1_5_2_0_not_monotone.2⟩

end Real
end MachLib
