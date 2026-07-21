import MachLib.WitnessResidualGrowthCompetitionDeriv
import MachLib.Decimal

/-! # The four concrete numeric facts, for `c1 = 2.2, c2 = 2.7`

`WitnessResidualGrowthCompetitionDeriv.lean` reduced `growthCompetitionWitness`'s derivative sign
to the sign of `quad(E) := (q-p)·E² - pq·E + p²q` (`p := log c1`, `q := log c2`) at `E := exp(exp
z)`. This file pins the construction to a CONCRETE instance (`c1=2.2, c2=2.7`) and proves the four
numeric facts the non-monotonicity argument needs: `quad(E) < 0` at two witnesses `E = 1.3, 2.3`
(feeding `quadratic_neg_between`), `quad(1.05) > 0` plus the accompanying vertex condition (feeding
`quadratic_pos_below_vertex`).

**Why axioms are needed at all.** `p = log 2.2` and `q = log 2.7` are transcendental — evaluating
`quad(E)`'s sign at a specific `E` needs SOME numeric handle on them. Two well-justified axioms
(`log_2_2_bounds`, `log_2_7_bounds`) bracket each to four decimal places — the same "trust the
well-known numeric fact" status as `exp_one_lt_three`/`pi_gt_three` (`IteratedExpBounds.lean`).
MachLib has no `nlinarith`-equivalent tactic yet (`Linarith.lean`'s own docstring flags this as
future work), so turning a 2-variable interval bound into a quadratic's sign needs to happen by
hand rather than automatically.

**The bounding technique.** Rather than jointly optimizing over the 2D `(p,q)` box (which would
need a genuine `nlinarith`), each of `quad`'s three terms is bounded INDEPENDENTLY using whichever
corner of the box is worst-case for THAT term alone (checked numerically first: this looser bound
still clears the true value with comfortable margin — e.g. loose bound `-0.050` vs. true value
`-0.056` at `E=1.3`). Concretely: `(q-p)` is bounded using `q`'s and `p`'s OWN one-sided bounds
(`mul_lt_mul_of_pos_right`/`_left`); products like `p·q` are bounded via `mul_lt_mul_pos` (both
factors move in the same direction); the three term-bounds are summed via `add_lt_add`; and the
whole thing reduces to a literal decimal inequality, closed by reformulating `A - B + C < 0` as `A
+ C < B` (pure addition, avoiding `mach_decimal`'s gap on general signed decimal subtraction — see
`Decimal.lean`'s new `decimal_sub_same`) and padding every literal to a UNIFORM decimal-place count
so every product lands at the same `realOfScientific` exponent, letting `decimal_add_same` combine
them before the final `realOfScientific_lt_of_nat` cross-multiplication check. -/

namespace MachLib
namespace Real

/-- `log(2.2) ∈ (0.7880, 0.7890)` — true value `≈ 0.788457`. -/
axiom log_2_2_bounds : (0.7880 : Real) < Real.log 2.2 ∧ Real.log 2.2 < 0.7890

/-- `log(2.7) ∈ (0.9930, 0.9940)` — true value `≈ 0.993252`. -/
axiom log_2_7_bounds : (0.9930 : Real) < Real.log 2.7 ∧ Real.log 2.7 < 0.9940

theorem mul_lt_mul_of_pos_left {a b c : Real} (h : a < b) (hc : 0 < c) : c * a < c * b := by
  rw [mul_comm c a, mul_comm c b]; exact mul_lt_mul_of_pos_right h hc

/-- Both factors move the same direction ⟹ the product does too (strict, needs both lower bounds
positive). -/
theorem mul_lt_mul_pos {a b c d : Real} (hac : a < c) (hbd : b < d) (ha : 0 < a) (hb : 0 < b) :
    a * b < c * d := by
  have h1 : a * b < c * b := mul_lt_mul_of_pos_right hac hb
  have hc : 0 < c := lt_trans_ax ha hac
  have h2 : c * b < c * d := mul_lt_mul_of_pos_left hbd hc
  exact lt_trans_ax h1 h2

/-- `quad(1.3) < 0` for `c1=2.2, c2=2.7` — derived from the log bounds via independent
term-by-term bounding. Loose bound ≈ -0.0503, true value ≈ -0.0555. -/
theorem growthCompetition_quad_neg_1_3 :
    (Real.log 2.7 - Real.log 2.2) * 1.3 * 1.3 - Real.log 2.2 * Real.log 2.7 * 1.3
      + Real.log 2.2 * Real.log 2.2 * Real.log 2.7 < 0 := by
  obtain ⟨hp_lo, hp_hi⟩ := log_2_2_bounds
  obtain ⟨hq_lo, hq_hi⟩ := log_2_7_bounds
  have hp_pos : (0:Real) < Real.log 2.2 := lt_trans_ax (by mach_decimal) hp_lo
  have hq_pos : (0:Real) < Real.log 2.7 := lt_trans_ax (by mach_decimal) hq_lo
  have term1 : (Real.log 2.7 - Real.log 2.2) * 1.3 * 1.3 < (0.9940 - 0.7880) * 1.3 * 1.3 := by
    have hdiff : Real.log 2.7 - Real.log 2.2 < 0.9940 - 0.7880 := by
      have h1 := add_lt_add hq_hi (neg_lt_neg_local hp_lo)
      have e1 : Real.log 2.7 + -Real.log 2.2 = Real.log 2.7 - Real.log 2.2 := (sub_def _ _).symm
      have e2 : (0.9940:Real) + -0.7880 = 0.9940 - 0.7880 := (sub_def _ _).symm
      rwa [e1, e2] at h1
    have hstep := mul_lt_mul_of_pos_right hdiff (by mach_decimal : (0:Real) < 1.3)
    exact mul_lt_mul_of_pos_right hstep (by mach_decimal : (0:Real) < 1.3)
  have term2 : -(Real.log 2.2 * Real.log 2.7 * 1.3) < -(0.7880 * 0.9930 * 1.3) := by
    have hprod : (0.7880:Real) * 0.9930 < Real.log 2.2 * Real.log 2.7 :=
      mul_lt_mul_pos hp_lo hq_lo (by mach_decimal) (by mach_decimal)
    have hstep : (0.7880:Real) * 0.9930 * 1.3 < Real.log 2.2 * Real.log 2.7 * 1.3 :=
      mul_lt_mul_of_pos_right hprod (by mach_decimal)
    exact neg_lt_neg_local hstep
  have term3 : Real.log 2.2 * Real.log 2.2 * Real.log 2.7 < 0.7890 * 0.7890 * 0.9940 := by
    have hpp : Real.log 2.2 * Real.log 2.2 < (0.7890:Real) * 0.7890 :=
      mul_lt_mul_pos hp_hi hp_hi hp_pos hp_pos
    exact mul_lt_mul_pos hpp hq_hi (mul_pos hp_pos hp_pos) hq_pos
  have hsum : (Real.log 2.7 - Real.log 2.2) * 1.3 * 1.3 - Real.log 2.2 * Real.log 2.7 * 1.3
      + Real.log 2.2 * Real.log 2.2 * Real.log 2.7
      < (0.9940 - 0.7880) * 1.3 * 1.3 - 0.7880 * 0.9930 * 1.3 + 0.7890 * 0.7890 * 0.9940 := by
    have h12 : (Real.log 2.7 - Real.log 2.2) * 1.3 * 1.3 - Real.log 2.2 * Real.log 2.7 * 1.3
        < (0.9940 - 0.7880) * 1.3 * 1.3 - 0.7880 * 0.9930 * 1.3 := by
      have e1 : (Real.log 2.7 - Real.log 2.2) * 1.3 * 1.3 - Real.log 2.2 * Real.log 2.7 * 1.3
          = (Real.log 2.7 - Real.log 2.2) * 1.3 * 1.3 + -(Real.log 2.2 * Real.log 2.7 * 1.3) :=
        sub_def _ _
      have e2 : (0.9940 - 0.7880 : Real) * 1.3 * 1.3 - 0.7880 * 0.9930 * 1.3
          = (0.9940 - 0.7880 : Real) * 1.3 * 1.3 + -(0.7880 * 0.9930 * 1.3) := sub_def _ _
      rw [e1, e2]
      exact add_lt_add term1 term2
    exact add_lt_add h12 term3
  have h13 : (1.3 : Real) = 1.3000 := by mach_decimal
  have hfinal : (0.9940 - 0.7880 : Real) * 1.3 * 1.3 - 0.7880 * 0.9930 * 1.3 + 0.7890 * 0.7890 * 0.9940 < 0 := by
    rw [h13]
    have haddform : ((0.9940 - 0.7880 : Real) * 1.3000 * 1.3000) + (0.7890 * 0.7890 * 0.9940)
        < (0.7880 * 0.9930 * 1.3000 : Real) := by
      simp (config := { decide := true }) only
        [ofSci_eq, mul_one_ax, one_mul_thm, add_zero, zero_add,
         one_sub_decimal, decimal_sub_same, decimal_add_same, decimal_mul, decimal_normalize]
      apply realOfScientific_lt_of_nat
      decide
    have e : (0.9940 - 0.7880 : Real) * 1.3000 * 1.3000 - 0.7880 * 0.9930 * 1.3000 + 0.7890 * 0.7890 * 0.9940
        = ((0.9940 - 0.7880 : Real) * 1.3000 * 1.3000 + 0.7890 * 0.7890 * 0.9940) - 0.7880 * 0.9930 * 1.3000 := by
      mach_mpoly [(0.9940 - 0.7880 : Real), (0.7880:Real), (0.9930:Real), (0.7890:Real), (0.9940:Real)]
    rw [e]
    exact sub_neg_of_lt' haddform
  exact lt_trans_ax hsum hfinal

/-- `quad(2.3) < 0` — same structure as the `1.3` case, `E=2.3` instead. Loose bound ≈ -0.0912,
true value ≈ -0.1046. -/
theorem growthCompetition_quad_neg_2_3 :
    (Real.log 2.7 - Real.log 2.2) * 2.3 * 2.3 - Real.log 2.2 * Real.log 2.7 * 2.3
      + Real.log 2.2 * Real.log 2.2 * Real.log 2.7 < 0 := by
  obtain ⟨hp_lo, hp_hi⟩ := log_2_2_bounds
  obtain ⟨hq_lo, hq_hi⟩ := log_2_7_bounds
  have hp_pos : (0:Real) < Real.log 2.2 := lt_trans_ax (by mach_decimal) hp_lo
  have hq_pos : (0:Real) < Real.log 2.7 := lt_trans_ax (by mach_decimal) hq_lo
  have term1 : (Real.log 2.7 - Real.log 2.2) * 2.3 * 2.3 < (0.9940 - 0.7880) * 2.3 * 2.3 := by
    have hdiff : Real.log 2.7 - Real.log 2.2 < 0.9940 - 0.7880 := by
      have h1 := add_lt_add hq_hi (neg_lt_neg_local hp_lo)
      have e1 : Real.log 2.7 + -Real.log 2.2 = Real.log 2.7 - Real.log 2.2 := (sub_def _ _).symm
      have e2 : (0.9940:Real) + -0.7880 = 0.9940 - 0.7880 := (sub_def _ _).symm
      rwa [e1, e2] at h1
    have hstep := mul_lt_mul_of_pos_right hdiff (by mach_decimal : (0:Real) < 2.3)
    exact mul_lt_mul_of_pos_right hstep (by mach_decimal : (0:Real) < 2.3)
  have term2 : -(Real.log 2.2 * Real.log 2.7 * 2.3) < -(0.7880 * 0.9930 * 2.3) := by
    have hprod : (0.7880:Real) * 0.9930 < Real.log 2.2 * Real.log 2.7 :=
      mul_lt_mul_pos hp_lo hq_lo (by mach_decimal) (by mach_decimal)
    have hstep : (0.7880:Real) * 0.9930 * 2.3 < Real.log 2.2 * Real.log 2.7 * 2.3 :=
      mul_lt_mul_of_pos_right hprod (by mach_decimal)
    exact neg_lt_neg_local hstep
  have term3 : Real.log 2.2 * Real.log 2.2 * Real.log 2.7 < 0.7890 * 0.7890 * 0.9940 := by
    have hpp : Real.log 2.2 * Real.log 2.2 < (0.7890:Real) * 0.7890 :=
      mul_lt_mul_pos hp_hi hp_hi hp_pos hp_pos
    exact mul_lt_mul_pos hpp hq_hi (mul_pos hp_pos hp_pos) hq_pos
  have hsum : (Real.log 2.7 - Real.log 2.2) * 2.3 * 2.3 - Real.log 2.2 * Real.log 2.7 * 2.3
      + Real.log 2.2 * Real.log 2.2 * Real.log 2.7
      < (0.9940 - 0.7880) * 2.3 * 2.3 - 0.7880 * 0.9930 * 2.3 + 0.7890 * 0.7890 * 0.9940 := by
    have h12 : (Real.log 2.7 - Real.log 2.2) * 2.3 * 2.3 - Real.log 2.2 * Real.log 2.7 * 2.3
        < (0.9940 - 0.7880) * 2.3 * 2.3 - 0.7880 * 0.9930 * 2.3 := by
      have e1 : (Real.log 2.7 - Real.log 2.2) * 2.3 * 2.3 - Real.log 2.2 * Real.log 2.7 * 2.3
          = (Real.log 2.7 - Real.log 2.2) * 2.3 * 2.3 + -(Real.log 2.2 * Real.log 2.7 * 2.3) :=
        sub_def _ _
      have e2 : (0.9940 - 0.7880 : Real) * 2.3 * 2.3 - 0.7880 * 0.9930 * 2.3
          = (0.9940 - 0.7880 : Real) * 2.3 * 2.3 + -(0.7880 * 0.9930 * 2.3) := sub_def _ _
      rw [e1, e2]
      exact add_lt_add term1 term2
    exact add_lt_add h12 term3
  have h23 : (2.3 : Real) = 2.3000 := by mach_decimal
  have hfinal : (0.9940 - 0.7880 : Real) * 2.3 * 2.3 - 0.7880 * 0.9930 * 2.3 + 0.7890 * 0.7890 * 0.9940 < 0 := by
    rw [h23]
    have haddform : ((0.9940 - 0.7880 : Real) * 2.3000 * 2.3000) + (0.7890 * 0.7890 * 0.9940)
        < (0.7880 * 0.9930 * 2.3000 : Real) := by
      simp (config := { decide := true }) only
        [ofSci_eq, mul_one_ax, one_mul_thm, add_zero, zero_add,
         one_sub_decimal, decimal_sub_same, decimal_add_same, decimal_mul, decimal_normalize]
      apply realOfScientific_lt_of_nat
      decide
    have e : (0.9940 - 0.7880 : Real) * 2.3000 * 2.3000 - 0.7880 * 0.9930 * 2.3000 + 0.7890 * 0.7890 * 0.9940
        = ((0.9940 - 0.7880 : Real) * 2.3000 * 2.3000 + 0.7890 * 0.7890 * 0.9940) - 0.7880 * 0.9930 * 2.3000 := by
      mach_mpoly [(0.9940 - 0.7880 : Real), (0.7880:Real), (0.9930:Real), (0.7890:Real), (0.9940:Real)]
    rw [e]
    exact sub_neg_of_lt' haddform
  exact lt_trans_ax hsum hfinal

/-- `quad(1.05) > 0` — lower-bound direction (opposite corner from the negative-region cases:
`p_hi,q_hi` for the negative middle term, `p_lo,q_lo` for the constant term, `q_lo-p_hi` for the
leading coefficient). Loose bound ≈ +0.0180, true value ≈ +0.0210. -/
theorem growthCompetition_quad_pos_1_05 :
    0 < (Real.log 2.7 - Real.log 2.2) * 1.05 * 1.05 - Real.log 2.2 * Real.log 2.7 * 1.05
      + Real.log 2.2 * Real.log 2.2 * Real.log 2.7 := by
  obtain ⟨hp_lo, hp_hi⟩ := log_2_2_bounds
  obtain ⟨hq_lo, hq_hi⟩ := log_2_7_bounds
  have hp_pos : (0:Real) < Real.log 2.2 := lt_trans_ax (by mach_decimal) hp_lo
  have hq_pos : (0:Real) < Real.log 2.7 := lt_trans_ax (by mach_decimal) hq_lo
  have term1 : (0.9930 - 0.7890 : Real) * 1.05 * 1.05 < (Real.log 2.7 - Real.log 2.2) * 1.05 * 1.05 := by
    have hdiff : (0.9930 - 0.7890 : Real) < Real.log 2.7 - Real.log 2.2 := by
      have h1 := add_lt_add hq_lo (neg_lt_neg_local hp_hi)
      have e1 : Real.log 2.7 + -Real.log 2.2 = Real.log 2.7 - Real.log 2.2 := (sub_def _ _).symm
      have e2 : (0.9930:Real) + -0.7890 = 0.9930 - 0.7890 := (sub_def _ _).symm
      rwa [e1, e2] at h1
    have hstep := mul_lt_mul_of_pos_right hdiff (by mach_decimal : (0:Real) < 1.05)
    exact mul_lt_mul_of_pos_right hstep (by mach_decimal : (0:Real) < 1.05)
  have term2 : -(0.7890 * 0.9940 * 1.05 : Real) < -(Real.log 2.2 * Real.log 2.7 * 1.05) := by
    have hprod : Real.log 2.2 * Real.log 2.7 < (0.7890:Real) * 0.9940 :=
      mul_lt_mul_pos hp_hi hq_hi hp_pos hq_pos
    have hstep : Real.log 2.2 * Real.log 2.7 * 1.05 < (0.7890:Real) * 0.9940 * 1.05 :=
      mul_lt_mul_of_pos_right hprod (by mach_decimal)
    exact neg_lt_neg_local hstep
  have term3 : (0.7880 * 0.7880 * 0.9930 : Real) < Real.log 2.2 * Real.log 2.2 * Real.log 2.7 := by
    have hpp : (0.7880:Real) * 0.7880 < Real.log 2.2 * Real.log 2.2 :=
      mul_lt_mul_pos hp_lo hp_lo (by mach_decimal) (by mach_decimal)
    exact mul_lt_mul_pos hpp hq_lo (mul_pos (by mach_decimal) (by mach_decimal)) (by mach_decimal)
  have hsum : (0.9930 - 0.7890 : Real) * 1.05 * 1.05 - 0.7890 * 0.9940 * 1.05 + 0.7880 * 0.7880 * 0.9930
      < (Real.log 2.7 - Real.log 2.2) * 1.05 * 1.05 - Real.log 2.2 * Real.log 2.7 * 1.05
        + Real.log 2.2 * Real.log 2.2 * Real.log 2.7 := by
    have h12 : (0.9930 - 0.7890 : Real) * 1.05 * 1.05 - 0.7890 * 0.9940 * 1.05
        < (Real.log 2.7 - Real.log 2.2) * 1.05 * 1.05 - Real.log 2.2 * Real.log 2.7 * 1.05 := by
      have e1 : (0.9930 - 0.7890 : Real) * 1.05 * 1.05 - 0.7890 * 0.9940 * 1.05
          = (0.9930 - 0.7890 : Real) * 1.05 * 1.05 + -(0.7890 * 0.9940 * 1.05) := sub_def _ _
      have e2 : (Real.log 2.7 - Real.log 2.2) * 1.05 * 1.05 - Real.log 2.2 * Real.log 2.7 * 1.05
          = (Real.log 2.7 - Real.log 2.2) * 1.05 * 1.05 + -(Real.log 2.2 * Real.log 2.7 * 1.05) :=
        sub_def _ _
      rw [e1, e2]
      exact add_lt_add term1 term2
    exact add_lt_add h12 term3
  have hstart : (0:Real) < (0.9930 - 0.7890 : Real) * 1.05 * 1.05 - 0.7890 * 0.9940 * 1.05 + 0.7880 * 0.7880 * 0.9930 := by
    have h105 : (1.05 : Real) = 1.0500 := by mach_decimal
    rw [h105]
    have haddform : (0.7890 * 0.9940 * 1.0500 : Real)
        < ((0.9930 - 0.7890 : Real) * 1.0500 * 1.0500) + (0.7880 * 0.7880 * 0.9930) := by
      simp (config := { decide := true }) only
        [ofSci_eq, mul_one_ax, one_mul_thm, add_zero, zero_add,
         one_sub_decimal, decimal_sub_same, decimal_add_same, decimal_mul, decimal_normalize]
      apply realOfScientific_lt_of_nat
      decide
    have e : (0.9930 - 0.7890 : Real) * 1.0500 * 1.0500 - 0.7890 * 0.9940 * 1.0500 + 0.7880 * 0.7880 * 0.9930
        = ((0.9930 - 0.7890 : Real) * 1.0500 * 1.0500 + 0.7880 * 0.7880 * 0.9930) - 0.7890 * 0.9940 * 1.0500 := by
      mach_mpoly [(0.9930 - 0.7890 : Real), (0.7890:Real), (0.9940:Real), (0.7880:Real), (0.9930:Real)]
    rw [e]
    exact sub_pos_of_lt haddform
  exact lt_trans_ax hstart hsum

/-- **The vertex condition for `quadratic_pos_below_vertex` at `b=1.05`**: `k·(2b)+m ≤ 0`. Loose
upper bound ≈ -0.3499, comfortably negative. -/
theorem growthCompetition_vertex_cond_1_05 :
    (Real.log 2.7 - Real.log 2.2) * (1.05 + 1.05) + -(Real.log 2.2 * Real.log 2.7) ≤ 0 := by
  obtain ⟨hp_lo, hp_hi⟩ := log_2_2_bounds
  obtain ⟨hq_lo, hq_hi⟩ := log_2_7_bounds
  have term1 : (Real.log 2.7 - Real.log 2.2) * (1.05 + 1.05) < (0.9940 - 0.7880 : Real) * (1.05 + 1.05) := by
    have hdiff : Real.log 2.7 - Real.log 2.2 < 0.9940 - 0.7880 := by
      have h1 := add_lt_add hq_hi (neg_lt_neg_local hp_lo)
      have e1 : Real.log 2.7 + -Real.log 2.2 = Real.log 2.7 - Real.log 2.2 := (sub_def _ _).symm
      have e2 : (0.9940:Real) + -0.7880 = 0.9940 - 0.7880 := (sub_def _ _).symm
      rwa [e1, e2] at h1
    exact mul_lt_mul_of_pos_right hdiff (by mach_decimal)
  have term2 : -(Real.log 2.2 * Real.log 2.7) < -(0.7880 * 0.9930 : Real) :=
    neg_lt_neg_local (mul_lt_mul_pos hp_lo hq_lo (by mach_decimal) (by mach_decimal))
  have hsum : (Real.log 2.7 - Real.log 2.2) * (1.05 + 1.05) + -(Real.log 2.2 * Real.log 2.7)
      < (0.9940 - 0.7880 : Real) * (1.05 + 1.05) + -(0.7880 * 0.9930) :=
    add_lt_add term1 term2
  have hfinal : (0.9940 - 0.7880 : Real) * (1.05 + 1.05) + -(0.7880 * 0.9930 : Real) < 0 := by
    have e : (0.9940 - 0.7880 : Real) * (1.05 + 1.05) + -(0.7880 * 0.9930 : Real)
        = (0.9940 - 0.7880 : Real) * (1.05 + 1.05) - 0.7880 * 0.9930 := (sub_def _ _).symm
    rw [e]
    have h105 : (1.05 : Real) = 1.0500 := by mach_decimal
    rw [h105]
    apply sub_neg_of_lt'
    simp (config := { decide := true }) only
      [ofSci_eq, mul_one_ax, one_mul_thm, add_zero, zero_add,
       one_sub_decimal, decimal_sub_same, decimal_add_same, decimal_mul, decimal_normalize]
    apply realOfScientific_lt_of_nat
    decide
  exact le_of_lt (lt_trans_ax hsum hfinal)

end Real
end MachLib
