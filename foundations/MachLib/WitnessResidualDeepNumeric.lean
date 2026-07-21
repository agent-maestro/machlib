import MachLib.WitnessResidualDeepDeriv
import MachLib.WitnessResidualGrowthCompetitionNumeric
import MachLib.WitnessResidualDepth1

/-! # The numeric witness facts pinning `growthCompetitionWitnessDeep`'s `g`-sign at `c1=1.5, c2=2.0`

Completes the last genuinely new piece flagged in `WitnessResidualDeepDeriv.lean`: numeric axioms
bracketing `log(1.5)`, `log(2.0)`, and — the piece `growthCompetitionWitness` never needed —
`exp` at the specific narrow ranges the witness points produce, combined into the two concrete
`g`-sign facts (`deep_g_pos_witness`, `deep_g_neg_witness`) that feed `g_lower_bound_on_interval`/
`g_upper_bound_on_interval`.

**Witnesses**: positive region `E ∈ [1.02, 1.03]`, negative region `E ∈ [1.48, 1.52]` (found in
`WitnessResidualGrowthCompetitionDeriv`'s cont. 32 numeric exploration — narrower and better
centered than the first attempt, which was too loose for this transcendental `g`).

**A key simplification, found while building this**: rather than tracking the EXACT irrational
argument `E/(E-p)` symbolically through to `exp`, it's enough to bound it by a clean ROUND number
with comfortable slack (`1.02/(1.02-log 1.5) < 1.7`, `1.35 < 1.52/(1.52-log 1.5)`) and axiomatize
`exp` at THAT round number instead (`exp(1.7) < 5.4740`, `3.8570 < exp(1.35)`) — avoiding ever
needing to axiomatize `exp` at a messy, parameter-dependent argument. Checked numerically first
that the resulting looser margins (`term1(E_hi)-term2(E_lo) ≈ +0.184` for the positive region,
`≈ -0.135` for the negative) still clear comfortably.

**One new monotonicity fact needed, not anticipated when the witnesses were first chosen**:
`term1_increasing_in_q` — `q/(E-q)²` is increasing in `q` (not just decreasing in `E`, which
`term1_decreasing` already covered) — needed because `log(1.5)` and `log(2.0)` are only known via
INTERVAL bounds, not exact values, so both `q`'s own numerator role in `term1` and `p`'s role
inside `term2`'s `p/(E-p)²` factor (the SAME functional shape, just relabeled) need this
direction too. Proved via the same cross-multiplication + `(q2-q1)(E²-q1q2) > 0` technique as
every other order fact in this arc.

**A recurring build gotcha, hit twice more this round**: applying a lemma with implicit arguments
inferable from EITHER the explicit hypothesis types OR the goal's expected type sometimes picks
the WRONG source, producing a hypothesis-type mismatch that looks like a wrong fact was supplied
rather than a wrong inference — fixed both times by pinning the implicits explicitly
(`(q1 := ...) (q2 := ...) (E := ...)`), matching the same fix needed in
`WitnessResidualDeepGSignControl.lean`. -/

namespace MachLib
namespace Real

axiom log_1_5_bounds : (0.4050 : Real) < Real.log 1.5 ∧ Real.log 1.5 < 0.4060
axiom log_2_0_bounds : (0.6925 : Real) < Real.log 2.0 ∧ Real.log 2.0 < 0.6935
axiom exp_1_7_upper : Real.exp 1.7 < 5.4740
axiom exp_1_35_lower : (3.8570 : Real) < Real.exp 1.35

theorem sub_lt_sub_left {a b : Real} (h : a < b) (c : Real) : c - b < c - a := by
  rw [sub_def, sub_def]
  exact add_lt_add_left (neg_lt_neg_local h) c

/-- `a < c*b → a/b < c`, for `b>0`. -/
theorem div_lt_of_lt_mul {a b c : Real} (h : a < c * b) (hb : 0 < b) : a / b < c := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hbinv : 0 < 1 / b := one_div_pos_of_pos hb
  have h2 : a * (1 / b) < c * b * (1 / b) := mul_lt_mul_of_pos_right h hbinv
  have e1 : c * b * (1 / b) = c * (b * (1 / b)) := mul_assoc c b (1 / b)
  have e2 : b * (1 / b) = 1 := mul_inv b hbne
  rw [e1, e2, mul_one_ax] at h2
  rwa [div_def a b hbne]

/-- `1.02/(1.02 - log 1.5) < 1.7`. -/
theorem ratio_102_lt_1_7 : (1.02 : Real) / (1.02 - Real.log 1.5) < 1.7 := by
  have hp : Real.log 1.5 < 0.4060 := (log_1_5_bounds).2
  have hden_pos : (0:Real) < 1.02 - Real.log 1.5 := by
    have h : (0.4060:Real) < 1.02 := by mach_decimal
    exact sub_pos_of_lt (lt_trans_ax hp h)
  apply div_lt_of_lt_mul _ hden_pos
  have hstep : (1.7:Real) * (1.02 - Real.log 1.5) = 1.7 * 1.02 - 1.7 * Real.log 1.5 := by
    mach_mpoly [Real.log 1.5]
  rw [hstep]
  have h1 : (1.7:Real) * Real.log 1.5 < 1.7 * 0.4060 := mul_lt_mul_of_pos_left hp (by mach_decimal)
  have h2add' : (1.0200:Real) * 1.0000 + 1.7000 * 0.4060 < 1.7000 * 1.0200 := by mach_decimal
  have e102 : (1.02:Real) = 1.0200 * 1.0000 := by mach_decimal
  have e17a : (1.7:Real) * 0.4060 = 1.7000 * 0.4060 := by mach_decimal
  have e17b : (1.7:Real) * 1.02 = 1.7000 * 1.0200 := by mach_decimal
  have h2add : (1.02:Real) + 1.7 * 0.4060 < 1.7 * 1.02 := by rw [e17b, e17a, e102]; exact h2add'
  have h2 : (1.02:Real) < 1.7 * 1.02 - 1.7 * 0.4060 := lt_sub_of_add_lt h2add
  have h3 : (1.7:Real) * 1.02 - 1.7 * 0.4060 < 1.7 * 1.02 - 1.7 * Real.log 1.5 :=
    sub_lt_sub_left h1 (1.7 * 1.02)
  exact lt_trans_ax h2 h3

/-- `c*b < a → c < a/b`, for `b>0`. -/
theorem lt_div_of_mul_lt {a b c : Real} (h : c * b < a) (hb : 0 < b) : c < a / b := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hbinv : 0 < 1 / b := one_div_pos_of_pos hb
  have h2 : c * b * (1 / b) < a * (1 / b) := mul_lt_mul_of_pos_right h hbinv
  have e1 : c * b * (1 / b) = c * (b * (1 / b)) := mul_assoc c b (1 / b)
  have e2 : b * (1 / b) = 1 := mul_inv b hbne
  rw [e1, e2, mul_one_ax] at h2
  rwa [div_def a b hbne]

/-- `1.35 < 1.52/(1.52 - log 1.5)`. -/
theorem ratio_152_gt_1_35 : (1.35 : Real) < 1.52 / (1.52 - Real.log 1.5) := by
  have hp : (0.4050:Real) < Real.log 1.5 := (log_1_5_bounds).1
  have hden_pos : (0:Real) < 1.52 - Real.log 1.5 := by
    have h : Real.log 1.5 < 1.52 := by
      have h2 := (log_1_5_bounds).2
      have h3 : (0.4060:Real) < 1.52 := by mach_decimal
      exact lt_trans_ax h2 h3
    exact sub_pos_of_lt h
  apply lt_div_of_mul_lt _ hden_pos
  have hstep : (1.35:Real) * (1.52 - Real.log 1.5) = 1.35 * 1.52 - 1.35 * Real.log 1.5 := by
    mach_mpoly [Real.log 1.5]
  rw [hstep]
  have h1 : (1.35:Real) * 0.4050 < 1.35 * Real.log 1.5 := mul_lt_mul_of_pos_left hp (by mach_decimal)
  have h2 : (1.35:Real) * 1.52 - 1.35 * Real.log 1.5 < 1.35 * 1.52 - 1.35 * 0.4050 :=
    sub_lt_sub_left h1 (1.35 * 1.52)
  have h3 : (1.35:Real) * 1.52 - 1.35 * 0.4050 < 1.52 := by
    have h3add' : (1.3500:Real) * 1.5200 < 1.5200 * 1.0000 + 1.3500 * 0.4050 := by mach_decimal
    have e152 : (1.52:Real) = 1.5200 * 1.0000 := by mach_decimal
    have e1352 : (1.35:Real) * 1.52 = 1.3500 * 1.5200 := by mach_decimal
    have e13504 : (1.35:Real) * 0.4050 = 1.3500 * 0.4050 := by mach_decimal
    have h3add : (1.35:Real) * 1.52 < 1.52 + 1.35 * 0.4050 := by
      rw [e1352, e13504, e152]; exact h3add'
    have hsub := sub_lt_sub_right_of_lt (r := (1.35:Real) * 0.4050) h3add
    have esimp : (1.52:Real) + 1.35 * 0.4050 - 1.35 * 0.4050 = 1.52 := by mach_ring
    rwa [esimp] at hsub
  exact lt_trans_ax h2 h3

/-- `exp(1.02/(1.02-log 1.5)) < exp(1.7) < 5.4740`. -/
theorem exp_ratio_102_upper : Real.exp (1.02 / (1.02 - Real.log 1.5)) < 5.4740 :=
  lt_trans_ax (Real.exp_lt ratio_102_lt_1_7) exp_1_7_upper

/-- `3.8570 < exp(1.35) < exp(1.52/(1.52-log 1.5))`. -/
theorem exp_ratio_152_lower : (3.8570:Real) < Real.exp (1.52 / (1.52 - Real.log 1.5)) :=
  lt_trans_ax exp_1_35_lower (Real.exp_lt ratio_152_gt_1_35)

theorem lt_of_mul_lt_mul_right_pos {a b c : Real} (h : a * c < b * c) (hc : 0 < c) : a < b := by
  have h2 := mul_lt_mul_of_pos_right h (one_div_pos_of_pos hc)
  rw [mul_assoc, mul_inv c (ne_of_gt hc), mul_one_ax,
      mul_assoc, mul_inv c (ne_of_gt hc), mul_one_ax] at h2
  exact h2

theorem div_lt_div_of_lt_of_pos {a b c d : Real} (h : a * d < c * b) (hb : 0 < b) (hd : 0 < d) :
    a / b < c / d := by
  have hbd : (0:Real) < b * d := mul_pos hb hd
  have e1 : a / b * (b * d) = a * d := by rw [← mul_assoc, div_mul_cancel (ne_of_gt hb)]
  have e2 : c / d * (b * d) = c * b := by
    rw [mul_comm b d, ← mul_assoc, div_mul_cancel (ne_of_gt hd)]
  have key : a / b * (b * d) < c / d * (b * d) := by rw [e1, e2]; exact h
  exact lt_of_mul_lt_mul_right_pos key hbd

theorem lt_of_sub_pos_local {a b : Real} (h : 0 < b - a) : a < b := by
  have h2 := add_lt_add_left h a
  have e1 : a + 0 = a := add_zero _
  have e2 : a + (b - a) = b := by mach_mpoly [a, b]
  rwa [e1, e2] at h2

/-- `q/(E-q)²` is strictly increasing in `q`, for `0 < q1 < q2 < E`. -/
theorem term1_increasing_in_q {q1 q2 E : Real} (hq1 : 0 < q1) (hq1q2 : q1 < q2) (hq2E : q2 < E) :
    q1 / ((E - q1) * (E - q1)) < q2 / ((E - q2) * (E - q2)) := by
  have hq2 : 0 < q2 := lt_trans_ax hq1 hq1q2
  have hq1E : q1 < E := lt_trans_ax hq1q2 hq2E
  have hEq1 : 0 < E - q1 := sub_pos_of_lt hq1E
  have hEq2 : 0 < E - q2 := sub_pos_of_lt hq2E
  apply div_lt_div_of_lt_of_pos _ (mul_pos hEq1 hEq1) (mul_pos hEq2 hEq2)
  have hcross : q2 * (E - q1) * (E - q1) - q1 * (E - q2) * (E - q2)
      = (q2 - q1) * (E * E - q1 * q2) := by mach_mpoly [q1, q2, E]
  have hq2mq1 : 0 < q2 - q1 := sub_pos_of_lt hq1q2
  have hqE : 0 < E := lt_trans_ax hq2 hq2E
  have hEsq : q1 * q2 < E * E := by
    have h1 : q1 * q2 < q2 * q2 := mul_lt_mul_of_pos_right hq1q2 hq2
    have h3 : q2 * q2 < q2 * E := mul_lt_mul_of_pos_left hq2E hq2
    have h4 : q2 * E < E * E := mul_lt_mul_of_pos_right hq2E hqE
    exact lt_trans_ax h1 (lt_trans_ax h3 h4)
  have hpos : 0 < (q2 - q1) * (E * E - q1 * q2) := mul_pos hq2mq1 (sub_pos_of_lt hEsq)
  rw [← hcross] at hpos
  have hlt : q1 * (E - q2) * (E - q2) < q2 * (E - q1) * (E - q1) := lt_of_sub_pos_local hpos
  have e1 : q1 * ((E - q2) * (E - q2)) = q1 * (E - q2) * (E - q2) := (mul_assoc q1 (E - q2) (E - q2)).symm
  have e2 : q2 * ((E - q1) * (E - q1)) = q2 * (E - q1) * (E - q1) := (mul_assoc q2 (E - q1) (E - q1)).symm
  rw [e1, e2]
  exact hlt

/-- The full positive-region numeric fact: `g`'s worst-case lower bound at `E∈[1.02,1.03]` for
`c1=1.5, c2=2.0` is genuinely positive. -/
theorem deep_g_pos_witness :
    0 < Real.log 2.0 / ((1.03 - Real.log 2.0) * (1.03 - Real.log 2.0))
      - Real.exp (1.02 / (1.02 - Real.log 1.5)) * (Real.log 1.5 / ((1.02 - Real.log 1.5) * (1.02 - Real.log 1.5))) := by
  have hq_lo : (0.6925:Real) < Real.log 2.0 := (log_2_0_bounds).1
  have hq_lt_103 : Real.log 2.0 < 1.03 := by
    have h2 := (log_2_0_bounds).2
    have h3 : (0.6935:Real) < 1.03 := by mach_decimal
    exact lt_trans_ax h2 h3
  have h6925_lt_103 : (0.6925:Real) < 1.03 := by mach_decimal
  have hterm1_lo : (0.6925:Real) / ((1.03 - 0.6925) * (1.03 - 0.6925))
      < Real.log 2.0 / ((1.03 - Real.log 2.0) * (1.03 - Real.log 2.0)) :=
    term1_increasing_in_q (by mach_decimal) hq_lo hq_lt_103
  have hp_hi : Real.log 1.5 < 0.4060 := (log_1_5_bounds).2
  have hp_pos : (0:Real) < Real.log 1.5 := by
    have h1 : (0:Real) < 0.4050 := by mach_decimal
    exact lt_trans_ax h1 (log_1_5_bounds).1
  have h406_lt_102 : (0.4060:Real) < 1.02 := by mach_decimal
  have hterm1_p_hi : Real.log 1.5 / ((1.02 - Real.log 1.5) * (1.02 - Real.log 1.5))
      < (0.4060:Real) / ((1.02 - 0.4060) * (1.02 - 0.4060)) :=
    term1_increasing_in_q hp_pos hp_hi h406_lt_102
  have hexp_pos : (0:Real) < Real.exp (1.02 / (1.02 - Real.log 1.5)) := Real.exp_pos _
  have hterm1p_pos : (0:Real) < Real.log 1.5 / ((1.02 - Real.log 1.5) * (1.02 - Real.log 1.5)) := by
    apply div_pos_of_pos_pos hp_pos
    have hden : (0:Real) < 1.02 - Real.log 1.5 := sub_pos_of_lt (lt_trans_ax hp_hi h406_lt_102)
    exact mul_pos hden hden
  have hterm2_lt : Real.exp (1.02 / (1.02 - Real.log 1.5))
      * (Real.log 1.5 / ((1.02 - Real.log 1.5) * (1.02 - Real.log 1.5)))
      < (5.4740:Real) * ((0.4060:Real) / ((1.02 - 0.4060) * (1.02 - 0.4060))) :=
    mul_lt_mul_pos exp_ratio_102_upper hterm1_p_hi hexp_pos hterm1p_pos
  have hfinal_numeric : (5.4740:Real) * ((0.4060:Real) / ((1.02 - 0.4060) * (1.02 - 0.4060)))
      < (0.6925:Real) / ((1.03 - 0.6925) * (1.03 - 0.6925)) := by
    have hZ : ((1.02:Real) - 0.4060) * (1.02 - 0.4060) ≠ 0 := by
      have h : (0:Real) < (1.02 - 0.4060) * (1.02 - 0.4060) := by
        have h1 : (0:Real) < 1.02 - 0.4060 := by
          have h2 : (0.4060:Real) < 1.02 := by mach_decimal
          exact sub_pos_of_lt h2
        exact mul_pos h1 h1
      exact ne_of_gt h
    have edist : (5.4740:Real) * ((0.4060:Real) / ((1.02 - 0.4060) * (1.02 - 0.4060)))
        = (5.4740 * 0.4060) / ((1.02 - 0.4060) * (1.02 - 0.4060)) := by
      rw [div_def 0.4060 _ hZ, div_def (5.4740 * 0.4060) _ hZ, mul_assoc]
    rw [edist]
    apply div_lt_div_of_lt_of_pos
    · show (5.4740 * 0.4060 : Real) * ((1.03 - 0.6925) * (1.03 - 0.6925))
        < (0.6925:Real) * ((1.02 - 0.4060) * (1.02 - 0.4060))
      have e103 : (1.03:Real) = 1.0300 := by mach_decimal
      have e102 : (1.02:Real) = 1.0200 := by mach_decimal
      rw [e103, e102]
      have e1 : (1.0300:Real) - 0.6925 = 0.3375 := by
        simp (config := { decide := true }) only [ofSci_eq, decimal_sub_same]
      have e2 : (1.0200:Real) - 0.4060 = 0.6140 := by
        simp (config := { decide := true }) only [ofSci_eq, decimal_sub_same]
      rw [e1, e2]
      mach_decimal
    · have h1 : (0.4060:Real) < 1.02 := by mach_decimal
      have hd : (0:Real) < 1.02 - 0.4060 := sub_pos_of_lt h1
      exact mul_pos hd hd
    · have h1 : (0.6925:Real) < 1.03 := by mach_decimal
      have hd : (0:Real) < 1.03 - 0.6925 := sub_pos_of_lt h1
      exact mul_pos hd hd
  have hchain := lt_trans_ax hterm2_lt hfinal_numeric
  have hchain2 := lt_trans_ax hchain hterm1_lo
  exact sub_pos_of_lt hchain2

/-- The full negative-region numeric fact: `g`'s worst-case upper bound at `E∈[1.48,1.52]` for
`c1=1.5, c2=2.0` is genuinely negative. -/
theorem deep_g_neg_witness :
    Real.log 2.0 / ((1.48 - Real.log 2.0) * (1.48 - Real.log 2.0))
      - Real.exp (1.52 / (1.52 - Real.log 1.5)) * (Real.log 1.5 / ((1.52 - Real.log 1.5) * (1.52 - Real.log 1.5))) < 0 := by
  have hq_hi : Real.log 2.0 < 0.6935 := (log_2_0_bounds).2
  have hq_pos : (0:Real) < Real.log 2.0 := by
    have h1 : (0:Real) < 0.6925 := by mach_decimal
    exact lt_trans_ax h1 (log_2_0_bounds).1
  have h6935_lt_148 : (0.6935:Real) < 1.48 := by mach_decimal
  have hterm1_hi : Real.log 2.0 / ((1.48 - Real.log 2.0) * (1.48 - Real.log 2.0))
      < (0.6935:Real) / ((1.48 - 0.6935) * (1.48 - 0.6935)) :=
    term1_increasing_in_q hq_pos hq_hi h6935_lt_148
  have hp_lo : (0.4050:Real) < Real.log 1.5 := (log_1_5_bounds).1
  have hp_pos : (0:Real) < Real.log 1.5 := by
    have h1 : (0:Real) < 0.4050 := by mach_decimal
    exact lt_trans_ax h1 (log_1_5_bounds).1
  have hp_lt_152 : Real.log 1.5 < 1.52 := by
    have h2 := (log_1_5_bounds).2
    have h3 : (0.4060:Real) < 1.52 := by mach_decimal
    exact lt_trans_ax h2 h3
  have hterm1_p_lo : (0.4050:Real) / ((1.52 - 0.4050) * (1.52 - 0.4050))
      < Real.log 1.5 / ((1.52 - Real.log 1.5) * (1.52 - Real.log 1.5)) :=
    term1_increasing_in_q (q1 := 0.4050) (q2 := Real.log 1.5) (E := 1.52)
      (by mach_decimal) hp_lo hp_lt_152
  have hterm1p_lo_pos : (0:Real) < (0.4050:Real) / ((1.52 - 0.4050) * (1.52 - 0.4050)) := by
    apply div_pos_of_pos_pos (by mach_decimal)
    have hden : (0:Real) < 1.52 - 0.4050 := sub_pos_of_lt (by mach_decimal)
    exact mul_pos hden hden
  have hexp_lo_pos : (0:Real) < (3.8570:Real) := by mach_decimal
  have hterm2_gt : (3.8570:Real) * ((0.4050:Real) / ((1.52 - 0.4050) * (1.52 - 0.4050)))
      < Real.exp (1.52 / (1.52 - Real.log 1.5))
        * (Real.log 1.5 / ((1.52 - Real.log 1.5) * (1.52 - Real.log 1.5))) :=
    mul_lt_mul_pos exp_ratio_152_lower hterm1_p_lo hexp_lo_pos hterm1p_lo_pos
  have hfinal_numeric : (0.6935:Real) / ((1.48 - 0.6935) * (1.48 - 0.6935))
      < (3.8570:Real) * ((0.4050:Real) / ((1.52 - 0.4050) * (1.52 - 0.4050))) := by
    have hZ : ((1.52:Real) - 0.4050) * (1.52 - 0.4050) ≠ 0 := by
      have h : (0:Real) < (1.52 - 0.4050) * (1.52 - 0.4050) := by
        have h1 : (0:Real) < 1.52 - 0.4050 := sub_pos_of_lt (by mach_decimal)
        exact mul_pos h1 h1
      exact ne_of_gt h
    have edist : (3.8570:Real) * ((0.4050:Real) / ((1.52 - 0.4050) * (1.52 - 0.4050)))
        = (3.8570 * 0.4050) / ((1.52 - 0.4050) * (1.52 - 0.4050)) := by
      rw [div_def 0.4050 _ hZ, div_def (3.8570 * 0.4050) _ hZ, mul_assoc]
    rw [edist]
    apply div_lt_div_of_lt_of_pos
    · show (0.6935:Real) * ((1.52 - 0.4050) * (1.52 - 0.4050))
        < (3.8570 * 0.4050 : Real) * ((1.48 - 0.6935) * (1.48 - 0.6935))
      have e152 : (1.52:Real) = 1.5200 := by mach_decimal
      have e148 : (1.48:Real) = 1.4800 := by mach_decimal
      rw [e152, e148]
      have e1 : (1.5200:Real) - 0.4050 = 1.1150 := by
        simp (config := { decide := true }) only [ofSci_eq, decimal_sub_same]
      have e2 : (1.4800:Real) - 0.6935 = 0.7865 := by
        simp (config := { decide := true }) only [ofSci_eq, decimal_sub_same]
      rw [e1, e2]
      mach_decimal
    · have hd : (0:Real) < 1.48 - 0.6935 := sub_pos_of_lt (by mach_decimal)
      exact mul_pos hd hd
    · have hd : (0:Real) < 1.52 - 0.4050 := sub_pos_of_lt (by mach_decimal)
      exact mul_pos hd hd
  have hchain := lt_trans_ax hterm1_hi hfinal_numeric
  have hchain2 := lt_trans_ax hchain hterm2_gt
  exact sub_neg_of_lt' hchain2

end Real
end MachLib
