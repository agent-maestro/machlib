import MachLib.EMLPfaffianValidOnCrossingObstruction
import MachLib.EMLZeroCrossingDomainSplit
import MachLib.EMLOscillationBarrier
import MachLib.WitnessResidualTwoEqualPointsClosure

/-! # MILESTONE: the ENTIRE crossing-family closes, unconditionally, for ANY `c > 1`

`WitnessResidualTwoEqualPointsClosure.lean` found that `expWrappedNonMonotonicWitnessC concreteC`
closes via a simple mechanism: `T1` is CONSTANT on its whole clamped region, and `sin` takes two
different values inside any ray — the collapsed equation forces those different values to be
equal, contradiction. That round left one question open: does this generalize past the one
concrete instance, to the WHOLE crossing-family this session built?

**Yes — completely.** This file proves `sin` takes two different values below ANY real target
`a`, with no restriction on `a`'s sign or size (`sin_two_different_values_le`, built from the
already-available `archimedean` axiom plus periodicity-shifting `0` and `π/2` far enough left).
Combined with the clamped-region fact — generalized here over `c` for the first time (previously
only proven for the specific instances `1+1` and `concreteC`) — this closes
`expWrappedNonMonotonicWitnessC c` for EVERY `c > 1`, not just the one hand-picked value: the
crossing can sit anywhere, positive or negative, and it makes no difference at all to this
argument.

**What this settles.** The entire "crossing-based construction" family explored across cont.
14–23 — `nonMonotonicWitness`, its `exp`-wrap, the parametrized family over `c`, the
positive-crossing instance — is now COMPLETELY closed as a potential source of witness-finding
counterexamples, unconditionally, by one clean elementary argument that needed no monotonicity,
no boundedness, no `EMLPfaffianValidOn`, and (as `eml_depth2_witness_of_const_sibling_two_equal_
points` shows explicitly) not even `c2 > 1`. Every earlier closure in this family — unbounded
above/below, strictly monotonic, the crossing lemmas, the heavy-machinery resolution — is now
subsumed by this one mechanism for this whole family (though NOT rendered pointless: each was a
genuine, independently interesting structural fact, and the general closures apply to trees
OUTSIDE this specific crossing shape too, which this new mechanism does not reach).

**What remains open, honestly.** This closes one large, natural family — but not every
conceivable tree in the residual's open classification. The mechanism here specifically needs
`T1` CONSTANT (not merely bounded) on an unbounded ray; a tree bounded-both-directions and
non-monotonic WITHOUT any such constant stretch (if one exists — none has been found in this
whole arc) would not be reached by it. Whether such a tree exists remains the standing open
question. -/

namespace MachLib
namespace Real

open EMLTree

theorem zero_lt_one_add_one_local : (0 : Real) < 1 + 1 := by
  have h := add_lt_add_left zero_lt_one_ax (1 : Real)
  have e : (1 : Real) + 0 = 1 := add_zero _
  rw [e] at h
  exact lt_trans_ax zero_lt_one_ax h

/-- The clamped-region fact, fully generalized over `c` (previously only proven for `1+1` and
`concreteC` separately) — the induction/algebra never actually depended on the specific value. -/
theorem nonMonotonicWitnessC_eval_clamped_general {c : Real} (hc : 1 < c) {x : Real}
    (hx : x ≤ Real.log (Real.log c)) :
    (nonMonotonicWitnessC c).eval x = 0 := by
  have hlogcpos : 0 < Real.log c := log_pos_of_gt_one hc
  have hDnonpos : Real.exp x - Real.log c ≤ 0 := by
    rcases (le_iff_lt_or_eq x (Real.log (Real.log c))).mp hx with h | h
    · have hexp : Real.exp x < Real.exp (Real.log (Real.log c)) := Real.exp_lt h
      have hexp0 : Real.exp (Real.log (Real.log c)) = Real.log c := Real.exp_log hlogcpos
      rw [hexp0] at hexp
      have e := sub_lt_sub_right_of_lt (r := Real.log c) hexp
      have e2 : Real.log c - Real.log c = 0 := by mach_ring
      rw [e2] at e
      exact le_of_lt e
    · rw [h]
      have hexp0 : Real.exp (Real.log (Real.log c)) = Real.log c := Real.exp_log hlogcpos
      have e : Real.exp (Real.log (Real.log c)) - Real.log c = 0 := by
        rw [hexp0]; mach_ring
      exact le_of_eq e
  show Real.exp x -
      Real.log (Real.exp ((EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x)
        - Real.log ((EMLTree.eml EMLTree.var (EMLTree.const c)).eval x)) = 0
  have hC : (EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x = Real.exp x - Real.log 1 := rfl
  have hD : (EMLTree.eml EMLTree.var (EMLTree.const c)).eval x
      = Real.exp x - Real.log c := rfl
  rw [hC, hD, log_one]
  have e1 : Real.exp x - 0 = Real.exp x := sub_zero _
  rw [e1, Real.log_nonpos hDnonpos, sub_zero, log_exp]
  mach_ring

theorem expWrappedNonMonotonicWitnessC_eval_general (c x : Real) :
    (expWrappedNonMonotonicWitnessC c).eval x = Real.exp ((nonMonotonicWitnessC c).eval x) := by
  show Real.exp ((nonMonotonicWitnessC c).eval x) - Real.log 1
      = Real.exp ((nonMonotonicWitnessC c).eval x)
  rw [log_one, sub_zero]

/-- Shifting by `k` full periods (`2π` each) leaves `sin` unchanged, in the SUBTRACT direction —
mirrors `sin_natCast_mul_pi`'s induction template (`EMLPfaffian.lean`), using `sin_periodic`
directly instead of re-deriving via `sin_add`. -/
theorem sin_sub_natCast_mul_two_pi (y : Real) (k : Nat) :
    Real.sin (y - natCast k * ((1 + 1) * Real.pi)) = Real.sin y := by
  induction k with
  | zero =>
    rw [natCast_zero, zero_mul]
    have e : y - 0 = y := sub_zero y
    rw [e]
  | succ n ih =>
    rw [natCast_succ]
    have hdistrib : (natCast n + 1) * ((1 + 1) * Real.pi)
        = natCast n * ((1 + 1) * Real.pi) + (1 + 1) * Real.pi := by
      rw [mul_distrib_right, one_mul_thm]
    rw [hdistrib]
    have e1 : y - (natCast n * ((1 + 1) * Real.pi) + (1 + 1) * Real.pi)
        = (y - natCast n * ((1 + 1) * Real.pi)) - (1 + 1) * Real.pi := by mach_ring
    rw [e1]
    have hper := Real.sin_periodic (y - natCast n * ((1 + 1) * Real.pi) - (1 + 1) * Real.pi)
    have e2 : y - natCast n * ((1 + 1) * Real.pi) - (1 + 1) * Real.pi + (1 + 1) * Real.pi
        = y - natCast n * ((1 + 1) * Real.pi) := by mach_ring
    rw [e2] at hper
    rw [← hper, ih]

/-- **`sin` is never eventually constant looking backward from any point.** For ANY target `a`
(positive, negative, whatever), two points `≤ a` exist with DIFFERENT `sin` values (`0` and `1`,
shifted arbitrarily far left via `archimedean` + `2π`-periodicity). No restriction on `a` at
all — the key generalization step this file needed past the one concrete instance. -/
theorem sin_two_different_values_le (a : Real) :
    ∃ x1 x2 : Real, x1 ≤ a ∧ x2 ≤ a ∧ Real.sin x1 ≠ Real.sin x2 := by
  obtain ⟨n, hn⟩ := archimedean (Real.pi / (1 + 1) - a)
  have hn0 : (0 : Real) ≤ natCast n := natCast_nonneg n
  have h2pi_ge_one : (1 : Real) ≤ (1 + 1) * Real.pi := by
    have h := mul_le_mul_of_nonneg_left (le_of_lt pi_gt_one) (le_of_lt zero_lt_one_add_one_local)
    have e : (1 + 1) * (1 : Real) = 1 + 1 := mul_one_ax _
    rw [e] at h
    exact le_trans (by
      have h2 := add_le_add_left (le_of_lt zero_lt_one_ax) (1 : Real)
      have e2 : (1 : Real) + 0 = 1 := add_zero _
      rwa [e2] at h2) h
  have hstep : natCast n ≤ natCast n * ((1 + 1) * Real.pi) :=
    le_mul_of_one_le_right hn0 h2pi_ge_one
  have hfinal : Real.pi / (1 + 1) - a < natCast n * ((1 + 1) * Real.pi) :=
    lt_of_lt_of_le hn hstep
  refine ⟨0 - natCast n * ((1 + 1) * Real.pi),
    Real.pi / (1 + 1) - natCast n * ((1 + 1) * Real.pi), ?_, ?_, ?_⟩
  · have h1 : Real.pi / (1 + 1) - natCast n * ((1 + 1) * Real.pi) < a := by
      have h := sub_lt_sub_right_of_lt (r := natCast n * ((1 + 1) * Real.pi)) hfinal
      have e : Real.pi / (1 + 1) - a - natCast n * ((1 + 1) * Real.pi)
          = Real.pi / (1 + 1) - natCast n * ((1 + 1) * Real.pi) - a := by mach_ring
      rw [e] at h
      have e2 : natCast n * ((1 + 1) * Real.pi) - natCast n * ((1 + 1) * Real.pi) = 0 := by
        mach_ring
      rw [e2] at h
      have h2 := add_lt_add_left h a
      have e3 : a + 0 = a := add_zero _
      have e4 : a + (Real.pi / (1 + 1) - natCast n * ((1 + 1) * Real.pi) - a)
          = Real.pi / (1 + 1) - natCast n * ((1 + 1) * Real.pi) := by mach_ring
      rwa [e3, e4] at h2
    have h0le : (0 : Real) - natCast n * ((1 + 1) * Real.pi)
        ≤ Real.pi / (1 + 1) - natCast n * ((1 + 1) * Real.pi) := by
      have hpidiv2pos : 0 < Real.pi / (1 + 1) := div_pos_of_pos_pos pi_pos zero_lt_one_add_one_local
      have h := sub_lt_sub_right_of_lt (r := natCast n * ((1 + 1) * Real.pi)) hpidiv2pos
      exact le_of_lt h
    exact le_trans h0le (le_of_lt h1)
  · have h1 : Real.pi / (1 + 1) - natCast n * ((1 + 1) * Real.pi) < a := by
      have h := sub_lt_sub_right_of_lt (r := natCast n * ((1 + 1) * Real.pi)) hfinal
      have e : Real.pi / (1 + 1) - a - natCast n * ((1 + 1) * Real.pi)
          = Real.pi / (1 + 1) - natCast n * ((1 + 1) * Real.pi) - a := by mach_ring
      rw [e] at h
      have e2 : natCast n * ((1 + 1) * Real.pi) - natCast n * ((1 + 1) * Real.pi) = 0 := by
        mach_ring
      rw [e2] at h
      have h2 := add_lt_add_left h a
      have e3 : a + 0 = a := add_zero _
      have e4 : a + (Real.pi / (1 + 1) - natCast n * ((1 + 1) * Real.pi) - a)
          = Real.pi / (1 + 1) - natCast n * ((1 + 1) * Real.pi) := by mach_ring
      rwa [e3, e4] at h2
    exact le_of_lt h1
  · rw [sin_sub_natCast_mul_two_pi, sin_sub_natCast_mul_two_pi, Real.sin_zero, sin_pi_div_two]
    exact ne_of_lt zero_lt_one_ax

/-- **THE FULL RESULT: the ENTIRE `expWrappedNonMonotonicWitnessC` family closes, for ANY
`c > 1` and ANY `c2`.** Combines the two generalization steps above with the two-equal-points
mechanism. -/
theorem eml_depth2_witness_of_expwrapped_family {c c2 : Real} (hc : 1 < c) {S3 : EMLTree}
    (hsin : ∀ x, (EMLTree.eml (expWrappedNonMonotonicWitnessC c)
      (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 := by
  obtain ⟨x1, x2, hx1, hx2, hsinne⟩ := sin_two_different_values_le (Real.log (Real.log c))
  have heq : (expWrappedNonMonotonicWitnessC c).eval x1
      = (expWrappedNonMonotonicWitnessC c).eval x2 := by
    rw [expWrappedNonMonotonicWitnessC_eval_general, expWrappedNonMonotonicWitnessC_eval_general,
      nonMonotonicWitnessC_eval_clamped_general hc hx1,
      nonMonotonicWitnessC_eval_clamped_general hc hx2]
  exact eml_depth2_witness_of_const_sibling_two_equal_points heq hsinne hsin

end Real
end MachLib
