import MachLib.WitnessResidualExpWrappedNonMonotonicCPositive
import MachLib.Linarith

/-! # CORRECTION: `expWrappedNonMonotonicWitnessC concreteC` closes after all — via a much
simpler mechanism the last two rounds didn't try

`WitnessResidualExpWrappedNonMonotonicCPositive.lean` established, with real care, that
`expWrappedNonMonotonicWitnessC concreteC` is a genuine member of the residual's open
classification AND resistant to the `EMLPfaffianValidOn`-based closure route. That framing was
accurate as far as it went — but "resistant to ONE technique" is not "unclosable", and this file
shows the tree closes anyway, via a technique simpler than everything else built this session.

**The idea.** Every closure built so far in this arc — unbounded above/below, strictly monotonic,
the crossing-family closures — works by deriving a contradiction from GLOBAL properties of `T1`
(growth, monotonicity everywhere). This file uses something much more local: `T1` is CONSTANT on
its whole clamped region (`eval x = K` for every `x ≤ x0`, not just bounded there). If `sin`
takes two DIFFERENT values at any two points inside that region, the collapsed equation
(`exp(T1.eval x) - c2 = sin x`) forces those two different `sin` values to be EQUAL (since `T1`'s
own output doesn't distinguish the two points) — an immediate contradiction, needing nothing
about `T1` beyond agreement at those two points. No monotonicity, no boundedness, no `c2 > 1`
even (the general lemma doesn't need it at all — checked, `c2`'s sign never enters the proof).

**Why this was missed for two rounds**: every prior closure attempt implicitly reached for a
GLOBAL argument (matching the "family" pattern already built), when the tree's own clamped
region — literally the source of "resistant to `EMLPfaffianValidOn`" two rounds ago — was ALSO
exactly the feature that makes this simpler argument work. The crossing sitting at `x0 = 1 ≥ 0`
meant `0` and `-π/2` (both trivially `≤ x0`) already have different `sin` values (`0` and `-1`),
closing it in a handful of lines.

**Honest correction to the record.** `expWrappedNonMonotonicWitnessC concreteC` is NOT a genuine
obstruction to witness-finding — it closes cleanly, just not via the technique the last two
rounds happened to try first. The residual's open classification remaining non-empty (cont. 19)
still stands as a fact about the CLASSIFICATION (bounded+non-constant+non-simple+non-monotonic
trees exist) — but no tree has yet been found that survives ALL available techniques, including
this new one. Whether this new mechanism generalizes to close the WHOLE classification (it needs
two points inside a region where `T1` doesn't distinguish sin's values — plausible for any
"clamped-on-a-ray" tree, not yet checked for the general case) is the natural next question, not
attempted here. -/

namespace MachLib
namespace Real

open EMLTree

theorem sin_neg_pi_div_two : Real.sin (-(Real.pi / (1 + 1))) = -1 := by
  rw [Real.sin_neg, sin_pi_div_two]

/-- **The general mechanism.** If `T1` takes the SAME value at two points where `sin` DIFFERS,
`T1` cannot satisfy the collapsed witness-finding equation — for ANY `c2` (the sign/size of `c2`
never enters the proof at all, unlike every other closure in this family). -/
theorem eml_depth2_witness_of_const_sibling_two_equal_points {T1 S3 : EMLTree} {c2 : Real}
    {x1 x2 : Real} (heq : T1.eval x1 = T1.eval x2)
    (hsinne : Real.sin x1 ≠ Real.sin x2)
    (hsin : ∀ x, (EMLTree.eml T1 (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, S3.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (S3.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hcollapse : ∀ x, Real.exp (T1.eval x) - c2 = Real.sin x := by
    intro x
    have hlog0 : Real.log (S3.eval x) = 0 := Real.log_nonpos (hallle x)
    have hNeval : (EMLTree.eml (EMLTree.const c2) S3).eval x = Real.exp c2 := by
      show Real.exp c2 - Real.log (S3.eval x) = Real.exp c2
      rw [hlog0, sub_zero]
    have h1 : Real.exp (T1.eval x) -
        Real.log ((EMLTree.eml (EMLTree.const c2) S3).eval x) = Real.sin x := hsin x
    rwa [hNeval, Real.log_exp] at h1
  have h1 := hcollapse x1
  have h2 := hcollapse x2
  rw [heq] at h1
  have heqsin : Real.sin x1 = Real.sin x2 := by rw [← h1, ← h2]
  exact hsinne heqsin

/-- **The correction, made concrete.** `expWrappedNonMonotonicWitnessC concreteC` closes for ANY
`c2`, using `x1 := 0` and `x2 := -π/2` — both inside the clamped region (`x0 = 1 ≥ 0`, so both
`0 ≤ 1` and `-π/2 < 0 ≤ 1` hold trivially, no numeric bound-chasing needed), where `sin` takes
values `0` and `-1` respectively. -/
theorem concreteC_closes_via_two_points {S3 : EMLTree} {c2 : Real}
    (hsin : ∀ x, (EMLTree.eml (expWrappedNonMonotonicWitnessC concreteC)
      (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 := by
  have hx0nonneg : (0 : Real) ≤ Real.log (Real.log concreteC) := by
    rw [concreteC_x0_eq_one]; exact le_of_lt zero_lt_one_ax
  have hnegpidiv2_le : -(Real.pi / (1 + 1)) ≤ Real.log (Real.log concreteC) := by
    have hpipos := pi_pos
    have hdivpos : 0 < Real.pi / (1 + 1) := div_pos_of_pos_pos hpipos zero_lt_one_add_one
    have h1 : -(Real.pi / (1 + 1)) < 0 := neg_neg_of_pos hdivpos
    exact le_trans (le_of_lt h1) hx0nonneg
  have h0eq : (expWrappedNonMonotonicWitnessC concreteC).eval 0 = 1 := by
    rw [expWrappedNonMonotonicWitnessC_eval, nonMonotonicWitnessC_eval_clamped hx0nonneg,
      Real.exp_zero]
  have hnegeq : (expWrappedNonMonotonicWitnessC concreteC).eval (-(Real.pi / (1 + 1))) = 1 := by
    rw [expWrappedNonMonotonicWitnessC_eval,
      nonMonotonicWitnessC_eval_clamped hnegpidiv2_le, Real.exp_zero]
  have heq : (expWrappedNonMonotonicWitnessC concreteC).eval 0
      = (expWrappedNonMonotonicWitnessC concreteC).eval (-(Real.pi / (1 + 1))) := by
    rw [h0eq, hnegeq]
  have hsinne : Real.sin 0 ≠ Real.sin (-(Real.pi / (1 + 1))) := by
    rw [Real.sin_zero, sin_neg_pi_div_two]
    intro h
    exact absurd h (ne_of_gt (neg_neg_of_pos zero_lt_one_ax))
  exact eml_depth2_witness_of_const_sibling_two_equal_points heq hsinne hsin

end Real
end MachLib
