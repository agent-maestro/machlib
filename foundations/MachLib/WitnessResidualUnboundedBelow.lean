import MachLib.EMLSmoothness
import MachLib.Forge

/-! # Mirror closure: `S2` constant, `c2 > 1`, whenever `T1` is unbounded BELOW

`EMLSmoothness.lean` already closes the "unbounded ABOVE" case for `T1` unconditionally
(`eml_depth2_witness_of_const_sibling_unbounded_T1`, any `c2`): if `S3` collapses to `≤ 0`
everywhere, `exp(T1.eval x) ≤ c2 + 1` for all `x` (via `sin_le_one`), but `T1` taking
arbitrarily large values forces `exp(T1.eval x) > T1.eval x` past all bounds
(`exp_grows_strictly_thm`) — contradiction, no constraint on `c2` needed.

This file proves the MIRROR: if `T1` is unbounded BELOW instead, the same collapse gives
`exp(T1.eval x) ≥ c2 - 1` for all `x` (via `neg_one_le_sin`), but `T1` taking arbitrarily
negative values forces `exp(T1.eval x)` arbitrarily close to `0` (via `exp`'s strict
monotonicity, `Real.exp_lt`, plus `Real.exp_log`) — contradiction, PROVIDED `c2 > 1` so that
`c2 - 1 > 0` and `Real.log (c2 - 1)` is meaningful. This constraint is harmless: the actual
witness-finding residual is already specifically about `c2 > 1` (the `c2 ≤ 1` case closes by
other means), so this mirror covers exactly the sub-case it needs to.

Net effect: combined with the existing theorem, ANY `T1` that is unbounded in EITHER direction
closes for free. The only territory left open is `T1` bounded BOTH above and below — exactly
the territory explored by `WitnessResidualBoundedNonConstant.lean` and
`WitnessResidualNonMonotonic.lean`. -/

namespace MachLib
namespace Real

open EMLTree

/-- **A free witness for `S2` constant, `c2 > 1`, whenever `T1` is unbounded below.** Mirror of
`eml_depth2_witness_of_const_sibling_unbounded_T1`. If `S3` collapsed to `≤ 0` everywhere,
`exp(T1.eval x) = sin x + c2 ≥ c2 - 1` for ALL `x` (via `neg_one_le_sin`) — but picking `x` with
`T1.eval x < log(c2 - 1)` (from unboundedness below, using `c2 > 1`) forces
`exp(T1.eval x) < exp(log(c2-1)) = c2 - 1` (via `exp_lt` + `exp_log`), directly contradicting the
lower bound. Same elementary-growth flavor as the unbounded-above case, no zero-counting. -/
theorem eml_depth2_witness_of_const_sibling_unbounded_below_T1 {T1 S3 : EMLTree} {c2 : Real}
    (hc2 : 1 < c2)
    (hT1unbddBelow : ∀ M : Real, ∃ x, T1.eval x < M)
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
  have hc2m1_pos : 0 < c2 - 1 := sub_pos_of_lt hc2
  obtain ⟨x, hx⟩ := hT1unbddBelow (Real.log (c2 - 1))
  have hexp_lt : Real.exp (T1.eval x) < Real.exp (Real.log (c2 - 1)) := Real.exp_lt hx
  rw [Real.exp_log hc2m1_pos] at hexp_lt
  have hge : c2 - 1 ≤ Real.exp (T1.eval x) := by
    have h2 : -1 ≤ Real.exp (T1.eval x) - c2 := by rw [hcollapse x]; exact neg_one_le_sin x
    have h3 := add_le_add_left h2 c2
    rwa [show c2 + (Real.exp (T1.eval x) - c2) = Real.exp (T1.eval x) from by mach_ring,
         show c2 + (-1 : Real) = c2 - 1 from by mach_ring] at h3
  exact lt_irrefl_ax _ (lt_of_le_of_lt hge hexp_lt)

end Real
end MachLib
