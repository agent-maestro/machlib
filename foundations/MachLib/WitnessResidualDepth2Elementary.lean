import MachLib.WitnessResidualChainSkeleton

/-!
# One elementary sub-case of `hvalidon_any_b`: `1 < c2 < 2` gives an immediate witness for `T1`'s own right child

Part of the 2026-07-20 continuation of Option D
(`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). `WitnessResidualChainSkeleton.lean` isolated
the whole remaining difficulty into one hypothesis: `∀b>0, EMLPfaffianValidOn T1 0 b`, which
(via `eml_pfaffian_validon_of_witnesses`) needs `EMLWitnesses T1 x0`. For `T1 = eml A B`
(compound, per `WitnessResidualDepth1.lean`'s depth-1 exclusion), `EMLWitnesses T1 x0` needs
THREE things: `EMLWitnesses A x0`, `EMLWitnesses B x0`, and `0 < B.eval x0`.

This file closes the THIRD conjunct elementarily, for `1 < c2 < 2` specifically — by exactly
the same trick that closed the ORIGINAL `S2 ≤ 1` case
(`eml_depth2_witness_of_const_le_one_sibling`, `EMLSmoothness.lean`), one level deeper: assume
`B ≤ 0` everywhere (so `log(B.eval x)` clamps to `0`), forcing `exp(A.eval x) = log(c2+sin x)`
for all `x` — and at `x = -π/2`, `log(c2 + sin(-π/2)) = log(c2 - 1)`, which is NEGATIVE
whenever `0 < c2 - 1 < 1`, i.e. exactly `1 < c2 < 2` — contradicting `exp(A.eval(-π/2)) > 0`.
Same point (`x = -π/2`), same mechanism, one recursion level down.

`c2 ≥ 2` is NOT covered here — there, `log(c2+sin x) ≥ 0` always, no single-point contradiction
of this shape exists (confirmed in the parent decision doc: it recurses into a MORE nested
target, `log(log(c2+sin x))`, needing the fuller induction). This file only closes the `1<c2<2`
slice, honestly.
-/

namespace MachLib
namespace Real

/-- **`1 < c2 < 2`: `T1`'s own right child `B` has an immediate witness.** If
`T1 = eml A B` satisfies `T1.eval x = log(c2+sin x)` globally and `1 < c2 < 2`, then `B` is not
`≤ 0` everywhere — `B` has a point where it's strictly positive, one of the three conjuncts
`EMLWitnesses T1 x0` needs. -/
theorem depth2_witness_B_of_c2_between_one_two
    {A B : EMLTree} {c2 : Real} (hc2lo : 1 < c2) (hc2hi : c2 < 1 + 1)
    (hT1eq : ∀ x, (EMLTree.eml A B).eval x = Real.log (c2 + Real.sin x)) :
    ∃ x0, 0 < B.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, B.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (B.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  let x0 : Real := -(pi / (1 + 1))
  have hsinx0 : Real.sin x0 = -1 := by
    show Real.sin (-(pi / (1 + 1))) = -1
    rw [Real.sin_neg, Real.sin_pi_div_two]
  have hlog0 : Real.log (B.eval x0) = 0 := Real.log_nonpos (hallle x0)
  have h1 : Real.exp (A.eval x0) - Real.log (B.eval x0) = Real.log (c2 + Real.sin x0) :=
    hT1eq x0
  rw [hlog0, sub_zero, hsinx0] at h1
  -- h1 : exp(A.eval x0) = log(c2 + (-1))
  have hrw : c2 + (-1 : Real) = c2 - 1 := by mach_ring
  rw [hrw] at h1
  -- h1 : exp(A.eval x0) = log(c2 - 1)
  have hc2m1_pos : (0 : Real) < c2 - 1 := by
    have h01 : (0 : Real) + 1 = 1 := by mach_ring
    exact lt_sub_of_add_lt (by rw [h01]; exact hc2lo)
  have hc2m1_lt1 : c2 - 1 < 1 := by
    have h := add_lt_add_left hc2hi (-1)
    have e1 : (-1 : Real) + c2 = c2 - 1 := by mach_ring
    have e2 : (-1 : Real) + (1 + 1) = 1 := by mach_ring
    rwa [e1, e2] at h
  have hlogneg : Real.log (c2 - 1) < 0 := log_neg_of_lt_one hc2m1_pos hc2m1_lt1
  rw [← h1] at hlogneg
  -- hlogneg : exp(A.eval x0) < 0, contradicting exp positivity
  exact lt_irrefl_ax 0 (lt_trans_ax (Real.exp_pos _) hlogneg)

end Real
end MachLib
