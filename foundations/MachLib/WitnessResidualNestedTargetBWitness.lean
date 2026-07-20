import MachLib.WitnessResidualNestedTargetFamily

/-!
# `∃x0, 0 < B.eval x0`, for the WHOLE nested-target family — generalizing the `1<c2<2` closure

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`).
`WitnessResidualDepth2Elementary.lean`'s `depth2_witness_B_of_c2_between_one_two` closed the
third `EMLWitnesses T1 x0` conjunct (`0 < B.eval x0`, for `T1 = eml A B`) elementarily, but only
for the single target `log(c2+sin x)` with `1 < c2 < 2`. This file asks: what was actually
special about `1 < c2 < 2` that made the elementary "assume `B ≤ 0`, evaluate at `x = -π/2`"
trick work, and does it generalize to the whole nested-target family
(`WitnessResidualNestedTargetFamily.lean`) now that one exists?

**The answer: `-π/2` isn't a coincidence, it's the family's own minimum point.** `sin(-π/2) = -1`
is `sin`'s minimum; `nestedTarget_at_neg_pi_div_two` proves, by the same one-line induction as
`nestedTarget_facts`, that `nestedTarget cs (-π/2) = nestedLo cs` for EVERY well-formed `cs` —
each layer's `log` is monotone, so it carries "achieves the minimum here" through unchanged.
`1 < c2 < 2` was exactly the condition `nestedWF [c2] ∧ nestedLo [c2] < 0` (`nestedLo [c2] =
log(c2-1)`, negative iff `c2 < 2`; `nestedWF [c2]` iff `c2 > 1`) — checked, not assumed, by
computing both sides and confirming they coincide exactly.

**The generalization** (`witness_B_not_le_zero_of_lo_neg`): for ANY well-formed `cs` with
`nestedLo cs < 0`, `T1 = eml A B` satisfying `T1.eval = nestedTarget cs` globally has
`∃x0, 0 < B.eval x0` — the same one-point elementary argument, now valid at every depth the
family reaches, not just the one level checked by hand before. `B` doesn't need to be a constant
here either (unlike `depth2_no_T1_with_const_B_small`) — the argument never used `B`'s shape,
only its SIGN, so it's genuinely more general on that axis too.

**Honest scope**: this closes the THIRD `EMLWitnesses T1 x0` conjunct for the whole family when
`nestedLo cs < 0` (the "target dips below zero" case — `nestedLo cs ≥ 0` needs the deeper
recursive argument sketched in the 2026-07-20 rescoping entry: `A` itself would have to realize
`nestedTarget (0 :: cs)`, which needs `A`'s own validity — the still-open piece). It does NOT
touch `EMLWitnesses A x0`/`EMLWitnesses B x0` themselves.
-/

namespace MachLib

open MachLib.Real

/-- **The nested target hits its own lower bound exactly at `-π/2`.** `sin`'s minimum point
survives every log-shift layer unchanged, since each layer is monotone. Mirrors
`nestedTarget_facts`'s induction shape but is simpler — an equality at ONE point, not a
three-part range/level/witness statement. -/
theorem nestedTarget_at_neg_pi_div_two (cs : List Real) (hwf : nestedWF cs) :
    nestedTarget cs (-(pi / (1 + 1))) = nestedLo cs := by
  induction cs with
  | nil =>
    show Real.sin (-(pi / (1 + 1))) = -1
    rw [Real.sin_neg, Real.sin_pi_div_two]
  | cons c cs' ih =>
    obtain ⟨hwf_c, hwf_cs'⟩ := hwf
    rw [nestedTarget_cons, nestedLo_cons, ih hwf_cs']

/-- **`∃x0, 0 < B.eval x0`, for the whole nested-target family.** Generalizes
`depth2_witness_B_of_c2_between_one_two` (`EMLWitnesses`'s third conjunct, previously closed
only for `log(c2+sin x)` with `1<c2<2`) to every well-formed member of the nested family with
`nestedLo cs < 0`. Same proof shape: assume `B ≤ 0` everywhere (so `log(B.eval x)` clamps to
`0`), forcing `exp(A.eval x) = nestedTarget cs x` for all `x`; at `x = -π/2` this gives
`exp(A.eval(-π/2)) = nestedLo cs < 0`, contradicting `exp > 0`. -/
theorem witness_B_not_le_zero_of_lo_neg
    {A B : EMLTree} {cs : List Real} (hwf : nestedWF cs) (hlo : nestedLo cs < 0)
    (hT1eq : ∀ x, (EMLTree.eml A B).eval x = nestedTarget cs x) :
    ∃ x0, 0 < B.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, B.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (B.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  let x0 : Real := -(pi / (1 + 1))
  have hlog0 : Real.log (B.eval x0) = 0 := Real.log_nonpos (hallle x0)
  have h1 : Real.exp (A.eval x0) - Real.log (B.eval x0) = nestedTarget cs x0 := hT1eq x0
  rw [hlog0, sub_zero] at h1
  rw [nestedTarget_at_neg_pi_div_two cs hwf] at h1
  -- h1 : exp(A.eval x0) = nestedLo cs, contradicting exp positivity via hlo : nestedLo cs < 0
  rw [← h1] at hlo
  exact lt_irrefl_ax 0 (lt_trans_ax (Real.exp_pos _) hlo)

end MachLib
