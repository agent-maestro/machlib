import MachLib.EMLDepthTameness

/-!
# `log` of a depth-≤2 tree has a floor WITHOUT a positivity hypothesis

`depth_le_two_decay_on_ray` (`EMLDepthTameness:2214`) already bounds `−log (t.eval x)` by
`C + log x` — a **logarithmic** ceiling, sharper than anything below — but only *given*
`0 < t.eval x`. This file removes that hypothesis and nothing else.

The removal is the whole content, and it is what the ladder consumes: the depth-1 analogue
`depth_le_one_log_lower_at_infinity` is unconditional, because a right child may oscillate in sign
and the rung must still bound its `log`. On the non-positive stretches MachLib's totalisation gives
`log b = 0`, which sits *above* any floor, so those points are free — the conditional lemma supplies
the rest.

## Correction, 2026-09-03

An earlier version of this file proved the same statement from scratch in ~60 lines with a much
weaker **exponential** floor `−(Cl + exp x)`, and a companion file proved
`depth_le_two_log_le_linear` — which was a **verbatim duplicate** of the existing
`depth_le_two_log_le_exp` (`EMLDepthTameness:3222`) and has been deleted.

Both mistakes had one cause: absence was checked by **name pattern**, extrapolated from depth 1
(`log_le_linear`, `log_lower_at_infinity`). This corpus names lemmas after the *shape of the bound*,
so the depth-2 versions are called `log_le_exp` and `decay_on_ray`. A search that cannot match its
target is not evidence of absence — which is what `tools/absence_audit.py` exists to enforce, and it
was not run. Search by STATEMENT here, not by name.
-/

namespace MachLib

open Real

/-- **The unconditional depth-≤2 log floor.** `depth_le_two_decay_on_ray` with its positivity
hypothesis discharged by the totalisation, at the same logarithmic height. -/
theorem depth_le_two_log_lower_at_infinity (B : EMLTree) (hB : B.depth ≤ 2) :
    ∃ Cl X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → -(Cl + log x) ≤ log (B.eval x) := by
  obtain ⟨C, X₀, hX₀, h⟩ := depth_le_two_decay_on_ray B hB
  have hmax : C ≤ max C 0 := le_max_left _ _
  have hmax0 : (0 : Real) ≤ max C 0 := le_max_right _ _
  refine ⟨max C 0, X₀, hX₀, fun x hx => ?_⟩
  have hx1 : (1 : Real) ≤ x := le_trans hX₀ hx
  have hlogx : (0 : Real) ≤ log x := by
    have hm := log_le_log zero_lt_one_ax hx1
    rw [log_one] at hm; exact hm
  have hsum : (0 : Real) ≤ max C 0 + log x := by
    have u := add_le_add_wit hmax0 hlogx
    have e : (0 : Real) + 0 = 0 := by mach_ring
    rw [e] at u; exact u
  have hnonpos : -(max C 0 + log x) ≤ 0 := by
    have w := neg_le_neg_wit hsum
    have e : -(0 : Real) = 0 := by mach_ring
    rw [e] at w; exact w
  rcases lt_total 0 (B.eval x) with hv | hv | hv
  · -- positive: the conditional lemma applies verbatim
    have hb := h x hx hv
    have hb' : -log (B.eval x) ≤ max C 0 + log x :=
      le_trans hb (add_le_add_wit hmax (le_refl (log x)))
    have w := neg_le_neg_wit hb'
    have e : - -log (B.eval x) = log (B.eval x) := by mach_ring
    rw [e] at w; exact w
  · rw [← hv, log_nonpos (le_refl 0)]; exact hnonpos
  · rw [log_nonpos (le_of_lt hv)]; exact hnonpos

end MachLib
