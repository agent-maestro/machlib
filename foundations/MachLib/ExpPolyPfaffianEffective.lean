import MachLib.ExpPolyBridge
import MachLib.ExpPolyEffectiveBound

/-!
# The crux, wired through the ExpPoly → PfaffianFn bridge (full generality)

`ExpPolyBridge` connects the constructive `ExpPoly` track to the abstract `PfaffianFn` track
(`ExpPoly.toPfaffianFn`, `ExpPoly.eval_toPfaffianFn`), but its end-to-end zero-count wire-through
(`PfaffianFn_singleExp_length_one_bound`) was **length-1 only** — a proof-of-concept using the trivial
`length_one_full_bound` (a single-coefficient `ExpPoly` is just a polynomial).

With `expPoly_effective_bound` now proved (the general single-exp Khovanskii bound, no propagation
hypotheses), that wire-through generalises to **arbitrary length**: the single-exp Pfaffian function
`ExpPoly.toPfaffianFn ep` has `≤ length + ΣsimplifiedDeg` zeros for *any* `ep`. This closes the gap the
length-1 demo left open — the full connection between the two tracks — and carries the crux's
`rolle_ct`-only footprint straight into the `PfaffianFn` framework.
-/

namespace MachLib.ExpPolyBridge

open MachLib.SingleExpKhovanskii
open MachLib.SingleExpKhovanskii.ExpPoly

/-- **General single-exp Pfaffian zero bound via the bridge.** For any `ExpPoly ep` non-vanishing
somewhere on `(a,b)`, the bridge Pfaffian function `ExpPoly.toPfaffianFn ep` has at most
`length + ΣsimplifiedDeg` zeros on `(a,b)` — the crux `expPoly_effective_bound` transported through
`ExpPoly.eval_toPfaffianFn`, at full generality (not just length 1). -/
theorem PfaffianFn_singleExp_effective_bound
    (ep : ExpPoly) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, a < x ∧ x < b ∧ (ExpPoly.toPfaffianFn ep).eval x ≠ 0) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (ExpPoly.toPfaffianFn ep).eval z = 0) →
      zeros.length ≤ ep.coeffs.length + sumSimplifiedDegrees ep.coeffs := by
  intro zeros hnodup hzeros
  have hne_ep : ∃ x : Real, a < x ∧ x < b ∧ ep.eval x ≠ 0 := by
    obtain ⟨x, hax, hxb, hx⟩ := hne
    exact ⟨x, hax, hxb, by rw [← ExpPoly.eval_toPfaffianFn ep x]; exact hx⟩
  have hzeros_ep : ∀ z ∈ zeros, a < z ∧ z < b ∧ ep.eval z = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hf⟩ := hzeros z hz
    exact ⟨haz, hzb, by rw [← ExpPoly.eval_toPfaffianFn ep z]; exact hf⟩
  exact expPoly_effective_bound ep a b hab hne_ep zeros hnodup hzeros_ep

end MachLib.ExpPolyBridge
