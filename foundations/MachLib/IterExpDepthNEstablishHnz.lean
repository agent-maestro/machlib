import MachLib.IterExpDepthNSynMeasure
import MachLib.IterExpDepthNAssembly

/-!
# Phase C→D absorption — `synMeasure` invariant under a `y`-free factor (helper for the deep trim)

`synMeasure_mul_yfree` — multiplying by a polynomial with all `degreeY_j = 0` leaves `synMeasure` unchanged.
This is what lets the deep-trim's `reconstructY`-based lift descend cleanly: the reconstructed leading
coefficient carries a `y`-free power-unit factor (`leadingCoeffY (yᵢ^D)`), which `synMeasure` (a tuple of raw
`degreeY`s) ignores. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.ChainExp2NoZeros

/-- **`synMeasure` ignores a `y`-free factor.** If `c` has `degreeY_j = 0` for every `j`, then
`synMeasure k (q * c) = synMeasure k q`. Induction on depth: raw `degreeY` is additive and `c` contributes
`0` at each level; the leading coefficient of `q * c` is `lcY q * c` (as `c` is its own leading coefficient),
and `dropLastY c` stays `y`-free, so the tail recurses. -/
theorem synMeasure_mul_yfree : ∀ (k : Nat) (q c : MultiPoly (k + 2)),
    (∀ (j : Fin (k + 2)), MultiPoly.degreeY j c = 0) →
    synMeasure k (MultiPoly.mul q c) = synMeasure k q := by
  intro k
  induction k with
  | zero =>
    intro q c hc
    show (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.mul q c), ((0 : Nat), (0 : Nat)))
        = (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q, (0, 0))
    have : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.mul q c)
        = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q := by
      show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) c
        = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q
      rw [hc (⟨1, by omega⟩ : Fin 2), Nat.add_zero]
    rw [this]
  | succ k ih =>
    intro q c hc
    show (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) (MultiPoly.mul q c),
          synMeasure k (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3))
            (MultiPoly.mul q c))))
        = (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q,
           synMeasure k (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)))
    have hdeg : MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) (MultiPoly.mul q c)
        = MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q := by
      show MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q
          + MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) c
        = MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q
      rw [hc (⟨k + 2, by omega⟩ : Fin (k + 3)), Nat.add_zero]
    have hlceq : MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) (MultiPoly.mul q c)
        = MultiPoly.mul (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q) c := by
      show MultiPoly.mul (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)
            (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) c)
        = MultiPoly.mul (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q) c
      rw [leadingCoeffY_eq_self_of_degreeY_zero (⟨k + 2, by omega⟩ : Fin (k + 3)) c
            (hc (⟨k + 2, by omega⟩ : Fin (k + 3)))]
    have hdc : ∀ (j : Fin (k + 2)), MultiPoly.degreeY j (MultiPoly.dropLastY c) = 0 := by
      intro j
      rw [degreeY_dropLastY_eq_prev (k + 2) (⟨j.val, by omega⟩ : Fin (k + 3)) j rfl c]
      exact hc (⟨j.val, by omega⟩ : Fin (k + 3))
    rw [hdeg, hlceq]
    show (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q,
          synMeasure k (MultiPoly.mul (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) (MultiPoly.dropLastY c)))
        = (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q,
           synMeasure k (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)))
    rw [ih _ (MultiPoly.dropLastY c) hdc]

end MachLib.IterExpDepthN
