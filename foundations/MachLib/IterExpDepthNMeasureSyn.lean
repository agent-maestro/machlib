import MachLib.IterExpDepthNMeasureEI
import MachLib.IterExpDepthNCanonBridge

/-!
# Phase C, brick 2 — the eval-invariant measure equals its syntactic form on the non-phantom branch (∀N)

The reduce-descent `D(k)` splits on whether the reduce result's top `y`-coefficient is phantom. On the
**non-phantom** branch the eval-invariant measure `chainNMeasureEI` coincides with its *syntactic* form —
canonical top-degree becomes the syntactic `degreeY`, and the canonical leading coefficient can be swapped
for the syntactic `leadingCoeffY` (they are eval-equal there, and the inner measure is eval-invariant). This
is exactly what lets `D(k)` reduce to the syntactic descent `S(k)`.

`chainNMeasureEI_eq_syntactic_of_nonphantom` — the depth-generic analog of
`chain2MeasureCanonEvalInv_eq_chain2MeasureCanon_of_nonphantom`, stated inline (the syntactic form is the
RHS pair), built from Phase C brick 1 + Phase B's eval-invariance and `dropLastY_eval_eq_of_topfree`.
No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly

/-- **Non-phantom ⇒ eval-invariant measure = syntactic measure.** For `q : MultiPoly (j+3)` whose top
`y`-coefficient is non-phantom, `chainNMeasureEI (j+1) q` equals the pair (syntactic top-degree, inner
measure of the syntactic leading coefficient projected down). The canonical outer becomes syntactic by
`cdegYAt_eq_degreeYAt_of_top`; the inner is unchanged because the canonical and syntactic leading
coefficients are eval-equal (`canonLcYAt_eval_eq_leadingCoeffY_of_nonphantom`), `dropLastY` preserves that,
and `chainNMeasureEI j` is eval-invariant. -/
theorem chainNMeasureEI_eq_syntactic_of_nonphantom (j : Nat) (q : MultiPoly (j + 3))
    (hnp : canonZeroB (ytopAt (⟨j + 2, by omega⟩ : Fin (j + 3)) q) = false) :
    chainNMeasureEI (j + 1) q
      = (MultiPoly.degreeY (⟨j + 2, by omega⟩ : Fin (j + 3)) q,
         chainNMeasureEI j (MultiPoly.dropLastY
           (MultiPoly.leadingCoeffY (⟨j + 2, by omega⟩ : Fin (j + 3)) q))) := by
  simp only [chainNMeasureEI]
  rw [cdegYAt_eq_degreeYAt_of_top (⟨j + 2, by omega⟩ : Fin (j + 3)) q hnp]
  congr 1
  apply chainNMeasureEI_eq_of_eval_eq j
  apply dropLastY_eval_eq_of_topfree
  · exact canonLcYAt_degreeY_zero (⟨j + 2, by omega⟩ : Fin (j + 3)) q
  · exact degreeY_leadingCoeffY (⟨j + 2, by omega⟩ : Fin (j + 3)) q
  · exact fun x env => canonLcYAt_eval_eq_leadingCoeffY_of_nonphantom
      (⟨j + 2, by omega⟩ : Fin (j + 3)) q hnp x env

end MachLib.IterExpDepthN
