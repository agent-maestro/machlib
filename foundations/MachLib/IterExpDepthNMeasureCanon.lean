import MachLib.IterExpDepthNMeasureEI

/-!
# Phase D (D3 step ii) — the top-level WF measure `chainNMeasureCanon`

The measure the outer WF induction descends. For a depth-`(m+3)` polynomial:

`chainNMeasureCanon m p = (degreeY_top p, chainNMeasureEI m (dropLastY (leadingCoeffY_top p)))`

— the **syntactic** top-`y`-degree (so the degree-trim arm can lower it) paired with the eval-invariant
inner measure on the dropped leading coefficient (whose descent the reduce arm rides). Its order is
`nestedOrder (m+3)` pulled back along the measure; well-founded from the backbone `nestedOrder_wf`.
This is the ∀N analog of `chain3MeasureCanon`. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod

/-- The top-level canonical measure of a depth-`(m+3)` polynomial: syntactic top degree, then the
eval-invariant measure of the dropped leading coefficient. -/
noncomputable def chainNMeasureCanon (m : Nat) (p : MultiPoly (m + 3)) : NestedNat (m + 3) :=
  (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p,
   chainNMeasureEI m (MultiPoly.dropLastY
     (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)))

/-- The top-level canonical order: `nestedOrder (m+3)` pulled back along `chainNMeasureCanon`. -/
def chainNOrderCanon (m : Nat) : MultiPoly (m + 3) → MultiPoly (m + 3) → Prop :=
  InvImage (nestedOrder (m + 3)) (chainNMeasureCanon m)

/-- **Well-founded** — directly from the depth-generic backbone `nestedOrder_wf` via `InvImage`. -/
theorem chainNOrderCanon_wf (m : Nat) : WellFounded (chainNOrderCanon m) :=
  InvImage.wf (chainNMeasureCanon m) (nestedOrder_wf (m + 3))

end MachLib.IterExpDepthN
