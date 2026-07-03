import MachLib.IterExpDepthNPhantomDescent

/-!
# Phase C→D absorption — the syntactic nested measure `synMeasure` (∀N)

The deep `¬hnzTower` case needs a measure that a *phantom-trim* (eval-preserving) can strictly lower — which
`chainNMeasureEI` (eval-invariant) cannot. `synMeasure` is the syntactic analog: a nested tuple of the
syntactic `degreeY` at each tower level. A phantom leading term at level `j` drops its `degreeY` while an
eval-preserving trim leaves `chainNMeasureEI` fixed — so appending `synMeasure` to the measure lets the deep
case descend. Well-founded from the backbone `nestedOrder_wf`. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly

/-- The **syntactic nested degree measure**: the syntactic top `y`-degree, then recurse on the dropped
leading coefficient. Mirrors `chainNMeasureEI`'s recursion but uses raw `degreeY`/`leadingCoeffY` (not the
canonical `cdegYAt`/`canonLcYAt`), so it is NOT eval-invariant — which is exactly what lets a phantom-trim
lower it. -/
noncomputable def synMeasure : (k : Nat) → MultiPoly (k + 2) → NestedNat (k + 2)
  | 0 => fun q => (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q, (0, 0))
  | k + 1 => fun q =>
      (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q,
       synMeasure k (MultiPoly.dropLastY
         (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)))

/-- The syntactic order: `nestedOrder (k+2)` pulled back along `synMeasure`. -/
def synOrder (k : Nat) : MultiPoly (k + 2) → MultiPoly (k + 2) → Prop :=
  InvImage (nestedOrder (k + 2)) (synMeasure k)

/-- **Well-founded** — from the depth-generic backbone `nestedOrder_wf` via `InvImage`. -/
theorem synOrder_wf (k : Nat) : WellFounded (synOrder k) :=
  InvImage.wf (synMeasure k) (nestedOrder_wf (k + 2))

end MachLib.IterExpDepthN
