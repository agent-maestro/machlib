import MachLib.IterExpDepthNSynMeasure
import MachLib.IterExpDepthNMeasureCanon

/-!
# Phase C→D absorption — the augmented measure `M5⁺` (∀N)

The final measure the WF assembly descends. `M5` (`chainNMeasureCanon`, `degreeY_{top-1}`) cannot descend the
deep `¬hnzTower` case (the eval-invariant `chainNMeasureCanon` is stuck, and only a phantom-trim helps there —
which drops `synMeasure`, not `chainNMeasureCanon`). `M5⁺` replaces the single `degreeY_{top-1}` tiebreaker by
the *full* syntactic nested measure `synMeasure` of the inner `q := dropLastY(lcY_top p)`:

`chainNMeasure5p m p = (chainNMeasureCanon m p, synMeasure m (dropLastY (lcY_top p)))`

* the reduce and `degreeY_top`-trim drop the FIRST component (`chainNMeasureCanon`);
* the deep phantom-trim TIES the first (eval-invariant + top-degree preserved) and drops the second
  (`synMeasure`) — the descent `establish_hnz_or_trim` provides.

Well-founded from `lexProd` of the two backbone orders. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod

/-- The augmented depth-`(m+3)` measure: the canonical measure paired with the syntactic nested measure of the
inner `q := dropLastY(lcY_top p)`. -/
noncomputable def chainNMeasure5p (m : Nat) (p : MultiPoly (m + 3)) :
    NestedNat (m + 3) × NestedNat (m + 2) :=
  (chainNMeasureCanon m p,
   synMeasure m (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)))

/-- The augmented order — `lexProd` of the backbone order on `chainNMeasureCanon` and the syntactic order on
`synMeasure`. -/
def chainNOrder5p (m : Nat) : MultiPoly (m + 3) → MultiPoly (m + 3) → Prop :=
  InvImage (LexProd.lexProd (nestedOrder (m + 3)) (nestedOrder (m + 2))) (chainNMeasure5p m)

/-- **Well-founded** — `lexProd` of the two backbone well-founded orders. -/
theorem chainNOrder5p_wf (m : Nat) : WellFounded (chainNOrder5p m) :=
  InvImage.wf (chainNMeasure5p m)
    (LexProd.lexProd_wf (nestedOrder_wf (m + 3)) (nestedOrder_wf (m + 2)))

end MachLib.IterExpDepthN
