import MachLib.IterExpDepthNRankRecDrop
import MachLib.IterExpDepthNEIrank
import MachLib.IterExpDepthNDescentInduction

/-!
# Chain-N explicit bound — `rankRec` drops on the ACTUAL reduce (connecting to `chainNMeasureEI`)

Instantiates the abstract `rankRec_drop` at the real measure: for a `Reducing m q`, the reduce's
`chainNMeasureEI` measure drops in `nestedOrder` (`chainNReduce_descends`), the reduced poly stays bounded
(`chainNMeasureEI_le_allB`, degreeX non-increasing + degreeY `≤ +1`/reduce — the step-2 towers), so `rankRec`
drops by ≥ 1. This is the `ir`-drop the outer `invPhiG(degreeY_top)` recursion consumes on the reduce arm.
-/

namespace MachLib.IterExpDepthN

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.IterExpDepthNReduce

/-- **`rankRec` of the reduce drops by ≥ 1**, at the bound grown by 1. For a `Reducing m q` with `q`'s
degrees bounded by `B`, `rankRec (m+2) (B+1) (chainNMeasureEI m (reduce)) + 1 ≤ rankRec (m+2) B
(chainNMeasureEI m q)`. Direct instantiation of `rankRec_drop`: the `nestedOrder` drop from
`chainNReduce_descends`, boundedness from `chainNMeasureEI_le_allB`, growth `≤ +1` from the reduce towers. -/
theorem rankRec_reduce_drop (m : Nat) (q : MultiPoly (m + 2)) (hred : Reducing m q) (B : Nat)
    (hqx : MultiPoly.degreeX q + 2 ≤ B) (hqy : ∀ i : Fin (m + 2), MultiPoly.degreeY i q ≤ B) :
    rankRec (m + 2) (B + 1) (chainNMeasureEI m (chainNReduce m (fullMult m q) q)) + 1
      ≤ rankRec (m + 2) B (chainNMeasureEI m q) := by
  refine rankRec_drop (m + 2) B (B + 1) (chainNMeasureEI m q)
    (chainNMeasureEI m (chainNReduce m (fullMult m q) q)) (Nat.le_refl _) ?_
    (chainNReduce_descends m q hred)
  refine chainNMeasureEI_le_allB m (chainNReduce m (fullMult m q) q) (B + 1) ?_ ?_
  · have hx := degreeX_chainNReduce_fullMult_le m q
    omega
  · intro i
    have hy := degreeY_chainNReduce_fullMult_growth_le m q i
    have hb := hqy i
    omega

end MachLib.IterExpDepthN
