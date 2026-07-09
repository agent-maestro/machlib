import MachLib.IterExpDepthNRankRec5p
import MachLib.IterExpDepthNBudgetMono
import MachLib.IterExpDepthNTrimQDegHelpers

/-!
# Chain-N explicit bound — the M5⁺ budget `budgetN5` and general inner-boundedness

`budgetN5 m B q` is the outer WF wrap's per-poly reduce-count budget: `invPhiG (descentBound (m+2))` over
`degreeY_top q` (level) and `rankRec` of the inner `chainNMeasureEI` (inner rank), with leaf bound `0`. The
outer invariant is `zeros(q) ≤ budgetN5 m B q + Ndep (B + budgetN5 m B q)` (the `+Ndep` is the depth-below
leaf). This file also gives the general inner-boundedness (`chainNMeasureEI` of `dropLastY(lcY_top r)` fits
under `allBNested B` when `r`'s degrees are `≤ B`) — the boundedness the trim/leaf/reduce arms feed to
`rankRec_lt`.
-/

namespace MachLib.IterExpDepthN

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.ExplicitBound
open MachLib.IterExpDepthNReduce

/-- The M5⁺ reduce-count budget. -/
noncomputable def budgetN5 (m B : Nat) (q : MultiPoly (m + 3)) : Nat :=
  invPhiG (descentBound (m + 2)) 0 (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) q)
    (rankRec (m + 2) B (chainNMeasureEI m (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) q)))) B

/-- **General inner boundedness.** If `r`'s degrees are `≤ B` (`degreeX r + 2 ≤ B`, all `degreeY ≤ B`), then
`chainNMeasureEI m (dropLastY(lcY_top r))` fits under the all-`B` bound vector. -/
theorem chainNMeasureEI_inner_le_allB (m : Nat) (r : MultiPoly (m + 3)) (B : Nat)
    (hrx : MultiPoly.degreeX r + 2 ≤ B) (hry : ∀ i : Fin (m + 3), MultiPoly.degreeY i r ≤ B) :
    nestedLe (m + 2) (chainNMeasureEI m (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) r))) (allBNested (m + 2) B) := by
  refine chainNMeasureEI_le_allB m (MultiPoly.dropLastY
    (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) r)) B ?_ ?_
  · have := degreeX_inner_le m r; omega
  · intro i
    exact Nat.le_trans (degreeY_inner_le m r i) (hry (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 3)))

/-- The inner rank of `dropLastY(lcY_top r)` is `< descentBound (m+2) B` when `r`'s degrees are `≤ B` — the
`ir' ≤ cap B'` hypothesis of `invPhiG_trim_any`. -/
theorem rankRec_inner_lt (m : Nat) (r : MultiPoly (m + 3)) (B : Nat)
    (hrx : MultiPoly.degreeX r + 2 ≤ B) (hry : ∀ i : Fin (m + 3), MultiPoly.degreeY i r ≤ B) :
    rankRec (m + 2) B (chainNMeasureEI m (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) r))) < descentBound (m + 2) B :=
  rankRec_lt_descentBound (m + 2) B _ (chainNMeasureEI_inner_le_allB m r B hrx hry)

end MachLib.IterExpDepthN
