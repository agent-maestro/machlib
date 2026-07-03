import MachLib.IterExpDepthNAbsorbedDescent
import MachLib.IterExpDepthNCapstone

/-!
# Phase C→D absorption — the `hnz` reduce descent on `M5` (∀N)

The absorbed descent `chainNReduce_descends_hnz` lifted to the top-level canonical and augmented measures,
mirroring `chainNReduce_orderCanon` / `chainNReduce_order5` but needing only `hnzTower` (not full `Reducing`).
This is the form the WF assembly's reduce arm dispatches to once it establishes `hnzTower`. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.IterExpDepthNReduce
open MachLib.ChainExp2Trim
open MachLib.IterExpDepth3CdegY1

/-- **The top-level reduce descent from `hnz`.** Mirror of `chainNReduce_orderCanon` fed by the absorbed
descent `chainNReduce_descends_hnz`, so it needs only `hnzTower M (dropLastY(lcY_top p))`. -/
theorem chainNReduce_orderCanon_hnz (M : Nat) (p : MultiPoly (M + 3))
    (hnz : hnzTower M (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) :
    chainNOrderCanon M (chainNReduce (M + 1) (fullMult (M + 1) p) p) p := by
  have key := chainNReduce_syntactic_descent M (⟨M + 2, by omega⟩ : Fin (M + 3)) rfl
    (liftLastY (fullMult M (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)))) p
    (degreeY_top_liftLastY _)
    (by rw [dropLastY_liftLastY]
        exact chainNReduce_descends_hnz M
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)) hnz)
  show nestedOrder (M + 3)
      (chainNMeasureCanon M (chainNReduce (M + 1) (fullMult (M + 1) p) p))
      (chainNMeasureCanon M p)
  simp only [chainNMeasureCanon, fullMult]
  exact key

/-- The `hnz` reduce descent lifts to `M5` (drops the first component). -/
theorem chainNReduce_order5_hnz (M : Nat) (p : MultiPoly (M + 3))
    (hnz : hnzTower M (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) :
    chainNOrder5 M (chainNReduce (M + 1) (fullMult (M + 1) p) p) p :=
  lexProd_of_fst (chainNReduce_orderCanon_hnz M p hnz)

end MachLib.IterExpDepthN
