import MachLib.IterExpDepthNRankRecReduce
import MachLib.IterExpDepthNReduceOrder5Hnz
import MachLib.ChainExp2ExplicitABound

/-!
# Chain-N explicit bound — the M5⁺-level reduce drop of `rankRec` (outer-wrap plumbing)

The M5⁺ reduce (on `p : MultiPoly (m+3)`) ties the OUTER `degreeY_top` (`chainNReduce_fst_preserved`) and
drops `chainNMeasureEI m (dropLastY(lcY_top ·))` — the inner whose `rankRec` is the outer `invPhiG`'s `ir`.
This file extracts that `chainNMeasureEI` drop from `chainNReduce_orderCanon_hnz` (via the `degreeY_top` tie)
and feeds it to `rankRec_drop`, giving the `ir`-drop the outer reduce arm consumes.
-/

namespace MachLib.IterExpDepthN

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.IterExpDepthNReduce
open MachLib.ChainExp2Explicit

/-- From a `nestedOrder (n+1)` step whose top components are EQUAL, extract the tail `nestedOrder n` step. -/
theorem nestedOrder_snd_of_fst_eq {n : Nat} {a b : NestedNat (n + 1)}
    (hfst : a.1 = b.1) (h : nestedOrder (n + 1) a b) : nestedOrder n a.2 b.2 := by
  simp only [nestedOrder, LexProd.lexProd] at h
  rcases h with hlt | ⟨_, hsnd⟩
  · exact absurd hlt (by rw [hfst]; exact Nat.lt_irrefl _)
  · exact hsnd

/-- **The M5⁺ reduce drops the inner `chainNMeasureEI` measure** (`degreeY_top` tied). Extracted from
`chainNReduce_orderCanon_hnz` by the `degreeY_top`-preservation tie. -/
theorem chainNMeasureEI_5p_reduce_drop_hnz (m : Nat) (p : MultiPoly (m + 3))
    (hnz : hnzTower m (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))) :
    nestedOrder (m + 2)
      (chainNMeasureEI m (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3))
        (chainNReduce (m + 1) (fullMult (m + 1) p) p))))
      (chainNMeasureEI m (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))) := by
  have hmr : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3))
      (liftLastY (fullMult m (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)))) = 0 := by
    rw [show (⟨m + 2, by omega⟩ : Fin (m + 3))
          = (⟨m + 2, Nat.lt_succ_self (m + 2)⟩ : Fin (m + 3)) from Fin.ext rfl]
    exact degreeY_top_liftLastY _
  have hm_top : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) (fullMult (m + 1) p) = 0 := by
    show Nat.max (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3))
            (gradedTop (m + 1) (⟨m + 2, by omega⟩ : Fin (m + 3)) p))
          (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3))
            (liftLastY (fullMult m (MultiPoly.dropLastY
              (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))))) = 0
    rw [gradedTop_degreeYtop_zero (m + 1) (⟨m + 2, by omega⟩ : Fin (m + 3)) rfl p, hmr]; decide
  have hfst : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3))
      (chainNReduce (m + 1) (fullMult (m + 1) p) p)
        = MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p :=
    chainNReduce_fst_preserved (m + 1) (⟨m + 2, by omega⟩ : Fin (m + 3)) rfl (fullMult (m + 1) p) p hm_top
  exact nestedOrder_snd_of_fst_eq hfst (chainNReduce_orderCanon_hnz m p hnz)

/-- **`rankRec` of the inner drops on the M5⁺ reduce** — the `ir`-drop the outer `invPhiG(degreeY_top)`
reduce arm consumes. Combines the `chainNMeasureEI` drop with `rankRec_drop`; the reduced inner's degrees
stay `≤ B+1` (degreeX non-increasing + degreeY `≤ +1`, threaded through `leadingCoeffY`/`dropLastY`). -/
theorem rankRec_5p_reduce_drop (m : Nat) (p : MultiPoly (m + 3))
    (hnz : hnzTower m (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))) (B : Nat)
    (hpx : MultiPoly.degreeX p + 2 ≤ B) (hpy : ∀ i : Fin (m + 3), MultiPoly.degreeY i p ≤ B) :
    rankRec (m + 2) (B + 1) (chainNMeasureEI m (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3))
          (chainNReduce (m + 1) (fullMult (m + 1) p) p)))) + 1
      ≤ rankRec (m + 2) B (chainNMeasureEI m (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))) := by
  refine rankRec_drop (m + 2) B (B + 1) _ _ (Nat.le_refl _) ?_
    (chainNMeasureEI_5p_reduce_drop_hnz m p hnz)
  refine chainNMeasureEI_le_allB m (MultiPoly.dropLastY (MultiPoly.leadingCoeffY
    (⟨m + 2, by omega⟩ : Fin (m + 3)) (chainNReduce (m + 1) (fullMult (m + 1) p) p))) (B + 1) ?_ ?_
  · -- degreeX(dropLastY(lcY_top(reduce))) + 2 ≤ B+1
    have h1 : MultiPoly.degreeX (MultiPoly.dropLastY (MultiPoly.leadingCoeffY
        (⟨m + 2, by omega⟩ : Fin (m + 3)) (chainNReduce (m + 1) (fullMult (m + 1) p) p)))
        = MultiPoly.degreeX (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3))
            (chainNReduce (m + 1) (fullMult (m + 1) p) p)) := degreeX_dropLastY _
    have h2 := degreeX_leadingCoeffY_le (⟨m + 2, by omega⟩ : Fin (m + 3))
      (chainNReduce (m + 1) (fullMult (m + 1) p) p)
    have h3 := degreeX_chainNReduce_fullMult_le (m + 1) p
    omega
  · intro i
    -- degreeY i (dropLastY(lcY_top(reduce))) ≤ B+1
    rw [degreeY_dropLastY_eq_prev (m + 2)
        (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 3)) i rfl]
    have h2 := degreeY_leadingCoeffY_le (⟨m + 2, by omega⟩ : Fin (m + 3))
      (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 3))
      (chainNReduce (m + 1) (fullMult (m + 1) p) p)
    have h3 := degreeY_chainNReduce_fullMult_growth_le (m + 1) p
      (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 3))
    have h4 := hpy (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 3))
    omega

end MachLib.IterExpDepthN
