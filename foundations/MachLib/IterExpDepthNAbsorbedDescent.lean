import MachLib.IterExpDepthNPhantomDescent
import MachLib.IterExpDepthNDescentInduction
import MachLib.IterExpDepthNBaseReduce

/-!
# Phase C→D absorption — the absorbed reduce descent `chainNReduce_descends_hnz` (∀N)

The payoff of the `hnz`-tower foundation: the reduce strictly descends `chainNMeasureEI` needing ONLY the
deepest-true-degree hypothesis `hnzTower` — NOT the full `Reducing` predicate. This is the ∀N lift of the
depth-2 `chain2MeasureCanonEvalInv_descends_hnz`, and the lemma that discharges the reduce arm's precondition.

Induction on depth. Non-phantom-at-every-level comes free from `hnz` (`nonphantom_of_hnzTower_step`); the only
new case beyond `chainNReduce_descends` is `degreeY_top q = 0` (which `Reducing` forbids but `hnz` allows), split
on whether the reduce is phantom:
* reduce non-phantom → the syntactic descent ties the top degree at `0` and rides the inner IH;
* reduce phantom → the reduce is `⟨top⟩`-free (`chainNReduce_fst_preserved`) and phantom, hence `≡ 0`, so its
  measure is the `nestedZero` floor (`chainNMeasureEI_const0`), strictly below `chainNMeasureEI q` by
  `hnzTower_measure_pos`.

No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.IterExpDepthNReduce
open MachLib.ChainExp2Reducer
open MachLib.ChainExp2CanonMeasure
open MachLib.IterExpDepth3CdegY1
open MachLib.IterExpDepth3CapstonePrep
open MachLib.ChainExp2NoZeros
open MachLib.MultiPolyReconstruct

/-- **The `hnz`-only base `D(0)`.** ∀N base at depth 2 needing only `hnz` (the depth-2 `_descends_hnz`
absorbs the non-phantom + positive-degree conditions). -/
theorem chainNReduce_evalinv_descent_base_hnz (p : MultiPoly 2)
    (hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)).2 ≠ 0) :
    nestedOrder 2
      (chainNMeasureEI 0 (chainNReduce 0 (MultiPoly.add (gradedTop 0 (⟨1, by omega⟩ : Fin 2) p)
        (MultiPoly.const (MachLib.Real.natCast
          (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))))) p))
      (chainNMeasureEI 0 p) := by
  rw [chainNReduce_zero_eq_chain2Reduce]
  show nestedLT (chain2MeasureCanonEvalInv (chain2Reduce (MachLib.Real.natCast
        (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))) p))
      (chain2MeasureCanonEvalInv p)
  exact chain2MeasureCanonEvalInv_descends_hnz p hnz

/-- **The absorbed reduce descent, ∀N.** For an `hnzTower` `q` at any depth, the reduce with the full graded
multiplier strictly lowers `chainNMeasureEI` — with NO positive-degree or per-level reducing hypothesis. -/
theorem chainNReduce_descends_hnz : ∀ (k : Nat) (q : MultiPoly (k + 2)), hnzTower k q →
    nestedOrder (k + 2) (chainNMeasureEI k (chainNReduce k (fullMult k q) q)) (chainNMeasureEI k q)
  | 0, q, hnz => by
      simp only [fullMult]
      exact chainNReduce_evalinv_descent_base_hnz q hnz
  | k + 1, q, hnz => by
      simp only [fullMult]
      have hnp : canonZeroB (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) q) = false :=
        nonphantom_of_hnzTower_step k q hnz
      have hInner : nestedOrder (k + 2)
          (chainNMeasureEI k (chainNReduce k (MultiPoly.dropLastY (liftLastY (fullMult k
            (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)))))
            (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))))
          (chainNMeasureEI k (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))) := by
        rw [dropLastY_liftLastY]
        exact chainNReduce_descends_hnz k
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) hnz
      by_cases hpos : 0 < MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q
      · exact chainNReduce_evalinv_descent k (⟨k + 2, by omega⟩ : Fin (k + 3)) rfl
          (liftLastY (fullMult k (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)))) q
          (degreeY_top_liftLastY _) hnp hpos hInner
      · -- degreeY_top q = 0 : the case Reducing forbids but hnz allows.
        have hd0 : MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q = 0 :=
          Nat.le_zero.mp (Nat.not_lt.mp hpos)
        have hm_top : MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3))
            (MultiPoly.add (gradedTop (k + 1) (⟨k + 2, by omega⟩ : Fin (k + 3)) q)
              (liftLastY (fullMult k (MultiPoly.dropLastY
                (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))))) = 0 := by
          show Nat.max (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3))
                (gradedTop (k + 1) (⟨k + 2, by omega⟩ : Fin (k + 3)) q))
              (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3))
                (liftLastY (fullMult k (MultiPoly.dropLastY
                  (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))))) = 0
          rw [gradedTop_degreeYtop_zero (k + 1) (⟨k + 2, by omega⟩ : Fin (k + 3)) rfl q,
              degreeY_top_liftLastY _]; decide
        rw [chainNMeasureEI_eq_syntactic_of_nonphantom k q hnp]
        generalize hRdef : chainNReduce (k + 1) (MultiPoly.add
          (gradedTop (k + 1) (⟨k + 2, by omega⟩ : Fin (k + 3)) q)
          (liftLastY (fullMult k (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))))) q = R
        by_cases hR_np : canonZeroB (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) R) = false
        · rw [chainNMeasureEI_eq_syntactic_of_nonphantom k R hR_np, ← hRdef]
          exact chainNReduce_syntactic_descent k (⟨k + 2, by omega⟩ : Fin (k + 3)) rfl
            (liftLastY (fullMult k (MultiPoly.dropLastY
              (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)))) q
            (degreeY_top_liftLastY _) hInner
        · -- reduce phantom → reduce ≡ 0 → floor
          have hR_ph : canonZeroB (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) R) = true := by
            cases hb : canonZeroB (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) R)
            · exact absurd hb hR_np
            · rfl
          have hRdeg : MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) R = 0 := by
            rw [← hRdef]
            exact (chainNReduce_fst_preserved (k + 1) (⟨k + 2, by omega⟩ : Fin (k + 3)) rfl _ q hm_top).trans hd0
          have hReval0 : ∀ (x : Real) (env : Fin (k + 3) → Real), MultiPoly.eval R x env = 0 := by
            intro x env
            have h1 : MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) R = R :=
              leadingCoeffY_eq_self_of_degreeY_zero (⟨k + 2, by omega⟩ : Fin (k + 3)) R hRdeg
            have h2 : MultiPoly.eval R x env
                = MultiPoly.eval (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) R) x env :=
              calc MultiPoly.eval R x env
                  = MultiPoly.eval (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) R) x env := by
                    rw [h1]
                _ = MultiPoly.eval (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) R) x env :=
                    eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general
                      (⟨k + 2, by omega⟩ : Fin (k + 3)) R
                      (MultiPoly.yCoeffsAt_nonempty (⟨k + 2, by omega⟩ : Fin (k + 3)) R) x env
            rw [h2]; exact (canonZeroB_true_iff _).mp hR_ph x env
          rw [chainNMeasureEI_eq_of_eval_eq (k + 1) R (MultiPoly.const 0)
                (fun x env => by rw [hReval0 x env]; symm; exact MultiPoly.eval_const 0 x env),
              chainNMeasureEI_const0 (k + 1), hd0]
          exact nestedOrder_of_snd rfl
            (hnzTower_measure_pos k (MultiPoly.dropLastY
              (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) hnz)

end MachLib.IterExpDepthN
