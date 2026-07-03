import MachLib.PfaffianGeneralWF
import MachLib.IterExpDepthNAbsorbedDescent
import MachLib.IterExpDepthNEstablishHnz
import MachLib.IterExpDepthNMeasure5PlusDescents

/-!
# Generalize — the phantom-absorption reduce descent (hnzTower) for exp-type Pfaffian chains

`chainReduce_descends_hnz_gen` is `chainReduce_descends_gen` with the reduce precondition weakened from
`ReducingGen` to the ∀N `hnzTower` (chain-agnostic), plus the extra `¬hpos` (top-degree-zero) absorption
arm that `hnzTower` allows but `ReducingGen` forbids. This is the descent that `establish_hnz_or_trim`
(also chain-agnostic) feeds — the honest discharge of the reduce dispatch, replacing the unsatisfiable
`hRD_glob` hypothesis. Conditional on the hnz depth-2 base `hBaseHnz`.
-/
namespace MachLib.PfaffianGeneralReduce
open MachLib.Real MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn MachLib.IterExpDepthN MachLib.ChainExp2NoZeros MachLib.MultiPolyReconstruct MachLib.IterExpTopIdentity

/-- Abstract-index helper: for an exp-type top relation, its top y-degree is 1. Proven with an ABSTRACT
top index to sidestep the whnf-hazard of the literal `⟨k+2,_⟩`. -/
private theorem reltop_deg1_hnz {N : Nat} (c : PfaffianChain (N + 1)) (top : Fin (N + 1)) (G : MultiPoly (N + 1))
    (hrel : c.relations top = MultiPoly.mul G (MultiPoly.varY top)) (hG : MultiPoly.degreeY top G = 0) :
    MultiPoly.degreeY top (c.relations top) = 1 := by
  rw [hrel, degreeY_mul' top G (MultiPoly.varY top), hG,
      (show MultiPoly.degreeY top (MultiPoly.varY top) = 1 from by
        show (if top = top then 1 else 0) = 1; rw [if_pos rfl])]

set_option maxHeartbeats 4000000 in
/-- **The recursive reduce descent from `hnzTower` (existential), conditional on the hnz depth-2 base.**
Strictly weaker precondition than `chainReduce_descends_gen`'s `ReducingGen` — `hnzTower` allows
`degreeY_top q = 0`, handled by the extra `¬hpos` phantom-absorption arm. This is what makes the reduce
dispatch (via `establish_hnz_or_trim`) real. -/
theorem chainReduce_descends_hnz_gen
    (hBaseHnz : ∀ (c' : PfaffianChain 2), IsExpChain c' → ∀ (q : MultiPoly 2), hnzTower 0 q →
      ∃ mm : MultiPoly 2, MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) mm = 0 ∧
        nestedOrder 2 (chainNMeasureEI 0 (chainReduce c' mm q)) (chainNMeasureEI 0 q)) :
    ∀ (k : Nat) (c : PfaffianChain (k + 2)), IsExpChain c → ∀ (q : MultiPoly (k + 2)), hnzTower k q →
      ∃ m : MultiPoly (k + 2), MultiPoly.degreeY (⟨k + 1, by omega⟩ : Fin (k + 2)) m = 0 ∧
        nestedOrder (k + 2) (chainNMeasureEI k (chainReduce c m q)) (chainNMeasureEI k q)
  | 0, c, hexp, q, hnz => hBaseHnz c hexp q hnz
  | k + 1, c, hexp, q, hnz => by
      obtain ⟨⟨G, hG, hrel⟩, htri⟩ := IsExpChain_top c hexp
      have hnp : canonZeroB (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) q) = false :=
        nonphantom_of_hnzTower_step k q hnz
      obtain ⟨m', hm'0, hm'desc⟩ := chainReduce_descends_hnz_gen hBaseHnz k (chainRestrict c)
        (IsExpChain_chainRestrict c hexp)
        (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) hnz
      have hmdeg : MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3))
          (gradedMultStep G (⟨k + 2, by omega⟩ : Fin (k + 3)) q (MultiPoly.liftLastY m')) = 0 :=
        gradedMultStep_degreeY_top_zero G (⟨k + 2, by omega⟩ : Fin (k + 3)) q
          (MultiPoly.liftLastY m') hG (MultiPoly.degreeY_top_liftLastY m')
      refine ⟨gradedMultStep G (⟨k + 2, by omega⟩ : Fin (k + 3)) q (MultiPoly.liftLastY m'), hmdeg, ?_⟩
      have hInner : nestedOrder (k + 2)
          (chainNMeasureEI k (chainReduce (chainRestrict c) (MultiPoly.dropLastY (MultiPoly.liftLastY m'))
            (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))))
          (chainNMeasureEI k (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))) := by
        rw [MultiPoly.dropLastY_liftLastY]; exact hm'desc
      by_cases hpos : 0 < MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q
      · exact chainReduce_evalinv_descent_gen c G hrel hG htri (MultiPoly.liftLastY m') q
          (MultiPoly.degreeY_top_liftLastY m') hnp hpos hInner
      · -- ¬hpos : degreeY_top q = 0 — the phantom-absorption arm (Reducing forbids, hnz allows).
        have hd0 : MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q = 0 := Nat.le_zero.mp (Nat.not_lt.mp hpos)
        rw [chainNMeasureEI_eq_syntactic_of_nonphantom k q hnp]
        generalize hRdef : chainReduce c (gradedMultStep G (⟨k + 2, by omega⟩ : Fin (k + 3)) q (MultiPoly.liftLastY m')) q = R
        by_cases hR_np : canonZeroB (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) R) = false
        · rw [chainNMeasureEI_eq_syntactic_of_nonphantom k R hR_np, ← hRdef]
          exact chainReduce_syntactic_descent_gen c G hrel hG htri (MultiPoly.liftLastY m') q
            (MultiPoly.degreeY_top_liftLastY m') hInner
        · have hR_ph : canonZeroB (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) R) = true := by
            cases hb : canonZeroB (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) R)
            · exact absurd hb hR_np
            · rfl
          have hRdeg : MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) R = 0 := by
            rw [← hRdef]
            exact (chainReduce_degreeY_top_preserved c (⟨k + 2, by omega⟩ : Fin (k + 3))
              (reltop_deg1_hnz c (⟨k + 2, by omega⟩ : Fin (k + 3)) G hrel hG) htri
              (gradedMultStep G (⟨k + 2, by omega⟩ : Fin (k + 3)) q (MultiPoly.liftLastY m')) q hmdeg).trans hd0
          have hReval0 : ∀ (x : Real) (env : Fin (k + 3) → Real), MultiPoly.eval R x env = 0 := by
            intro x env
            have h1 : MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) R = R :=
              leadingCoeffY_eq_self_of_degreeY_zero (⟨k + 2, by omega⟩ : Fin (k + 3)) R hRdeg
            have h2 : MultiPoly.eval R x env
                = MultiPoly.eval (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) R) x env := by
              calc MultiPoly.eval R x env
                  = MultiPoly.eval (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) R) x env := by rw [h1]
                _ = MultiPoly.eval (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) R) x env :=
                    eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨k + 2, by omega⟩ : Fin (k + 3)) R
                      (MultiPoly.yCoeffsAt_nonempty (⟨k + 2, by omega⟩ : Fin (k + 3)) R) x env
            rw [h2]; exact (canonZeroB_true_iff _).mp hR_ph x env
          rw [chainNMeasureEI_eq_of_eval_eq (k + 1) R (MultiPoly.const 0)
                (fun x env => by rw [hReval0 x env]; symm; exact MultiPoly.eval_const 0 x env),
              chainNMeasureEI_const0 (k + 1), hd0]
          exact nestedOrder_of_snd rfl
            (hnzTower_measure_pos k (MultiPoly.dropLastY
              (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) hnz)

end MachLib.PfaffianGeneralReduce
