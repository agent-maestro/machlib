import MachLib.PfaffianGeneralHnz
import MachLib.PfaffianGeneralVehExpoTower
import MachLib.PfaffianGeneralBoundPos
namespace MachLib.PfaffianGeneralReduce
open MachLib.Real MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn MachLib.IterExpDepthN MachLib.ChainExp2NoZeros MachLib.MultiPolyReconstruct MachLib.IterExpTopIdentity MachLib.IterExpDepth3CdegY1
open MachLib.PfaffianGeneralVehExpo MachLib.ChainExp2CanonMeasure

/-- Abstract-index helper (avoids the literal-`⟨k+2⟩` whnf-hazard): `relations top = G·y_top` with top-free
`G` has `degreeY_top`-degree 1. Public mirror of the private `reltop_deg1_hnz`. -/
theorem reltop_deg1_hnz_pub {N : Nat} (c : PfaffianChain (N + 1)) (top : Fin (N + 1)) (G : MultiPoly (N + 1))
    (hrel : c.relations top = MultiPoly.mul G (MultiPoly.varY top)) (hG : MultiPoly.degreeY top G = 0) :
    MultiPoly.degreeY top (c.relations top) = 1 := by
  rw [hrel, degreeY_mul' top G (MultiPoly.varY top), hG,
      (show MultiPoly.degreeY top (MultiPoly.varY top) = 1 from by
        show (if top = top then 1 else 0) = 1; rw [if_pos rfl])]

set_option maxHeartbeats 4000000 in
/-- **The tower reduce recursion, carrying its integrating factor.** Strengthens `chainReduce_descends_hnz
_gen` — same `m` (existential), same measure descent — to ALSO return an integrating factor `E` for `m` on
`(a,b)` (`E' = −(pfaffianChainFn c m).eval`), given positive coherence. Base (k=0) = the explicit depth-2
reduce multiplier (`bound2Mult`) with descent `chain2MeasureCanonEvalInv_descends_gen_hnz` (brick 36) and
`E = hE_vehExpo_bound2` (brick 39); step (k+1) copies the phantom-absorbing descent arms verbatim and appends
`E` via `vehExpo_tower_step` (brick 41). This discharges `hIF_glob` for the reduce multipliers that actually
arise. -/
theorem chainReduce_descends_hnz_gen_IF (a b : Real) :
    ∀ (k : Nat) (c : PfaffianChain (k + 2)), IsExpChain c → c.IsCoherentOn a b →
      (∀ z, a < z → z < b → ∀ i : Fin (k + 2), 0 < c.evals i z) →
      ∀ (q : MultiPoly (k + 2)), hnzTower k q →
      ∃ m : MultiPoly (k + 2), MultiPoly.degreeY (⟨k + 1, by omega⟩ : Fin (k + 2)) m = 0 ∧
        nestedOrder (k + 2) (chainNMeasureEI k (chainReduce c m q)) (chainNMeasureEI k q) ∧
        (∃ E : Real → Real, ∀ z, a < z → z < b → HasDerivAt E (-(pfaffianChainFn c m).eval z) z)
  | 0, c, hexp, hcoh, hposit, q, hnz => by
      obtain ⟨⟨G0, hG0, hrel0⟩, htri0⟩ := hexp (⟨0, by omega⟩ : Fin 2)
      obtain ⟨⟨G1, hG1, hrel1⟩, _⟩ := hexp (⟨1, by omega⟩ : Fin 2)
      have hnz' : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 ≠ 0 := hnz
      have hG0y1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) G0 = 0 := by
        have h := htri0 (⟨1, by omega⟩ : Fin 2) Nat.zero_lt_one
        rw [hrel0, degreeY_mul' (⟨1, by omega⟩ : Fin 2) G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))] at h
        omega
      have htri1 : ∀ (j : Fin 2), j ≠ (⟨1, by omega⟩ : Fin 2) →
          MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c.relations j) = 0 := by
        intro j hj
        have hne1 : j.val ≠ 1 := fun h => hj (Fin.ext h)
        have hj0 : j = (⟨0, by omega⟩ : Fin 2) := by apply Fin.ext; show j.val = 0; have := j.isLt; omega
        rw [hj0]; exact htri0 (⟨1, by omega⟩ : Fin 2) Nat.zero_lt_one
      have hreltop1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c.relations (⟨1, by omega⟩ : Fin 2)) = 1 := by
        rw [hrel1, degreeY_mul' (⟨1, by omega⟩ : Fin 2) G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)), hG1]
        show 0 + (if (⟨1, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) then 1 else 0) = 1
        rw [if_pos rfl]
      have hmLow : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
          (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)))) G0) = 0 := by
        rw [degreeY_mul' (⟨1, by omega⟩ : Fin 2) _ G0, degreeY_const, hG0y1]
      refine ⟨bound2Mult G0 G1 q, ?_, ?_,
        logVehExpoAux c (bound2Deg q) 2 (Nat.le_refl 2), ?_⟩
      · exact gradedMultStep_degreeY_top_zero G1 (⟨1, by omega⟩ : Fin 2) q _ hG1 hmLow
      · exact chain2MeasureCanonEvalInv_descends_gen_hnz G0 G1 hrel0 hG0 hG0y1 hrel1 hG1 htri1 hreltop1 q hnz'
      · exact hE_vehExpo_bound2 G0 G1 q a b hrel0 hrel1 hcoh hposit
  | k + 1, c, hexp, hcoh, hposit, q, hnz => by
      obtain ⟨⟨G, hG, hrel⟩, htri⟩ := IsExpChain_top c hexp
      have hnp : canonZeroB (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) q) = false :=
        nonphantom_of_hnzTower_step k q hnz
      obtain ⟨m', hm'0, hm'desc, E', hE'⟩ := chainReduce_descends_hnz_gen_IF a b k (chainRestrict c)
        (IsExpChain_chainRestrict c hexp) (chainRestrict_isCoherentOn c hexp a b hcoh)
        (positivity_chainRestrict c a b hposit)
        (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) hnz
      have hmdeg : MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3))
          (gradedMultStep G (⟨k + 2, by omega⟩ : Fin (k + 3)) q (MultiPoly.liftLastY m')) = 0 :=
        gradedMultStep_degreeY_top_zero G (⟨k + 2, by omega⟩ : Fin (k + 3)) q
          (MultiPoly.liftLastY m') hG (MultiPoly.degreeY_top_liftLastY m')
      refine ⟨gradedMultStep G (⟨k + 2, by omega⟩ : Fin (k + 3)) q (MultiPoly.liftLastY m'), hmdeg, ?_, ?_⟩
      · have hInner : nestedOrder (k + 2)
            (chainNMeasureEI k (chainReduce (chainRestrict c) (MultiPoly.dropLastY (MultiPoly.liftLastY m'))
              (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))))
            (chainNMeasureEI k (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))) := by
          rw [MultiPoly.dropLastY_liftLastY]; exact hm'desc
        by_cases hpos : 0 < MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q
        · exact chainReduce_evalinv_descent_gen c G hrel hG htri (MultiPoly.liftLastY m') q
            (MultiPoly.degreeY_top_liftLastY m') hnp hpos hInner
        · have hd0 : MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q = 0 := Nat.le_zero.mp (Nat.not_lt.mp hpos)
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
                (reltop_deg1_hnz_pub c (⟨k + 2, by omega⟩ : Fin (k + 3)) G hrel hG) htri
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
      · exact vehExpo_tower_step c G q m' a b hrel hcoh
          (fun z hza hzb => hposit z hza hzb (⟨k + 2, by omega⟩ : Fin (k + 3))) E' hE'

end MachLib.PfaffianGeneralReduce
