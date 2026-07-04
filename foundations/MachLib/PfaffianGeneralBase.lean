import MachLib.PfaffianGeneralSingleExpDescent

/-!
# Generalize — the depth-2 base wrapper (hBaseHnz), piece 1: the lcY1 eval connection

The depth-2 base `hBaseHnz` needs the reduce's leading y1-coefficient to evaluate to the single-exp reduce
`seReduceGen` on `lcY1 q`, so brick 31 (`singleExpMeasureCanon_seReduceGen_lt`) supplies the inner drop of
`chain2MeasureCanonEvalInv`. The multiplier is `gradedMultStep G1 ⟨1⟩ q mLow`; brick 5's y1-injection
cancels its top term, leaving `cTD c'(lcY1 q) − mLow·lcY1 q` — instantiating `mLow = const(degreeY0(lcY1 q))
·G0` gives exactly `seReduceGen c' G0 (lcY1 q)`.
-/
namespace MachLib.PfaffianGeneralReduce
open MachLib.Real MachLib.MultiPolyMod MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn MachLib.IterExpDepthN MachLib.IterExpTopIdentity MachLib.ChainExp2NoZeros
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2CdegInv
open MachLib.IterExpDepth3CdegY1
open MachLib.ChainExp2Reducer
open MachLib.ChainExp2SingleExpDescent

set_option maxHeartbeats 2000000 in
/-- **Depth-2 lcY1 eval (mLow-parametric).** For any top-free `mLow`, the reduce with multiplier
`gradedMultStep G1 ⟨1⟩ q mLow` has leading y1-coeff evaluating to `cTD c'(lcY1 q) − mLow·lcY1 q` — the
y1-injection (brick 5) cancels gradedMultStep's top term. -/
theorem chain2ReduceGen_lcY1_eval_aux {c' : PfaffianChain 2} (G1 : MultiPoly 2)
    (hrel1 : c'.relations (⟨1, by omega⟩ : Fin 2) = MultiPoly.mul G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))
    (hG1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) G1 = 0)
    (htri1 : ∀ (j : Fin 2), j ≠ (⟨1, by omega⟩ : Fin 2) → MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations j) = 0)
    (mLow : MultiPoly 2) (hmLow : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) mLow = 0)
    (q : MultiPoly 2) (x : Real) (env : Fin 2 → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
      (chainReduce c' (gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) q mLow) q)) x env
    = MultiPoly.eval (chainTotalDeriv c' (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)) x env
      - MultiPoly.eval mLow x env * MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q) x env := by
  have hmm_top : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) q mLow) = 0 :=
    gradedMultStep_degreeY_top_zero G1 (⟨1, by omega⟩ : Fin 2) q mLow hG1 hmLow
  have hreltop_deg : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations (⟨1, by omega⟩ : Fin 2)) = 1 := by
    rw [hrel1, degreeY_mul' (⟨1, by omega⟩ : Fin 2) G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)), hG1]
    show 0 + (if (⟨1, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) then 1 else 0) = 1; rw [if_pos rfl]
  have hdeg_eq : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (chainTotalDeriv c' q)
      = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.mul (gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) q mLow) q) := by
    rw [degreeYtop_cTD_eq_gen c' (⟨1, by omega⟩ : Fin 2) hreltop_deg htri1 q,
        degreeY_mul' (⟨1, by omega⟩ : Fin 2) _ q, hmm_top, Nat.zero_add]
  unfold chainReduce
  rw [MultiPoly.leadingCoeffY_sub_of_eq (⟨1, by omega⟩ : Fin 2) _ _ hdeg_eq,
      (show MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.mul (gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) q mLow) q)
          = MultiPoly.mul (gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) q mLow) (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q) from by
        rw [lcY_mul (⟨1, by omega⟩ : Fin 2) _ q, leadingCoeffY_eq_self_of_degreeY_zero (⟨1, by omega⟩ : Fin 2) _ hmm_top]),
      MultiPoly.eval_sub, MultiPoly.eval_mul,
      leadingCoeffYtop_cTD_eval_gen c' G1 (⟨1, by omega⟩ : Fin 2) hrel1 hG1 htri1 q x env]
  unfold gradedMultStep
  simp only [MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_const]
  mach_ring

set_option maxHeartbeats 2000000 in
/-- **The general depth-2 syntactic descent (mm-parametric).** For a top-free `mm` whose reduce's leading
y1-coeff evals to `seReduceGen c' G0 (lcY1 q)` (`heval`), `chain2MeasureCanon` drops: degreeY1 ties, and
the inner `singleExpMeasureCanon` drops via brick 31. -/
theorem chain2ReduceGen_nestedLT_canon {c' : PfaffianChain 2} (G0 : MultiPoly 2)
    (hrel0 : c'.relations (⟨0, by omega⟩ : Fin 2) = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hG0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) G0 = 0)
    (hreltop1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations (⟨1, by omega⟩ : Fin 2)) = 1)
    (htri1 : ∀ (j : Fin 2), j ≠ (⟨1, by omega⟩ : Fin 2) → MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations j) = 0)
    (q mm : MultiPoly 2) (hmm : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) mm = 0)
    (heval : ∀ (x : Real) (env : Fin 2 → Real),
      MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (chainReduce c' mm q)) x env
        = MultiPoly.eval (seReduceGen c' G0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)) x env)
    (htop : coeffCanonZeroB (y0top (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)) = false) :
    nestedLT (chain2MeasureCanon (chainReduce c' mm q)) (chain2MeasureCanon q) := by
  refine LexProd.lexProd_of_snd ?_ ?_
  · exact chainReduce_degreeY_top_preserved c' (⟨1, by omega⟩ : Fin 2) hreltop1 htri1 mm q hmm
  · have hbridge : singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (chainReduce c' mm q))
        = singleExpMeasureCanon (seReduceGen c' G0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)) :=
      singleExpMeasureCanon_eq_of_eval_eq _ _ heval
    show LexProd.lexProd (· < ·) (· < ·)
      (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (chainReduce c' mm q)))
      (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))
    rw [hbridge]
    exact singleExpMeasureCanon_seReduceGen_lt G0 hrel0 hG0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)
      (MultiPoly.degreeY_leadingCoeffY (⟨1, by omega⟩ : Fin 2) q) htop

end MachLib.PfaffianGeneralReduce
