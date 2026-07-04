import MachLib.PfaffianGeneralSingleExp
import MachLib.ChainExp2SingleExpDescent

/-!
# Generalize — the general single-exponential `singleExpMeasureCanon` descent

`singleExpMeasureCanon_seReduceGen_lt` mirrors the IterExp `singleExpMeasureCanon_seReduce_lt` for
`seReduceGen` (arbitrary exp-type chain). The bridges (bricks 27-30) make it mechanical: `seReduceGen`'s
leading `y₀`-coefficient evals to the x-derivative of `lcY₀ q` — chain-independent, since `lcY₀ q` is
y-free — so the 2-case argument (canon-nonzero ⟹ x-degree drops via the derivative; canon-zero ⟹ `cdegY0`
drops) is identical to the IterExp proof.
-/
namespace MachLib.PfaffianGeneralReduce
open MachLib.Real MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly MachLib.MultiPolyReconstruct
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianFn MachLib.IterExpChainMod
open MachLib.ChainExp2SDR MachLib.PolynomialCanonical MachLib.ChainExp2SingleExpDescent
open MachLib.ChainExp2CanonMeasure MachLib.IterExpDepthN MachLib.PolynomialRootCount MachLib.ChainExp2CdegInv

set_option maxHeartbeats 4000000 in
/-- **The general single-exp descent.** `singleExpMeasureCanon` strictly drops under `seReduceGen`, for a
non-phantom y1-free `q`. Mirrors `singleExpMeasureCanon_seReduce_lt`: the leading y0-coeff evals to the
x-derivative of `lcY0 q` (chain-independent, via the bridges), so the 2-case argument is identical. -/
theorem singleExpMeasureCanon_seReduceGen_lt {c' : PfaffianChain 2} (G0 : MultiPoly 2)
    (hrel0 : c'.relations (⟨0, by omega⟩ : Fin 2) = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hG0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) G0 = 0) (q : MultiPoly 2)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0)
    (htop : coeffCanonZeroB (y0top q) = false) :
    LexProd.lexProd (· < · : Nat → Nat → Prop) (· < ·)
      (singleExpMeasureCanon (seReduceGen c' G0 q)) (singleExpMeasureCanon q) := by
  have hcd_q : cdegY0 q = MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := cdegY0_eq_degreeY0_of_top q htop
  have hcl_q : canonLcY0 q = y0top q := canonLcY0_eq_top q htop
  have hgl : ∀ (Z : MultiPoly 2) (x : Real),
      MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) Z) x (fun _ => 0)
        = MultiPoly.eval (y0top Z) x (fun _ => 0) := fun Z x =>
    eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨0, by omega⟩ : Fin 2) Z
      (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) Z) x (fun _ => 0)
  have htd_q : polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 q)))
             = polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))) := by
    apply polyTrueDegreeStrict_eq_of_evalCoeffs_eq
    intro x
    rw [evalCoeffs_polyCoeffs_mP2PFL, evalCoeffs_polyCoeffs_mP2PFL, hcl_q, ← hgl q x]
  have htd_pos : 0 < polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))) := by
    have hnz : ¬ CanonicallyZero (polyCoeffs (multiPolyToPolyForLex (y0top q))) := by
      have := htop; unfold coeffCanonZeroB at this; exact of_decide_eq_false this
    have hstep : polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (y0top q)))
               = polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))) := by
      rw [← hcl_q]; exact htd_q
    rw [← hstep, polyTrueDegreeStrict_of_not_canonicallyZero _ hnz]; omega
  have hlc0d : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q) = 0 :=
    MultiPoly.degreeY_leadingCoeffY (⟨0, by omega⟩ : Fin 2) q
  have hlc1d : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q) = 0 :=
    degreeYtop_leadingCoeffYprev_zero 2 (⟨1, by omega⟩ : Fin 2) (⟨0, by omega⟩ : Fin 2) q hy1
  have htdR : polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (y0top (seReduceGen c' G0 q))))
            = polyTrueDegreeStrict (polyDerivativeCoeffs (polyCoeffs (multiPolyToPolyForLex
                (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)))) := by
    have h1 : polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (y0top (seReduceGen c' G0 q))))
            = polyTrueDegreeStrict (polyCoeffs (polyDerivative (multiPolyToPolyForLex
                (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q)))) := by
      apply polyTrueDegreeStrict_eq_of_evalCoeffs_eq
      intro x
      rw [evalCoeffs_polyCoeffs_mP2PFL, ← hgl (seReduceGen c' G0 q) x,
          seReduceGen_lcY0_eval G0 hrel0 hG0 q x (fun _ => 0) hy1,
          cTD_yfree_eq_IterExp (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q) hlc0d hlc1d,
          ← eval_multiPolyToPolyForLex_eq_eval_zero,
          multiPolyToPolyForLex_eval_chainTotalDeriv_IterExp, polyCoeffs_eval]
    rw [h1, polyTrueDegreeStrict_polyDerivative_eq_polyDerivativeCoeffs]
  by_cases htopR : coeffCanonZeroB (y0top (seReduceGen c' G0 q)) = true
  · by_cases hdpos : 0 < MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q
    · refine Or.inl ?_
      show cdegY0 (seReduceGen c' G0 q) < cdegY0 q
      rw [hcd_q]
      have := cdegY0_lt_degreeY0_of_top (seReduceGen c' G0 q) htopR
                (by rw [degreeY0_seReduceGen G0 hrel0 hG0 q hy1]; exact hdpos)
      rwa [degreeY0_seReduceGen G0 hrel0 hG0 q hy1] at this
    · have hdeg0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q = 0 := by omega
      refine Or.inr ⟨?_, ?_⟩
      · show cdegY0 (seReduceGen c' G0 q) = cdegY0 q
        have h1 : cdegY0 (seReduceGen c' G0 q) ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (seReduceGen c' G0 q) := cdegY0_le_degreeY0 _
        rw [degreeY0_seReduceGen G0 hrel0 hG0 q hy1, hdeg0] at h1
        rw [hcd_q, hdeg0]; omega
      · show polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 (seReduceGen c' G0 q))))
            < polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 q)))
        rw [canonLcY0_eq_const0_of_top_deg0 (seReduceGen c' G0 q) htopR
              (by rw [degreeY0_seReduceGen G0 hrel0 hG0 q hy1]; exact hdeg0), htd_q]
        have hz0 : polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (MultiPoly.const 0 : MultiPoly 2))) = 0 := by
          apply polyTrueDegreeStrict_of_canonicallyZero
          have := coeffCanonZeroB_const0; unfold coeffCanonZeroB at this; exact of_decide_eq_true this
        rw [hz0]; exact htd_pos
  · have htopR' : coeffCanonZeroB (y0top (seReduceGen c' G0 q)) = false := by
      cases h : coeffCanonZeroB (y0top (seReduceGen c' G0 q))
      · rfl
      · exact absurd h htopR
    refine Or.inr ⟨?_, ?_⟩
    · show cdegY0 (seReduceGen c' G0 q) = cdegY0 q
      rw [cdegY0_eq_degreeY0_of_top (seReduceGen c' G0 q) htopR', degreeY0_seReduceGen G0 hrel0 hG0 q hy1, hcd_q]
    · show polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 (seReduceGen c' G0 q))))
          < polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 q)))
      rw [canonLcY0_eq_top (seReduceGen c' G0 q) htopR', htdR, htd_q]
      exact polyTrueDegreeStrict_polyDerivativeCoeffs_lt
        (polyCoeffs (multiPolyToPolyForLex (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 2) q))) htd_pos

end MachLib.PfaffianGeneralReduce
