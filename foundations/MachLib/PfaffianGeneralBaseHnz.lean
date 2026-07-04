import MachLib.PfaffianGeneralSingleExpCanon
import MachLib.PfaffianGeneralBase
import MachLib.IterExpDepth3CapstonePrep
import MachLib.IterExpDepthNBaseReduce
import MachLib.IterExpDepthNPhantomDescent
namespace MachLib.PfaffianGeneralReduce
open MachLib.Real MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianFn
open MachLib.ChainExp2CanonMeasure MachLib.IterExpTopIdentity MachLib.ChainExp2NoZeros
open MachLib.ChainExp2CdegInv MachLib.IterExpDepth3CdegY1 MachLib.ChainExp2Reducer
open MachLib.ChainExp2SingleExpDescent MachLib.IterExpDepth3CapstonePrep
open MachLib.IterExpDepthN

set_option maxHeartbeats 2000000 in
/-- **Helper (small context): the reduce's lcY₁ evals to `seReduceCanonGen`.** Extracted standalone so its
`unfold seReduceCanonGen; simp` runs in a small metavariable context. Combines brick 32
(`chain2ReduceGen_lcY1_eval_aux` with `mLow = cdegY0(lcY₁ q)·G0`) with `eval(mLow) = cdegY0(lcY₁ q)·eval G0`. -/
theorem chain2ReduceGen_lcY1_eval_seReduceCanonGen {c' : PfaffianChain 2} (G0 G1 : MultiPoly 2)
    (hrel1 : c'.relations (⟨1, by omega⟩ : Fin 2) = MultiPoly.mul G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))
    (hG1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) G1 = 0)
    (htri1 : ∀ (j : Fin 2), j ≠ (⟨1, by omega⟩ : Fin 2) → MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations j) = 0)
    (hG0y1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) G0 = 0)
    (q : MultiPoly 2) (x : Real) (env : Fin 2 → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
      (chainReduce c' (gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) q
        (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)))) G0)) q)) x env
    = MultiPoly.eval (seReduceCanonGen c' G0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)) x env := by
  have hmLow : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
      (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)))) G0) = 0 := by
    rw [degreeY_mul' (⟨1, by omega⟩ : Fin 2) _ G0, degreeY_const, hG0y1]
  rw [chain2ReduceGen_lcY1_eval_aux G1 hrel1 hG1 htri1 _ hmLow q x env]
  unfold seReduceCanonGen
  simp only [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_const]

set_option maxHeartbeats 2000000 in
/-- **Abstract-`mm` general depth-2 canonical descent (hnz-only).** Keeps `mm` a VARIABLE (so all terms stay
small); the concrete instantiation is `chain2ReduceGen_nestedLT_canon_hnz` below. Mirrors brick 33
(`chain2ReduceGen_nestedLT_canon`) but swaps brick 31 → brick 35 (canonical single-exp descent) and drops
the `htop` requirement for `hnz`. -/
theorem chain2ReduceGen_nestedLT_canon_hnz_abstract {c' : PfaffianChain 2} (G0 : MultiPoly 2)
    (hrel0 : c'.relations (⟨0, by omega⟩ : Fin 2) = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hG0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) G0 = 0)
    (hreltop1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations (⟨1, by omega⟩ : Fin 2)) = 1)
    (htri1 : ∀ (j : Fin 2), j ≠ (⟨1, by omega⟩ : Fin 2) → MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations j) = 0)
    (q mm : MultiPoly 2) (hmm : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) mm = 0)
    (heval : ∀ (x : Real) (env : Fin 2 → Real),
      MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (chainReduce c' mm q)) x env
        = MultiPoly.eval (seReduceCanonGen c' G0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)) x env)
    (hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 ≠ 0) :
    nestedLT (chain2MeasureCanon (chainReduce c' mm q)) (chain2MeasureCanon q) := by
  refine LexProd.lexProd_of_snd ?_ ?_
  · exact chainReduce_degreeY_top_preserved c' (⟨1, by omega⟩ : Fin 2) hreltop1 htri1 mm q hmm
  · have hbridge : singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (chainReduce c' mm q))
        = singleExpMeasureCanon (seReduceCanonGen c' G0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)) :=
      singleExpMeasureCanon_eq_of_eval_eq _ _ heval
    show LexProd.lexProd (· < ·) (· < ·)
      (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (chainReduce c' mm q)))
      (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))
    rw [hbridge]
    exact singleExpMeasureCanon_seReduceCanonGen_lt G0 hrel0 hG0
      (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))
      (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q) rfl
      (MultiPoly.degreeY_leadingCoeffY (⟨1, by omega⟩ : Fin 2) q) hnz

/-- **The general depth-2 canonical descent (hnz-only), concrete multiplier.** Instantiates the abstract
descent with `mm = gradedMultStep G1 ⟨1⟩ q (cdegY0(lcY₁ q)·G0)` and the eval helper. -/
theorem chain2ReduceGen_nestedLT_canon_hnz {c' : PfaffianChain 2} (G0 G1 : MultiPoly 2)
    (hrel0 : c'.relations (⟨0, by omega⟩ : Fin 2) = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hG0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) G0 = 0)
    (hG0y1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) G0 = 0)
    (hrel1 : c'.relations (⟨1, by omega⟩ : Fin 2) = MultiPoly.mul G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))
    (hG1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) G1 = 0)
    (htri1 : ∀ (j : Fin 2), j ≠ (⟨1, by omega⟩ : Fin 2) → MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations j) = 0)
    (hreltop1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations (⟨1, by omega⟩ : Fin 2)) = 1)
    (q : MultiPoly 2)
    (hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 ≠ 0) :
    nestedLT
      (chain2MeasureCanon (chainReduce c'
        (gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) q
          (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)))) G0)) q))
      (chain2MeasureCanon q) := by
  have hmLow : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
      (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)))) G0) = 0 := by
    rw [degreeY_mul' (⟨1, by omega⟩ : Fin 2) _ G0, degreeY_const, hG0y1]
  exact chain2ReduceGen_nestedLT_canon_hnz_abstract G0 hrel0 hG0 hreltop1 htri1 q
    (gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) q
      (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)))) G0))
    (gradedMultStep_degreeY_top_zero G1 (⟨1, by omega⟩ : Fin 2) q _ hG1 hmLow)
    (fun x env => chain2ReduceGen_lcY1_eval_seReduceCanonGen G0 G1 hrel1 hG1 htri1 hG0y1 q x env)
    hnz

set_option maxHeartbeats 2000000 in
/-- **Abstract-`mm` general depth-2 EVAL-INVARIANT descent (hnz-only).** Mirrors the concrete
`chain2MeasureCanonEvalInv_descends_hnz`: `hq_np` collapses `q`'s eval-invariant measure to the syntactic
one, then three cases on the reduce result — non-phantom (both collapse, apply Lemma A abstract),
phantom+degreeY₁>0 (`cdegY1` first-component drop), phantom+degreeY₁=0 (`y₁`-free ⟹ eval-zero ⟹ floor to
`(0,(0,0))`, `< (0, smc(lcY₁ q))` since `hnz`). `mm` stays a VARIABLE so all terms remain small. -/
theorem chain2MeasureCanonEvalInv_descends_gen_hnz_abstract {c' : PfaffianChain 2} (G0 : MultiPoly 2)
    (hrel0 : c'.relations (⟨0, by omega⟩ : Fin 2) = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hG0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) G0 = 0)
    (hreltop1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations (⟨1, by omega⟩ : Fin 2)) = 1)
    (htri1 : ∀ (j : Fin 2), j ≠ (⟨1, by omega⟩ : Fin 2) → MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations j) = 0)
    (q mm : MultiPoly 2) (hmm : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) mm = 0)
    (heval : ∀ (x : Real) (env : Fin 2 → Real),
      MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (chainReduce c' mm q)) x env
        = MultiPoly.eval (seReduceCanonGen c' G0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)) x env)
    (hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 ≠ 0) :
    nestedLT (chain2MeasureCanonEvalInv (chainReduce c' mm q)) (chain2MeasureCanonEvalInv q) := by
  have hq_np := nonphantom_of_hnz q hnz
  rw [chain2MeasureCanonEvalInv_eq_chain2MeasureCanon_of_nonphantom q hq_np]
  by_cases hR_np : coeffCanonZeroB1 (y1top (chainReduce c' mm q)) = false
  · rw [chain2MeasureCanonEvalInv_eq_chain2MeasureCanon_of_nonphantom _ hR_np]
    exact chain2ReduceGen_nestedLT_canon_hnz_abstract G0 hrel0 hG0 hreltop1 htri1 q mm hmm heval hnz
  · have hR_ph : coeffCanonZeroB1 (y1top (chainReduce c' mm q)) = true := by
      cases hb : coeffCanonZeroB1 (y1top (chainReduce c' mm q)) with
      | false => exact absurd hb hR_np
      | true => rfl
    have hRdeg : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (chainReduce c' mm q)
        = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q :=
      chainReduce_degreeY_top_preserved c' (⟨1, by omega⟩ : Fin 2) hreltop1 htri1 mm q hmm
    by_cases hpos : 0 < MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q
    · refine lexProd_of_fst ?_
      show cdegY1 (chainReduce c' mm q) < MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q
      have h1 := cdegY1_lt_degreeY1_of_top (chainReduce c' mm q) hR_ph (by rw [hRdeg]; exact hpos)
      rw [hRdeg] at h1; exact h1
    · have hd0 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by omega
      have hred_yf : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (chainReduce c' mm q) = 0 := by
        rw [hRdeg, hd0]
      have hred_zero := eval_zero_of_coeffCanonZeroB1_y1top_yfree (chainReduce c' mm q) hred_yf hR_ph
      rw [chain2MeasureCanonEvalInv_eq_of_eval_eq (chainReduce c' mm q) (MultiPoly.const (0 : Real))
            (fun x env => by rw [hred_zero x env]; symm; exact MultiPoly.eval_const 0 x env),
          chain2MeasureCanonEvalInv_const0]
      refine LexProd.lexProd_of_snd hd0.symm ?_
      rcases Nat.eq_zero_or_pos (singleExpMeasureCanon
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).1 with ha | ha
      · exact LexProd.lexProd_of_snd ha.symm (Nat.pos_of_ne_zero hnz)
      · exact lexProd_of_fst ha

/-- **The general depth-2 EVAL-INVARIANT descent (hnz-only), concrete multiplier.** -/
theorem chain2MeasureCanonEvalInv_descends_gen_hnz {c' : PfaffianChain 2} (G0 G1 : MultiPoly 2)
    (hrel0 : c'.relations (⟨0, by omega⟩ : Fin 2) = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hG0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) G0 = 0)
    (hG0y1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) G0 = 0)
    (hrel1 : c'.relations (⟨1, by omega⟩ : Fin 2) = MultiPoly.mul G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))
    (hG1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) G1 = 0)
    (htri1 : ∀ (j : Fin 2), j ≠ (⟨1, by omega⟩ : Fin 2) → MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations j) = 0)
    (hreltop1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations (⟨1, by omega⟩ : Fin 2)) = 1)
    (q : MultiPoly 2)
    (hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 ≠ 0) :
    nestedLT
      (chain2MeasureCanonEvalInv (chainReduce c'
        (gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) q
          (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)))) G0)) q))
      (chain2MeasureCanonEvalInv q) := by
  have hmLow : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
      (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)))) G0) = 0 := by
    rw [degreeY_mul' (⟨1, by omega⟩ : Fin 2) _ G0, degreeY_const, hG0y1]
  exact chain2MeasureCanonEvalInv_descends_gen_hnz_abstract G0 hrel0 hG0 hreltop1 htri1 q
    (gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) q
      (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)))) G0))
    (gradedMultStep_degreeY_top_zero G1 (⟨1, by omega⟩ : Fin 2) q _ hG1 hmLow)
    (fun x env => chain2ReduceGen_lcY1_eval_seReduceCanonGen G0 G1 hrel1 hG1 htri1 hG0y1 q x env)
    hnz

set_option maxHeartbeats 2000000 in
/-- **`hBaseHnz` DISCHARGED.** The depth-2 base of the general Khovanskii WF induction: for any exp-chain
`c'` and any `q` with `hnzTower 0 q` (= `(smc(lcY₁ q)).2 ≠ 0`), the multiplier
`mm = gradedMultStep G1 ⟨1⟩ q (cdegY0(lcY₁ q)·G0)` is y₁-free and the general reduce strictly lowers
`chainNMeasureEI 0` (= `chain2MeasureCanonEvalInv`, `nestedOrder 2` = `nestedLT`). `G0, G1, htri1, hreltop1`
are extracted from `IsExpChain c'` with the file's own index literals; the descent is
`chain2MeasureCanonEvalInv_descends_gen_hnz`. This is exactly the `hBaseHnz` hypothesis of
`pfaffian_khovanskii_bound_hnz_gen` — so that bound is now unconditional in its base. -/
theorem pfaffian_base_hnz_gen :
    ∀ (c' : PfaffianChain 2), IsExpChain c' → ∀ (q : MultiPoly 2), hnzTower 0 q →
      ∃ mm : MultiPoly 2, MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) mm = 0 ∧
        nestedOrder 2 (chainNMeasureEI 0 (chainReduce c' mm q)) (chainNMeasureEI 0 q) := by
  intro c' hexp q hnz
  obtain ⟨⟨G0, hG0, hrel0⟩, htri0⟩ := hexp (⟨0, by omega⟩ : Fin 2)
  obtain ⟨⟨G1, hG1, hrel1⟩, _⟩ := hexp (⟨1, by omega⟩ : Fin 2)
  have hnz' : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 ≠ 0 := hnz
  have hG0y1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) G0 = 0 := by
    have h := htri0 (⟨1, by omega⟩ : Fin 2) Nat.zero_lt_one
    rw [hrel0, degreeY_mul' (⟨1, by omega⟩ : Fin 2) G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))] at h
    omega
  have htri1 : ∀ (j : Fin 2), j ≠ (⟨1, by omega⟩ : Fin 2) →
      MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations j) = 0 := by
    intro j hj
    have hne1 : j.val ≠ 1 := fun h => hj (Fin.ext h)
    have hj0 : j = (⟨0, by omega⟩ : Fin 2) := by
      apply Fin.ext
      show j.val = 0
      have := j.isLt
      omega
    rw [hj0]
    exact htri0 (⟨1, by omega⟩ : Fin 2) Nat.zero_lt_one
  have hreltop1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c'.relations (⟨1, by omega⟩ : Fin 2)) = 1 := by
    rw [hrel1, degreeY_mul' (⟨1, by omega⟩ : Fin 2) G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)), hG1]
    show 0 + (if (⟨1, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) then 1 else 0) = 1
    rw [if_pos rfl]
  have hmLow : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
      (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)))) G0) = 0 := by
    rw [degreeY_mul' (⟨1, by omega⟩ : Fin 2) _ G0, degreeY_const, hG0y1]
  refine ⟨gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) q
      (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)))) G0), ?_, ?_⟩
  · exact gradedMultStep_degreeY_top_zero G1 (⟨1, by omega⟩ : Fin 2) q _ hG1 hmLow
  · exact chain2MeasureCanonEvalInv_descends_gen_hnz G0 G1 hrel0 hG0 hG0y1 hrel1 hG1 htri1 hreltop1 q hnz'

end MachLib.PfaffianGeneralReduce
