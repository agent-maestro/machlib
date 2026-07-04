import MachLib.PfaffianGeneralCTDCongr
namespace MachLib.PfaffianGeneralReduce
open MachLib.Real MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly MachLib.MultiPolyReconstruct
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianFn MachLib.IterExpChainMod
open MachLib.ChainExp2SDR MachLib.PolynomialCanonical MachLib.ChainExp2SingleExpDescent
open MachLib.ChainExp2CanonMeasure MachLib.ChainExp2CdegInv MachLib.IterExpDepth3CdegY1
open MachLib.ChainExp2Reducer MachLib.ChainExp2NoZeros MachLib.ChainExp2Trim MachLib.IterExpTopIdentity MachLib.ChainExp2PhantomDescent MachLib.ChainExp2YPIT

/-- The general single-exp CANONICAL reduce (cdegY0 multiplier). -/
noncomputable def seReduceCanonGen (c' : PfaffianChain 2) (G0 : MultiPoly 2) (q : MultiPoly 2) : MultiPoly 2 :=
  MultiPoly.sub (chainTotalDeriv c' q)
    (MultiPoly.mul (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 q))) G0) q)

set_option maxHeartbeats 2000000 in
/-- **Eval-congruence of `seReduceCanonGen` under a y₁-free, cdegY0-preserving eval-equal swap `q ~ q'`.**
Extracted as a standalone lemma so its `isDefEq`-heavy `rw` chain (the general cTD congruence, brick 34)
elaborates in a small metavariable context — the strong-induction body below carries ~20 hypotheses that
otherwise bloat every unification and blow the heartbeat budget. -/
theorem seReduceCanonGen_eval_congr {c' : PfaffianChain 2} (G0 q q' : MultiPoly 2)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0)
    (hy1' : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q' = 0)
    (hqq' : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval q x env = MultiPoly.eval q' x env)
    (hcd' : cdegY0 q' = cdegY0 q)
    (x : Real) (env : Fin 2 → Real) :
    MultiPoly.eval (seReduceCanonGen c' G0 q) x env = MultiPoly.eval (seReduceCanonGen c' G0 q') x env := by
  unfold seReduceCanonGen
  rw [MultiPoly.eval_sub, MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_mul, MultiPoly.eval_mul, MultiPoly.eval_mul,
      MultiPoly.eval_const, MultiPoly.eval_const,
      eval_cTD_congr_y1free_gen c' q q' hy1 hy1' hqq' x env, hcd', (hqq' x env).symm]

set_option maxHeartbeats 2000000 in
/-- **The general single-exp canonical descent** (strong induction on degreeY0, phantom-peeling). Base
(htop) = seReduceCanonGen = seReduceGen (cdegY0=degreeY0) → brick 31. Recursion peels a canon-zero top y0
via dropLeadingYAt ⟨0⟩ (eval-equal, smaller degreeY0), bridging by the general cTD congruence (brick 34). -/
theorem singleExpMeasureCanon_seReduceCanonGen_lt {c' : PfaffianChain 2} (G0 : MultiPoly 2)
    (hrel0 : c'.relations (⟨0, by omega⟩ : Fin 2) = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hG0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) G0 = 0) :
    ∀ (D : Nat) (q : MultiPoly 2), MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q = D →
      MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 →
      (singleExpMeasureCanon q).2 ≠ 0 →
      LexProd.lexProd (· < · : Nat → Nat → Prop) (· < ·)
        (singleExpMeasureCanon (seReduceCanonGen c' G0 q)) (singleExpMeasureCanon q) := by
  intro D
  induction D using Nat.strongRecOn with
  | ind D ih =>
    intro q hD hy1 hnz
    by_cases htop : coeffCanonZeroB (y0top q) = false
    · have hbase_eq : seReduceCanonGen c' G0 q = seReduceGen c' G0 q := by
        show MultiPoly.sub (chainTotalDeriv c' q) (MultiPoly.mul (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 q))) G0) q)
           = MultiPoly.sub (chainTotalDeriv c' q) (MultiPoly.mul (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q))) G0) q)
        rw [cdegY0_eq_degreeY0_of_top q htop]
      rw [hbase_eq]
      exact singleExpMeasureCanon_seReduceGen_lt G0 hrel0 hG0 q hy1 htop
    · have htop_true : coeffCanonZeroB (y0top q) = true := by
        cases h : coeffCanonZeroB (y0top q) with
        | false => exact absurd h htop
        | true => rfl
      have hpos : 0 < MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q :=
        Nat.pos_of_ne_zero (fun hdeg0 => hnz (by
          show polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 q))) = 0
          rw [canonLcY0_eq_const0_of_top_deg0 q htop_true hdeg0]
          apply polyTrueDegreeStrict_of_canonicallyZero
          have := coeffCanonZeroB_const0; unfold coeffCanonZeroB at this; exact of_decide_eq_true this))
      have hyfree := (by
        refine ⟨?_, ?_⟩
        · exact yCoeffsAt_entries_degreeY_zero (⟨0, by omega⟩ : Fin 2) q _ (List.getLast_mem (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q))
        · exact yCoeffsAt0_entries_degreeY1_zero q hy1 _ (List.getLast_mem (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q))
        : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (y0top q) = 0 ∧ MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (y0top q) = 0)
      have hcz0 : ∀ (x : Real), MultiPoly.eval (y0top q) x (fun _ => 0) = 0 := by
        have hcanon : CanonicallyZero (polyCoeffs (multiPolyToPolyForLex (y0top q))) := by
          have := htop_true; unfold coeffCanonZeroB at this; exact of_decide_eq_true this
        intro x; exact (canonZero_iff_eval_zero_at_0 (y0top q)).mp hcanon x
      have hlastzero : ∀ (x : Real) (env : Fin 2 → Real),
          MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).getLast (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q)) x env = 0 := by
        intro x env
        show MultiPoly.eval (y0top q) x env = 0
        have hstep0 : MultiPoly.eval (y0top q) x env = MultiPoly.eval (y0top q) x (fun j => if j = (⟨0, by omega⟩ : Fin 2) then (0 : Real) else env j) := by
          apply eval_eq_of_env_agree_off (⟨0, by omega⟩ : Fin 2) (y0top q) x env _ _ hyfree.1
          intro j hj; show env j = (if j = (⟨0, by omega⟩ : Fin 2) then (0 : Real) else env j); rw [if_neg hj]
        have hstep1 : MultiPoly.eval (y0top q) x (fun j => if j = (⟨0, by omega⟩ : Fin 2) then (0 : Real) else env j) = MultiPoly.eval (y0top q) x (fun _ => 0) := by
          apply eval_eq_of_env_agree_off (⟨1, by omega⟩ : Fin 2) (y0top q) x _ (fun _ => 0) _ hyfree.2
          intro j hj
          show (if j = (⟨0, by omega⟩ : Fin 2) then (0 : Real) else env j) = 0
          by_cases hj0 : j = (⟨0, by omega⟩ : Fin 2)
          · rw [if_pos hj0]
          · exfalso; have h0 : j.val ≠ 0 := fun h => hj0 (Fin.ext h); have h1 : j.val ≠ 1 := fun h => hj (Fin.ext h); have := j.isLt; omega
        rw [hstep0, hstep1]; exact hcz0 x
      have hq'q : ∀ (x : Real) (env : Fin 2 → Real),
          MultiPoly.eval (dropLeadingYAt (⟨0, by omega⟩ : Fin 2) q) x env = MultiPoly.eval q x env := fun x env =>
        eval_dropLeadingYAt_of_last_canonically_zero (⟨0, by omega⟩ : Fin 2) q (yCoeffsAt_nonempty (⟨0, by omega⟩ : Fin 2) q) hlastzero x env
      have hqq' : ∀ (x : Real) (env : Fin 2 → Real),
          MultiPoly.eval q x env = MultiPoly.eval (dropLeadingYAt (⟨0, by omega⟩ : Fin 2) q) x env := fun x env => (hq'q x env).symm
      have hy1' : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (dropLeadingYAt (⟨0, by omega⟩ : Fin 2) q) = 0 := degreeY1_dropLeadingYAt0_zero q hy1
      have hdeg' : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (dropLeadingYAt (⟨0, by omega⟩ : Fin 2) q) < MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := degreeY_dropLeadingYAt_lt (⟨0, by omega⟩ : Fin 2) q hpos
      have hcd' : cdegY0 (dropLeadingYAt (⟨0, by omega⟩ : Fin 2) q) = cdegY0 q := cdegY0_eq_of_eval_eq _ q hq'q
      have hmeq : singleExpMeasureCanon (dropLeadingYAt (⟨0, by omega⟩ : Fin 2) q) = singleExpMeasureCanon q := singleExpMeasureCanon_eq_of_eval_eq _ q hq'q
      have hnz' : (singleExpMeasureCanon (dropLeadingYAt (⟨0, by omega⟩ : Fin 2) q)).2 ≠ 0 := by rw [hmeq]; exact hnz
      have hih := ih (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (dropLeadingYAt (⟨0, by omega⟩ : Fin 2) q)) (hD ▸ hdeg') (dropLeadingYAt (⟨0, by omega⟩ : Fin 2) q) rfl hy1' hnz'
      have hred_eq : ∀ (x : Real) (env : Fin 2 → Real),
          MultiPoly.eval (seReduceCanonGen c' G0 q) x env = MultiPoly.eval (seReduceCanonGen c' G0 (dropLeadingYAt (⟨0, by omega⟩ : Fin 2) q)) x env :=
        seReduceCanonGen_eval_congr G0 q (dropLeadingYAt (⟨0, by omega⟩ : Fin 2) q) hy1 hy1' hqq' hcd'
      have hred_meq : singleExpMeasureCanon (seReduceCanonGen c' G0 q) = singleExpMeasureCanon (seReduceCanonGen c' G0 (dropLeadingYAt (⟨0, by omega⟩ : Fin 2) q)) := singleExpMeasureCanon_eq_of_eval_eq _ _ hred_eq
      rw [hred_meq, hmeq.symm]; exact hih

end MachLib.PfaffianGeneralReduce
