import MachLib.PfaffianGeneralHnzIF
import MachLib.PfaffianGeneralHnzWF
import MachLib.PfaffianGeneralBoundPos
namespace MachLib.PfaffianGeneralReduce
open MachLib.Real MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn MachLib.IterExpDepthN MachLib.ChainExp2Trim
open MachLib.MultiPolyReconstruct MachLib.ChainExp2NoZeros MachLib.IterExpTopIdentity
open MachLib.IterExpDepth3CdegY1 MachLib.PfaffianGeneralVehExpo MachLib.ChainExp2CanonMeasure

set_option maxHeartbeats 2000000 in
/-- **orderCanon reduce descent carrying its integrating factor.** Mirror of `chainReduce_orderCanon_hnz_gen`
using the IF recursion (brick 42) so the reduce multiplier's integrating factor `E` comes along. -/
theorem chainReduce_orderCanon_hnz_gen_IF (a b : Real)
    {M : Nat} (c : PfaffianChain (M + 3)) (hexp : IsExpChain c) (hcoh : c.IsCoherentOn a b)
    (hposit : ∀ z, a < z → z < b → ∀ i : Fin (M + 3), 0 < c.evals i z)
    (p : MultiPoly (M + 3))
    (hnz : hnzTower M (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) :
    ∃ m : MultiPoly (M + 3), MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) m = 0 ∧
      nestedOrder (M + 3) (chainNMeasureCanon M (chainReduce c m p)) (chainNMeasureCanon M p) ∧
      (∃ E : Real → Real, ∀ z, a < z → z < b → HasDerivAt E (-(pfaffianChainFn c m).eval z) z) := by
  obtain ⟨⟨G, hG, hrel⟩, htri⟩ := IsExpChain_top c hexp
  obtain ⟨m', hm'0, hm'desc, E', hE'⟩ := chainReduce_descends_hnz_gen_IF a b M (chainRestrict c)
    (IsExpChain_chainRestrict c hexp) (chainRestrict_isCoherentOn c hexp a b hcoh)
    (positivity_chainRestrict c a b hposit)
    (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)) hnz
  refine ⟨gradedMultStep G (⟨M + 2, by omega⟩ : Fin (M + 3)) p (MultiPoly.liftLastY m'),
    gradedMultStep_degreeY_top_zero G (⟨M + 2, by omega⟩ : Fin (M + 3)) p (MultiPoly.liftLastY m') hG
      (MultiPoly.degreeY_top_liftLastY m'), ?_, ?_⟩
  · have hInner : nestedOrder (M + 2)
        (chainNMeasureEI M (chainReduce (chainRestrict c) (MultiPoly.dropLastY (MultiPoly.liftLastY m'))
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))))
        (chainNMeasureEI M (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) := by
      rw [MultiPoly.dropLastY_liftLastY]; exact hm'desc
    show nestedOrder (M + 3)
      (chainNMeasureCanon M (chainReduce c (gradedMultStep G (⟨M + 2, by omega⟩ : Fin (M + 3)) p (MultiPoly.liftLastY m')) p))
      (chainNMeasureCanon M p)
    simp only [chainNMeasureCanon]
    exact chainReduce_syntactic_descent_gen c G hrel hG htri (MultiPoly.liftLastY m') p
      (MultiPoly.degreeY_top_liftLastY m') hInner
  · exact vehExpo_tower_step c G p m' a b hrel hcoh
      (fun z hza hzb => hposit z hza hzb (⟨M + 2, by omega⟩ : Fin (M + 3))) E' hE'

/-- **order5p reduce descent carrying its integrating factor.** -/
theorem chainReduce_order5p_hnz_gen_IF (a b : Real)
    {M : Nat} (c : PfaffianChain (M + 3)) (hexp : IsExpChain c) (hcoh : c.IsCoherentOn a b)
    (hposit : ∀ z, a < z → z < b → ∀ i : Fin (M + 3), 0 < c.evals i z)
    (p : MultiPoly (M + 3))
    (hnz : hnzTower M (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) :
    ∃ m : MultiPoly (M + 3), MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) m = 0 ∧
      chainNOrder5p M (chainReduce c m p) p ∧
      (∃ E : Real → Real, ∀ z, a < z → z < b → HasDerivAt E (-(pfaffianChainFn c m).eval z) z) := by
  obtain ⟨m, hm0, hdesc, E, hE⟩ := chainReduce_orderCanon_hnz_gen_IF a b c hexp hcoh hposit p hnz
  exact ⟨m, hm0, lexProd_of_fst hdesc, E, hE⟩

set_option maxHeartbeats 2000000 in
/-- **The general Pfaffian–Khovanskii WF step — hIF DISCHARGED (via the tower vehExpo).** Copy of
`pfaffian_bound_step_hnz_gen` with the reduce arm's `hIF m` replaced by the integrating factor the strengthened
reduce (`chainReduce_order5p_hnz_gen_IF`) now carries. Drops both `hBaseHnz` and `hIF`; adds positive
coherence. -/
theorem pfaffian_bound_step_hnz_gen_IF {M : Nat} (c : PfaffianChain (M + 3)) (hexp : IsExpChain c)
    (a b : Real) (hab : a < b) (hcoh : c.IsCoherentOn a b)
    (hposit : ∀ z, a < z → z < b → ∀ i : Fin (M + 3), 0 < c.evals i z)
    (IH_depth : ∀ (q : MultiPoly (M + 2)),
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z ≠ 0) →
        ∃ Mb, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z = 0) → zeros.length ≤ Mb)
    (p : MultiPoly (M + 3)) (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) → zeros.length ≤ N := by
  refine WellFounded.induction
    (C := fun q => (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z ≠ 0) →
      ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z = 0) → zeros.length ≤ N)
    (chainNOrder5p_wf M) p ?_ hne
  clear hne p
  intro p ih hne
  by_cases hd_top : MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) p = 0
  · exact pfaffianChainFn_bound_of_degreeYtop_zero c p hd_top a b hab hne IH_depth
  · have hd_pos : 0 < MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) p := Nat.pos_of_ne_zero hd_top
    by_cases hlc0 : ∀ (x : Real) (env : Fin (M + 3) → Real),
        MultiPoly.eval (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p) x env = 0
    · have hlast : ∀ (x : Real) (env : Fin (M + 3) → Real),
          MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨M + 2, by omega⟩ : Fin (M + 3)) p).getLast
            (MultiPoly.yCoeffsAt_nonempty (⟨M + 2, by omega⟩ : Fin (M + 3)) p)) x env = 0 := by
        intro x env
        rw [← eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨M + 2, by omega⟩ : Fin (M + 3)) p
              (MultiPoly.yCoeffsAt_nonempty (⟨M + 2, by omega⟩ : Fin (M + 3)) p) x env]
        exact hlc0 x env
      have hne_trim : ∃ z, a < z ∧ z < b ∧
          (pfaffianChainFn c (dropLeadingYAt (⟨M + 2, by omega⟩ : Fin (M + 3)) p)).eval z ≠ 0 := by
        obtain ⟨z, hza, hzb, hzne⟩ := hne
        exact ⟨z, hza, hzb, by rw [← pfaffianChainFn_degreeYtop_trim_eval c p hlast z]; exact hzne⟩
      obtain ⟨N, hN⟩ := ih _ (chainN_degreeYtop_trim_order5p M p hd_pos) hne_trim
      refine ⟨N, fun zeros hnd hz => hN zeros hnd (fun z hzmem => ?_)⟩
      obtain ⟨ha, hb', hzero⟩ := hz z hzmem
      exact ⟨ha, hb', by rw [← pfaffianChainFn_degreeYtop_trim_eval c p hlast z]; exact hzero⟩
    · have hlcnz : canonZeroB (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)) = false := by
        cases h : canonZeroB (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))
        · rfl
        · exact absurd (dropLastY_eval_zero_of_yfree
            (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)
            (MultiPoly.degreeY_leadingCoeffY _ _) ((canonZeroB_true_iff _).mp h)) hlc0
      rcases establish_hnz_or_trim M (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)) hlcnz with hnz | ⟨q', hq'_eval, hq'_syn⟩
      · obtain ⟨m, hm0, horder, E, hE⟩ := chainReduce_order5p_hnz_gen_IF a b c hexp hcoh hposit p hnz
        rcases Classical.em (∀ z, a < z → z < b →
            (pfaffianChainFn c (chainReduce c m p)).eval z = 0) with hrz | hrz
        · obtain ⟨z₀, hz₀a, hz₀b, hz₀ne⟩ := hne
          have hnoz := pfaffianChainFn_no_zeros_of_reduct_zero_gen c m p a b hab E hcoh hE hrz z₀ hz₀a hz₀b hz₀ne
          refine ⟨0, fun zeros _ hz => ?_⟩
          cases zeros with
          | nil => exact Nat.le_refl 0
          | cons z zs =>
            obtain ⟨ha, hb', hzero⟩ := hz z (List.mem_cons_self _ _)
            exact absurd hzero (hnoz z ha hb')
        · have hne' : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c (chainReduce c m p)).eval z ≠ 0 :=
            Classical.byContradiction fun hcon =>
              hrz fun z hza hzb => Classical.byContradiction fun hz0 => hcon ⟨z, hza, hzb, hz0⟩
          obtain ⟨N, hN⟩ := ih _ horder hne'
          exact ⟨N + 1, fun zeros hnd hz =>
            pfaffianChainFn_reduce_step_gen c m p a b hab E hcoh hE N hN zeros hnd hz⟩
      · have hswap : ∀ (x : Real) (env : Fin (M + 3) → Real),
            MultiPoly.eval (liftLastY q') x env
              = MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨M + 2, by omega⟩ : Fin (M + 3)) p).getLast
                (MultiPoly.yCoeffsAt_nonempty (⟨M + 2, by omega⟩ : Fin (M + 3)) p)) x env := by
          intro x env
          rw [eval_liftLastY q' x env, hq'_eval x _,
              eval_dropLastY (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)
                (MultiPoly.degreeY_leadingCoeffY _ _) x env]
          exact eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general
            (⟨M + 2, by omega⟩ : Fin (M + 3)) p
            (MultiPoly.yCoeffsAt_nonempty (⟨M + 2, by omega⟩ : Fin (M + 3)) p) x env
        have heval : ∀ z, (pfaffianChainFn c (liftInner M p q')).eval z = (pfaffianChainFn c p).eval z :=
          fun z => eval_liftInner M p q' hswap z (c.chainValues z)
        have hne_lift : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c (liftInner M p q')).eval z ≠ 0 := by
          obtain ⟨z, hza, hzb, hzne⟩ := hne
          exact ⟨z, hza, hzb, by rw [heval z]; exact hzne⟩
        obtain ⟨N, hN⟩ := ih _ (liftInner_order5p M p q' hd_pos hq'_eval hq'_syn) hne_lift
        refine ⟨N, fun zeros hnd hz => hN zeros hnd (fun z hzmem => ?_)⟩
        obtain ⟨ha, hb', hzero⟩ := hz z hzmem
        exact ⟨ha, hb', by rw [heval z]; exact hzero⟩

/-- **THE general Khovanskii finiteness bound for positive-coherent exp-chains — UNCONDITIONAL (mod
positivity).** No `hIF_glob`, no `hBaseHnz`, no `hBound2`: for a positive-coherent exp-type Pfaffian chain of
any depth, a non-vanishing `p` has finitely many zeros on `(a,b)`. Induction on the extra depth `M`: base is
`pfaffian_bound2_gen`, step is `pfaffian_bound_step_hnz_gen_IF` (which builds its own integrating factor via
the tower vehExpo). `rolle` remains the sole analytic axiom. -/
theorem pfaffian_khovanskii_bound_gen_uncond (a b : Real) (hab : a < b) :
    ∀ (M : Nat) (c : PfaffianChain (M + 2)), IsExpChain c → c.IsCoherentOn a b →
      (∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z) →
      ∀ (p : MultiPoly (M + 2)), (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
      ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) → zeros.length ≤ N := by
  intro M
  induction M with
  | zero =>
    intro c hexp hcoh hposit p hne
    exact pfaffian_bound2_gen c hexp a b hab hcoh hposit p hne
  | succ M ih =>
    intro c hexp hcoh hposit p hne
    exact pfaffian_bound_step_hnz_gen_IF c hexp a b hab hcoh hposit
      (ih (chainRestrict c) (IsExpChain_chainRestrict c hexp)
        (chainRestrict_isCoherentOn c hexp a b hcoh)
        (positivity_chainRestrict c a b hposit)) p hne

end MachLib.PfaffianGeneralReduce
