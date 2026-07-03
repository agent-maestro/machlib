import MachLib.PfaffianGeneralHnz

/-!
# Generalize — the honest general Pfaffian–Khovanskii bound (reduce dispatch discharged)

`pfaffian_bound_step_hnz_gen` restructures the per-depth WF step onto the augmented measure `M5⁺`
(`chainNOrder5p`) and discharges the reduce arm's precondition INTERNALLY via the chain-agnostic
`establish_hnz_or_trim` (hnzTower ∨ eval-equal synOrder-smaller trim) — no `hRD` hypothesis. The outer
`pfaffian_khovanskii_bound_hnz_gen` is then conditional on exactly THREE satisfiable hypotheses:
`hBaseHnz`, `hIF_glob`, `hBound2`. This supersedes `pfaffian_khovanskii_bound_gen`, whose `hRD_glob` was
unsatisfiable (ReducingGen strictly stronger than hnzTower).
-/
namespace MachLib.PfaffianGeneralReduce
open MachLib.Real MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn MachLib.IterExpDepthN MachLib.ChainExp2Trim
open MachLib.MultiPolyReconstruct MachLib.ChainExp2NoZeros

set_option maxHeartbeats 2000000 in
/-- **The general WF step (single depth), M5⁺ — reduce dispatch DISCHARGED internally.** No `hRD`: the
reduce precondition is supplied by the chain-agnostic `establish_hnz_or_trim` (hnzTower ∨ eval-equal
synOrder-smaller trim). Conditional only on `hBaseHnz` (hnz depth-2 base) + `hIF` (integrating factors) +
`IH_depth`. Mirrors `chainN_bound_step_uncond`. -/
theorem pfaffian_bound_step_hnz_gen {M : Nat} (c : PfaffianChain (M + 3)) (hexp : IsExpChain c)
    (a b : Real) (hab : a < b) (hcoh : c.IsCoherentOn a b)
    (hBaseHnz : ∀ (c' : PfaffianChain 2), IsExpChain c' → ∀ (q : MultiPoly 2), hnzTower 0 q →
      ∃ mm : MultiPoly 2, MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) mm = 0 ∧
        nestedOrder 2 (chainNMeasureEI 0 (chainReduce c' mm q)) (chainNMeasureEI 0 q))
    (hIF : ∀ (mm : MultiPoly (M + 3)), ∃ E : Real → Real,
        ∀ z, a < z → z < b → HasDerivAt E (-(pfaffianChainFn c mm).eval z) z)
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
      · obtain ⟨m, hm0, horder⟩ := chainReduce_order5p_hnz_gen hBaseHnz c hexp p hnz
        obtain ⟨E, hE⟩ := hIF m
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

/-- **The general Pfaffian–Khovanskii finiteness bound — reduce dispatch DISCHARGED.** Same as
`pfaffian_khovanskii_bound_gen` but the unsatisfiable `hRD_glob` is GONE: the reduce dispatch is handled
internally by `establish_hnz_or_trim`. Conditional on exactly THREE satisfiable hypotheses: `hBaseHnz`
(hnz depth-2 base), `hIF_glob` (integrating factors), and `hBound2` (depth-2 finiteness bound). -/
theorem pfaffian_khovanskii_bound_hnz_gen (a b : Real) (hab : a < b)
    (hBaseHnz : ∀ (c' : PfaffianChain 2), IsExpChain c' → ∀ (q : MultiPoly 2), hnzTower 0 q →
      ∃ mm : MultiPoly 2, MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) mm = 0 ∧
        nestedOrder 2 (chainNMeasureEI 0 (chainReduce c' mm q)) (chainNMeasureEI 0 q))
    (hIF_glob : ∀ (d : Nat) (c' : PfaffianChain d) (mm : MultiPoly d),
        ∃ E : Real → Real, ∀ z, a < z → z < b → HasDerivAt E (-(pfaffianChainFn c' mm).eval z) z)
    (hBound2 : ∀ (c2 : PfaffianChain 2), IsExpChain c2 → c2.IsCoherentOn a b → ∀ (p2 : MultiPoly 2),
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c2 p2).eval z ≠ 0) →
        ∃ N, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c2 p2).eval z = 0) → zeros.length ≤ N) :
    ∀ (M : Nat) (c : PfaffianChain (M + 2)), IsExpChain c → c.IsCoherentOn a b →
      ∀ (p : MultiPoly (M + 2)), (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
      ∃ N, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) → zeros.length ≤ N := by
  intro M
  induction M with
  | zero => intro c hexp hcoh p hne; exact hBound2 c hexp hcoh p hne
  | succ M ih =>
    intro c hexp hcoh p hne
    exact pfaffian_bound_step_hnz_gen c hexp a b hab hcoh hBaseHnz (hIF_glob (M + 3) c)
      (ih (chainRestrict c) (IsExpChain_chainRestrict c hexp) (chainRestrict_isCoherentOn c hexp a b hcoh)) p hne

end MachLib.PfaffianGeneralReduce
