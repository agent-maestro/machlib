import MachLib.IterExpDepthNBudget5
import MachLib.IterExpDepthNBoundUncond

/-!
# Chain-N explicit bound — the M5⁺ WF recursion (explicit `budgetN5 + Ndep` invariant)

The explicit analog of `chainN_bound_step_uncond`: instead of `∃N`, it carries the invariant
`zeros(q) ≤ budgetN5 m B q + Ndep (B + budgetN5 m B q)` over a `∀B` motive, and discharges the four M5⁺ arms
with the pure closures (`invPhiG_reduce`/`_trim_any`/`_mono_B`), the M5⁺ reduce drop (`rankRec_5p_reduce_drop`),
the Rolle transfer, the eval-preservations, and `IH_depth` at the leaf. Given the depth-`(m+2)` explicit bound
as a monotone `Ndep`, it produces the depth-`(m+3)` explicit bound.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpDepthNReduce
open MachLib.ChainExp2Trim
open MachLib.ChainExp2NoZeros
open MachLib.ExplicitBound
open MachLib.ChainExp2Explicit

/-- **The explicit M5⁺ WF step.** -/
theorem chainN_bound_step_explicit (m : Nat) (Ndep : Nat → Nat)
    (hNdep : ∀ {D D' : Nat}, D ≤ D' → Ndep D ≤ Ndep D')
    (IH_depth : ∀ (q : MultiPoly (m + 2)) (D : Nat) (a' b' : Real), a' < b' →
        MultiPoly.degreeX q ≤ D → (∀ i : Fin (m + 2), MultiPoly.degreeY i q ≤ D) →
        (∃ z, a' < z ∧ z < b' ∧ (chainNFn (m + 2) q).eval z ≠ 0) →
        ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a' < z ∧ z < b' ∧ (chainNFn (m + 2) q).eval z = 0) → zeros.length ≤ Ndep D)
    (p : MultiPoly (m + 3)) (a b : Real) (hab : a < b) (B : Nat)
    (hpx : MultiPoly.degreeX p + 2 ≤ B) (hpy : ∀ i : Fin (m + 3), MultiPoly.degreeY i p ≤ B)
    (hne : ∃ z, a < z ∧ z < b ∧ (chainNFn (m + 3) p).eval z ≠ 0) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (chainNFn (m + 3) p).eval z = 0) →
      zeros.length ≤ budgetN5 m B p + Ndep (B + budgetN5 m B p) := by
  refine WellFounded.induction
    (C := fun q => ∀ (B : Nat), MultiPoly.degreeX q + 2 ≤ B → (∀ i : Fin (m + 3), MultiPoly.degreeY i q ≤ B) →
      (∃ z, a < z ∧ z < b ∧ (chainNFn (m + 3) q).eval z ≠ 0) →
      ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (chainNFn (m + 3) q).eval z = 0) →
        zeros.length ≤ budgetN5 m B q + Ndep (B + budgetN5 m B q))
    (chainNOrder5p_wf m) p ?_ B hpx hpy hne
  clear hne hpx hpy p B
  intro p ih B hpx hpy hne zeros hnd hz
  by_cases hd_top : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p = 0
  · -- LEAF: budgetN5 = 0, bound = Ndep B, via IH_depth on dropLastY p
    have hbud0 : budgetN5 m B p = 0 := by unfold budgetN5; rw [hd_top]; rfl
    have heval : ∀ z, (chainNFn (m + 3) p).eval z = (chainNFn (m + 2) (MultiPoly.dropLastY p)).eval z :=
      fun z => dropLastY_eval_IterExp (m + 1) p hd_top z
    have hxD : MultiPoly.degreeX (MultiPoly.dropLastY p) ≤ B := by
      rw [degreeX_dropLastY]; omega
    have hyD : ∀ i : Fin (m + 2), MultiPoly.degreeY i (MultiPoly.dropLastY p) ≤ B := by
      intro i
      rw [degreeY_dropLastY_eq_prev (m + 2) (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 3)) i rfl]
      exact hpy _
    have hne' : ∃ z, a < z ∧ z < b ∧ (chainNFn (m + 2) (MultiPoly.dropLastY p)).eval z ≠ 0 := by
      obtain ⟨z, hza, hzb, hzne⟩ := hne
      exact ⟨z, hza, hzb, by rw [← heval z]; exact hzne⟩
    have hIH := IH_depth (MultiPoly.dropLastY p) B a b hab hxD hyD hne' zeros hnd
      (fun z hzmem => by
        obtain ⟨ha, hb', hzero⟩ := hz z hzmem
        exact ⟨ha, hb', by rw [← heval z]; exact hzero⟩)
    rw [hbud0]; simpa using hIH
  · have hd_pos : 0 < MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p := Nat.pos_of_ne_zero hd_top
    obtain ⟨d', hd'⟩ : ∃ d', MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p = d' + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hd_pos).symm⟩
    by_cases hlc0 : ∀ (x : Real) (env : Fin (m + 3) → Real),
        MultiPoly.eval (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p) x env = 0
    · -- TRIM
      have hlast : ∀ (x : Real) (env : Fin (m + 3) → Real),
          MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p).getLast
            (MultiPoly.yCoeffsAt_nonempty (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) x env = 0 := by
        intro x env
        rw [← eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨m + 2, by omega⟩ : Fin (m + 3)) p
              (MultiPoly.yCoeffsAt_nonempty (⟨m + 2, by omega⟩ : Fin (m + 3)) p) x env]
        exact hlc0 x env
      let trim := dropLeadingYAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p
      have htx : MultiPoly.degreeX trim + 2 ≤ B :=
        Nat.le_trans (Nat.add_le_add_right (degreeX_dropLeadingYAt_le _ p) 2) hpx
      have hty : ∀ i : Fin (m + 3), MultiPoly.degreeY i trim ≤ B :=
        fun i => Nat.le_trans (degreeY_dropLeadingYAt_le_all _ p hd_pos i) (hpy i)
      have hne_trim : ∃ z, a < z ∧ z < b ∧ (chainNFn (m + 3) trim).eval z ≠ 0 := by
        obtain ⟨z, hza, hzb, hzne⟩ := hne
        exact ⟨z, hza, hzb, by rw [← chainNFn_degreeYtop_trim_eval m p hlast z]; exact hzne⟩
      have hzt : ∀ z ∈ zeros, a < z ∧ z < b ∧ (chainNFn (m + 3) trim).eval z = 0 := by
        intro z hzmem; obtain ⟨ha, hb', hzero⟩ := hz z hzmem
        exact ⟨ha, hb', by rw [← chainNFn_degreeYtop_trim_eval m p hlast z]; exact hzero⟩
      have hIH := ih trim (chainN_degreeYtop_trim_order5p m p hd_pos) B htx hty hne_trim zeros hnd hzt
      -- budgetN5 trim ≤ budgetN5 p  (invPhiG_trim_any)
      have hle : budgetN5 m B trim ≤ budgetN5 m B p := by
        unfold budgetN5; rw [hd']
        refine invPhiG_trim_any (descentBound (m + 2))
          (fun {_ _} hh => descentBound_mono (m + 2) hh) 0
          (rankRec (m + 2) B (chainNMeasureEI m (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))))
          _ B B ?_ (Nat.le_refl _) (Nat.le_of_lt (rankRec_inner_lt m trim B htx hty))
        · have hlt := degreeY_dropLeadingYAt_lt (⟨m + 2, by omega⟩ : Fin (m + 3)) p hd_pos
          rw [hd'] at hlt; exact Nat.le_of_lt_succ hlt
      exact Nat.le_trans hIH (Nat.add_le_add hle (hNdep (by omega)))
    · -- lcY_top ≢ 0
      have hlcnz : canonZeroB (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) = false := by
        cases h : canonZeroB (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))
        · rfl
        · exact absurd (dropLastY_eval_zero_of_yfree
            (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)
            (MultiPoly.degreeY_leadingCoeffY _ _) ((canonZeroB_true_iff _).mp h)) hlc0
      rcases establish_hnz_or_trim_deg m (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) hlcnz
        with hnz | ⟨q', hq'_eval, hq'_syn, _hq'X, _hq'Y⟩
      · -- REDUCE
        rcases Classical.em (∀ z, a < z → z < b →
            (chainNFn (m + 3) (chainNReduce (m + 1) (fullMult (m + 1) p) p)).eval z = 0) with hrz | hrz
        · -- vehicle: no zeros
          obtain ⟨z₀, hz₀a, hz₀b, hz₀ne⟩ := hne
          have hnoz := chainNFn_no_zeros_of_reduct_zero (m + 1) p a b hab hrz z₀ hz₀a hz₀b hz₀ne
          cases zeros with
          | nil => exact Nat.zero_le _
          | cons z zs =>
            obtain ⟨ha, hb', hzero⟩ := hz z (List.mem_cons_self _ _)
            exact absurd hzero (hnoz z ha hb')
        · have hne' : ∃ z, a < z ∧ z < b ∧
              (chainNFn (m + 3) (chainNReduce (m + 1) (fullMult (m + 1) p) p)).eval z ≠ 0 :=
            Classical.byContradiction fun hcon =>
              hrz fun z hza hzb => Classical.byContradiction fun hz0 => hcon ⟨z, hza, hzb, hz0⟩
          let red := chainNReduce (m + 1) (fullMult (m + 1) p) p
          have hrx : MultiPoly.degreeX red + 2 ≤ B + 1 := by
            have hh : MultiPoly.degreeX red ≤ MultiPoly.degreeX p := degreeX_chainNReduce_fullMult_le (m + 1) p
            omega
          have hry : ∀ i : Fin (m + 3), MultiPoly.degreeY i red ≤ B + 1 := by
            intro i
            have hh : MultiPoly.degreeY i red ≤ MultiPoly.degreeY i p + 1 :=
              degreeY_chainNReduce_fullMult_growth_le (m + 1) p i
            have := hpy i; omega
          have hIH := ih red (chainNReduce_order5p_hnz m p hnz) (B + 1) hrx hry hne'
          -- reduce Rolle: zeros(p) ≤ zeros(red) bound + 1
          refine Nat.le_trans (chainNFn_reduce_step (m + 1) p a b hab
            (budgetN5 m (B + 1) red + Ndep ((B + 1) + budgetN5 m (B + 1) red))
            hIH zeros hnd hz) ?_
          -- budgetN5 (B+1) red + 1 ≤ budgetN5 B p, and Ndep term monotone
          have hbud : budgetN5 m (B + 1) red + 1 ≤ budgetN5 m B p := by
            unfold budgetN5
            have htie : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) red
                = MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p :=
              chainNReduce_fst_preserved (m + 1) (⟨m + 2, by omega⟩ : Fin (m + 3)) rfl
                (fullMult (m + 1) p) p (by
                  show Nat.max _ _ = 0
                  rw [gradedTop_degreeYtop_zero (m + 1) (⟨m + 2, by omega⟩ : Fin (m + 3)) rfl p,
                    show MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3))
                        (liftLastY (fullMult m (MultiPoly.dropLastY
                          (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)))) = 0 from by
                      rw [show (⟨m + 2, by omega⟩ : Fin (m + 3))
                            = (⟨m + 2, Nat.lt_succ_self (m + 2)⟩ : Fin (m + 3)) from Fin.ext rfl]
                      exact degreeY_top_liftLastY _]
                  decide)
            rw [htie, hd']
            exact invPhiG_reduce (descentBound (m + 2)) (fun {_ _} hh => descentBound_mono (m + 2) hh)
              0 d' _ _ B (B + 1) (rankRec_5p_reduce_drop m p hnz B hpx hpy) (Nat.le_refl _)
          have hNdle : Ndep ((B + 1) + budgetN5 m (B + 1) red) ≤ Ndep (B + budgetN5 m B p) :=
            hNdep (by omega)
          omega
      · -- LIFT
        have hswap : ∀ (x : Real) (env : Fin (m + 3) → Real),
            MultiPoly.eval (liftLastY q') x env
              = MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p).getLast
                (MultiPoly.yCoeffsAt_nonempty (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) x env := by
          intro x env
          rw [eval_liftLastY q' x env, hq'_eval x _,
              eval_dropLastY (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)
                (MultiPoly.degreeY_leadingCoeffY _ _) x env]
          exact eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general
            (⟨m + 2, by omega⟩ : Fin (m + 3)) p
            (MultiPoly.yCoeffsAt_nonempty (⟨m + 2, by omega⟩ : Fin (m + 3)) p) x env
        have heval : ∀ z, (chainNFn (m + 3) (liftInner m p q')).eval z = (chainNFn (m + 3) p).eval z :=
          fun z => eval_liftInner m p q' hswap z ((IterExpChain (m + 3)).chainValues z)
        let lift := liftInner m p q'
        have hlx : MultiPoly.degreeX lift + 2 ≤ B :=
          Nat.le_trans (Nat.add_le_add_right (degreeX_liftInner_q_le m p q' _hq'X) 2) hpx
        have hly : ∀ i : Fin (m + 3), MultiPoly.degreeY i lift ≤ B :=
          fun i => Nat.le_trans (degreeY_liftInner_q_le m p q' _hq'Y i) (hpy i)
        have hne_lift : ∃ z, a < z ∧ z < b ∧ (chainNFn (m + 3) lift).eval z ≠ 0 := by
          obtain ⟨z, hza, hzb, hzne⟩ := hne
          exact ⟨z, hza, hzb, by rw [heval z]; exact hzne⟩
        have hzl : ∀ z ∈ zeros, a < z ∧ z < b ∧ (chainNFn (m + 3) lift).eval z = 0 := by
          intro z hzmem; obtain ⟨ha, hb', hzero⟩ := hz z hzmem
          exact ⟨ha, hb', by rw [heval z]; exact hzero⟩
        have hIH := ih lift (liftInner_order5p m p q' hd_pos hq'_eval hq'_syn) B hlx hly hne_lift zeros hnd hzl
        -- budgetN5 lift = budgetN5 p (chainNMeasureCanon ties)
        have hcanon := chainNMeasureCanon_liftInner_eq m p q' hd_pos hq'_eval
        have heq : budgetN5 m B lift = budgetN5 m B p := by
          unfold budgetN5
          have h1 : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) lift
              = MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p :=
            congrArg Prod.fst hcanon
          have h2 : chainNMeasureEI m (MultiPoly.dropLastY (MultiPoly.leadingCoeffY
                (⟨m + 2, by omega⟩ : Fin (m + 3)) lift))
              = chainNMeasureEI m (MultiPoly.dropLastY (MultiPoly.leadingCoeffY
                (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) :=
            congrArg Prod.snd hcanon
          rw [h1, h2]
        rw [heq] at hIH; exact hIH

end MachLib.IterExpDepthN
