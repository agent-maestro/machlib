import MachLib.PfaffianGeneralBoundUncond
import MachLib.PfaffianGeneralHnzIFDeg
import MachLib.PfaffianGeneralBudgetN5Alpha
import MachLib.PfaffianGeneralFormatDegree
import MachLib.IterExpDepthNStepExplicit

/-!
# The general Pfaffian explicit bound — the M5⁺ WF step (explicit `budgetN5A + Ndep` invariant)

The general-chain analog of `chainN_bound_step_explicit`. Instead of `∃N` (the qualitative
`pfaffian_bound_step_hnz_gen_IF`), it carries the *explicit* invariant

    zeros(q) ≤ budgetN5A D M B q + Ndep (B + budgetN5A D M B q)

over a `∀B` motive along `chainNOrder5p_wf`, and discharges the four M5⁺ arms with the α-budget
closures (`budgetN5A_leaf`/`_trim`/`_lift`/`_reduce`, at α = the format `D`), the general reduce carrying
its integrating factor (`chainReduce_orderCanon_hnz_gen_IF_deg`, which also delivers the multiplier
degree bounds), the format-scaled reduce degree growth (`degreeX`/`degreeY_chainReduce_le_format`), the
general reduce Rolle step (`pfaffianChainFn_reduce_step_gen`), the eval-preservations, and `IH_depth` on
`chainRestrict c` at the leaf.

Two structural differences from the closed `chainN` build:
* the reduce multiplier is *existential* (the IF-carrying descent), not the fixed `fullMult`, so its
  degree bounds ride along from `_deg`;
* the reduce grows `degreeX` by the format `D` (not `+1`), so the recursion re-enters at cap `B+D` and
  the reduce closure drops the budget by the full `D` (`budgetN5A_reduce`), which the `Ndep`-monotone
  step consumes.

Given the depth-`(M+2)` explicit bound as a monotone `Ndep`, it produces the depth-`(M+3)` bound.
-/

namespace MachLib.PfaffianGeneralReduce

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn MachLib.IterExpDepthN MachLib.ChainExp2Trim
open MachLib.MultiPolyReconstruct MachLib.ChainExp2NoZeros MachLib.IterExpTopIdentity
open MachLib.IterExpDepth3CdegY1 MachLib.ExplicitBound MachLib.ChainExp2Explicit
open MachLib.IterExpDepthNReduce

/-- **`chainReduce` preserves `degreeY_top` for an exp-type chain.** The `hexp`-level wrapper around
`chainReduce_degreeY_top_preserved`: the top relation is `G · y_top` (so `degreeY_top (relations top) =
1`) and every other relation omits `y_top` (triangularity), so a multiplier free of `y_top` leaves
`degreeY_top` unchanged under the reduce. This is the `htie` the reduce budget closure needs. -/
theorem chainReduce_degreeYtop_eq_of_expChain {M : Nat} (c : PfaffianChain (M + 3))
    (hexp : IsExpChain c) (m p : MultiPoly (M + 3))
    (hm : MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) m = 0) :
    MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) (chainReduce c m p)
      = MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) p := by
  obtain ⟨⟨G, hG, hrel⟩, htri⟩ := IsExpChain_top c hexp
  exact chainReduce_degreeY_top_preserved c (⟨M + 2, Nat.lt_succ_self (M + 2)⟩ : Fin (M + 3))
    (by rw [hrel, degreeY_mul' (⟨M + 2, Nat.lt_succ_self (M + 2)⟩ : Fin (M + 3)) G
          (MultiPoly.varY (⟨M + 2, Nat.lt_succ_self (M + 2)⟩ : Fin (M + 3))), hG,
        (show MultiPoly.degreeY (⟨M + 2, Nat.lt_succ_self (M + 2)⟩ : Fin (M + 3))
            (MultiPoly.varY (⟨M + 2, Nat.lt_succ_self (M + 2)⟩ : Fin (M + 3))) = 1 from by
          show (if (⟨M + 2, Nat.lt_succ_self (M + 2)⟩ : Fin (M + 3))
              = (⟨M + 2, Nat.lt_succ_self (M + 2)⟩ : Fin (M + 3)) then 1 else 0) = 1
          rw [if_pos rfl])])
    htri m p hm

set_option maxHeartbeats 4000000 in
/-- **The general Pfaffian explicit M5⁺ WF step.** Explicit `budgetN5A + Ndep` invariant over the general
reduce; the α-budget closures (α = format `D`) discharge the four arms. -/
theorem pfaffian_bound_step_explicit {M : Nat} (c : PfaffianChain (M + 3)) (hexp : IsExpChain c)
    (a b : Real) (hab : a < b) (hcoh : c.IsCoherentOn a b)
    (hposit : ∀ z, a < z → z < b → ∀ i : Fin (M + 3), 0 < c.evals i z)
    (D : Nat) (hD : 1 ≤ D)
    (hfmtX : ∀ i : Fin (M + 3), MultiPoly.degreeX (c.relations i) ≤ D)
    (hfmtY : ∀ i j : Fin (M + 3), MultiPoly.degreeY j (c.relations i) ≤ D)
    (Ndep : Nat → Nat) (hNdep : ∀ {D₁ D₂ : Nat}, D₁ ≤ D₂ → Ndep D₁ ≤ Ndep D₂)
    (IH_depth : ∀ (q : MultiPoly (M + 2)) (Dq : Nat),
        MultiPoly.degreeX q ≤ Dq → (∀ i : Fin (M + 2), MultiPoly.degreeY i q ≤ Dq) →
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z ≠ 0) →
        ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z = 0) →
          zeros.length ≤ Ndep Dq)
    (p : MultiPoly (M + 3)) (B : Nat)
    (hpx : MultiPoly.degreeX p + 2 ≤ B) (hpy : ∀ i : Fin (M + 3), MultiPoly.degreeY i p ≤ B)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) →
      zeros.length ≤ budgetN5A D M B p + Ndep (B + budgetN5A D M B p) := by
  refine WellFounded.induction
    (C := fun q => ∀ (B : Nat), MultiPoly.degreeX q + 2 ≤ B →
      (∀ i : Fin (M + 3), MultiPoly.degreeY i q ≤ B) →
      (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z ≠ 0) →
      ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z = 0) →
        zeros.length ≤ budgetN5A D M B q + Ndep (B + budgetN5A D M B q))
    (chainNOrder5p_wf M) p ?_ B hpx hpy hne
  clear hne hpx hpy p B
  intro p ih B hpx hpy hne zeros hnd hz
  by_cases hd_top : MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) p = 0
  · -- LEAF: budgetN5A = 0, bound = Ndep B, via IH_depth on dropLastY p over chainRestrict c
    have hbud0 : budgetN5A D M B p = 0 := budgetN5A_leaf D M B p hd_top
    have heval : ∀ z, (pfaffianChainFn c p).eval z
        = (pfaffianChainFn (chainRestrict c) (MultiPoly.dropLastY p)).eval z :=
      fun z => dropLastY_eval_chainRestrict c p hd_top z
    have hxD : MultiPoly.degreeX (MultiPoly.dropLastY p) ≤ B := by
      rw [degreeX_dropLastY]; omega
    have hyD : ∀ i : Fin (M + 2), MultiPoly.degreeY i (MultiPoly.dropLastY p) ≤ B := by
      intro i
      rw [degreeY_dropLastY_eq_prev (M + 2) (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (M + 3)) i rfl]
      exact hpy _
    have hne' : ∃ z, a < z ∧ z < b ∧
        (pfaffianChainFn (chainRestrict c) (MultiPoly.dropLastY p)).eval z ≠ 0 := by
      obtain ⟨z, hza, hzb, hzne⟩ := hne
      exact ⟨z, hza, hzb, by rw [← heval z]; exact hzne⟩
    have hIH := IH_depth (MultiPoly.dropLastY p) B hxD hyD hne' zeros hnd
      (fun z hzmem => by
        obtain ⟨ha, hb', hzero⟩ := hz z hzmem
        exact ⟨ha, hb', by rw [← heval z]; exact hzero⟩)
    rw [hbud0]; simpa using hIH
  · have hd_pos : 0 < MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) p :=
      Nat.pos_of_ne_zero hd_top
    obtain ⟨d', hd'⟩ : ∃ d', MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) p = d' + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hd_pos).symm⟩
    by_cases hlc0 : ∀ (x : Real) (env : Fin (M + 3) → Real),
        MultiPoly.eval (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p) x env = 0
    · -- TRIM
      have hlast : ∀ (x : Real) (env : Fin (M + 3) → Real),
          MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨M + 2, by omega⟩ : Fin (M + 3)) p).getLast
            (MultiPoly.yCoeffsAt_nonempty (⟨M + 2, by omega⟩ : Fin (M + 3)) p)) x env = 0 := by
        intro x env
        rw [← eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨M + 2, by omega⟩ : Fin (M + 3)) p
              (MultiPoly.yCoeffsAt_nonempty (⟨M + 2, by omega⟩ : Fin (M + 3)) p) x env]
        exact hlc0 x env
      let trim := dropLeadingYAt (⟨M + 2, by omega⟩ : Fin (M + 3)) p
      have htx : MultiPoly.degreeX trim + 2 ≤ B :=
        Nat.le_trans (Nat.add_le_add_right (degreeX_dropLeadingYAt_le _ p) 2) hpx
      have hty : ∀ i : Fin (M + 3), MultiPoly.degreeY i trim ≤ B :=
        fun i => Nat.le_trans (degreeY_dropLeadingYAt_le_all _ p hd_pos i) (hpy i)
      have hne_trim : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c trim).eval z ≠ 0 := by
        obtain ⟨z, hza, hzb, hzne⟩ := hne
        exact ⟨z, hza, hzb, by rw [← pfaffianChainFn_degreeYtop_trim_eval c p hlast z]; exact hzne⟩
      have hzt : ∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c trim).eval z = 0 := by
        intro z hzmem; obtain ⟨ha, hb', hzero⟩ := hz z hzmem
        exact ⟨ha, hb', by rw [← pfaffianChainFn_degreeYtop_trim_eval c p hlast z]; exact hzero⟩
      have hIH := ih trim (chainN_degreeYtop_trim_order5p M p hd_pos) B htx hty hne_trim zeros hnd hzt
      have hle : budgetN5A D M B trim ≤ budgetN5A D M B p :=
        budgetN5A_trim D M B d' hD trim p hd'
          (by
            have hlt := degreeY_dropLeadingYAt_lt (⟨M + 2, by omega⟩ : Fin (M + 3)) p hd_pos
            rw [hd'] at hlt; exact Nat.le_of_lt_succ hlt)
          htx hty
      exact Nat.le_trans hIH (Nat.add_le_add hle (hNdep (by omega)))
    · -- lcY_top ≢ 0
      have hlcnz : canonZeroB (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)) = false := by
        cases h : canonZeroB (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))
        · rfl
        · exact absurd (dropLastY_eval_zero_of_yfree
            (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)
            (MultiPoly.degreeY_leadingCoeffY _ _) ((canonZeroB_true_iff _).mp h)) hlc0
      rcases establish_hnz_or_trim_deg M (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)) hlcnz
        with hnz | ⟨q', hq'_eval, hq'_syn, _hq'X, _hq'Y⟩
      · -- REDUCE (existential IF-carrying multiplier, degree-bounded)
        obtain ⟨m, hm0, hdesc, ⟨E, hE⟩, hmdegX, hmdegY⟩ :=
          chainReduce_orderCanon_hnz_gen_IF_deg a b D c hexp hcoh hposit hfmtX hfmtY p hnz
        rcases Classical.em (∀ z, a < z → z < b →
            (pfaffianChainFn c (chainReduce c m p)).eval z = 0) with hrz | hrz
        · -- vehicle: p has no zeros on (a,b)
          obtain ⟨z₀, hz₀a, hz₀b, hz₀ne⟩ := hne
          have hnoz := pfaffianChainFn_no_zeros_of_reduct_zero_gen c m p a b hab E hcoh hE hrz
            z₀ hz₀a hz₀b hz₀ne
          cases zeros with
          | nil => exact Nat.zero_le _
          | cons z zs =>
            obtain ⟨ha, hb', hzero⟩ := hz z (List.mem_cons_self _ _)
            exact absurd hzero (hnoz z ha hb')
        · have hne' : ∃ z, a < z ∧ z < b ∧
              (pfaffianChainFn c (chainReduce c m p)).eval z ≠ 0 :=
            Classical.byContradiction fun hcon =>
              hrz fun z hza hzb => Classical.byContradiction fun hz0 => hcon ⟨z, hza, hzb, hz0⟩
          let red := chainReduce c m p
          have hrx : MultiPoly.degreeX red + 2 ≤ B + D := by
            have hh : MultiPoly.degreeX red ≤ MultiPoly.degreeX p + D :=
              degreeX_chainReduce_le_format c D m p hfmtX hmdegX
            omega
          have hry : ∀ i : Fin (M + 3), MultiPoly.degreeY i red ≤ B + D := by
            intro i
            have hh : MultiPoly.degreeY i red ≤ MultiPoly.degreeY i p + D :=
              degreeY_chainReduce_le_format c i D m p (fun k => hfmtY k i) (hmdegY i)
            have := hpy i; omega
          have htie : MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) red
              = MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) p :=
            chainReduce_degreeYtop_eq_of_expChain c hexp m p hm0
          have hEI : nestedOrder (M + 2)
              (chainNMeasureEI M (MultiPoly.dropLastY
                (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) red)))
              (chainNMeasureEI M (MultiPoly.dropLastY
                (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) :=
            nestedOrder_snd_of_fst_eq htie hdesc
          have hN := ih red (lexProd_of_fst hdesc) (B + D) hrx hry hne'
          refine Nat.le_trans (pfaffianChainFn_reduce_step_gen c m p a b hab E hcoh hE
            (budgetN5A D M (B + D) red + Ndep ((B + D) + budgetN5A D M (B + D) red))
            hN zeros hnd hz) ?_
          have hbud : budgetN5A D M (B + D) red + D ≤ budgetN5A D M B p :=
            budgetN5A_reduce M B D d' red p htie hd' hEI hrx hry
          have hNdle : Ndep ((B + D) + budgetN5A D M (B + D) red)
              ≤ Ndep (B + budgetN5A D M B p) := hNdep (by omega)
          omega
      · -- LIFT (inner phantom trim; canonical measure ties)
        have hswap : ∀ (x : Real) (env : Fin (M + 3) → Real),
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
        have heval : ∀ z, (pfaffianChainFn c (liftInner M p q')).eval z
            = (pfaffianChainFn c p).eval z :=
          fun z => eval_liftInner M p q' hswap z (c.chainValues z)
        let lift := liftInner M p q'
        have hlx : MultiPoly.degreeX lift + 2 ≤ B :=
          Nat.le_trans (Nat.add_le_add_right (degreeX_liftInner_q_le M p q' _hq'X) 2) hpx
        have hly : ∀ i : Fin (M + 3), MultiPoly.degreeY i lift ≤ B :=
          fun i => Nat.le_trans (degreeY_liftInner_q_le M p q' _hq'Y i) (hpy i)
        have hne_lift : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c lift).eval z ≠ 0 := by
          obtain ⟨z, hza, hzb, hzne⟩ := hne
          exact ⟨z, hza, hzb, by rw [heval z]; exact hzne⟩
        have hzl : ∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c lift).eval z = 0 := by
          intro z hzmem; obtain ⟨ha, hb', hzero⟩ := hz z hzmem
          exact ⟨ha, hb', by rw [heval z]; exact hzero⟩
        have hIH := ih lift (liftInner_order5p M p q' hd_pos hq'_eval hq'_syn) B hlx hly
          hne_lift zeros hnd hzl
        have hcanon := chainNMeasureCanon_liftInner_eq M p q' hd_pos hq'_eval
        have heq : budgetN5A D M B lift = budgetN5A D M B p :=
          budgetN5A_lift D M B lift p (congrArg Prod.fst hcanon) (congrArg Prod.snd hcanon)
        rw [heq] at hIH; exact hIH

end MachLib.PfaffianGeneralReduce
