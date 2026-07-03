import MachLib.IterExpDepthNMeasure5PlusDescents
import MachLib.IterExpDepthNBaseArm
import MachLib.IterExpDepthNTrimArm
import MachLib.IterExpDepthNVehicleNoZeros
import MachLib.IterExpDepthNReduceStep

/-!
# The UNCONDITIONAL arbitrary-depth Khovanskii bound

`chainN_khovanskii_bound_unconditional` — for every depth and every chain-`N` polynomial not identically zero
on `(a,b)`, `chainNFn p` has finitely many zeros — with NO `zero_count_bound_classical` and NO hypothesis.

The WF assembly is now on the augmented measure `chainNOrder5p` (M5⁺), and the reduce arm's `Reducing`
precondition is discharged by `establish_hnz_or_trim`: on the inner `q := dropLastY(lcY_top p)`, either
`hnzTower m q` (the absorbed reduce descent fires) or a `synMeasure`-smaller eval-equal trim (lifted to `p`
by `liftInner`, descending M5⁺'s second component). This closes the last gap — the `hRD` hypothesis of
`chainN_khovanskii_bound_of_reducing` is now a theorem.

Path B; no `sorry`; `#print axioms`-clean of `zero_count_bound_classical`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpDepthNReduce
open MachLib.ChainExp2Trim
open MachLib.ChainExp2NoZeros

/-- **The WF assembly on M5⁺.** Given the depth-`(m+2)` bound `IH_depth`, every non-identically-zero chain-`(m+3)`
`p` has finitely many zeros. Four dispatch arms via `WellFounded.induction` on `chainNOrder5p m`; the reduce arm's
precondition is supplied by `establish_hnz_or_trim`. -/
theorem chainN_bound_step_uncond (m : Nat)
    (IH_depth : ∀ (q : MultiPoly (m + 2)) (a' b' : Real), a' < b' →
        (∃ z, a' < z ∧ z < b' ∧ (chainNFn (m + 2) q).eval z ≠ 0) →
        ∃ M, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a' < z ∧ z < b' ∧ (chainNFn (m + 2) q).eval z = 0) → zeros.length ≤ M)
    (p : MultiPoly (m + 3)) (a b : Real) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧ (chainNFn (m + 3) p).eval z ≠ 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (chainNFn (m + 3) p).eval z = 0) → zeros.length ≤ N := by
  refine WellFounded.induction
    (C := fun q => (∃ z, a < z ∧ z < b ∧ (chainNFn (m + 3) q).eval z ≠ 0) →
      ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (chainNFn (m + 3) q).eval z = 0) → zeros.length ≤ N)
    (chainNOrder5p_wf m) p ?_ hne
  clear hne p
  intro p ih hne
  by_cases hd_top : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p = 0
  · exact chainNFn_bound_of_degreeYtop_zero (m + 1) p hd_top a b hab hne IH_depth
  · have hd_pos : 0 < MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p := Nat.pos_of_ne_zero hd_top
    by_cases hlc0 : ∀ (x : Real) (env : Fin (m + 3) → Real),
        MultiPoly.eval (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p) x env = 0
    · -- lcY_top p ≡ 0 : degree-trim
      have hlast : ∀ (x : Real) (env : Fin (m + 3) → Real),
          MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p).getLast
            (MultiPoly.yCoeffsAt_nonempty (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) x env = 0 := by
        intro x env
        rw [← eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨m + 2, by omega⟩ : Fin (m + 3)) p
              (MultiPoly.yCoeffsAt_nonempty (⟨m + 2, by omega⟩ : Fin (m + 3)) p) x env]
        exact hlc0 x env
      have hne_trim : ∃ z, a < z ∧ z < b ∧
          (chainNFn (m + 3) (dropLeadingYAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p)).eval z ≠ 0 := by
        obtain ⟨z, hza, hzb, hzne⟩ := hne
        exact ⟨z, hza, hzb, by rw [← chainNFn_degreeYtop_trim_eval m p hlast z]; exact hzne⟩
      obtain ⟨N, hN⟩ := ih _ (chainN_degreeYtop_trim_order5p m p hd_pos) hne_trim
      refine ⟨N, fun zeros hnd hz => hN zeros hnd (fun z hzmem => ?_)⟩
      obtain ⟨ha, hb', hzero⟩ := hz z hzmem
      exact ⟨ha, hb', by rw [← chainNFn_degreeYtop_trim_eval m p hlast z]; exact hzero⟩
    · -- lcY_top p ≢ 0
      have hlcnz : canonZeroB (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) = false := by
        cases h : canonZeroB (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))
        · rfl
        · exact absurd (dropLastY_eval_zero_of_yfree
            (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)
            (MultiPoly.degreeY_leadingCoeffY _ _) ((canonZeroB_true_iff _).mp h)) hlc0
      rcases establish_hnz_or_trim m (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) hlcnz with hnz | ⟨q', hq'_eval, hq'_syn⟩
      · -- hnzTower : reduce
        rcases Classical.em (∀ z, a < z → z < b →
            (chainNFn (m + 3) (chainNReduce (m + 1) (fullMult (m + 1) p) p)).eval z = 0) with hrz | hrz
        · obtain ⟨z₀, hz₀a, hz₀b, hz₀ne⟩ := hne
          have hnoz := chainNFn_no_zeros_of_reduct_zero (m + 1) p a b hab hrz z₀ hz₀a hz₀b hz₀ne
          refine ⟨0, fun zeros _ hz => ?_⟩
          cases zeros with
          | nil => exact Nat.le_refl 0
          | cons z zs =>
            obtain ⟨ha, hb', hzero⟩ := hz z (List.mem_cons_self _ _)
            exact absurd hzero (hnoz z ha hb')
        · have hne' : ∃ z, a < z ∧ z < b ∧
              (chainNFn (m + 3) (chainNReduce (m + 1) (fullMult (m + 1) p) p)).eval z ≠ 0 :=
            Classical.byContradiction fun hcon =>
              hrz fun z hza hzb => Classical.byContradiction fun hz0 => hcon ⟨z, hza, hzb, hz0⟩
          obtain ⟨N, hN⟩ := ih _ (chainNReduce_order5p_hnz m p hnz) hne'
          exact ⟨N + 1, fun zeros hnd hz =>
            chainNFn_reduce_step (m + 1) p a b hab N hN zeros hnd hz⟩
      · -- trim : lift q' to p' = liftInner m p q' (eval-equal p, M5⁺ descends)
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
        have hne_lift : ∃ z, a < z ∧ z < b ∧ (chainNFn (m + 3) (liftInner m p q')).eval z ≠ 0 := by
          obtain ⟨z, hza, hzb, hzne⟩ := hne
          exact ⟨z, hza, hzb, by rw [heval z]; exact hzne⟩
        obtain ⟨N, hN⟩ := ih _ (liftInner_order5p m p q' hd_pos hq'_eval hq'_syn) hne_lift
        refine ⟨N, fun zeros hnd hz => hN zeros hnd (fun z hzmem => ?_)⟩
        obtain ⟨ha, hb', hzero⟩ := hz z hzmem
        exact ⟨ha, hb', by rw [heval z]; exact hzero⟩

/-- **The UNCONDITIONAL arbitrary-depth Khovanskii bound.** For all depths, every non-identically-zero
chain-`(m+2)` polynomial along the iterated-exponential tower has finitely many zeros — no
`zero_count_bound_classical`, no hypotheses. Outer induction on depth: base `chainNFn 2 = chain2Fn`
(definitionally) is the proven depth-2 bound; each step is `chainN_bound_step_uncond`. -/
theorem chainN_khovanskii_bound_unconditional :
    ∀ (m : Nat) (p : MultiPoly (m + 2)) (a b : Real), a < b →
      (∃ z, a < z ∧ z < b ∧ (chainNFn (m + 2) p).eval z ≠ 0) →
      ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (chainNFn (m + 2) p).eval z = 0) → zeros.length ≤ N := by
  intro m
  induction m with
  | zero =>
    intro p a b hab hne
    exact chain2_khovanskii_bound_unconditional p a b hab hne
  | succ m ih =>
    intro p a b hab hne
    exact chainN_bound_step_uncond m ih p a b hab hne

end MachLib.IterExpDepthN
