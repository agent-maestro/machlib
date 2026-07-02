import MachLib.IterExpDepthNCapstone
import MachLib.IterExpDepthNVehicleNoZeros
import MachLib.IterExpDepthNBaseArm
import MachLib.IterExpDepthNTrimArm

/-!
# Phase D (D3 step ii) — the ∀N WF assembly (conditional on the reduce-arm `Reducing` dispatch)

`chainN_bound_step` — the depth-`(m+3)` Khovanskii bound follows from the depth-`(m+2)` bound
(`IH_depth`, the outer depth-induction hypothesis) **modulo** one explicit hypothesis `hReducing`: that
whenever the four-way dispatch reaches the reduce arm (top `y`-degree nonzero, inner leading `y_{top-1}`-term
non-phantom), the projected inner `q := dropLastY(lcY_top p)` is `Reducing m`.

This wires ALL FOUR arms — base (`chainNFn_bound_of_degreeYtop_zero`), degree-trim
(`chainN_degreeYtop_trim_*`), inner-trim (`eval_innerTrimN` + `innerTrimN_order5`), reduce
(`chainNReduce_order5` + `chainNFn_reduce_step` / `chainNFn_no_zeros_of_reduct_zero`) — into a single
`WellFounded.induction` on `chainNOrder5`, exactly as the depth-3 `chain3_khovanskii_bound_unconditional`
(IterExpDepth3Bound). It confirms the four arms COMPOSE; the sole remaining obligation to make the bound
unconditional at every depth is discharging `hReducing` (the phantom-absorption lift — see the arc notes).

`#print axioms`-clean of `zero_count_bound_classical` (it is never used); the `Reducing` gap is an explicit
hypothesis, NOT a `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpDepthNReduce
open MachLib.ChainExp2Trim
open MachLib.ChainExp2NoZeros
open MachLib.MultiPolyReconstruct

/-- **The ∀N WF assembly, conditional on the reduce-arm `Reducing` dispatch.** Given the depth-`(m+2)` bound
`IH_depth` and the dispatch hypothesis `hReducing`, every non-identically-zero chain-`(m+3)` `p` has finitely
many zeros. Four dispatch arms via `WellFounded.induction` on `chainNOrder5 m`. -/
theorem chainN_bound_step (m : Nat)
    (IH_depth : ∀ (q : MultiPoly (m + 2)) (a' b' : Real), a' < b' →
        (∃ z, a' < z ∧ z < b' ∧ (chainNFn (m + 2) q).eval z ≠ 0) →
        ∃ M, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a' < z ∧ z < b' ∧ (chainNFn (m + 2) q).eval z = 0) → zeros.length ≤ M)
    (hReducing : ∀ (p : MultiPoly (m + 3)),
        MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p ≠ 0 →
        ¬(∀ (x : Real) (env : Fin (m + 3) → Real),
            MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨m + 1, by omega⟩ : Fin (m + 3))
              (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)).getLast
              (MultiPoly.yCoeffsAt_nonempty (⟨m + 1, by omega⟩ : Fin (m + 3))
                (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))) x env = 0) →
        Reducing m (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)))
    (p : MultiPoly (m + 3)) (a b : Real) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧ (chainNFn (m + 3) p).eval z ≠ 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (chainNFn (m + 3) p).eval z = 0) → zeros.length ≤ N := by
  refine WellFounded.induction
    (C := fun q => (∃ z, a < z ∧ z < b ∧ (chainNFn (m + 3) q).eval z ≠ 0) →
      ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (chainNFn (m + 3) q).eval z = 0) → zeros.length ≤ N)
    (chainNOrder5_wf m) p ?_ hne
  clear hne p
  intro p ih hne
  by_cases hd_top : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p = 0
  · -- Base arm: top variable absent ⟹ the depth-(m+2) bound (IH_depth).
    exact chainNFn_bound_of_degreeYtop_zero (m + 1) p hd_top a b hab hne IH_depth
  · by_cases hph : ∀ (x : Real) (env : Fin (m + 3) → Real),
        MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨m + 1, by omega⟩ : Fin (m + 3))
          (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨m + 1, by omega⟩ : Fin (m + 3))
            (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))) x env = 0
    · -- Inner leading y_{top-1}-term is phantom.
      by_cases hd1 : MultiPoly.degreeY (⟨m + 1, by omega⟩ : Fin (m + 3))
          (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p) = 0
      · -- degreeY_{top-1}(lcY_top p) = 0 ⟹ lcY_top p ≡ 0 ⟹ degree-trim.
        have hlc0 : ∀ (x : Real) (env : Fin (m + 3) → Real),
            MultiPoly.eval (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p) x env = 0 := by
          intro x env
          have hself := leadingCoeffY_eq_self_of_degreeY_zero (⟨m + 1, by omega⟩ : Fin (m + 3))
            (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p) hd1
          have hgl := eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general
            (⟨m + 1, by omega⟩ : Fin (m + 3))
            (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)
            (MultiPoly.yCoeffsAt_nonempty (⟨m + 1, by omega⟩ : Fin (m + 3))
              (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) x env
          rw [← hself, hgl]; exact hph x env
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
        obtain ⟨N, hN⟩ := ih _ (chainN_degreeYtop_trim_order5 m p (Nat.pos_of_ne_zero hd_top)) hne_trim
        refine ⟨N, fun zeros hnd hz => hN zeros hnd (fun z hzmem => ?_)⟩
        obtain ⟨ha, hb', hzero⟩ := hz z hzmem
        exact ⟨ha, hb', by rw [← chainNFn_degreeYtop_trim_eval m p hlast z]; exact hzero⟩
      · -- degreeY_{top-1}(lcY_top p) > 0 ⟹ inner-trim.
        have hd1pos : 0 < MultiPoly.degreeY (⟨m + 1, by omega⟩ : Fin (m + 3))
            (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p) := Nat.pos_of_ne_zero hd1
        have hd2pos : 0 < MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p :=
          Nat.pos_of_ne_zero hd_top
        have heval : ∀ z, (chainNFn (m + 3) (innerTrimN m p)).eval z = (chainNFn (m + 3) p).eval z :=
          fun z => eval_innerTrimN m p hph z ((IterExpChain (m + 3)).chainValues z)
        have hne_it : ∃ z, a < z ∧ z < b ∧ (chainNFn (m + 3) (innerTrimN m p)).eval z ≠ 0 := by
          obtain ⟨z, hza, hzb, hzne⟩ := hne
          exact ⟨z, hza, hzb, by rw [heval z]; exact hzne⟩
        obtain ⟨N, hN⟩ := ih _ (innerTrimN_order5 m p hd2pos hd1pos hph) hne_it
        refine ⟨N, fun zeros hnd hz => hN zeros hnd (fun z hzmem => ?_)⟩
        obtain ⟨ha, hb', hzero⟩ := hz z hzmem
        exact ⟨ha, hb', by rw [heval z]; exact hzero⟩
    · -- Inner leading y_{top-1}-term non-phantom ⟹ reduce.
      rcases Classical.em (∀ z, a < z → z < b →
          (chainNFn (m + 3) (chainNReduce (m + 1) (fullMult (m + 1) p) p)).eval z = 0) with hrz | hrz
      · -- reduce ≡ 0 ⟹ p has no zeros (vehicle argument).
        obtain ⟨z₀, hz₀a, hz₀b, hz₀ne⟩ := hne
        have hnoz := chainNFn_no_zeros_of_reduct_zero (m + 1) p a b hab hrz z₀ hz₀a hz₀b hz₀ne
        refine ⟨0, fun zeros _ hz => ?_⟩
        cases zeros with
        | nil => exact Nat.le_refl 0
        | cons z zs =>
          obtain ⟨ha, hb', hzero⟩ := hz z (List.mem_cons_self _ _)
          exact absurd hzero (hnoz z ha hb')
      · -- reduce ≢ 0 ⟹ recurse and add 1 (Rolle).
        have hne' : ∃ z, a < z ∧ z < b ∧
            (chainNFn (m + 3) (chainNReduce (m + 1) (fullMult (m + 1) p) p)).eval z ≠ 0 :=
          Classical.byContradiction fun hcon =>
            hrz fun z hza hzb =>
              Classical.byContradiction fun hz0 => hcon ⟨z, hza, hzb, hz0⟩
        obtain ⟨N, hN⟩ := ih _ (chainNReduce_order5 m p (hReducing p hd_top hph)) hne'
        exact ⟨N + 1, fun zeros hnd hz =>
          chainNFn_reduce_step (m + 1) p a b hab N hN zeros hnd hz⟩

/-- **The ∀N Khovanskii bound, conditional on the reduce-arm `Reducing` dispatch family.** By outer
induction on depth: the base `chainNFn 2 = chain2Fn` (definitionally) is the proven unconditional depth-2
bound; each step is `chainN_bound_step`. So — GIVEN `hRD` (the dispatch supplies `Reducing` in every reduce
arm at every depth) — every chain-`(m+2)` polynomial that is not identically zero on `(a,b)` has finitely
many zeros there, for ALL depths `m`. The single remaining obligation for the fully unconditional theorem
is discharging `hRD` (the phantom-absorption lift). `#print axioms`-clean of `zero_count_bound_classical`. -/
theorem chainN_khovanskii_bound_of_reducing
    (hRD : ∀ (m : Nat) (p : MultiPoly (m + 3)),
        MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p ≠ 0 →
        ¬(∀ (x : Real) (env : Fin (m + 3) → Real),
            MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨m + 1, by omega⟩ : Fin (m + 3))
              (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)).getLast
              (MultiPoly.yCoeffsAt_nonempty (⟨m + 1, by omega⟩ : Fin (m + 3))
                (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))) x env = 0) →
        Reducing m (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))) :
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
    exact chainN_bound_step m ih (hRD m) p a b hab hne

end MachLib.IterExpDepthN
