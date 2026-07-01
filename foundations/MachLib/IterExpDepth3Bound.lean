import MachLib.IterExpDepth3Capstone
import MachLib.IterExpDepth3Assembly
import MachLib.IterExpDepth3Rolle

/-!
# The unconditional depth-3 (triple-exponential) Khovanskii bound

`chain3_khovanskii_bound_unconditional` — for every `MultiPoly 3` `p` that is not identically zero on
`(a,b)`, the number of zeros of `chain3Fn p` (its evaluation along `IterExpChain 3`, i.e. `y₀ = eˣ`,
`y₁ = e^{eˣ}`, `y₂ = e^{e^{eˣ}}`) on `(a,b)` is finitely bounded — with NO `terminal_nonzero` hypothesis
and NO appeal to the Khovanskii-citation axiom `zero_count_bound_classical`.

Well-founded recursion on `chain3Order5` (the augmented `M5` measure), mirroring the depth-2
`chain2_khovanskii_bound_unconditional`, with four dispatch arms:

* `degreeY₂ p = 0` → the base bridge to the (proven) depth-2 bound;
* inner `q := dropLastY(lcY₂ p)` canonically-zero-leading (`hcz`) with `degreeY₁ q = 0` → `q ≡ 0` ⟹
  `lcY₂ p ≡ 0` → `degreeY₂`-trim;
* `hcz` with `degreeY₁ q > 0` → inner-trim (drop the phantom leading `y₁`-term of `lcY₂ p`);
* otherwise → reduce, splitting on whether the reduce value is `≡ 0` on `(a,b)`: if so, `p` has no zeros
  (the vehicle argument); if not, recurse and add `1` (Rolle).

Path B; no `sorry`; `#print axioms`-clean of `zero_count_bound_classical`.
-/

namespace MachLib.IterExpDepth3Bound

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpDepth3Descent
open MachLib.IterExpDepth3Vehicle
open MachLib.IterExpDepth3Rolle
open MachLib.IterExpDepth3Bridge
open MachLib.IterExpDepth3CdegY1
open MachLib.IterExpDepth3InnerTrim
open MachLib.IterExpDepth3Assembly
open MachLib.IterExpDepth3Capstone
open MachLib.ChainExp2Reducer
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2Capstone
open MachLib.ChainExp2NoZeros

/-- **The unconditional depth-3 Khovanskii bound.** For every chain-3 `p` nonzero at some interior point
of `(a,b)`, `chain3Fn p` has finitely many zeros there. `#print axioms`-clean of `zero_count_bound_classical`. -/
theorem chain3_khovanskii_bound_unconditional (p : MultiPoly 3) (a b : Real) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧ (chain3Fn p).eval z ≠ 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain3Fn p).eval z = 0) → zeros.length ≤ N := by
  refine WellFounded.induction
    (C := fun q => (∃ z, a < z ∧ z < b ∧ (chain3Fn q).eval z ≠ 0) →
      ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain3Fn q).eval z = 0) → zeros.length ≤ N)
    chain3Order5_wf p ?_ hne
  clear hne p
  intro p ih hne
  by_cases hd2 : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p = 0
  · -- Base: p is y₂-free ⟹ the depth-2 bound.
    exact chain3Fn_bound_of_degreeY2_zero p hd2 a b hab hne
  · by_cases hcz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
      (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)))).2 = 0
    · -- lcY₁ q canonically zero.
      have hlcq0 : ∀ (x : Real) (env : Fin 2 → Real),
          MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
            (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))) x env = 0 :=
        smc2_zero_eval_zero (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)))
          (MultiPoly.degreeY_leadingCoeffY _ _) hcz
      by_cases hd1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) = 0
      · -- degreeY₁ q = 0 ⟹ q ≡ 0 ⟹ lcY₂ p ≡ 0 ⟹ degreeY₂-trim.
        have hq0 : ∀ (x : Real) (env : Fin 2 → Real),
            MultiPoly.eval (MultiPoly.dropLastY
              (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) x env = 0 := by
          have hself := leadingCoeffY_eq_self_of_degreeY_zero (⟨1, by omega⟩ : Fin 2)
            (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) hd1
          intro x env; rw [← hself]; exact hlcq0 x env
        have hlc0 : ∀ (x : Real) (env : Fin 3 → Real),
            MultiPoly.eval (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p) x env = 0 :=
          dropLastY_eval_zero_of_yfree (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)
            (MultiPoly.degreeY_leadingCoeffY _ _) hq0
        have hlast : ∀ (x : Real) (env : Fin 3 → Real),
            MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
              (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p)) x env = 0 := by
          intro x env
          rw [← eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨2, by omega⟩ : Fin 3) p
                (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p) x env]
          exact hlc0 x env
        have hne_trim : ∃ z, a < z ∧ z < b ∧
            (chain3Fn (MachLib.ChainExp2Trim.dropLeadingYAt (⟨2, by omega⟩ : Fin 3) p)).eval z ≠ 0 := by
          obtain ⟨z, hza, hzb, hzne⟩ := hne
          exact ⟨z, hza, hzb, by rw [← chain3_degreeY2_trim_eval p hlast z]; exact hzne⟩
        obtain ⟨N, hN⟩ := ih _ (chain3_degreeY2_trim_order5 p hd2) hne_trim
        refine ⟨N, fun zeros hnd hz => hN zeros hnd (fun z hzmem => ?_)⟩
        obtain ⟨ha, hb', hzero⟩ := hz z hzmem
        exact ⟨ha, hb', by rw [← chain3_degreeY2_trim_eval p hlast z]; exact hzero⟩
      · -- degreeY₁ q > 0 ⟹ inner-trim.
        have hlcp0 : ∀ (x : Real) (env : Fin 3 → Real),
            MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3)
              (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) x env = 0 := by
          apply dropLastY_eval_zero_of_yfree
            (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 3)
              (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))
            (degreeY2_leadingCoeffY1_zero _ (MultiPoly.degreeY_leadingCoeffY _ _))
          intro x env2
          rw [dropLastY_leadingCoeffY1_commute (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)]
          exact hlcq0 x env2
        have h_phantom : ∀ (x : Real) (env : Fin 3 → Real),
            MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨1, by omega⟩ : Fin 3)
              (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)).getLast
              (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 3)
                (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))) x env = 0 := by
          intro x env
          rw [← eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨1, by omega⟩ : Fin 3)
                (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)
                (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 3)
                  (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) x env]
          exact hlcp0 x env
        have hd2pos : 0 < MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p := Nat.pos_of_ne_zero hd2
        have hd1pos : 0 < MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3)
            (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p) := by
          rw [← degreeY1_dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)]
          exact Nat.pos_of_ne_zero hd1
        have heval : ∀ z, (chain3Fn (innerTrim3 p)).eval z = (chain3Fn p).eval z := fun z =>
          eval_innerTrim3 p h_phantom z ((IterExpChain 3).chainValues z)
        have hne_it : ∃ z, a < z ∧ z < b ∧ (chain3Fn (innerTrim3 p)).eval z ≠ 0 := by
          obtain ⟨z, hza, hzb, hzne⟩ := hne
          exact ⟨z, hza, hzb, by rw [heval z]; exact hzne⟩
        obtain ⟨N, hN⟩ := ih _ (innerTrim3_order5 p hd2pos hd1pos h_phantom) hne_it
        refine ⟨N, fun zeros hnd hz => hN zeros hnd (fun z hzmem => ?_)⟩
        obtain ⟨ha, hb', hzero⟩ := hz z hzmem
        exact ⟨ha, hb', by rw [heval z]; exact hzero⟩
    · -- lcY₁ q not canonically zero: reduce.
      rcases Classical.em (∀ z, a < z → z < b →
          (chain3Fn (chain3Reduce (MachLib.Real.natCast (cdegY0
            (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
              (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))))) p)).eval z = 0)
        with hrz | hrz
      · -- reduce value ≡ 0 ⟹ p has no zeros (vehicle argument).
        obtain ⟨z₀, hz₀a, hz₀b, hz₀ne⟩ := hne
        have hnoz := chain3Fn_no_zeros_of_reduct_zero p _ a b hab hrz z₀ hz₀a hz₀b hz₀ne
        refine ⟨0, fun zeros _ hz => ?_⟩
        cases zeros with
        | nil => exact Nat.le_refl 0
        | cons z zs =>
          obtain ⟨ha, hb', hzero⟩ := hz z (List.mem_cons_self _ _)
          exact absurd hzero (hnoz z ha hb')
      · -- reduce value ≢ 0: recurse and add 1 (Rolle).
        have hne' : ∃ z, a < z ∧ z < b ∧
            (chain3Fn (chain3Reduce (MachLib.Real.natCast (cdegY0
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
                (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))))) p)).eval z ≠ 0 :=
          Classical.byContradiction fun hcon =>
            hrz fun z hza hzb =>
              Classical.byContradiction fun hz0 => hcon ⟨z, hza, hzb, hz0⟩
        obtain ⟨N, hN⟩ := ih _ (chain3Reduce_order5_hnz p hcz) hne'
        exact ⟨N + 1, fun zeros hnd hz =>
          chain3Fn_reduce_step _ p a b hab N hN zeros hnd hz⟩

end MachLib.IterExpDepth3Bound
