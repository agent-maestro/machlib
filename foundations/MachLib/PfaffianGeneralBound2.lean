import MachLib.PfaffianGeneralVehExpoConnect
import MachLib.PfaffianGeneralBaseHnz
import MachLib.PfaffianGeneralWF
import MachLib.ChainExp2Capstone
namespace MachLib.PfaffianGeneralVehExpo
open MachLib.Real MachLib.PfaffianChainMod MachLib.MultiPolyMod
open MachLib.PfaffianGeneralReduce MachLib.ChainExp2CanonMeasure MachLib.IterExpTopIdentity
open MachLib.ChainExp2NoZeros MachLib.ChainExp2Capstone MachLib.ChainExp2Trim
open MachLib.MultiPolyMod.MultiPoly MachLib.MultiPolyReconstruct

/-- The graded reduce degrees for depth-2: `deg ⟨1⟩ = degreeY₁ p`, `deg ⟨0⟩ = cdegY0(lcY₁ p)`. -/
noncomputable def bound2Deg (p : MultiPoly 2) : Fin 2 → Nat :=
  fun i => if i.val = 0 then cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)
           else MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p

/-- The depth-2 reduce multiplier `gradedMultStep G1 ⟨1⟩ p (cdegY0(lcY₁ p)·G0)`. -/
noncomputable def bound2Mult (G0 G1 p : MultiPoly 2) : MultiPoly 2 :=
  gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) p
    (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)))) G0)

set_option maxHeartbeats 1000000 in
/-- **The vehExpo integrating factor for the depth-2 reduce.** Combines brick 37 (HasDerivAt of the
log-vehExpo) with brick 38 (its derivative = −eval(reduce mult)): the log-vehExpo `E` satisfies
`E' = −(pfaffianChainFn c2 (reduce mult)).eval` on `(a,b)` — exactly the `hE` the no-zeros/Rolle arms need.
Needs positive coherence (`yᵢ>0`). -/
theorem hE_vehExpo_bound2 {c2 : PfaffianChain 2} (G0 G1 p : MultiPoly 2) (a b : Real)
    (hrel0 : c2.relations (⟨0, by omega⟩ : Fin 2) = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hrel1 : c2.relations (⟨1, by omega⟩ : Fin 2) = MultiPoly.mul G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))
    (hcoh : c2.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin 2, 0 < c2.evals i z) :
    ∀ z, a < z → z < b →
      HasDerivAt (logVehExpoAux c2 (bound2Deg p) 2 (Nat.le_refl 2))
        (-(pfaffianChainFn c2 (bound2Mult G0 G1 p)).eval z) z := by
  intro z hza hzb
  have h37 := HasDerivAt_logVehExpoAux c2 (bound2Deg p) z (hcoh z hza hzb) (hpos z hza hzb) 2 (Nat.le_refl 2)
  have h38 := logVehExpoDeriv2_eq_neg_reduceMult G0 G1 p z (bound2Deg p)
    (rfl) (rfl) hrel0 hrel1
    (ne_of_gt (hpos z hza hzb (⟨0, by omega⟩ : Fin 2)))
    (ne_of_gt (hpos z hza hzb (⟨1, by omega⟩ : Fin 2)))
  show HasDerivAt (logVehExpoAux c2 (bound2Deg p) 2 (Nat.le_refl 2))
    (-(pfaffianChainFn c2 (bound2Mult G0 G1 p)).eval z) z
  rw [show (bound2Mult G0 G1 p) = gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) p
        (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)))) G0) from rfl,
      ← h38]
  exact h37

set_option maxHeartbeats 2000000 in
/-- **The general depth-2 Khovanskii finiteness (with positive coherence).** For a positive-coherent
exp-chain `c2` of depth 2, any `p` not identically vanishing on `(a,b)` has finitely many zeros there.
Mirrors the iterated-exp `chain2_khovanskii_bound_unconditional`: WF recursion on `chain2OrderCanon`, 4-arm
dispatch — `lcY₁ p` canon-zero ∧ `degreeY₁=0` ⟹ `p≡0` (contradiction); canon-zero ∧ `degreeY₁>0` ⟹ trim;
else reduce, splitting on the reduct value: `≡0` ⟹ no zeros (vehicle, `pfaffianChainFn_no_zeros_of_reduct_
zero_gen` with `E`=the log-vehExpo, brick 37+38); `≢0` ⟹ recurse + Rolle (`pfaffianChainFn_reduce_step_gen`).
Discharges the flagship's `hBound2` — MODULO the positivity hypothesis (the honest new input, threaded through
the vehExpo). -/
theorem pfaffian_bound2_gen (c2 : PfaffianChain 2) (hexp : IsExpChain c2) (a b : Real) (hab : a < b)
    (hcoh : c2.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin 2, 0 < c2.evals i z)
    (p0 : MultiPoly 2) (hne0 : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c2 p0).eval z ≠ 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c2 p0).eval z = 0) → zeros.length ≤ N := by
  obtain ⟨⟨G0, hG0, hrel0⟩, htri0⟩ := hexp (⟨0, by omega⟩ : Fin 2)
  obtain ⟨⟨G1, hG1, hrel1⟩, _⟩ := hexp (⟨1, by omega⟩ : Fin 2)
  have hG0y1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) G0 = 0 := by
    have h := htri0 (⟨1, by omega⟩ : Fin 2) Nat.zero_lt_one
    rw [hrel0, degreeY_mul' (⟨1, by omega⟩ : Fin 2) G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))] at h
    omega
  have htri1 : ∀ (j : Fin 2), j ≠ (⟨1, by omega⟩ : Fin 2) →
      MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c2.relations j) = 0 := by
    intro j hj
    have hne1 : j.val ≠ 1 := fun h => hj (Fin.ext h)
    have hj0 : j = (⟨0, by omega⟩ : Fin 2) := by
      apply Fin.ext; show j.val = 0; have := j.isLt; omega
    rw [hj0]; exact htri0 (⟨1, by omega⟩ : Fin 2) Nat.zero_lt_one
  have hreltop1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c2.relations (⟨1, by omega⟩ : Fin 2)) = 1 := by
    rw [hrel1, degreeY_mul' (⟨1, by omega⟩ : Fin 2) G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)), hG1]
    show 0 + (if (⟨1, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) then 1 else 0) = 1
    rw [if_pos rfl]
  refine WellFounded.induction
    (C := fun q => (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c2 q).eval z ≠ 0) →
      ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c2 q).eval z = 0) → zeros.length ≤ N)
    chain2OrderCanon_wf p0 ?_ hne0
  clear hne0 p0
  intro p ih hne
  by_cases hcz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)).2 = 0
  · by_cases hd1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0
    · exfalso
      have hlcp : MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p = p :=
        leadingCoeffY_eq_self_of_degreeY_zero (⟨1, by omega⟩ : Fin 2) p hd1
      have hpz : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval p x env = 0 := by
        have h := smc2_zero_eval_zero (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)
          (MultiPoly.degreeY_leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) hcz
        rw [hlcp] at h; exact h
      obtain ⟨z, _, _, hzne⟩ := hne
      exact hzne (hpz z (c2.chainValues z))
    · have hlast : ∀ (x : Real) (env : Fin 2 → Real),
          MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨1, by omega⟩ : Fin 2) p).getLast
            (yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) p)) x env = 0 := by
        intro x env
        rw [← eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨1, by omega⟩ : Fin 2) p
              (yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) p) x env]
        exact smc2_zero_eval_zero (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)
          (MultiPoly.degreeY_leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) hcz x env
      have htrim_eval : ∀ z, (pfaffianChainFn c2 p).eval z
          = (pfaffianChainFn c2 (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)).eval z := fun z =>
        (eval_dropLeadingYAt_of_last_canonically_zero (⟨1, by omega⟩ : Fin 2) p
          (yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) p) hlast z (c2.chainValues z)).symm
      have hne_trim : ∃ z, a < z ∧ z < b ∧
          (pfaffianChainFn c2 (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)).eval z ≠ 0 := by
        obtain ⟨z, hza, hzb, hzne⟩ := hne
        exact ⟨z, hza, hzb, by rw [← htrim_eval z]; exact hzne⟩
      obtain ⟨N, hN⟩ := ih _ (chain2_trim_order p hd1) hne_trim
      refine ⟨N, fun zeros hnd hz => hN zeros hnd (fun z hzmem => ?_)⟩
      obtain ⟨ha, hb', hzero⟩ := hz z hzmem
      exact ⟨ha, hb', by rw [← htrim_eval z]; exact hzero⟩
  · have hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)).2 ≠ 0 := hcz
    rcases Classical.em (∀ z, a < z → z < b →
        (pfaffianChainFn c2 (chainReduce c2 (bound2Mult G0 G1 p) p)).eval z = 0) with hrz | hrz
    · obtain ⟨z₀, hz₀a, hz₀b, hz₀ne⟩ := hne
      have hnoz := pfaffianChainFn_no_zeros_of_reduct_zero_gen c2 (bound2Mult G0 G1 p) p a b hab
        (logVehExpoAux c2 (bound2Deg p) 2 (Nat.le_refl 2)) hcoh
        (hE_vehExpo_bound2 G0 G1 p a b hrel0 hrel1 hcoh hpos) hrz z₀ hz₀a hz₀b hz₀ne
      refine ⟨0, fun zeros _ hz => ?_⟩
      cases zeros with
      | nil => exact Nat.le_refl 0
      | cons z zs =>
        obtain ⟨ha, hb', hzero⟩ := hz z (List.mem_cons_self _ _)
        exact absurd hzero (hnoz z ha hb')
    · have hne' : ∃ z, a < z ∧ z < b ∧
          (pfaffianChainFn c2 (chainReduce c2 (bound2Mult G0 G1 p) p)).eval z ≠ 0 :=
        Classical.byContradiction fun hcon =>
          hrz fun z hza hzb => Classical.byContradiction fun hz0 => hcon ⟨z, hza, hzb, hz0⟩
      obtain ⟨N, hN⟩ := ih (chainReduce c2 (bound2Mult G0 G1 p) p)
        (chain2ReduceGen_nestedLT_canon_hnz G0 G1 hrel0 hG0 hG0y1 hrel1 hG1 htri1 hreltop1 p hnz) hne'
      refine ⟨N + 1, ?_⟩
      exact pfaffianChainFn_reduce_step_gen c2 (bound2Mult G0 G1 p) p a b hab
        (logVehExpoAux c2 (bound2Deg p) 2 (Nat.le_refl 2)) hcoh
        (hE_vehExpo_bound2 G0 G1 p a b hrel0 hrel1 hcoh hpos) N hN

end MachLib.PfaffianGeneralVehExpo
