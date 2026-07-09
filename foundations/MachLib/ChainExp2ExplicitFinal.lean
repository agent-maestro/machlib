import MachLib.ChainExp2NoZeros
import MachLib.ChainExp2ExplicitABound
import MachLib.ChainExp2ExplicitLevelBudget

/-!
# The EXPLICIT chain-2 Khovanskii bound

`chain2_khovanskii_bound_unconditional` (`ChainExp2NoZeros`) gives `∃ N, zeros.length ≤ N`. This closes
the explicit-bound program: an EXPLICIT `N(degrees)` via the level-indexed recurrence.

`chain2_khovanskii_bound_explicit`: for every chain-2 `p` with `degreeX p ≤ Dx`, the number of zeros of
`chain2Fn p` on `(a,b)` is `≤ levelBudget-based invPhi` in the degrees of `p`:

    zeros.length ≤ invPhi (Dx+2) (degreeY₁ p) (innerRank (Dx+2) p) (degreeY₀ p).

Proof: the SAME well-founded recursion as the existential version, but carrying the invariant
`zeros(q) ≤ invPhi B (degreeY₁ q) (innerRank B q) (degreeY₀ q)` (B := Dx+2) instead of `∃ N`, with a
`degreeX q ≤ Dx` invariant threaded (degreeX is non-increasing under both arms). Each arm discharges by
the machine-checked closure lemmas:
  * reduce → `invPhi_reduce`, citing `innerRank_reduce_lt` (ir drops) + `degreeY0_chain2Reduce_le` (g+1)
    + the Rolle transfer `zero_count_polyMultReduce_transfer`;
  * trim   → `invPhi_trim_any`, citing `degreeY0_dropLeadingYAt1_le` (g'≤g) + `innerRank_succ_le` (hir)
    + trim eval-preservation `chain2_trim_eval`;
  * vehicle → 0.
`b(q) ≤ B` throughout via the bridge `singleExpMeasureCanon_snd_le` + `degreeX q ≤ Dx`.

sorryAx-free, and — like the existential version — free of the classical `zero_count_bound_classical`.
-/

namespace MachLib.ChainExp2NoZeros

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2Reducer
open MachLib.ChainExp2PolyMultRolle
open MachLib.ChainExp2Bound
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2PhantomDescent
open MachLib.ChainExp2Capstone
open MachLib.ChainExp2Explicit MachLib.ExplicitBound

/-- **The explicit chain-2 Khovanskii bound.** `zeros.length ≤ invPhi (Dx+2) (degreeY₁ p)
(innerRank (Dx+2) p) (degreeY₀ p)` for every chain-2 `p` with `degreeX p ≤ Dx` not identically zero on
`(a,b)`. The explicit `N(degrees)` — closing the explicit-bound program. -/
theorem chain2_khovanskii_bound_explicit (Dx : Nat) (a b : Real) (hab : a < b) :
    ∀ (p : MultiPoly 2), MultiPoly.degreeX p ≤ Dx →
      (∃ z, a < z ∧ z < b ∧ (chain2Fn p).eval z ≠ 0) →
      ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn p).eval z = 0) →
        zeros.length ≤ invPhi (Dx + 2) (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
          (innerRank (Dx + 2) p) (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p) := by
  -- b(q) ≤ Dx+2 whenever degreeX q ≤ Dx (the bridge)
  have hbnd : ∀ q : MultiPoly 2, MultiPoly.degreeX q ≤ Dx →
      (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 ≤ Dx + 2 :=
    fun q h => Nat.le_trans (singleExpMeasureCanon_snd_le q) (Nat.add_le_add_right h 2)
  intro p
  refine WellFounded.induction
    (C := fun q => MultiPoly.degreeX q ≤ Dx →
      (∃ z, a < z ∧ z < b ∧ (chain2Fn q).eval z ≠ 0) →
      ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn q).eval z = 0) →
        zeros.length ≤ invPhi (Dx + 2) (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q)
          (innerRank (Dx + 2) q) (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q))
    chain2OrderCanon_wf p ?_
  clear p
  intro p ih hdx hne zeros hnd hz
  by_cases hcz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)).2 = 0
  · -- lcY₁ p canonically zero
    by_cases hd1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0
    · -- degreeY₁ = 0 ⇒ p ≡ 0, contradicting non-vanishing
      exfalso
      have hlcp : MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p = p :=
        leadingCoeffY_eq_self_of_degreeY_zero (⟨1, by omega⟩ : Fin 2) p hd1
      have hpz : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval p x env = 0 := by
        have h := smc2_zero_eval_zero (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)
          (MultiPoly.degreeY_leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) hcz
        rw [hlcp] at h; exact h
      obtain ⟨z, _, _, hzne⟩ := hne
      exact hzne (hpz z ((IterExpChain 2).chainValues z))
    · -- degreeY₁ > 0: TRIM (q' := dropLeadingYAt ⟨1⟩ p, inlined — `set` is a Mathlib tactic)
      have hne_trim : ∃ z, a < z ∧ z < b ∧
          (chain2Fn (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)).eval z ≠ 0 := by
        obtain ⟨z, hza, hzb, hzne⟩ := hne
        exact ⟨z, hza, hzb, by rw [← chain2_trim_eval p hcz z]; exact hzne⟩
      have hdx' : MultiPoly.degreeX (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)
          ≤ Dx := Nat.le_trans (degreeX_dropLeadingYAt_le (⟨1, by omega⟩ : Fin 2) p) hdx
      have hzeros' : ∀ z ∈ zeros, a < z ∧ z < b ∧
          (chain2Fn (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)).eval z = 0 :=
        fun z hzmem => by
          obtain ⟨ha, hb', hzero⟩ := hz z hzmem
          exact ⟨ha, hb', by rw [← chain2_trim_eval p hcz z]; exact hzero⟩
      have hlen := ih (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)
        (chain2_trim_order p hd1) hdx' hne_trim zeros hnd hzeros'
      obtain ⟨d, hd⟩ : ∃ d, MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = d + 1 :=
        ⟨MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p - 1, by omega⟩
      have hdrop_lt : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
            (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)
          < MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p :=
        MachLib.ChainExp2Trim.degreeY_dropLeadingYAt_lt (⟨1, by omega⟩ : Fin 2) p (by omega)
      have htrim := invPhi_trim_any (Dx + 2) d
        (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
          (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p))
        (innerRank (Dx + 2) p)
        (innerRank (Dx + 2) (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p))
        (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p)
        (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2)
          (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p))
        (by omega) (degreeY0_dropLeadingYAt1_le p)
        (Nat.le_trans
          (innerRank_succ_le (Dx + 2)
            (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p) (hbnd _ hdx'))
          (Nat.mul_le_mul (Nat.add_le_add_right (degreeY0_dropLeadingYAt1_le p) 1) (Nat.le_refl _)))
      rw [hd]
      exact Nat.le_trans hlen htrim
  · -- lcY₁ p not canonically zero: REDUCE
    let c := MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))
    rcases Classical.em (∀ z, a < z → z < b → (chain2Fn (chain2Reduce c p)).eval z = 0) with hrz | hrz
    · -- vehicle: reduce ≡ 0 ⇒ p has no zeros
      obtain ⟨z₀, hz₀a, hz₀b, hz₀ne⟩ := hne
      have hnoz := chain2Fn_no_zeros_of_reduct_zero p _ a b hab hrz z₀ hz₀a hz₀b hz₀ne
      cases zeros with
      | nil => exact Nat.zero_le _
      | cons z zs =>
        obtain ⟨ha, hb', hzero⟩ := hz z (List.mem_cons_self _ _)
        exact absurd hzero (hnoz z ha hb')
    · -- reduce ≢ 0: recurse and add 1 (Rolle)
      have hne' : ∃ z, a < z ∧ z < b ∧ (chain2Fn (chain2Reduce c p)).eval z ≠ 0 :=
        Classical.byContradiction fun hcon =>
          hrz fun z hza hzb => Classical.byContradiction fun hz0 => hcon ⟨z, hza, hzb, hz0⟩
      have hdxr : MultiPoly.degreeX (chain2Reduce c p) ≤ Dx :=
        Nat.le_trans (degreeX_chain2Reduce_le c p) hdx
      have hN := ih (chain2Reduce c p) (chain2Reduce_nestedLT_canon p hcz) hdxr hne'
      -- degreeY₁ preserved by reduce
      have hfst : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (chain2Reduce c p)
          = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p :=
        chain2MeasureCanon_fst_chain2Reduce c p
      have hcoh : (chain2Fn p).chain.IsCoherentOn a b := IterExpChain_isCoherentOn 2 a b
      have hstep := zero_count_polyMultReduce_transfer (chain2Fn p)
        (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p) c a b hab hcoh
        (invPhi (Dx + 2) (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (chain2Reduce c p))
          (innerRank (Dx + 2) (chain2Reduce c p))
          (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chain2Reduce c p)))
        (fun zeros' hnd' hz' => hN zeros' hnd' (fun z hzmem => by
          obtain ⟨ha, hb', hval⟩ := hz' z hzmem
          exact ⟨ha, hb', by rw [chain2Fn_chain2Reduce_eval]; exact hval⟩))
      have hqbound := hstep zeros hnd hz
      -- hqbound : zeros.length ≤ invPhi (Dx+2) (degreeY₁ reduce) (ir reduce) (degreeY₀ reduce) + 1
      have hred := invPhi_reduce (Dx + 2) (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
        (innerRank (Dx + 2) p) (innerRank (Dx + 2) (chain2Reduce c p))
        (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p)
        (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chain2Reduce c p))
        (innerRank_reduce_lt (Dx + 2) p hcz (hbnd (chain2Reduce c p) hdxr))
        (degreeY0_chain2Reduce_le c p)
      rw [hfst] at hqbound
      exact Nat.le_trans hqbound hred

end MachLib.ChainExp2NoZeros
