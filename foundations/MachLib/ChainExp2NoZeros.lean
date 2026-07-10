import MachLib.ChainExp2Capstone
import MachLib.Rolle

/-!
# Removing `terminal_nonzero` — the vehicle no-zeros lemma

The chain-2 bound's `terminal_nonzero` hypothesis fails exactly for functions whose reduction reaches a
`≡ 0` reduct — e.g. a pure exponential `p = y₁` (which has 0 zeros). This file supplies the missing
argument: if the polynomial-multiplier reduce value is `≡ 0` on `(a,b)` and `p` is not identically zero
there, then `chain2Fn p` has **no zeros** on `(a,b)`. Reason: the integrating-factor vehicle
`vehicleM p = p·e^{−∫m}` has derivative `E·reduct ≡ 0`, so it is constant (mean value theorem); being
nonzero at one point, it is nonzero everywhere, and `E ≠ 0` forces `p ≠ 0`.

`#print axioms`-clean of `zero_count_bound_classical` (uses only `rolle`/MVT + `HasDerivAt`).
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

/-- The vehicle-derivative factoring `A·E + P·(E·(−nd·ez − cc)) = E·(A − (nd·ez + cc)·P)` (standalone so
`mach_mpoly` sees the atoms). -/
private theorem vehicle_deriv_factor (A P E ez nd cc : Real) :
    A * E + P * (E * ((-nd) * ez + (-cc))) = E * (A - (nd * ez + cc) * P) := by
  mach_mpoly [A, P, E, ez, nd, cc]

set_option maxHeartbeats 1600000 in
/-- **The vehicle no-zeros lemma.** If the poly-multiplier reduce value of `p` is `≡ 0` on `(a,b)` and
`chain2Fn p` is nonzero at some `z₀ ∈ (a,b)`, then `chain2Fn p` has no zeros on `(a,b)`. -/
theorem chain2Fn_no_zeros_of_reduct_zero (p : MultiPoly 2) (c : Real) (a b : Real) (hab : a < b)
    (h_reduct : ∀ z, a < z → z < b → (chain2Fn (chain2Reduce c p)).eval z = 0)
    (z₀ : Real) (hz₀a : a < z₀) (hz₀b : z₀ < b) (hne₀ : (chain2Fn p).eval z₀ ≠ 0) :
    ∀ z, a < z → z < b → (chain2Fn p).eval z ≠ 0 := by
  -- the integrating-factor vehicle for f = chain2Fn p, d = degreeY₁ p.
  let d := MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
  let V := vehicleM (chain2Fn p) d c
  -- V has zero derivative at every interior point.
  have hVderiv : ∀ z, a < z → z < b → HasDerivAt V 0 z := by
    intro z hza hzb
    have hf : HasDerivAt (chain2Fn p).eval ((chain2Fn p).chainTotalDerivative.eval z) z :=
      hasDerivAt_eval_natural (chain2Fn p) z (IterExpChain_isCoherentAt 2 z)
    have hvm := hasDerivAt_vehicleM (chain2Fn p) d c z hf
    -- the reduce value vanishes at z.
    have hred_z : (chain2Fn p).chainTotalDerivative.eval z
                    - (MachLib.Real.natCast d * Real.exp z + c) * (chain2Fn p).eval z = 0 := by
      have h := h_reduct z hza hzb
      rw [chain2Fn_chain2Reduce_eval] at h; exact h
    -- the derivative expression factors as `E · reduct`, hence 0.
    have hD0 : (chain2Fn p).chainTotalDerivative.eval z
                 * Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z)
               + (chain2Fn p).eval z
                 * (Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z)
                    * ((-MachLib.Real.natCast d) * Real.exp z + (-c))) = 0 := by
      have hfactor : (chain2Fn p).chainTotalDerivative.eval z
                 * Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z)
               + (chain2Fn p).eval z
                 * (Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z)
                    * ((-MachLib.Real.natCast d) * Real.exp z + (-c)))
             = Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z)
               * ((chain2Fn p).chainTotalDerivative.eval z
                   - (MachLib.Real.natCast d * Real.exp z + c) * (chain2Fn p).eval z) :=
        vehicle_deriv_factor ((chain2Fn p).chainTotalDerivative.eval z) ((chain2Fn p).eval z)
          (Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z)) (Real.exp z)
          (MachLib.Real.natCast d) c
      rw [hfactor, hred_z, MachLib.Real.mul_zero]
    rwa [hD0] at hvm
  -- V is constant on (a,b) (MVT + zero derivative).
  have hVeq : ∀ z₁ z₂, a < z₁ → z₂ < b → z₁ < z₂ → V z₁ = V z₂ := by
    intro z₁ z₂ hz₁a hz₂b hz₁z₂
    obtain ⟨cc, f', hcc1, hcc2, hderiv_cc, hmvt⟩ :=
      mean_value_theorem_ct V z₁ z₂ hz₁z₂
        (fun c' hc'1 hc'2 => ⟨0, hVderiv c' (lt_of_lt_of_le_r hz₁a hc'1) (lt_of_le_of_lt_r hc'2 hz₂b)⟩)
    have hf'0 : f' = 0 :=
      HasDerivAt_unique V f' 0 cc hderiv_cc
        (hVderiv cc (lt_trans_ax hz₁a hcc1) (lt_trans_ax hcc2 hz₂b))
    rw [hf'0, zero_mul] at hmvt
    -- hmvt : V z₂ - V z₁ = 0. abstract the vehicle values, then Real algebra.
    revert hmvt
    generalize V z₁ = v1
    generalize V z₂ = v2
    intro hmvt
    calc v1 = v2 - (v2 - v1) := by mach_ring
      _ = v2 - 0 := by rw [hmvt]
      _ = v2 := by mach_ring
  -- V z₀ ≠ 0.
  have hVz₀ : V z₀ ≠ 0 := fun h => hne₀ ((vehicleM_zero_iff (chain2Fn p) d c z₀).mp h)
  -- conclude: any z ∈ (a,b) with V z = V z₀ ≠ 0 has chain2Fn p .eval z ≠ 0.
  intro z hza hzb hz_zero
  have hVz : V z = 0 := (vehicleM_zero_iff (chain2Fn p) d c z).mpr hz_zero
  rcases lt_total z z₀ with hlt | heq | hgt
  · rw [hVeq z z₀ hza hz₀b hlt] at hVz; exact hVz₀ hVz
  · rw [heq] at hVz; exact hVz₀ hVz
  · rw [← hVeq z₀ z hz₀a hzb hgt] at hVz; exact hVz₀ hVz

/-! ### The unconditional chain-2 Khovanskii bound (non-vanishing hypothesis only) -/

/-- When `p` doesn't depend on `y_i`, its `y_i`-leading coefficient is `p` itself. -/
theorem leadingCoeffY_eq_self_of_degreeY_zero {n : Nat} (i : Fin n) (p : MultiPoly n)
    (hd : MultiPoly.degreeY i p = 0) : MultiPoly.leadingCoeffY i p = p := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY j =>
    show (if j = i then MultiPoly.const 1 else MultiPoly.varY j) = MultiPoly.varY j
    have hji : j ≠ i := by
      intro h; rw [h] at hd
      exact absurd hd (by show (if i = i then (1 : Nat) else 0) ≠ 0; rw [if_pos rfl]; decide)
    rw [if_neg hji]
  | add p q ihp ihq =>
    have hp : MultiPoly.degreeY i p = 0 := by
      have h' : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) = 0 := hd
      have hle : MultiPoly.degreeY i p ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) :=
        Nat.le_max_left _ _
      omega
    have hq : MultiPoly.degreeY i q = 0 := by
      have h' : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) = 0 := hd
      have hle : MultiPoly.degreeY i q ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) :=
        Nat.le_max_right _ _
      omega
    show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
          else if MultiPoly.degreeY i q > MultiPoly.degreeY i p then MultiPoly.leadingCoeffY i q
          else MultiPoly.add (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q))
         = MultiPoly.add p q
    rw [if_neg (by rw [hp, hq]; exact Nat.lt_irrefl 0),
        if_neg (by rw [hp, hq]; exact Nat.lt_irrefl 0), ihp hp, ihq hq]
  | sub p q ihp ihq =>
    have hp : MultiPoly.degreeY i p = 0 := by
      have h' : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) = 0 := hd
      have hle : MultiPoly.degreeY i p ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) :=
        Nat.le_max_left _ _
      omega
    have hq : MultiPoly.degreeY i q = 0 := by
      have h' : Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) = 0 := hd
      have hle : MultiPoly.degreeY i q ≤ Nat.max (MultiPoly.degreeY i p) (MultiPoly.degreeY i q) :=
        Nat.le_max_right _ _
      omega
    show (if MultiPoly.degreeY i p > MultiPoly.degreeY i q then MultiPoly.leadingCoeffY i p
          else if MultiPoly.degreeY i q > MultiPoly.degreeY i p
               then MultiPoly.sub (MultiPoly.const 0) (MultiPoly.leadingCoeffY i q)
               else MultiPoly.sub (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q))
         = MultiPoly.sub p q
    rw [if_neg (by rw [hp, hq]; exact Nat.lt_irrefl 0),
        if_neg (by rw [hp, hq]; exact Nat.lt_irrefl 0), ihp hp, ihq hq]
  | mul p q ihp ihq =>
    have hp : MultiPoly.degreeY i p = 0 := by
      have h' : MultiPoly.degreeY i p + MultiPoly.degreeY i q = 0 := hd; omega
    have hq : MultiPoly.degreeY i q = 0 := by
      have h' : MultiPoly.degreeY i p + MultiPoly.degreeY i q = 0 := hd; omega
    show MultiPoly.mul (MultiPoly.leadingCoeffY i p) (MultiPoly.leadingCoeffY i q)
       = MultiPoly.mul p q
    rw [ihp hp, ihq hq]

/-- **The unconditional chain-2 Khovanskii bound.** For every chain-2 `p` that is not identically zero on
`(a,b)`, the number of zeros of `chain2Fn p` on `(a,b)` is finitely bounded — with NO `terminal_nonzero`
hypothesis. `#print axioms`-clean of `zero_count_bound_classical`.

Well-founded recursion on `chain2OrderCanon`. Dispatch: `lcY₁ p` canonically zero and `degreeY₁ > 0` →
trim; `lcY₁ p` canonically zero and `degreeY₁ = 0` → `p ≡ 0`, contradicting non-vanishing; otherwise
reduce, splitting on whether the reduce value is `≡ 0` on `(a,b)` — if so, `p` has no zeros (the vehicle
argument, `chain2Fn_no_zeros_of_reduct_zero`); if not, recurse and add `1` (Rolle). -/
theorem chain2_khovanskii_bound_unconditional (p : MultiPoly 2) (a b : Real) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧ (chain2Fn p).eval z ≠ 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn p).eval z = 0) → zeros.length ≤ N := by
  refine WellFounded.induction
    (C := fun q => (∃ z, a < z ∧ z < b ∧ (chain2Fn q).eval z ≠ 0) →
      ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn q).eval z = 0) → zeros.length ≤ N)
    chain2OrderCanon_wf p ?_ hne
  clear hne p
  intro p ih hne
  by_cases hcz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)).2 = 0
  · -- lcY₁ p canonically zero.
    by_cases hd1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0
    · -- degreeY₁ = 0 ⇒ lcY₁ p = p ⇒ p ≡ 0, contradicting non-vanishing.
      exfalso
      have hlcp : MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p = p :=
        leadingCoeffY_eq_self_of_degreeY_zero (⟨1, by omega⟩ : Fin 2) p hd1
      have hpz : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval p x env = 0 := by
        have h := smc2_zero_eval_zero (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)
          (MultiPoly.degreeY_leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) hcz
        rw [hlcp] at h; exact h
      obtain ⟨z, _, _, hzne⟩ := hne
      exact hzne (hpz z ((IterExpChain 2).chainValues z))
    · -- degreeY₁ > 0: trim (eval-equal, degreeY₁ drops).
      have hne_trim : ∃ z, a < z ∧ z < b ∧
          (chain2Fn (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)).eval z ≠ 0 := by
        obtain ⟨z, hza, hzb, hzne⟩ := hne
        exact ⟨z, hza, hzb, by rw [← chain2_trim_eval p hcz z]; exact hzne⟩
      obtain ⟨N, hN⟩ := ih _ (chain2_trim_order p hd1) hne_trim
      refine ⟨N, fun zeros hnd hz => hN zeros hnd (fun z hzmem => ?_)⟩
      obtain ⟨ha, hb', hzero⟩ := hz z hzmem
      exact ⟨ha, hb', by rw [← chain2_trim_eval p hcz z]; exact hzero⟩
  · -- lcY₁ p not canonically zero: reduce.
    rcases Classical.em (∀ z, a < z → z < b →
        (chain2Fn (chain2Reduce (MachLib.Real.natCast
          (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))) p)).eval z = 0)
      with hrz | hrz
    · -- reduce value ≡ 0 ⇒ p has no zeros (vehicle argument).
      obtain ⟨z₀, hz₀a, hz₀b, hz₀ne⟩ := hne
      have hnoz := chain2Fn_no_zeros_of_reduct_zero p _ a b hab hrz z₀ hz₀a hz₀b hz₀ne
      refine ⟨0, fun zeros _ hz => ?_⟩
      cases zeros with
      | nil => exact Nat.le_refl 0
      | cons z zs =>
        obtain ⟨ha, hb', hzero⟩ := hz z (List.mem_cons_self _ _)
        exact absurd hzero (hnoz z ha hb')
    · -- reduce value ≢ 0: recurse and add 1 (Rolle).
      have hne' : ∃ z, a < z ∧ z < b ∧
          (chain2Fn (chain2Reduce (MachLib.Real.natCast
            (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))) p)).eval z ≠ 0 :=
        Classical.byContradiction fun hcon =>
          hrz fun z hza hzb =>
            Classical.byContradiction fun hz0 => hcon ⟨z, hza, hzb, hz0⟩
      obtain ⟨N, hN⟩ := ih _ (chain2Reduce_nestedLT_canon p hcz) hne'
      refine ⟨N + 1, fun zeros hnd hz => ?_⟩
      have hcoh : (chain2Fn p).chain.IsCoherentOn a b := IterExpChain_isCoherentOn 2 a b
      have hstep := zero_count_polyMultReduce_transfer (chain2Fn p)
        (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
        (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)))
        a b hab hcoh N
        (fun zeros' hnd' hz' => hN zeros' hnd' (fun z hzmem => by
          obtain ⟨ha, hb', hval⟩ := hz' z hzmem
          exact ⟨ha, hb', by rw [chain2Fn_chain2Reduce_eval]; exact hval⟩))
      exact hstep zeros hnd hz

end MachLib.ChainExp2NoZeros
