import MachLib.IterExpDepthNReduceStep

/-!
# Phase D (D3, reduce arm's "no zeros" branch) — the ∀N vehicle no-zeros lemma

`chainNFn_no_zeros_of_reduct_zero` — if the graded reduce value is `≡ 0` on `(a,b)` and `chainNFn p` is
nonzero at some `z₀ ∈ (a,b)`, then `chainNFn p` has NO zeros on `(a,b)`. The reduce-arm branch the WF
assembly takes when the reduce vanishes identically: the integrating-factor vehicle `V = chainNFn p · exp`
then has derivative `0` everywhere (its derivative factors through the reduce value), so `V` — hence
`chainNFn p`, which shares zeros with `V` — is constant and nonvanishing. One `mean_value_theorem`
application. Mirrors depth-3 `chain3Fn_no_zeros_of_reduct_zero`, ∀N. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpDepthNReduce

private theorem veh_factor_nz (f' E fv R : Real) :
    f' * E + fv * (E * (-R)) = E * (f' - R * fv) := by mach_mpoly [f', E, fv, R]

set_option maxHeartbeats 1600000 in
/-- **Vehicle no-zeros — chain-agnostic (ANY Pfaffian chain).** For any `PfaffianFn f` coherent on
`(a,b)`, if `f` satisfies the first-order linear ODE `f' = reductMult d c · f` on `(a,b)` (its
`chainTotalDerivative` equals `reductMult d c m` times `f`) and `f` is nonzero at some interior `z₀`,
then `f` has NO zeros on `(a,b)`. The integrating-factor vehicle `V = f · exp(vehExpo)` has derivative
`0` everywhere (it factors through the ODE residual), so `V` — and `f`, which shares zeros with `V` —
is constant and nonvanishing (one `mean_value_theorem`).

This is the **chain-independent heart** of the reduce arm's "no zeros" branch: it uses only general
`PfaffianFn` coherence + the general exponential (`Real.exp` positivity via `vehicleN_zero_iff`), never
the iterated-exponential structure. The ∀N corollary `chainNFn_no_zeros_of_reduct_zero` below is its
instantiation — the only iterated-exp-specific inputs are the chain's coherence
(`IterExpChain_isCoherentOn`) and the reduce→ODE identity. First brick of lifting the descent to
arbitrary Pfaffian chains. -/
theorem pfaffianFn_no_zeros_of_ode (f : PfaffianFn) (a b : Real) (hab : a < b)
    (d : Nat → Nat) (c : Real) (m : Nat)
    (hcoh : f.chain.IsCoherentOn a b)
    (h_ode : ∀ z, a < z → z < b →
      f.chainTotalDerivative.eval z - reductMult d c z m * f.eval z = 0)
    (z₀ : Real) (hz₀a : a < z₀) (hz₀b : z₀ < b) (hne₀ : f.eval z₀ ≠ 0) :
    ∀ z, a < z → z < b → f.eval z ≠ 0 := by
  have hVderiv : ∀ z, a < z → z < b →
      HasDerivAt (vehicleN f d c m) 0 z := by
    intro z hza hzb
    have hf : HasDerivAt f.eval (f.chainTotalDerivative.eval z) z :=
      hasDerivAt_eval_natural f z (hcoh z hza hzb)
    have hvm := hasDerivAt_vehicleN f d c m z hf
    have hred_z : f.chainTotalDerivative.eval z
        - reductMult d c z m * f.eval z = 0 := h_ode z hza hzb
    have hexpr : f.chainTotalDerivative.eval z
          * Real.exp (vehExpo d c m z)
        + f.eval z
          * (Real.exp (vehExpo d c m z)
            * vehExpoDeriv d c z m) = 0 := by
      rw [vehExpoDeriv_eq_neg_reductMult,
          veh_factor_nz (f.chainTotalDerivative.eval z)
            (Real.exp (vehExpo d c m z))
            (f.eval z) (reductMult d c z m),
          hred_z, MachLib.Real.mul_zero]
    rwa [hexpr] at hvm
  have hVeq : ∀ z₁ z₂, a < z₁ → z₂ < b → z₁ < z₂ →
      vehicleN f d c m z₁ = vehicleN f d c m z₂ := by
    intro z₁ z₂ hz₁a hz₂b hz₁z₂
    obtain ⟨cc, f', hcc1, hcc2, hderiv_cc, hmvt⟩ :=
      mean_value_theorem _ z₁ z₂ hz₁z₂
        (fun c' hc'1 hc'2 => ⟨0, hVderiv c' (lt_trans_ax hz₁a hc'1) (lt_trans_ax hc'2 hz₂b)⟩)
    have hf'0 : f' = 0 :=
      HasDerivAt_unique _ f' 0 cc hderiv_cc
        (hVderiv cc (lt_trans_ax hz₁a hcc1) (lt_trans_ax hcc2 hz₂b))
    rw [hf'0, zero_mul] at hmvt
    revert hmvt
    generalize vehicleN f d c m z₁ = v1
    generalize vehicleN f d c m z₂ = v2
    intro hmvt
    calc v1 = v2 - (v2 - v1) := by mach_ring
      _ = v2 - 0 := by rw [hmvt]
      _ = v2 := by mach_ring
  have hVz₀ : vehicleN f d c m z₀ ≠ 0 :=
    fun h => hne₀ ((vehicleN_zero_iff f d c m z₀).mp h)
  intro z hza hzb hz_zero
  have hVz : vehicleN f d c m z = 0 :=
    (vehicleN_zero_iff f d c m z).mpr hz_zero
  rcases lt_total z z₀ with hlt | heq | hgt
  · rw [hVeq z z₀ hza hz₀b hlt] at hVz; exact hVz₀ hVz
  · rw [heq] at hVz; exact hVz₀ hVz
  · rw [← hVeq z₀ z hz₀a hzb hgt] at hVz; exact hVz₀ hVz

set_option maxHeartbeats 1600000 in
/-- **The ∀N vehicle no-zeros lemma.** If the graded reduce value is `≡ 0` on `(a,b)` and `chainNFn p` is
nonzero at some interior `z₀`, then `chainNFn p` has no zeros on `(a,b)`. -/
theorem chainNFn_no_zeros_of_reduct_zero (k : Nat) (p : MultiPoly (k + 2)) (a b : Real) (hab : a < b)
    (h_reduct : ∀ z, a < z → z < b →
      (chainNFn (k + 2) (chainNReduce k (fullMult k p) p)).eval z = 0)
    (z₀ : Real) (hz₀a : a < z₀) (hz₀b : z₀ < b) (hne₀ : (chainNFn (k + 2) p).eval z₀ ≠ 0) :
    ∀ z, a < z → z < b → (chainNFn (k + 2) p).eval z ≠ 0 :=
  -- Instantiation of the chain-agnostic `pfaffianFn_no_zeros_of_ode`: the only
  -- iterated-exp-specific inputs are the chain's coherence and the reduce→ODE identity.
  pfaffianFn_no_zeros_of_ode (chainNFn (k + 2) p) a b hab (dExtract k p) (cExtract k p) (k + 1)
    (IterExpChain_isCoherentOn (k + 2) a b)
    (fun z hza hzb => by
      have h := h_reduct z hza hzb
      rw [chainNFn_reduce_eval, reductMultP_eq_reductMult k p z] at h
      exact h)
    z₀ hz₀a hz₀b hne₀

end MachLib.IterExpDepthN
