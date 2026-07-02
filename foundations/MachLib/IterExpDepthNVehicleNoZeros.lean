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
/-- **The ∀N vehicle no-zeros lemma.** If the graded reduce value is `≡ 0` on `(a,b)` and `chainNFn p` is
nonzero at some interior `z₀`, then `chainNFn p` has no zeros on `(a,b)`. -/
theorem chainNFn_no_zeros_of_reduct_zero (k : Nat) (p : MultiPoly (k + 2)) (a b : Real) (hab : a < b)
    (h_reduct : ∀ z, a < z → z < b →
      (chainNFn (k + 2) (chainNReduce k (fullMult k p) p)).eval z = 0)
    (z₀ : Real) (hz₀a : a < z₀) (hz₀b : z₀ < b) (hne₀ : (chainNFn (k + 2) p).eval z₀ ≠ 0) :
    ∀ z, a < z → z < b → (chainNFn (k + 2) p).eval z ≠ 0 := by
  have hVderiv : ∀ z, a < z → z < b →
      HasDerivAt (vehicleN (chainNFn (k + 2) p) (dExtract k p) (cExtract k p) (k + 1)) 0 z := by
    intro z hza hzb
    have hf : HasDerivAt (chainNFn (k + 2) p).eval
        ((chainNFn (k + 2) p).chainTotalDerivative.eval z) z :=
      hasDerivAt_eval_natural (chainNFn (k + 2) p) z
        ((IterExpChain_isCoherentOn (k + 2) a b) z hza hzb)
    have hvm := hasDerivAt_vehicleN (chainNFn (k + 2) p) (dExtract k p) (cExtract k p) (k + 1) z hf
    have hred_z : (chainNFn (k + 2) p).chainTotalDerivative.eval z
        - reductMult (dExtract k p) (cExtract k p) z (k + 1) * (chainNFn (k + 2) p).eval z = 0 := by
      have h := h_reduct z hza hzb
      rw [chainNFn_reduce_eval, reductMultP_eq_reductMult k p z] at h
      exact h
    have hexpr : (chainNFn (k + 2) p).chainTotalDerivative.eval z
          * Real.exp (vehExpo (dExtract k p) (cExtract k p) (k + 1) z)
        + (chainNFn (k + 2) p).eval z
          * (Real.exp (vehExpo (dExtract k p) (cExtract k p) (k + 1) z)
            * vehExpoDeriv (dExtract k p) (cExtract k p) z (k + 1)) = 0 := by
      rw [vehExpoDeriv_eq_neg_reductMult,
          veh_factor_nz ((chainNFn (k + 2) p).chainTotalDerivative.eval z)
            (Real.exp (vehExpo (dExtract k p) (cExtract k p) (k + 1) z))
            ((chainNFn (k + 2) p).eval z) (reductMult (dExtract k p) (cExtract k p) z (k + 1)),
          hred_z, MachLib.Real.mul_zero]
    rwa [hexpr] at hvm
  have hVeq : ∀ z₁ z₂, a < z₁ → z₂ < b → z₁ < z₂ →
      vehicleN (chainNFn (k + 2) p) (dExtract k p) (cExtract k p) (k + 1) z₁
      = vehicleN (chainNFn (k + 2) p) (dExtract k p) (cExtract k p) (k + 1) z₂ := by
    intro z₁ z₂ hz₁a hz₂b hz₁z₂
    obtain ⟨cc, f', hcc1, hcc2, hderiv_cc, hmvt⟩ :=
      mean_value_theorem _ z₁ z₂ hz₁z₂
        (fun c' hc'1 hc'2 => ⟨0, hVderiv c' (lt_trans_ax hz₁a hc'1) (lt_trans_ax hc'2 hz₂b)⟩)
    have hf'0 : f' = 0 :=
      HasDerivAt_unique _ f' 0 cc hderiv_cc
        (hVderiv cc (lt_trans_ax hz₁a hcc1) (lt_trans_ax hcc2 hz₂b))
    rw [hf'0, zero_mul] at hmvt
    revert hmvt
    generalize vehicleN (chainNFn (k + 2) p) (dExtract k p) (cExtract k p) (k + 1) z₁ = v1
    generalize vehicleN (chainNFn (k + 2) p) (dExtract k p) (cExtract k p) (k + 1) z₂ = v2
    intro hmvt
    calc v1 = v2 - (v2 - v1) := by mach_ring
      _ = v2 - 0 := by rw [hmvt]
      _ = v2 := by mach_ring
  have hVz₀ : vehicleN (chainNFn (k + 2) p) (dExtract k p) (cExtract k p) (k + 1) z₀ ≠ 0 :=
    fun h => hne₀ ((vehicleN_zero_iff (chainNFn (k + 2) p) (dExtract k p) (cExtract k p) (k + 1) z₀).mp h)
  intro z hza hzb hz_zero
  have hVz : vehicleN (chainNFn (k + 2) p) (dExtract k p) (cExtract k p) (k + 1) z = 0 :=
    (vehicleN_zero_iff (chainNFn (k + 2) p) (dExtract k p) (cExtract k p) (k + 1) z).mpr hz_zero
  rcases lt_total z z₀ with hlt | heq | hgt
  · rw [hVeq z z₀ hza hz₀b hlt] at hVz; exact hVz₀ hVz
  · rw [heq] at hVz; exact hVz₀ hVz
  · rw [← hVeq z₀ z hz₀a hzb hgt] at hVz; exact hVz₀ hVz

end MachLib.IterExpDepthN
