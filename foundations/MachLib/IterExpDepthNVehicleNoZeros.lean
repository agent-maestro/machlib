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

/-- Ring identity behind the general integrating-factor vehicle. -/
private theorem veh_factor_gen (f' E fv M : Real) :
    f' * E + fv * (E * M) = E * (f' + M * fv) := by mach_mpoly [f', E, fv, M]

/-- **General integrating-factor vehicle:** `f.eval x · exp(E x)` for an ARBITRARY exponent `E`.
Unlike `vehicleN`, the exponent is not tied to the iterated-exponential `vehExpo` — any `E` with the
right derivative works, which is exactly what a general Pfaffian chain must supply. -/
noncomputable def vehicleGen (f : PfaffianFn) (E : Real → Real) : Real → Real :=
  fun x => f.eval x * Real.exp (E x)

/-- The general vehicle vanishes exactly where `f` does (`exp > 0`). -/
theorem vehicleGen_zero_iff (f : PfaffianFn) (E : Real → Real) (x : Real) :
    vehicleGen f E x = 0 ↔ f.eval x = 0 := by
  show f.eval x * Real.exp (E x) = 0 ↔ f.eval x = 0
  constructor
  · intro h; rw [mul_comm] at h; exact mul_eq_zero_of_factor_ne_zero (exp_ne_zero _) h
  · intro h; rw [h, zero_mul]

/-- Product/chain rule for the general vehicle: given `f' = chainTotalDerivative.eval` and `E' = M`,
`(f·exp E)' = f'·exp E + f·(exp E · M)`. -/
theorem hasDerivAt_vehicleGen (f : PfaffianFn) (E : Real → Real) (M : Real) (x : Real)
    (hf : HasDerivAt f.eval (f.chainTotalDerivative.eval x) x)
    (hE : HasDerivAt E M x) :
    HasDerivAt (vehicleGen f E)
      (f.chainTotalDerivative.eval x * Real.exp (E x)
        + f.eval x * (Real.exp (E x) * M)) x := by
  have hEc := HasDerivAt_comp Real.exp E M (Real.exp (E x)) x hE (HasDerivAt_exp _)
  exact HasDerivAt_mul f.eval (fun y => Real.exp (E y))
    (f.chainTotalDerivative.eval x) (Real.exp (E x) * M) x hf hEc

set_option maxHeartbeats 1600000 in
/-- **Vehicle no-zeros — chain-AND-multiplier agnostic.** For any `PfaffianFn f` coherent on `(a,b)`,
if there is an integrating-factor exponent `E` with `E' = M` on `(a,b)`, `f` satisfies the linear ODE
`f' + M·f = 0` there, and `f z₀ ≠ 0`, then `f` has NO zeros on `(a,b)`. The vehicle `f·exp(E)` has
derivative `exp(E)·(f' + M·f) = 0`, so it is constant and (since `exp > 0`) nonvanishing. This isolates
the SOLE analytic requirement a general Pfaffian chain must meet for the reduce arm's no-zeros branch:
an antiderivative `E` of the reduce multiplier. `pfaffianFn_no_zeros_of_ode` below is the special case
`E := vehExpo`, `M := vehExpoDeriv = −reductMult` (the iterated-exponential integrating factor). -/
theorem pfaffianFn_no_zeros_of_ode_gen (f : PfaffianFn) (a b : Real) (hab : a < b)
    (E : Real → Real) (M : Real → Real)
    (hcoh : f.chain.IsCoherentOn a b)
    (hE : ∀ z, a < z → z < b → HasDerivAt E (M z) z)
    (h_ode : ∀ z, a < z → z < b →
      f.chainTotalDerivative.eval z + M z * f.eval z = 0)
    (z₀ : Real) (hz₀a : a < z₀) (hz₀b : z₀ < b) (hne₀ : f.eval z₀ ≠ 0) :
    ∀ z, a < z → z < b → f.eval z ≠ 0 := by
  have hVderiv : ∀ z, a < z → z < b → HasDerivAt (vehicleGen f E) 0 z := by
    intro z hza hzb
    have hf : HasDerivAt f.eval (f.chainTotalDerivative.eval z) z :=
      hasDerivAt_eval_natural f z (hcoh z hza hzb)
    have hvm := hasDerivAt_vehicleGen f E (M z) z hf (hE z hza hzb)
    have hexpr : f.chainTotalDerivative.eval z * Real.exp (E z)
        + f.eval z * (Real.exp (E z) * M z) = 0 := by
      rw [veh_factor_gen (f.chainTotalDerivative.eval z) (Real.exp (E z)) (f.eval z) (M z),
          h_ode z hza hzb, MachLib.Real.mul_zero]
    rwa [hexpr] at hvm
  have hVeq : ∀ z₁ z₂, a < z₁ → z₂ < b → z₁ < z₂ →
      vehicleGen f E z₁ = vehicleGen f E z₂ := by
    intro z₁ z₂ hz₁a hz₂b hz₁z₂
    obtain ⟨cc, f', hcc1, hcc2, hderiv_cc, hmvt⟩ :=
      mean_value_theorem _ z₁ z₂ hz₁z₂
        (fun c' hc'1 hc'2 => ⟨0, hVderiv c' (lt_trans_ax hz₁a hc'1) (lt_trans_ax hc'2 hz₂b)⟩)
    have hf'0 : f' = 0 :=
      HasDerivAt_unique _ f' 0 cc hderiv_cc
        (hVderiv cc (lt_trans_ax hz₁a hcc1) (lt_trans_ax hcc2 hz₂b))
    rw [hf'0, zero_mul] at hmvt
    revert hmvt
    generalize vehicleGen f E z₁ = v1
    generalize vehicleGen f E z₂ = v2
    intro hmvt
    calc v1 = v2 - (v2 - v1) := by mach_ring
      _ = v2 - 0 := by rw [hmvt]
      _ = v2 := by mach_ring
  have hVz₀ : vehicleGen f E z₀ ≠ 0 :=
    fun h => hne₀ ((vehicleGen_zero_iff f E z₀).mp h)
  intro z hza hzb hz_zero
  have hVz : vehicleGen f E z = 0 := (vehicleGen_zero_iff f E z).mpr hz_zero
  rcases lt_total z z₀ with hlt | heq | hgt
  · rw [hVeq z z₀ hza hz₀b hlt] at hVz; exact hVz₀ hVz
  · rw [heq] at hVz; exact hVz₀ hVz
  · rw [← hVeq z₀ z hz₀a hzb hgt] at hVz; exact hVz₀ hVz

set_option maxHeartbeats 1600000 in
/-- **Vehicle no-zeros — chain-agnostic (ANY Pfaffian chain).** For any `PfaffianFn f` coherent on
`(a,b)`, if `f` satisfies the first-order linear ODE `f' = reductMult d c · f` on `(a,b)` (its
`chainTotalDerivative` equals `reductMult d c m` times `f`) and `f` is nonzero at some interior `z₀`,
then `f` has NO zeros on `(a,b)`. The integrating-factor vehicle `V = f · exp(vehExpo)` has derivative
`0` everywhere (it factors through the ODE residual), so `V` — and `f`, which shares zeros with `V` —
is constant and nonvanishing (one `mean_value_theorem`).

The `reductMult`/`vehExpo` here are the *iterated-exponential* integrating factor; this lemma is the
`E := vehExpo` special case of `pfaffianFn_no_zeros_of_ode_gen` above, which abstracts the exponent to
an ARBITRARY antiderivative `E` of the multiplier and is the truly chain-independent heart. The ∀N
corollary `chainNFn_no_zeros_of_reduct_zero` below instantiates *this* one; its only iterated-exp-
specific inputs are the chain's coherence (`IterExpChain_isCoherentOn`) and the reduce→ODE identity. -/
theorem pfaffianFn_no_zeros_of_ode (f : PfaffianFn) (a b : Real) (hab : a < b)
    (d : Nat → Nat) (c : Real) (m : Nat)
    (hcoh : f.chain.IsCoherentOn a b)
    (h_ode : ∀ z, a < z → z < b →
      f.chainTotalDerivative.eval z - reductMult d c z m * f.eval z = 0)
    (z₀ : Real) (hz₀a : a < z₀) (hz₀b : z₀ < b) (hne₀ : f.eval z₀ ≠ 0) :
    ∀ z, a < z → z < b → f.eval z ≠ 0 :=
  -- Special case of the chain-AND-multiplier-agnostic `pfaffianFn_no_zeros_of_ode_gen`:
  -- exponent `E := vehExpo d c m`, multiplier `M := vehExpoDeriv d c · m = −reductMult d c · m`.
  pfaffianFn_no_zeros_of_ode_gen f a b hab (vehExpo d c m) (fun z => vehExpoDeriv d c z m) hcoh
    (fun z _ _ => HasDerivAt_vehExpo d c z m)
    (fun z hza hzb => by
      show f.chainTotalDerivative.eval z + vehExpoDeriv d c z m * f.eval z = 0
      have h := h_ode z hza hzb
      rw [vehExpoDeriv_eq_neg_reductMult]
      have hring : f.chainTotalDerivative.eval z + (- reductMult d c z m) * f.eval z
          = f.chainTotalDerivative.eval z - reductMult d c z m * f.eval z := by
        mach_mpoly [f.chainTotalDerivative.eval z, reductMult d c z m, f.eval z]
      rw [hring]; exact h)
    z₀ hz₀a hz₀b hne₀

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
