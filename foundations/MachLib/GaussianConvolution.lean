import MachLib.GaussianConjugacy

/-!
# Sum of independent Gaussians — the convolution (probability frontier)

`X ~ N(μ₁,σ₁²)` and `Y ~ N(μ₂,σ₂²)` independent ⇒ `X + Y ~ N(μ₁+μ₂, σ₁²+σ₂²)`. The density of the
sum is the convolution `∫ gaussianDensity μ₁ σ₁² x · gaussianDensity μ₂ σ₂² (z-x) dx`, and it equals
`gaussianDensity (μ₁+μ₂) (σ₁²+σ₂²) z`.

This is a corollary of the marginal-is-Gaussian result (`jointDensity_marginal_tendsto`): that proved
the noise-mean-0 case (`Y = X + N`, `N ~ N(0,r²)`, marginal `N(μ, σ²+r²)`). A mean shift by `μ₂`
reduces the general case to it — `gaussianDensity μ₂ σ₂² (z-x) = gaussianDensity 0 σ₂² ((z-μ₂)-x)`
by shift-invariance, so the convolution at `z` is the noise-mean-0 marginal at `z-μ₂`, whose limit is
`gaussianDensity μ₁ (σ₁²+σ₂²) (z-μ₂) = gaussianDensity (μ₁+μ₂) (σ₁²+σ₂²) z`.

`sorryAx`-free, zero new axioms.
-/

namespace MachLib
namespace Real

/-! ## §1 — shift-invariance of the Gaussian density -/

/-- **Shift invariance**: `gaussianDensity μ σ² w = gaussianDensity (μ+a) σ² (w+a)` — the density
depends on `w` only through `w-μ`, and `(w+a)-(μ+a) = w-μ`. -/
theorem gaussianDensity_shift (mu sig2 w a : Real) :
    gaussianDensity mu sig2 w = gaussianDensity (mu + a) sig2 (w + a) := by
  rw [gaussianDensity, gaussianDensity, show (w + a) - (mu + a) = w - mu from by mach_mpoly [w, mu, a]]

/-! ## §2 — the convolution integral -/

private theorem cri_congr {f g : Real → Real} (hfg : f = g) {a b : Real} (hab : a ≤ b)
    (hcf : ∀ z, a ≤ z → z ≤ b → ContinuousAt f z) (hcg : ∀ z, a ≤ z → z ≤ b → ContinuousAt g z) :
    Classical.choose (continuous_riemann_integrable f a b hab hcf)
      = Classical.choose (continuous_riemann_integrable g a b hab hcg) := by
  subst hfg; rfl

/-- Continuity of `x ↦ z - x`. -/
private theorem continuousAt_zsubx (z x0 : Real) : ContinuousAt (fun x => z - x) x0 :=
  hasDerivAt_continuousAt (HasDerivAt_sub (fun _ => z) (fun x => x) 0 1 x0
    (HasDerivAt_const z x0) (HasDerivAt_id x0))

/-- Continuity of the convolution integrand `x ↦ N(μ₁,σ₁²)(x)·N(μ₂,σ₂²)(z-x)`. -/
private theorem continuousAt_convIntegrand (mu1 sig1 mu2 sig2 z : Real) (hsig1 : 0 < sig1)
    (hsig2 : 0 < sig2) (x0 : Real) :
    ContinuousAt (fun x => gaussianDensity mu1 sig1 x * gaussianDensity mu2 sig2 (z - x)) x0 :=
  continuousAt_mul (continuousAt_gaussianDensity mu1 sig1 hsig1 x0)
    (continuousAt_comp (continuousAt_zsubx z x0)
      (continuousAt_gaussianDensity mu2 sig2 hsig2 (z - x0)))

/-- `∫_{-R}^R N(μ₁,σ₁²)(x)·N(μ₂,σ₂²)(z-x) dx` — the finite convolution integral (density of `X+Y`). -/
noncomputable def convSymInt (mu1 sig1 mu2 sig2 : Real) (hsig1 : 0 < sig1) (hsig2 : 0 < sig2)
    (z R : Real) : Real :=
  if h : 0 < R then
    Classical.choose (continuous_riemann_integrable
      (fun x => gaussianDensity mu1 sig1 x * gaussianDensity mu2 sig2 (z - x)) (-R) R
      (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun x _ _ => continuousAt_convIntegrand mu1 sig1 mu2 sig2 z hsig1 hsig2 x))
  else 0

/-- The convolution integral equals the noise-mean-0 marginal at the shifted point `z-μ₂`. -/
private theorem convSymInt_eq (mu1 sig1 mu2 sig2 : Real) (hsig1 : 0 < sig1) (hsig2 : 0 < sig2)
    {z R : Real} (hR : 0 < R) :
    convSymInt mu1 sig1 mu2 sig2 hsig1 hsig2 z R
      = jointDensitySymInt mu1 sig1 sig2 (z - mu2) hsig1 hsig2 R := by
  have hab : -R < R := lt_trans_ax (neg_neg_of_pos hR) hR
  have hfun : (fun x => gaussianDensity mu1 sig1 x * gaussianDensity mu2 sig2 (z - x))
      = (fun x => jointDensity mu1 sig1 sig2 x (z - mu2)) := by
    funext x
    rw [jointDensity, gaussianDensity_shift mu2 sig2 (z - x) (-mu2),
      show mu2 + -mu2 = 0 from by mach_mpoly [mu2],
      show z - x + -mu2 = z - mu2 - x from by mach_mpoly [z, x, mu2]]
  show (if h : 0 < R then Classical.choose (continuous_riemann_integrable
      (fun x => gaussianDensity mu1 sig1 x * gaussianDensity mu2 sig2 (z - x)) (-R) R _ _)
      else 0) = _
  rw [dif_pos hR,
    cri_congr hfun (le_of_lt hab)
      (fun x _ _ => continuousAt_convIntegrand mu1 sig1 mu2 sig2 z hsig1 hsig2 x)
      (fun x _ _ => continuousAt_jointDensity_x mu1 sig1 sig2 (z - mu2) hsig1 hsig2 x)]
  show _ = jointDensitySymInt mu1 sig1 sig2 (z - mu2) hsig1 hsig2 R
  rw [jointDensitySymInt, dif_pos hR]

/-- **Sum of independent Gaussians**: the convolution `∫ N(μ₁,σ₁²)(x)·N(μ₂,σ₂²)(z-x) dx` tends to
`N(μ₁+μ₂, σ₁²+σ₂²)(z)` — i.e. `X+Y ~ N(μ₁+μ₂, σ₁²+σ₂²)`. -/
theorem gaussian_convolution_tendsto (mu1 sig1 mu2 sig2 : Real) (hsig1 : 0 < sig1) (hsig2 : 0 < sig2) :
    ∀ z ε : Real, 0 < ε → ∃ R₀ : Real, 0 < R₀ ∧ ∀ R : Real, R₀ ≤ R →
      abs (convSymInt mu1 sig1 mu2 sig2 hsig1 hsig2 z R
            - gaussianDensity (mu1 + mu2) (sig1 + sig2) z) < ε := by
  intro z ε hε
  obtain ⟨R0, hR0p, hR0⟩ := jointDensity_marginal_tendsto mu1 sig1 sig2 (z - mu2) hsig1 hsig2 ε hε
  refine ⟨R0, hR0p, ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le hR0p hR
  rw [convSymInt_eq mu1 sig1 mu2 sig2 hsig1 hsig2 hRpos]
  -- target: gaussianDensity μ₁ (margVar σ₁² σ₂²) (z-μ₂) = gaussianDensity (μ₁+μ₂) (σ₁²+σ₂²) z
  have htgt : gaussianDensity (mu1 + mu2) (sig1 + sig2) z
      = gaussianDensity mu1 (margVar sig1 sig2) (z - mu2) := by
    rw [margVar, gaussianDensity_shift mu1 (sig1 + sig2) (z - mu2) mu2,
      show z - mu2 + mu2 = z from by mach_mpoly [z, mu2]]
  rw [htgt]
  exact hR0 R hR

end Real
end MachLib
