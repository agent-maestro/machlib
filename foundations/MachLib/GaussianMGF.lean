import MachLib.GaussianConjugacy

/-!
# Gaussian moment generating function (probability frontier)

`E[exp(tX)] = exp(μt + σ²t²/2)` for `X ~ N(μ, σ²)`, proven from scratch on the second-moment
theory, no measure theory, zero new axioms. Same completing-the-square technique as the Bayesian
conjugacy: the pointwise identity

    exp(t·x) · gaussianDensity μ σ² x = exp(μt + σ²t²/2) · gaussianDensity (μ + σ²t) σ² x

(a mean shift by `σ²t` plus a constant factor) reduces the MGF integral to `∫ (shifted density) = 1`
(S3, `gaussianDensity_symInt_tendsto_one`). Differentiating `M(t)` at `0` recovers every moment; the
first two match the mean `μ` and variance `σ²` already proven directly.

`sorryAx`-free.
-/

namespace MachLib
namespace Real

/-! ## §1 — the completing-the-square exponent identity -/

/-- **The MGF exponent identity**: `t·x − (x−μ)²/(2σ²) = (μt+σ²t²/2) − (x−(μ+σ²t))²/(2σ²)`. -/
private theorem mgf_expArg (mu sig2 t x : Real) (hsig2 : 0 < sig2) :
    t * x - (x - mu) * (x - mu) / ((1 + 1) * sig2)
      = mu * t + sig2 * t * t / (1 + 1)
        - (x - (mu + sig2 * t)) * (x - (mu + sig2 * t)) / ((1 + 1) * sig2) := by
  have h2 : (1 + 1 : Real) ≠ 0 := ne_of_gt two_pos
  have hs : sig2 ≠ 0 := ne_of_gt hsig2
  have hD : (1 + 1) * sig2 ≠ 0 := mul_ne_zero h2 hs
  apply mul_right_cancel' hD
  -- clear the three /((1+1)sig2) terms and the /(1+1) constant term, then reduce to mgf_poly
  rw [show (t * x - (x - mu) * (x - mu) / ((1 + 1) * sig2)) * ((1 + 1) * sig2)
      = t * x * ((1 + 1) * sig2) - (x - mu) * (x - mu) / ((1 + 1) * sig2) * ((1 + 1) * sig2)
        from by mach_mpoly [(t * x : Real), ((x - mu) * (x - mu) / ((1 + 1) * sig2) : Real),
          ((1 + 1) * sig2 : Real)],
    div_mul_cancel hD,
    show (mu * t + sig2 * t * t / (1 + 1)
          - (x - (mu + sig2 * t)) * (x - (mu + sig2 * t)) / ((1 + 1) * sig2)) * ((1 + 1) * sig2)
      = mu * t * ((1 + 1) * sig2) + sig2 * t * t / (1 + 1) * ((1 + 1) * sig2)
        - (x - (mu + sig2 * t)) * (x - (mu + sig2 * t)) / ((1 + 1) * sig2) * ((1 + 1) * sig2)
        from by mach_mpoly [(mu * t : Real), (sig2 * t * t / (1 + 1) : Real),
          ((x - (mu + sig2 * t)) * (x - (mu + sig2 * t)) / ((1 + 1) * sig2) : Real),
          ((1 + 1) * sig2 : Real)],
    div_mul_cancel hD,
    show sig2 * t * t / (1 + 1) * ((1 + 1) * sig2) = sig2 * t * t / (1 + 1) * (1 + 1) * sig2
      from by mach_mpoly [(sig2 * t * t / (1 + 1) : Real), sig2, (1 + 1 : Real)],
    div_mul_cancel h2]
  -- goal now a polynomial identity in x, mu, sig2, t
  mach_mpoly [x, mu, sig2, t]

/-! ## §2 — the pointwise density identity -/

private theorem sub_eq_add_neg_m (a b : Real) : a - b = a + -b := by mach_mpoly [a, b]
private theorem exp_mul_div_l (P Q N : Real) (hN : N ≠ 0) :
    Real.exp P * (Real.exp Q / N) = Real.exp (P + Q) / N := by
  apply mul_right_cancel' hN
  rw [mul_assoc, div_mul_cancel hN, div_mul_cancel hN, ← exp_add]
private theorem div_mul_exp_r (Q N C : Real) (hN : N ≠ 0) :
    Real.exp Q / N * Real.exp C = Real.exp (Q + C) / N := by
  apply mul_right_cancel' hN
  rw [div_mul_cancel hN,
    show Real.exp Q / N * Real.exp C * N = Real.exp Q / N * N * Real.exp C from by
      mach_mpoly [(Real.exp Q / N : Real), (Real.exp C : Real), N],
    div_mul_cancel hN, ← exp_add]

/-- **The MGF pointwise identity**: `exp(t·x)·N(μ,σ²)(x) = N(μ+σ²t, σ²)(x)·exp(μt+σ²t²/2)`. A mean
shift by `σ²t` times a constant — the density-level completing-the-square. -/
theorem exp_mul_gaussianDensity (mu sig2 t x : Real) (hsig2 : 0 < sig2) :
    Real.exp (t * x) * gaussianDensity mu sig2 x
      = gaussianDensity (mu + sig2 * t) sig2 x * Real.exp (mu * t + sig2 * t * t / (1 + 1)) := by
  have hN : sqrt ((1 + 1) * (pi * sig2)) ≠ 0 :=
    ne_of_gt (sqrt_pos (mul_pos two_pos (mul_pos pi_pos hsig2)))
  rw [gaussianDensity_eq_standard mu sig2 hsig2 x,
    gaussianDensity_eq_standard (mu + sig2 * t) sig2 hsig2 x,
    exp_mul_div_l _ _ _ hN, div_mul_exp_r _ _ _ hN]
  have hexp : t * x + -((x - mu) * (x - mu) / ((1 + 1) * sig2))
      = -((x - (mu + sig2 * t)) * (x - (mu + sig2 * t)) / ((1 + 1) * sig2))
        + (mu * t + sig2 * t * t / (1 + 1)) := by
    have h := mgf_expArg mu sig2 t x hsig2
    rw [sub_eq_add_neg_m (t * x) ((x - mu) * (x - mu) / ((1 + 1) * sig2)),
      sub_eq_add_neg_m (mu * t + sig2 * t * t / (1 + 1))
        ((x - (mu + sig2 * t)) * (x - (mu + sig2 * t)) / ((1 + 1) * sig2)),
      add_comm (mu * t + sig2 * t * t / (1 + 1))
        (-((x - (mu + sig2 * t)) * (x - (mu + sig2 * t)) / ((1 + 1) * sig2)))] at h
    exact h
  rw [hexp]

/-! ## §3 — the MGF as an improper integral -/

private theorem cri_congr {f g : Real → Real} (hfg : f = g) {a b : Real} (hab : a ≤ b)
    (hcf : ∀ z, a ≤ z → z ≤ b → ContinuousAt f z) (hcg : ∀ z, a ≤ z → z ≤ b → ContinuousAt g z) :
    Classical.choose (continuous_riemann_integrable f a b hab hcf)
      = Classical.choose (continuous_riemann_integrable g a b hab hcg) := by
  subst hfg; rfl

/-- Coefficient-scaling closer: `|S-1| < ε/(|c|+1) ⇒ |S·c - c| < ε`. -/
private theorem mgf_final_bound (S c ε : Real) (hS : abs (S - 1) < ε / (abs c + 1)) :
    abs (S * c - c) < ε := by
  have hcoef : 0 < abs c + 1 := add_pos_of_nonneg_pos (abs_nonneg c) one_pos
  rw [show S * c - c = (S - 1) * c from by mach_mpoly [S, c], abs_mul]
  have h1 : abs (S - 1) * (abs c + 1) < ε := by
    have h := mul_lt_mul_of_pos_right hS hcoef
    rwa [div_mul_cancel (ne_of_gt hcoef)] at h
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (le_of_lt one_pos)) (abs_nonneg _)) h1

/-- Continuity of `x ↦ exp(t·x)·N(μ,σ²)(x)` — via the pointwise identity, a constant times a shifted
Gaussian density. -/
private theorem continuousAt_mgfIntegrand (mu sig2 t : Real) (hsig2 : 0 < sig2) (z : Real) :
    ContinuousAt (fun x => Real.exp (t * x) * gaussianDensity mu sig2 x) z := by
  have hfun : (fun x => Real.exp (t * x) * gaussianDensity mu sig2 x)
      = (fun x => gaussianDensity (mu + sig2 * t) sig2 x
          * Real.exp (mu * t + sig2 * t * t / (1 + 1))) := by
    funext x; exact exp_mul_gaussianDensity mu sig2 t x hsig2
  rw [hfun]
  exact continuousAt_mul_const (continuousAt_gaussianDensity (mu + sig2 * t) sig2 hsig2 z) _

/-- `∫_{-R}^R exp(t·x)·gaussianDensity μ σ² x dx` — the finite MGF integral. -/
noncomputable def mgfSymInt (mu sig2 t : Real) (hsig2 : 0 < sig2) (R : Real) : Real :=
  if h : 0 < R then
    Classical.choose (continuous_riemann_integrable
      (fun x => Real.exp (t * x) * gaussianDensity mu sig2 x) (-R) R
      (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun z _ _ => continuousAt_mgfIntegrand mu sig2 t hsig2 z))
  else 0

/-- The MGF integral factors as `(∫ shifted density)·exp(μt+σ²t²/2)`. -/
private theorem mgfSymInt_eq (mu sig2 t : Real) (hsig2 : 0 < sig2) {R : Real} (hR : 0 < R) :
    mgfSymInt mu sig2 t hsig2 R
      = gaussianDensitySymInt (mu + sig2 * t) sig2 hsig2 R
        * Real.exp (mu * t + sig2 * t * t / (1 + 1)) := by
  have hab : -R < R := lt_trans_ax (neg_neg_of_pos hR) hR
  have hcg : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (gaussianDensity (mu + sig2 * t) sig2) z :=
    fun z _ _ => continuousAt_gaussianDensity (mu + sig2 * t) sig2 hsig2 z
  have hcp : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun x => gaussianDensity (mu + sig2 * t) sig2 x
        * Real.exp (mu * t + sig2 * t * t / (1 + 1))) z :=
    fun z hz0 hz1 => continuousAt_mul_const (hcg z hz0 hz1) _
  have hfun : (fun x => Real.exp (t * x) * gaussianDensity mu sig2 x)
      = (fun x => gaussianDensity (mu + sig2 * t) sig2 x
          * Real.exp (mu * t + sig2 * t * t / (1 + 1))) := by
    funext x; exact exp_mul_gaussianDensity mu sig2 t x hsig2
  show (if h : 0 < R then Classical.choose (continuous_riemann_integrable
      (fun x => Real.exp (t * x) * gaussianDensity mu sig2 x) (-R) R _ _) else 0) = _
  rw [dif_pos hR, cri_congr hfun (le_of_lt hab)
      (fun z _ _ => continuousAt_mgfIntegrand mu sig2 t hsig2 z) hcp,
    riemann_integral_mul_const (le_of_lt hab) hcg hcp]
  show _ * _ = gaussianDensitySymInt (mu + sig2 * t) sig2 hsig2 R * _
  rw [gaussianDensitySymInt, dif_pos hR]

/-- **The Gaussian MGF**: `E[exp(tX)] = exp(μt + σ²t²/2)` — the finite integral tends to it as
`R→∞`. Differentiating in `t` at `0` recovers all moments (first two = mean μ, variance σ²). -/
theorem gaussian_mgf_tendsto (mu sig2 t : Real) (hsig2 : 0 < sig2) :
    ∀ ε : Real, 0 < ε → ∃ R₀ : Real, 0 < R₀ ∧ ∀ R : Real, R₀ ≤ R →
      abs (mgfSymInt mu sig2 t hsig2 R
            - Real.exp (mu * t + sig2 * t * t / (1 + 1))) < ε := by
  intro ε hε
  have hm : 0 < abs (Real.exp (mu * t + sig2 * t * t / (1 + 1))) + 1 :=
    add_pos_of_nonneg_pos (abs_nonneg _) one_pos
  obtain ⟨R0, hR0p, hR0⟩ := gaussianDensity_symInt_tendsto_one (mu + sig2 * t) sig2 hsig2
    (ε / (abs (Real.exp (mu * t + sig2 * t * t / (1 + 1))) + 1)) (div_pos_of_pos_pos hε hm)
  refine ⟨max R0 1, lt_of_lt_of_le one_pos (le_max_right R0 1), ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_trans (le_max_right R0 1) hR)
  rw [mgfSymInt_eq mu sig2 t hsig2 hRpos]
  exact mgf_final_bound (gaussianDensitySymInt (mu + sig2 * t) sig2 hsig2 R)
    (Real.exp (mu * t + sig2 * t * t / (1 + 1))) ε (hR0 R (le_trans (le_max_left R0 1) hR))

end Real
end MachLib
