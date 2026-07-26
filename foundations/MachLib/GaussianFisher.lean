import MachLib.GaussianConjugacy

/-!
# Fisher information of the Gaussian (probability frontier)

The Fisher information of `X ~ N(μ, σ²)` with respect to the mean is `I(μ) = 1/σ²`, proven from
scratch on the second-moment theory, zero new axioms. The score (derivative of the log-density in
`μ`) is `∂_μ log N(μ,σ²)(x) = (x-μ)/σ²`, and the Fisher information is its second moment:

    I(μ) = E[ score² ] = ∫ ((x-μ)/σ²)² · gaussianDensity μ σ² x dx
         = (1/σ²)² · ∫ (x-μ)² · gaussianDensity μ σ² x dx
         = (1/σ²)² · σ²                                    (variance = σ², already proven)
         = 1/σ².

So the whole result is the variance integral scaled by the constant `(1/σ²)²` — a direct reuse of
`gaussianVarSymInt_tendsto_sigma2`. The Cramér-Rao lower bound (any unbiased estimator of the mean
has variance ≥ `1/I = σ²`) is the natural next step; it needs a Cauchy-Schwarz-for-integrals lemma
MachLib does not yet have, so it is flagged, not proven here.

`sorryAx`-free.
-/

namespace MachLib
namespace Real

/-- `(a·k)·(a·k)·d = a·a·d·(k·k)` — regroups score² · density into (variance integrand) · constant. -/
private theorem sq_scale (a k d : Real) : a * k * (a * k) * d = a * a * d * (k * k) := by
  mach_mpoly [a, k, d]

private theorem reassoc_l (s k : Real) : s * (k * k) = k * (s * k) := by mach_mpoly [s, k]

private theorem cri_congr {f g : Real → Real} (hfg : f = g) {a b : Real} (hab : a ≤ b)
    (hcf : ∀ z, a ≤ z → z ≤ b → ContinuousAt f z) (hcg : ∀ z, a ≤ z → z ≤ b → ContinuousAt g z) :
    Classical.choose (continuous_riemann_integrable f a b hab hcf)
      = Classical.choose (continuous_riemann_integrable g a b hab hcg) := by
  subst hfg; rfl

/-- Continuity of `y ↦ y - μ` (affine). -/
private theorem continuousAt_ymu (mu z : Real) : ContinuousAt (fun y => y - mu) z :=
  hasDerivAt_continuousAt (HasDerivAt_sub (fun y => y) (fun _ => mu) 1 0 z
    (HasDerivAt_id z) (HasDerivAt_const mu z))

/-- Continuity of the variance integrand `(y-μ)²·density`. -/
private theorem continuousAt_varInt' (mu sig2 : Real) (hsig2 : 0 < sig2) (z : Real) :
    ContinuousAt (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y) z :=
  continuousAt_mul (continuousAt_mul (continuousAt_ymu mu z) (continuousAt_ymu mu z))
    (continuousAt_gaussianDensity mu sig2 hsig2 z)

/-- Continuity of the score² integrand `((y-μ)·(1/σ²))²·density`. -/
private theorem continuousAt_scoreSq (mu sig2 : Real) (hsig2 : 0 < sig2) (z : Real) :
    ContinuousAt (fun y => (y - mu) * (1 / sig2) * ((y - mu) * (1 / sig2))
      * gaussianDensity mu sig2 y) z :=
  continuousAt_mul (continuousAt_mul
    (continuousAt_mul_const (continuousAt_ymu mu z) _)
    (continuousAt_mul_const (continuousAt_ymu mu z) _))
    (continuousAt_gaussianDensity mu sig2 hsig2 z)

/-- `∫_{-R}^R score² · density dx` — the finite Fisher-information integral (`score = (x-μ)/σ²`). -/
noncomputable def fisherSymInt (mu sig2 : Real) (hsig2 : 0 < sig2) (R : Real) : Real :=
  if h : 0 < R then
    Classical.choose (continuous_riemann_integrable
      (fun y => (y - mu) * (1 / sig2) * ((y - mu) * (1 / sig2)) * gaussianDensity mu sig2 y) (-R) R
      (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun z _ _ => continuousAt_scoreSq mu sig2 hsig2 z))
  else 0

/-- The Fisher integral factors as `(variance integral)·(1/σ²)²`. -/
private theorem fisherSymInt_eq (mu sig2 : Real) (hsig2 : 0 < sig2) {R : Real} (hR : 0 < R) :
    fisherSymInt mu sig2 hsig2 R
      = gaussianVarSymInt mu sig2 hsig2 R * (1 / sig2 * (1 / sig2)) := by
  have hab : -R < R := lt_trans_ax (neg_neg_of_pos hR) hR
  have hcg : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y) z :=
    fun z _ _ => continuousAt_varInt' mu sig2 hsig2 z
  have hcp : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y
        * (1 / sig2 * (1 / sig2))) z :=
    fun z hz0 hz1 => continuousAt_mul_const (hcg z hz0 hz1) _
  have hfun : (fun y => (y - mu) * (1 / sig2) * ((y - mu) * (1 / sig2)) * gaussianDensity mu sig2 y)
      = (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y * (1 / sig2 * (1 / sig2))) := by
    funext y; exact sq_scale (y - mu) (1 / sig2) (gaussianDensity mu sig2 y)
  show (if h : 0 < R then Classical.choose (continuous_riemann_integrable
      (fun y => (y - mu) * (1 / sig2) * ((y - mu) * (1 / sig2)) * gaussianDensity mu sig2 y)
      (-R) R _ _) else 0) = _
  rw [dif_pos hR, cri_congr hfun (le_of_lt hab)
      (fun z _ _ => continuousAt_scoreSq mu sig2 hsig2 z) hcp,
    riemann_integral_mul_const (le_of_lt hab) hcg hcp]
  show _ * _ = gaussianVarSymInt mu sig2 hsig2 R * _
  rw [gaussianVarSymInt, dif_pos hR]

/-- Coefficient-scaling closer: `|S - L| < ε/(|c|+1) ⇒ |S·c - L·c| < ε`. -/
private theorem scale_final_bound (S L c ε : Real) (hS : abs (S - L) < ε / (abs c + 1)) :
    abs (S * c - L * c) < ε := by
  have hcoef : 0 < abs c + 1 := add_pos_of_nonneg_pos (abs_nonneg c) one_pos
  rw [show S * c - L * c = (S - L) * c from by mach_mpoly [S, L, c], abs_mul]
  have h1 : abs (S - L) * (abs c + 1) < ε := by
    have h := mul_lt_mul_of_pos_right hS hcoef
    rwa [div_mul_cancel (ne_of_gt hcoef)] at h
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (le_of_lt one_pos)) (abs_nonneg _)) h1

/-- **The Fisher information of `N(μ,σ²)` w.r.t. the mean is `1/σ²`** — the score-squared integral
`∫((x-μ)/σ²)²·N(μ,σ²) dx` tends to `1/σ²`. Direct scaling of the variance integral (`= σ²`) by
`(1/σ²)²`. -/
theorem gaussian_fisher_tendsto (mu sig2 : Real) (hsig2 : 0 < sig2) :
    ∀ ε : Real, 0 < ε → ∃ R₀ : Real, 0 < R₀ ∧ ∀ R : Real, R₀ ≤ R →
      abs (fisherSymInt mu sig2 hsig2 R - 1 / sig2) < ε := by
  intro ε hε
  have hsne : sig2 ≠ 0 := ne_of_gt hsig2
  -- 1/σ² = σ²·(1/σ²·1/σ²)
  have hL : (1 : Real) / sig2 = sig2 * (1 / sig2 * (1 / sig2)) := by
    rw [reassoc_l sig2 (1 / sig2), mul_inv sig2 hsne, mul_one_ax]
  have hm : 0 < abs (1 / sig2 * (1 / sig2)) + 1 := add_pos_of_nonneg_pos (abs_nonneg _) one_pos
  obtain ⟨R0, hR0p, hR0⟩ := gaussianVarSymInt_tendsto_sigma2 mu sig2 hsig2
    (ε / (abs (1 / sig2 * (1 / sig2)) + 1)) (div_pos_of_pos_pos hε hm)
  refine ⟨max R0 1, lt_of_lt_of_le one_pos (le_max_right R0 1), ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_trans (le_max_right R0 1) hR)
  rw [hL, fisherSymInt_eq mu sig2 hsig2 hRpos]
  exact scale_final_bound (gaussianVarSymInt mu sig2 hsig2 R) sig2 (1 / sig2 * (1 / sig2)) ε
    (hR0 R (le_trans (le_max_left R0 1) hR))

end Real
end MachLib
