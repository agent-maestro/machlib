import MachLib.GaussianLaplaceRoute
import MachLib.RiemannIntegralAddition

/-!
# The full-line Gaussian integral and the normalized Gaussian density

Stages S1–S3 of the scalar Bayesian/MMSE-optimality "probability pillar" arc. Goal:
`gaussianDensity μ σ² x := exp(-(x-μ)²/(2σ²)) / sqrt(2πσ²)` integrates to `1` over the whole line —
"MachLib now has a genuine, normalized Gaussian probability density function, for the first time,"
the arc's analogue of the √π project's first landed milestone `tan(π/4)=1`.

**Key device (avoids ALL mesh-level change-of-variables):** the standard Gaussian kernel
`exp(-t²)` has no elementary antiderivative, BUT `gaussianI` (the total-wrapper `∫₀ᵗexp(-s²)ds`) IS
one for `t > 0` (`gaussianI_hasDerivAt_pos`). Extending it to an ODD function
`gaussianISigned t := if 0 ≤ t then gaussianI t else -gaussianI(-t)` gives the genuine
antiderivative of `exp(-t²)` on the WHOLE real line — differentiable everywhere, `HasDerivAt
gaussianISigned (exp(-t²)) t` for every `t` (the odd extension removes `gaussianI`'s kink at 0).
Then every finite integral is a plain `ftc_riemann` application (`∫_a^b exp(-t²)dt =
gaussianISigned b - gaussianISigned a`), and the full-line and general-Gaussian integrals follow by
composing that antiderivative with an affine map and taking improper limits — no substitution
lemma, no 2-D integration, no new axiom.

`sorryAx`-free, no new axioms.
-/

namespace MachLib
namespace Real

/-! ## §1 — `gaussianISigned`, the odd extension of `gaussianI` = the everywhere-antiderivative -/

/-- The odd extension of `gaussianI`. Equals `∫₀ᵗexp(-s²)ds` for `t ≥ 0` and `-∫₀^{-t}exp(-s²)ds`
for `t < 0`, so it is the genuine antiderivative of `exp(-t²)` on all of `ℝ`. -/
noncomputable def gaussianISigned (t : Real) : Real :=
  if 0 ≤ t then gaussianI t else -gaussianI (-t)

private theorem not_nonneg_of_neg {t : Real} (ht : t < 0) : ¬ (0 ≤ t) :=
  fun h => lt_irrefl_ax t (lt_of_lt_of_le ht h)

private theorem neg_neg_local (a : Real) : - -a = a := by mach_mpoly [a]

theorem gaussianISigned_zero : gaussianISigned 0 = 0 := by
  show (if 0 ≤ (0:Real) then gaussianI 0 else -gaussianI (-0)) = 0
  rw [if_pos (le_refl 0), gaussianI_zero_eq]

theorem gaussianISigned_pos {t : Real} (ht : 0 ≤ t) : gaussianISigned t = gaussianI t := by
  show (if 0 ≤ t then gaussianI t else -gaussianI (-t)) = gaussianI t
  rw [if_pos ht]

theorem gaussianISigned_neg_arg {t : Real} (ht : t < 0) : gaussianISigned t = -gaussianI (-t) := by
  show (if 0 ≤ t then gaussianI t else -gaussianI (-t)) = -gaussianI (-t)
  rw [if_neg (not_nonneg_of_neg ht)]

/-- `gaussianISigned(-R) = -gaussianI(R)` for `R ≥ 0` — the reflection fact the full-line limit
needs (the left tail equals the negated right tail). -/
theorem gaussianISigned_neg_of_nonneg {R : Real} (hR : 0 ≤ R) : gaussianISigned (-R) = -gaussianI R := by
  rcases (le_iff_lt_or_eq 0 R).mp hR with hpos | heq
  · rw [gaussianISigned_neg_arg (neg_neg_of_pos hpos), neg_neg_local]
  · rw [← heq, neg_zero, gaussianISigned_zero, gaussianI_zero_eq, neg_zero]

/-! ## §2 — `gaussianISigned` is differentiable everywhere, with derivative `exp(-t²)` -/

/-- For `t > 0`: `gaussianISigned` agrees with `gaussianI` on a neighborhood, so inherits its
derivative via local congruence. -/
theorem hasDerivAt_gaussianISigned_pos {t : Real} (ht : 0 < t) :
    HasDerivAt gaussianISigned (Real.exp (-(t * t))) t := by
  refine HasDerivAt_congr gaussianI gaussianISigned (Real.exp (-(t * t))) t ⟨t, ht, ?_⟩
    (gaussianI_hasDerivAt_pos ht)
  intro y hy
  have hy0 : 0 ≤ y := by
    have h1 := (abs_lt_split hy).2
    have h2 := add_lt_add_left h1 t
    rw [show t + -t = (0:Real) from by mach_mpoly [t], show t + (y - t) = y from by mach_mpoly [t, y]]
      at h2
    exact le_of_lt h2
  exact (gaussianISigned_pos hy0).symm

/-- For `t < 0`: `gaussianISigned` agrees with `-gaussianI(-·)` on a neighborhood; the derivative
comes from the chain rule (`gaussianI` at `-t > 0`, composed with `y ↦ -y`, then negated). -/
theorem hasDerivAt_gaussianISigned_neg {t : Real} (ht : t < 0) :
    HasDerivAt gaussianISigned (Real.exp (-(t * t))) t := by
  have hnt : 0 < -t := neg_pos_of_neg ht
  -- inner: y ↦ -y, derivative -1
  have hinner : HasDerivAt (fun y => -y) (-1) t := by
    have h := HasDerivAt_neg (fun y => y) 1 t (HasDerivAt_id t)
    exact h
  -- gaussianI at -t, derivative exp(-((-t)²)) = exp(-(t²))
  have houter : HasDerivAt gaussianI (Real.exp (-(t * t))) (-t) := by
    have h := gaussianI_hasDerivAt_pos hnt
    rwa [show -t * -t = t * t from by mach_mpoly [t]] at h
  -- compose: y ↦ gaussianI(-y), derivative exp(-(t²)) * (-1)
  have hcomp : HasDerivAt (fun y => gaussianI (-y)) (Real.exp (-(t * t)) * -1) t :=
    HasDerivAt_comp gaussianI (fun y => -y) (-1) (Real.exp (-(t * t))) t hinner houter
  -- negate: y ↦ -gaussianI(-y), derivative -(exp(-(t²)) * -1) = exp(-(t²))
  have hnegcomp : HasDerivAt (fun y => -gaussianI (-y)) (-(Real.exp (-(t * t)) * -1)) t :=
    HasDerivAt_neg (fun y => gaussianI (-y)) (Real.exp (-(t * t)) * -1) t hcomp
  rw [show -(Real.exp (-(t * t)) * -1) = Real.exp (-(t * t)) from by
    mach_mpoly [Real.exp (-(t * t))]] at hnegcomp
  -- transfer to gaussianISigned via local congruence (neighborhood of t stays < 0)
  refine HasDerivAt_congr (fun y => -gaussianI (-y)) gaussianISigned (Real.exp (-(t * t))) t
    ⟨-t, hnt, ?_⟩ hnegcomp
  intro y hy
  have hyneg : y < 0 := by
    have h1 := (abs_lt_split hy).1
    have h2 := add_lt_add_left h1 t
    rw [show t + (y - t) = y from by mach_mpoly [t, y], show t + -t = (0:Real) from by mach_mpoly [t]]
      at h2
    exact h2
  exact (gaussianISigned_neg_arg hyneg).symm

/-! ### The subtle point: differentiability AT `0` (the odd extension removes `gaussianI`'s kink).

`|gaussianI(w) - w| ≤ w³` for `w ≥ 0`: `gaussianI(w) ≤ w` (`gaussianIntegral_le_self`) and
`gaussianI(w) ≥ w·exp(-w²)` (level-0 lower Darboux sum, the min of `exp(-s²)` on `[0,w]` is
`exp(-w²)`), so `w - gaussianI(w) ≤ w(1-exp(-w²)) ≤ w·w²` (via `1-exp(-w²) ≤ w²`, from
`one_add_le_exp`). That cubic bound is exactly what a two-sided `HasDerivAt … 1 0` needs. -/

private theorem gaussianI_le_self' {w : Real} (hw : 0 ≤ w) : gaussianI w ≤ w := by
  rw [gaussianI_eq w hw]; exact gaussianIntegral_le_self w hw

/-- `gaussianI(w) ≥ w·exp(-w²)` for `w ≥ 0` — the level-0 lower Darboux sum, since `exp(-s²) ≥
exp(-w²)` on `[0,w]`. -/
theorem gaussianI_ge_w_mul_exp {w : Real} (hw : 0 ≤ w) :
    w * Real.exp (-(w * w)) ≤ gaussianI w := by
  rw [gaussianI_eq w hw]
  have hgspec := Classical.choose_spec (gaussian_integral_exists w hw)
  have hpt : ∀ z : Real, 0 ≤ z → z ≤ w → Real.exp (-(w * w)) ≤ Real.exp (-(z * z)) :=
    fun z hz0 hzw => exp_monotone (neg_le_neg (mul_le_mul' hz0 hzw hz0 hzw))
  have hminge := minSub_ge_global_bound (fun s => Real.exp (-(s * s))) 0 w hw
    (fun z _ _ => gaussian_continuous z) (Real.exp (-(w * w))) hpt (2 ^ 0) (two_pow_pos 0) 0
  have hls : lowerSumCont (fun s => Real.exp (-(s * s))) 0 w hw (fun z _ _ => gaussian_continuous z)
      (2 ^ 0) (two_pow_pos 0)
      = minSub (fun s => Real.exp (-(s * s))) 0 w hw (fun z _ _ => gaussian_continuous z)
        (2 ^ 0) (two_pow_pos 0) 0 * meshWidth 0 w (2 ^ 0) := by
    show partialSum (minSub (fun s => Real.exp (-(s * s))) 0 w hw (fun z _ _ => gaussian_continuous z)
        (2 ^ 0) (two_pow_pos 0)) (2 ^ 0) * meshWidth 0 w (2 ^ 0)
      = minSub (fun s => Real.exp (-(s * s))) 0 w hw (fun z _ _ => gaussian_continuous z)
        (2 ^ 0) (two_pow_pos 0) 0 * meshWidth 0 w (2 ^ 0)
    rw [partialSum_one]
  rw [meshWidth_zero_one_pow] at hls
  have hstep1 : Real.exp (-(w * w)) * w
      ≤ minSub (fun s => Real.exp (-(s * s))) 0 w hw (fun z _ _ => gaussian_continuous z)
        (2 ^ 0) (two_pow_pos 0) 0 * w := mul_le_mul_of_nonneg_right hminge hw
  rw [← hls] at hstep1
  rw [mul_comm w (Real.exp (-(w * w)))]
  exact le_trans hstep1 (hgspec.1 0).1

private theorem add_neg_eq_sub_g (a b : Real) : a + -b = a - b := by mach_mpoly [a, b]
private theorem factor_w_sub (a c : Real) : a - a * c = a * (1 - c) := by mach_mpoly [a, c]
private theorem neg_sub_reorder (g y : Real) : -g - y = -y - g := by mach_mpoly [g, y]
private theorem neg_sub_swap' (a b : Real) : -(a - b) = b - a := by mach_mpoly [a, b]
private theorem sub_zero_one_mul (A y : Real) : A - 0 - 1 * (y - 0) = A - y := by mach_mpoly [A, y]

private theorem one_sub_exp_le_sq (w : Real) : 1 - Real.exp (-(w * w)) ≤ w * w := by
  have h := one_add_le_exp (-(w * w))
  have h2 := add_le_add_both h (le_refl (w * w - Real.exp (-(w * w))))
  rwa [show 1 + -(w * w) + (w * w - Real.exp (-(w * w))) = 1 - Real.exp (-(w * w)) from by
      mach_mpoly [(w * w : Real), Real.exp (-(w * w))],
    show Real.exp (-(w * w)) + (w * w - Real.exp (-(w * w))) = w * w from by
      mach_mpoly [(w * w : Real), Real.exp (-(w * w))]] at h2

/-- `|gaussianISigned(y) - y| ≤ |y|³` — the cubic approximation bound at the origin, both signs. -/
theorem abs_gaussianISigned_sub_le (y : Real) :
    abs (gaussianISigned y - y) ≤ abs y * (abs y * abs y) := by
  -- reduce to the w ≥ 0 cubic bound `w - gaussianI w ≤ w·(w·w)` with w = |y|
  have hcubic : ∀ w : Real, 0 ≤ w → w - gaussianI w ≤ w * (w * w) := by
    intro w hw
    have hle := gaussianI_le_self' hw
    have hge := gaussianI_ge_w_mul_exp hw
    have h1 : w - gaussianI w ≤ w - w * Real.exp (-(w * w)) := by
      have h := add_le_add_both (le_refl w) (neg_le_neg hge)
      rwa [add_neg_eq_sub_g w (gaussianI w), add_neg_eq_sub_g w (w * Real.exp (-(w * w)))] at h
    have h3 : w * (1 - Real.exp (-(w * w))) ≤ w * (w * w) :=
      mul_le_mul_of_nonneg_left (one_sub_exp_le_sq w) hw
    rw [factor_w_sub w (Real.exp (-(w * w)))] at h1
    exact le_trans h1 h3
  rcases lt_total y 0 with hy | hy | hy
  · -- y < 0: gaussianISigned y - y = (-y) - gaussianI(-y), and |y| = -y
    rw [gaussianISigned_neg_arg hy, iv_aon hy]
    have hw : 0 ≤ -y := le_of_lt (neg_pos_of_neg hy)
    rw [neg_sub_reorder (gaussianI (-y)) y]
    rw [abs_of_nonneg (sub_nonneg_of_le (gaussianI_le_self' hw))]
    exact hcubic (-y) hw
  · subst hy
    rw [gaussianISigned_zero, sub_zero, abs_zero, zero_mul]
    exact le_refl 0
  · -- y > 0: gaussianISigned y - y = gaussianI y - y ≤ 0, |y| = y
    rw [gaussianISigned_pos (le_of_lt hy), abs_of_nonneg (le_of_lt hy)]
    rw [abs_of_nonpos (sub_nonpos_of_le (gaussianI_le_self' (le_of_lt hy))),
      neg_sub_swap' (gaussianI y) y]
    exact hcubic y (le_of_lt hy)

theorem hasDerivAt_gaussianISigned_zero : HasDerivAt gaussianISigned 1 0 := by
  apply HasDerivAt_of_eps_delta
  intro ε hε
  refine ⟨sqrt ε, sqrt_pos hε, ?_⟩
  intro y hy
  have hyabs : abs y < sqrt ε := by rwa [sub_zero] at hy
  have hinner : gaussianISigned y - gaussianISigned 0 - 1 * (y - 0) = gaussianISigned y - y := by
    rw [gaussianISigned_zero]; exact sub_zero_one_mul (gaussianISigned y) y
  rw [hinner, sub_zero]
  -- goal: abs (gaussianISigned y - y) ≤ ε * abs y
  have hww : abs y * abs y ≤ ε := by
    have h := mul_le_mul' (abs_nonneg y) (le_of_lt hyabs) (abs_nonneg y) (le_of_lt hyabs)
    rwa [sqrt_sq_nonneg ε (le_of_lt hε)] at h
  have hcube : abs y * (abs y * abs y) ≤ ε * abs y := by
    rw [mul_comm ε (abs y)]
    exact mul_le_mul_of_nonneg_left hww (abs_nonneg y)
  exact le_trans (abs_gaussianISigned_sub_le y) hcube

/-- **`gaussianISigned` is the antiderivative of `exp(-t²)` on all of ℝ.** -/
theorem hasDerivAt_gaussianISigned (t : Real) :
    HasDerivAt gaussianISigned (Real.exp (-(t * t))) t := by
  rcases lt_total t 0 with ht | ht | ht
  · exact hasDerivAt_gaussianISigned_neg ht
  · rw [ht, mul_zero, neg_zero, Real.exp_zero]
    exact hasDerivAt_gaussianISigned_zero
  · exact hasDerivAt_gaussianISigned_pos ht

/-! ## §3 — the symmetric finite integral `∫_{-R}^R exp(-x²) dx = 2·gaussianI(R)`, by FTC

The first payoff of the everywhere-defined antiderivative: `ftc_riemann` applies on `[-R,R]` with
NO domain restriction on the derivative hypothesis (unlike `gaussianI`, whose derivative is only
available for positive argument). The reflection `gaussianISigned(-R) = -gaussianI(R)` then collapses
the two endpoints into `2·gaussianI(R)`. -/

theorem integral_exp_neg_sq_symmetric {R : Real} (hR : 0 < R) :
    Classical.choose (continuous_riemann_integrable (fun x => Real.exp (-(x * x))) (-R) R
      (le_of_lt (lt_trans_ax (neg_neg_of_pos hR) hR)) (fun z _ _ => gaussian_continuous z))
      = (1 + 1) * gaussianI R := by
  have hab : -R < R := lt_trans_ax (neg_neg_of_pos hR) hR
  have hspec := Classical.choose_spec (continuous_riemann_integrable
    (fun x => Real.exp (-(x * x))) (-R) R (le_of_lt hab) (fun z _ _ => gaussian_continuous z))
  have hftc := ftc_riemann (fun x => Real.exp (-(x * x))) gaussianISigned (-R) R hab
    (fun z _ _ => gaussian_continuous z) (fun z _ _ => hasDerivAt_gaussianISigned z) _
    (fun k => (hspec.1 k).1) (fun k => (hspec.1 k).2) hspec.2
  rw [hftc, gaussianISigned_pos (le_of_lt hR), gaussianISigned_neg_of_nonneg (le_of_lt hR)]
  mach_mpoly [gaussianI R]

end Real
end MachLib
