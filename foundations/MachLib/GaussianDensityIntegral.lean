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
private theorem two_mul_sub_helper (a c : Real) :
    (1 + 1) * a - (1 + 1) * c = -((1 + 1) * (c - a)) := by mach_mpoly [a, c]

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

/-! ## §4 — the full-line integral `∫_{-∞}^∞ exp(-x²) dx = √π` (S2)

A total wrapper `symExpNegSqInt R := ∫_{-R}^R exp(-x²)` (`0` for `R ≤ 0`), which equals
`2·gaussianI(R)` by §3, converges to `√π` as `R → ∞` — reusing the √π arc's own
`gaussianI_close_to_improper` (`gaussianI(R) → gaussianImproperIntegral = √π/2`). Stated as a
genuine ε–R₀ limit, since MachLib has no two-sided improper-integral object and this is the honest
convergence statement. -/

/-- `∫_{-R}^R exp(-x²) dx` as a total function (`0` off `R > 0`). -/
noncomputable def symExpNegSqInt (R : Real) : Real :=
  if h : 0 < R then
    Classical.choose (continuous_riemann_integrable (fun x => Real.exp (-(x * x))) (-R) R
      (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h)) (fun z _ _ => gaussian_continuous z))
  else 0

theorem symExpNegSqInt_eq {R : Real} (hR : 0 < R) : symExpNegSqInt R = (1 + 1) * gaussianI R := by
  show (if h : 0 < R then Classical.choose (continuous_riemann_integrable
      (fun x => Real.exp (-(x * x))) (-R) R (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun z _ _ => gaussian_continuous z)) else 0) = (1 + 1) * gaussianI R
  rw [dif_pos hR]
  exact integral_exp_neg_sq_symmetric hR

/-- **`∫_{-∞}^∞ exp(-x²) dx = √π`**, as an ε–R₀ limit of the symmetric finite integral. -/
theorem symExpNegSqInt_tendsto_sqrt_pi : ∀ ε : Real, 0 < ε → ∃ R₀ : Real, 0 < R₀ ∧
    ∀ R : Real, R₀ ≤ R → abs (symExpNegSqInt R - sqrt pi) < ε := by
  intro ε hε
  have hε2 : 0 < ε / (1 + 1) := div_pos_of_pos_pos hε two_pos
  obtain ⟨T, hT0, hT⟩ := gaussianI_close_to_improper (ε / (1 + 1)) hε2
  refine ⟨T + 1, add_pos_of_nonneg_pos hT0 one_pos, ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le (add_pos_of_nonneg_pos hT0 one_pos) hR
  have hRT : T ≤ R := le_trans (le_add_of_nonneg_right (le_of_lt one_pos)) hR
  rw [symExpNegSqInt_eq hRpos]
  have hsqrtpi : (1 + 1) * gaussianImproperIntegral = sqrt pi := by
    rw [gaussianImproperIntegral_eq_sqrt_pi_div_two]; exact mul_div_cancel' two_ne_zero
  have hclose := hT R hRT
  have hle := gaussianI_le_gaussianImproperIntegral (le_of_lt hRpos)
  have hdiff : (1 + 1) * gaussianI R - sqrt pi
      = -((1 + 1) * (gaussianImproperIntegral - gaussianI R)) := by
    rw [← hsqrtpi]; exact two_mul_sub_helper (gaussianI R) gaussianImproperIntegral
  rw [hdiff, abs_neg,
    abs_of_nonneg (mul_nonneg (le_of_lt two_pos) (sub_nonneg_of_le hle))]
  have h2 := mul_lt_mul_of_pos_left hclose two_pos
  rwa [mul_div_cancel' two_ne_zero] at h2

/-! ## §5 — the normalized Gaussian density integrates to 1 (S3, the milestone)

`gaussianDensity μ σ² x := exp(-(x-μ)²/(2σ²)) / sqrt(2πσ²)`. Its symmetric finite integral tends to
`1` as `R → ∞`: the antiderivative of the un-normalized kernel is `Φ(x) := c·gaussianISigned((x-μ)·k)`
with `c := sqrt(2σ²)`, `k := 1/c` (so `c·k = 1`), giving `Φ' = exp(-((x-μ)·k)²)` by the chain rule
(`c·k` cancels). The normalizer `sqrt(2πσ²) = √π·c` is pulled out with `riemann_integral_mul_const`,
and the two endpoint limits `gaussianISigned((±R-μ)·k) → ±√π/2` (argument → ±∞) come from the √π
arc's `gaussianI_close_to_improper` — no substitution lemma, no new axiom. -/

/-- Inner affine map `(y-μ)·k` has derivative `k`. -/
private theorem hasDerivAt_innerAffine (mu k x : Real) :
    HasDerivAt (fun y => (y - mu) * k) k x := by
  have hsub : HasDerivAt (fun y => y - mu) (1 - 0) x :=
    HasDerivAt_sub (fun y => y) (fun _ => mu) 1 0 x (HasDerivAt_id x) (HasDerivAt_const mu x)
  rw [sub_zero] at hsub
  have hinner := HasDerivAt_mul (fun y => y - mu) (fun _ => k) 1 0 x hsub (HasDerivAt_const k x)
  rwa [show (1 : Real) * k + (x - mu) * 0 = k from by mach_mpoly [k, x, mu]] at hinner

/-- The everywhere-antiderivative of the affinely-scaled kernel `exp(-((x-μ)·k)²)`, namely
`c·gaussianISigned((x-μ)·k)`, when `c·k = 1`. -/
private theorem hasDerivAt_scaledAnti (mu c k x : Real) (hck : c * k = 1) :
    HasDerivAt (fun y => c * gaussianISigned ((y - mu) * k))
      (Real.exp (-(((x - mu) * k) * ((x - mu) * k)))) x := by
  have hinner := hasDerivAt_innerAffine mu k x
  have hgs := hasDerivAt_gaussianISigned ((x - mu) * k)
  have hcomp : HasDerivAt (fun y => gaussianISigned ((y - mu) * k))
      (Real.exp (-(((x - mu) * k) * ((x - mu) * k))) * k) x :=
    HasDerivAt_comp gaussianISigned (fun y => (y - mu) * k) k
      (Real.exp (-(((x - mu) * k) * ((x - mu) * k)))) x hinner hgs
  have hmul := HasDerivAt_mul (fun _ => c) (fun y => gaussianISigned ((y - mu) * k))
    0 (Real.exp (-(((x - mu) * k) * ((x - mu) * k))) * k) x (HasDerivAt_const c x) hcomp
  rw [show (0 : Real) * gaussianISigned ((x - mu) * k)
      + c * (Real.exp (-(((x - mu) * k) * ((x - mu) * k))) * k)
      = c * k * Real.exp (-(((x - mu) * k) * ((x - mu) * k))) from by
    mach_mpoly [c, k, Real.exp (-(((x - mu) * k) * ((x - mu) * k))),
      gaussianISigned ((x - mu) * k)], hck, one_mul_thm] at hmul
  exact hmul

/-- The scaled kernel's derivative: `d/dx exp(-((x-μ)·k)²) = -2k²(x-μ)·exp(-((x-μ)·k)²)`. -/
private theorem hasDerivAt_scaledKernel (mu k x : Real) :
    HasDerivAt (fun y => Real.exp (-(((y - mu) * k) * ((y - mu) * k))))
      (Real.exp (-(((x - mu) * k) * ((x - mu) * k))) * -((1 + 1) * ((x - mu) * (k * k)))) x := by
  have hp := hasDerivAt_innerAffine mu k x
  have hpp := HasDerivAt_mul (fun y => (y - mu) * k) (fun y => (y - mu) * k) k k x hp hp
  have hneg := HasDerivAt_neg (fun y => (y - mu) * k * ((y - mu) * k))
    (k * ((x - mu) * k) + (x - mu) * k * k) x hpp
  have hexp := HasDerivAt_comp Real.exp (fun y => -((y - mu) * k * ((y - mu) * k)))
    (-(k * ((x - mu) * k) + (x - mu) * k * k)) (Real.exp (-((x - mu) * k * ((x - mu) * k)))) x
    hneg (HasDerivAt_exp _)
  rwa [show Real.exp (-((x - mu) * k * ((x - mu) * k))) * -(k * ((x - mu) * k) + (x - mu) * k * k)
      = Real.exp (-(((x - mu) * k) * ((x - mu) * k))) * -((1 + 1) * ((x - mu) * (k * k))) from by
    mach_mpoly [Real.exp (-(((x - mu) * k) * ((x - mu) * k))), x, mu, k]] at hexp

/-- The scaled kernel `exp(-((x-μ)·k)²)` is continuous. -/
private theorem continuousAt_scaledKernel (mu k x : Real) :
    ContinuousAt (fun y => Real.exp (-(((y - mu) * k) * ((y - mu) * k)))) x :=
  hasDerivAt_continuousAt (hasDerivAt_scaledKernel mu k x)

/-- The scaled kernel's symmetric finite integral in closed form, by FTC on the everywhere-
antiderivative. -/
private theorem integral_scaledKernel_symmetric (mu c k : Real) (hck : c * k = 1) {R : Real}
    (hR : 0 < R) :
    Classical.choose (continuous_riemann_integrable
        (fun x => Real.exp (-(((x - mu) * k) * ((x - mu) * k)))) (-R) R
        (le_of_lt (lt_trans_ax (neg_neg_of_pos hR) hR))
        (fun z _ _ => continuousAt_scaledKernel mu k z))
      = c * gaussianISigned ((R - mu) * k) - c * gaussianISigned ((-R - mu) * k) := by
  have hab : -R < R := lt_trans_ax (neg_neg_of_pos hR) hR
  have hspec := Classical.choose_spec (continuous_riemann_integrable
    (fun x => Real.exp (-(((x - mu) * k) * ((x - mu) * k)))) (-R) R (le_of_lt hab)
    (fun z _ _ => continuousAt_scaledKernel mu k z))
  exact ftc_riemann (fun x => Real.exp (-(((x - mu) * k) * ((x - mu) * k))))
    (fun y => c * gaussianISigned ((y - mu) * k)) (-R) R hab
    (fun z _ _ => continuousAt_scaledKernel mu k z)
    (fun z _ _ => hasDerivAt_scaledAnti mu c k z hck) _
    (fun j => (hspec.1 j).1) (fun j => (hspec.1 j).2) hspec.2

/-- `gaussianISigned S → gaussianImproperIntegral (= √π/2)` as `S → +∞`. -/
theorem gaussianISigned_tendsto_pos_inf : ∀ ε : Real, 0 < ε → ∃ S₀ : Real, 0 ≤ S₀ ∧
    ∀ S : Real, S₀ ≤ S → abs (gaussianISigned S - gaussianImproperIntegral) < ε := by
  intro ε hε
  obtain ⟨T, hT0, hT⟩ := gaussianI_close_to_improper ε hε
  refine ⟨T, hT0, ?_⟩
  intro S hS
  have hS0 : 0 ≤ S := le_trans hT0 hS
  rw [gaussianISigned_pos hS0, abs_of_nonpos
    (sub_nonpos_of_le (gaussianI_le_gaussianImproperIntegral hS0)),
    neg_sub_swap' (gaussianI S) gaussianImproperIntegral]
  exact hT S hS

/-- `gaussianISigned S → -gaussianImproperIntegral (= -√π/2)` as `S → -∞`. -/
theorem gaussianISigned_tendsto_neg_inf : ∀ ε : Real, 0 < ε → ∃ S₀ : Real, S₀ < 0 ∧
    ∀ S : Real, S ≤ S₀ → abs (gaussianISigned S + gaussianImproperIntegral) < ε := by
  intro ε hε
  obtain ⟨T, hT0, hT⟩ := gaussianI_close_to_improper ε hε
  refine ⟨-(T + 1), neg_neg_of_pos (add_pos_of_nonneg_pos hT0 one_pos), ?_⟩
  intro S hS
  have hSneg : S < 0 := lt_of_le_of_lt hS (neg_neg_of_pos (add_pos_of_nonneg_pos hT0 one_pos))
  have hnST : T ≤ -S := by
    have h1 : T + 1 ≤ -S := by
      have h := neg_le_neg hS
      rwa [neg_neg_local (T + 1)] at h
    exact le_trans (le_add_of_nonneg_right (le_of_lt one_pos)) h1
  rw [gaussianISigned_neg_arg hSneg]
  rw [show -gaussianI (-S) + gaussianImproperIntegral = gaussianImproperIntegral - gaussianI (-S)
    from by mach_mpoly [gaussianI (-S), gaussianImproperIntegral]]
  rw [abs_of_nonneg (sub_nonneg_of_le (gaussianI_le_gaussianImproperIntegral (le_of_lt
    (neg_pos_of_neg hSneg))))]
  exact hT (-S) hnST

/-- **The scalar Gaussian probability density** `N(μ, σ²)`. Written with the scale factored inside
the square (`(x-μ)·(1/√(2σ²))`) and the normalizer `√π·√(2σ²) = √(2πσ²)` — manifestly a Gaussian,
and in exactly the scaled-kernel form the FTC antiderivative uses. -/
noncomputable def gaussianDensity (mu sig2 x : Real) : Real :=
  Real.exp (-(((x - mu) * (1 / sqrt ((1 + 1) * sig2))) * ((x - mu) * (1 / sqrt ((1 + 1) * sig2)))))
    / (sqrt pi * sqrt ((1 + 1) * sig2))

/-- Local copy of the `Classical.choose`-across-equal-integrands congruence (the version in
`GaussianLaplaceRoute` is `private`). By `Prop` proof-irrelevance the two continuity witnesses
give defeq integrability propositions once the functions coincide. -/
private theorem cri_congr {f g : Real → Real} (hfg : f = g) {a b : Real} (hab : a ≤ b)
    (hcontf : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hcontg : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt g z) :
    Classical.choose (continuous_riemann_integrable f a b hab hcontf)
      = Classical.choose (continuous_riemann_integrable g a b hab hcontg) := by
  subst hfg; rfl

private theorem two_sig2_pos {sig2 : Real} (hsig2 : 0 < sig2) : 0 < (1 + 1) * sig2 :=
  mul_pos two_pos hsig2

private theorem density_norm_pos {sig2 : Real} (hsig2 : 0 < sig2) :
    0 < sqrt pi * sqrt ((1 + 1) * sig2) :=
  mul_pos (sqrt_pos pi_pos) (sqrt_pos (two_sig2_pos hsig2))

theorem gaussianDensity_pos (mu sig2 : Real) (hsig2 : 0 < sig2) (z : Real) :
    0 < gaussianDensity mu sig2 z := by
  rw [gaussianDensity]
  exact div_pos_of_pos_pos (exp_pos _) (density_norm_pos hsig2)

/-- `gaussianDensity μ σ² = scaledKernel · (1/N)` as functions — the bridge to `riemann_integral_
mul_const`. -/
private theorem gaussianDensity_eq_kernel_mul (mu sig2 : Real) (hsig2 : 0 < sig2) :
    gaussianDensity mu sig2
      = fun x => Real.exp (-(((x - mu) * (1 / sqrt ((1 + 1) * sig2)))
          * ((x - mu) * (1 / sqrt ((1 + 1) * sig2)))))
          * (1 / (sqrt pi * sqrt ((1 + 1) * sig2))) := by
  funext x
  exact div_def _ _ (ne_of_gt (density_norm_pos hsig2))

private theorem continuousAt_gaussianDensity (mu sig2 : Real) (hsig2 : 0 < sig2) (x : Real) :
    ContinuousAt (gaussianDensity mu sig2) x := by
  rw [gaussianDensity_eq_kernel_mul mu sig2 hsig2]
  exact continuousAt_mul (continuousAt_scaledKernel mu (1 / sqrt ((1 + 1) * sig2)) x)
    (continuousAt_const _ x)

/-- `∫_{-R}^R gaussianDensity μ σ² dx` as a total function (`0` off `R > 0`). -/
noncomputable def gaussianDensitySymInt (mu sig2 : Real) (hsig2 : 0 < sig2) (R : Real) : Real :=
  if h : 0 < R then
    Classical.choose (continuous_riemann_integrable (gaussianDensity mu sig2) (-R) R
      (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun z _ _ => continuousAt_gaussianDensity mu sig2 hsig2 z))
  else 0

private theorem gaussianDensitySymInt_eq (mu sig2 : Real) (hsig2 : 0 < sig2) {R : Real} (hR : 0 < R) :
    gaussianDensitySymInt mu sig2 hsig2 R
      = (sqrt ((1 + 1) * sig2) * gaussianISigned ((R - mu) * (1 / sqrt ((1 + 1) * sig2)))
          - sqrt ((1 + 1) * sig2) * gaussianISigned ((-R - mu) * (1 / sqrt ((1 + 1) * sig2))))
        * (1 / (sqrt pi * sqrt ((1 + 1) * sig2))) := by
  have hc : 0 < sqrt ((1 + 1) * sig2) := sqrt_pos (two_sig2_pos hsig2)
  have hck : sqrt ((1 + 1) * sig2) * (1 / sqrt ((1 + 1) * sig2)) = 1 := mul_inv _ (ne_of_gt hc)
  have hab : -R < R := lt_trans_ax (neg_neg_of_pos hR) hR
  have hkercont : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => Real.exp (-(((y - mu) * (1 / sqrt ((1 + 1) * sig2)))
        * ((y - mu) * (1 / sqrt ((1 + 1) * sig2)))))) z :=
    fun z _ _ => continuousAt_scaledKernel mu (1 / sqrt ((1 + 1) * sig2)) z
  have hprodcont : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun x => Real.exp (-(((x - mu) * (1 / sqrt ((1 + 1) * sig2)))
        * ((x - mu) * (1 / sqrt ((1 + 1) * sig2)))))
        * (1 / (sqrt pi * sqrt ((1 + 1) * sig2)))) z :=
    fun z hz0 hz1 => continuousAt_mul (hkercont z hz0 hz1) (continuousAt_const _ z)
  show (if h : 0 < R then Classical.choose (continuous_riemann_integrable (gaussianDensity mu sig2)
      (-R) R (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun z _ _ => continuousAt_gaussianDensity mu sig2 hsig2 z)) else 0) = _
  rw [dif_pos hR]
  rw [cri_congr (gaussianDensity_eq_kernel_mul mu sig2 hsig2)
    (le_of_lt hab) (fun z _ _ => continuousAt_gaussianDensity mu sig2 hsig2 z) hprodcont]
  rw [riemann_integral_mul_const (le_of_lt hab) hkercont hprodcont]
  rw [integral_scaledKernel_symmetric mu (sqrt ((1 + 1) * sig2)) (1 / sqrt ((1 + 1) * sig2)) hck hR]

/-- **`∫_{-∞}^∞ gaussianDensity μ σ² dx = 1`** — the scalar Gaussian density is normalized. Stated
as an ε–R₀ limit of the symmetric finite integral (S3, the arc's first "probability" milestone).
The normalizer `√(2πσ²)` exactly cancels the `c·√π` the two endpoint limits of `gaussianISigned`
produce. -/
-- Algebra helpers for the final assembly (abstract vars to avoid the overlapping-atom mach_mpoly
-- bug, since `1/c`, `1/(√π·c)` syntactically contain `c`).
private theorem sub_from_add_le {a b R : Real} (h : a + b ≤ R) : b ≤ R - a := by
  have h2 := add_le_add_both h (le_refl (-a))
  rwa [show a + b + -a = b from by mach_mpoly [a, b],
    show R + -a = R - a from by mach_mpoly [R, a]] at h2

private theorem arg_lower_helper {Sp mu R c : Real} (hc : 0 < c) (hcinv : c * (1 / c) = 1)
    (h : mu + Sp * c ≤ R) : Sp ≤ (R - mu) * (1 / c) := by
  have h2 := mul_le_mul_of_nonneg_right (sub_from_add_le h) (le_of_lt (one_div_pos_of_pos hc))
  rwa [mul_assoc Sp c (1 / c), hcinv, mul_one_ax] at h2

private theorem arg_upper_helper {Sm mu R c : Real} (hc : 0 < c) (hcinv : c * (1 / c) = 1)
    (h : -mu - Sm * c ≤ R) : (-R - mu) * (1 / c) ≤ Sm := by
  have h1 : -R - mu ≤ Sm * c := by
    have h2 := add_le_add_both h (le_refl (Sm * c - R))
    rwa [show -mu - Sm * c + (Sm * c - R) = -R - mu from by mach_mpoly [mu, Sm, c, R],
      show R + (Sm * c - R) = Sm * c from by mach_mpoly [R, Sm, c]] at h2
  have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt (one_div_pos_of_pos hc))
  rwa [mul_assoc Sm c (1 / c), hcinv, mul_one_ax] at h2

private theorem density_value_key (A B imp c sp inv : Real)
    (hinv : sp * c * inv = 1) (himp : sp = imp + imp) :
    ((c * A - c * B) * inv - 1) * sp = A - imp - (B + imp) := by
  rw [show ((c * A - c * B) * inv - 1) * sp = (A - B) * (sp * c * inv) - sp from by
    mach_mpoly [A, B, c, inv, sp], hinv, himp]
  mach_mpoly [A, B, imp]

private theorem half_add_half (X : Real) : X / (1 + 1) + X / (1 + 1) = X := by
  rw [← mul_two_eq_add_self (X / (1 + 1))]
  exact div_mul_cancel (ne_of_gt two_pos)

/-- Given `(V-1)·sp = (A-imp) - (B+imp)` with both `|A-imp|` and `|B+imp| < ε·sp/2`, conclude
`|V-1| < ε` (cancel the positive `sp`). -/
private theorem final_bound (V A B imp sp ε : Real) (hsp : 0 < sp)
    (hkey : (V - 1) * sp = A - imp - (B + imp))
    (hA : abs (A - imp) < ε * sp / (1 + 1)) (hB : abs (B + imp) < ε * sp / (1 + 1)) :
    abs (V - 1) < ε := by
  have habs1 : abs ((V - 1) * sp) = abs (V - 1) * sp := by
    rw [abs_mul, abs_of_nonneg (le_of_lt hsp)]
  have hchain : abs (V - 1) * sp = abs (A - imp - (B + imp)) := by rw [← habs1, hkey]
  have htri : abs (A - imp - (B + imp)) ≤ abs (A - imp) + abs (B + imp) := by
    have h := abs_add (A - imp) (-(B + imp))
    rwa [show A - imp + -(B + imp) = A - imp - (B + imp) from by mach_mpoly [A, imp, B], abs_neg] at h
  have hsum : abs (A - imp) + abs (B + imp) < ε * sp := by
    have h := add_lt_add_both hA hB
    rwa [half_add_half (ε * sp)] at h
  have hlt : abs (V - 1) * sp < ε * sp := by rw [hchain]; exact lt_of_le_of_lt htri hsum
  exact lt_of_mul_lt_mul_right_pos hlt hsp

/-- **`∫_{-∞}^∞ gaussianDensity μ σ² dx = 1`** — the scalar Gaussian density is normalized. Stated
as an ε–R₀ limit of the symmetric finite integral (S3, the arc's first "probability" milestone).
The normalizer `√(2πσ²)` exactly cancels the `c·√π` the two endpoint limits of `gaussianISigned`
produce. -/
theorem gaussianDensity_symInt_tendsto_one (mu sig2 : Real) (hsig2 : 0 < sig2) :
    ∀ ε : Real, 0 < ε → ∃ R₀ : Real, 0 < R₀ ∧
      ∀ R : Real, R₀ ≤ R → abs (gaussianDensitySymInt mu sig2 hsig2 R - 1) < ε := by
  intro ε hε
  have hc : 0 < sqrt ((1 + 1) * sig2) := sqrt_pos (two_sig2_pos hsig2)
  have hcinv : sqrt ((1 + 1) * sig2) * (1 / sqrt ((1 + 1) * sig2)) = 1 := mul_inv _ (ne_of_gt hc)
  have hspi : 0 < sqrt pi := sqrt_pos pi_pos
  have hN : 0 < sqrt pi * sqrt ((1 + 1) * sig2) := mul_pos hspi hc
  have hNinv : sqrt pi * sqrt ((1 + 1) * sig2) * (1 / (sqrt pi * sqrt ((1 + 1) * sig2))) = 1 :=
    mul_inv _ (ne_of_gt hN)
  have himp : sqrt pi = gaussianImproperIntegral + gaussianImproperIntegral := by
    rw [gaussianImproperIntegral_eq_sqrt_pi_div_two, ← mul_two_eq_add_self,
      div_mul_cancel (ne_of_gt two_pos)]
  -- δ := ε·√π/2, split evenly between the two endpoint limits
  have hδ : 0 < ε * sqrt pi / (1 + 1) := div_pos_of_pos_pos (mul_pos hε hspi) two_pos
  obtain ⟨Sp, _, hSp⟩ := gaussianISigned_tendsto_pos_inf (ε * sqrt pi / (1 + 1)) hδ
  obtain ⟨Sm, _, hSm⟩ := gaussianISigned_tendsto_neg_inf (ε * sqrt pi / (1 + 1)) hδ
  refine ⟨max (max (mu + Sp * sqrt ((1 + 1) * sig2)) (-mu - Sm * sqrt ((1 + 1) * sig2))) 1,
    lt_of_lt_of_le one_pos (le_max_right _ 1), ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_trans (le_max_right _ 1) hR)
  have hRp : mu + Sp * sqrt ((1 + 1) * sig2) ≤ R :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ 1)) hR
  have hRm : -mu - Sm * sqrt ((1 + 1) * sig2) ≤ R :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ 1)) hR
  rw [gaussianDensitySymInt_eq mu sig2 hsig2 hRpos]
  -- A := gsigned((R-μ)/c), B := gsigned((-R-μ)/c); the two endpoint limits + the algebra identity.
  have hA := hSp _ (arg_lower_helper hc hcinv hRp)
  have hB := hSm _ (arg_upper_helper hc hcinv hRm)
  exact final_bound
    ((sqrt ((1 + 1) * sig2) * gaussianISigned ((R - mu) * (1 / sqrt ((1 + 1) * sig2)))
        - sqrt ((1 + 1) * sig2) * gaussianISigned ((-R - mu) * (1 / sqrt ((1 + 1) * sig2))))
      * (1 / (sqrt pi * sqrt ((1 + 1) * sig2))))
    (gaussianISigned ((R - mu) * (1 / sqrt ((1 + 1) * sig2))))
    (gaussianISigned ((-R - mu) * (1 / sqrt ((1 + 1) * sig2)))) gaussianImproperIntegral
    (sqrt pi) ε hspi
    (density_value_key (gaussianISigned ((R - mu) * (1 / sqrt ((1 + 1) * sig2))))
      (gaussianISigned ((-R - mu) * (1 / sqrt ((1 + 1) * sig2)))) gaussianImproperIntegral
      (sqrt ((1 + 1) * sig2)) (sqrt pi) (1 / (sqrt pi * sqrt ((1 + 1) * sig2))) hNinv himp)
    hA hB

/-! ## §6 — the Stein-type derivative of the density (S5)

`d/dx gaussianDensity μ σ² x = -((x-μ)/σ²)·gaussianDensity μ σ² x`. Chain rule on the scaled
kernel (`-2k²(x-μ)` with `k := 1/√(2σ²)`) times the constant normalizer, then `2k² = 1/σ²`. The
building block for the variance formula (S6). -/

private theorem two_mul_one_div_two_mul {a : Real} (ha : 0 < a) :
    (1 + 1) * (1 / ((1 + 1) * a)) = 1 / a := by
  have hne : (1 + 1) * a ≠ 0 := ne_of_gt (mul_pos two_pos ha)
  apply mul_right_cancel' hne
  rw [show (1 + 1) * (1 / ((1 + 1) * a)) * ((1 + 1) * a)
      = (1 + 1) * (1 / ((1 + 1) * a) * ((1 + 1) * a)) from by mach_ring, div_mul_cancel hne,
    mul_one_ax, show 1 / a * ((1 + 1) * a) = (1 + 1) * (1 / a * a) from by mach_ring,
    div_mul_cancel (ne_of_gt ha), mul_one_ax]

private theorem two_k_sq_eq {sig2 : Real} (hsig2 : 0 < sig2) :
    (1 + 1) * (1 / sqrt ((1 + 1) * sig2) * (1 / sqrt ((1 + 1) * sig2))) = 1 / sig2 := by
  rw [one_div_mul_one_div (sqrt_pos (two_sig2_pos hsig2)),
    sqrt_sq_nonneg _ (le_of_lt (two_sig2_pos hsig2))]
  exact two_mul_one_div_two_mul hsig2

/-- Abstract coefficient identity for the Stein derivative (abstract atoms so `mach_mpoly` avoids
the shared-`sqrt` overlapping-atom bug). -/
private theorem stein_coeff_key (E iN xm kk invS : Real) (h : (1 + 1) * kk = invS) :
    E * -((1 + 1) * (xm * kk)) * iN + E * 0 = -(xm * invS) * (E * iN) := by
  rw [show (1 + 1) * (xm * kk) = xm * ((1 + 1) * kk) from by mach_mpoly [xm, kk], h]
  mach_mpoly [E, iN, xm, invS]

theorem hasDerivAt_gaussianDensity (mu sig2 : Real) (hsig2 : 0 < sig2) (x : Real) :
    HasDerivAt (gaussianDensity mu sig2) (-((x - mu) / sig2) * gaussianDensity mu sig2 x) x := by
  have hmul := HasDerivAt_mul
    (fun y => Real.exp (-(((y - mu) * (1 / sqrt ((1 + 1) * sig2)))
      * ((y - mu) * (1 / sqrt ((1 + 1) * sig2))))))
    (fun _ => 1 / (sqrt pi * sqrt ((1 + 1) * sig2)))
    (Real.exp (-(((x - mu) * (1 / sqrt ((1 + 1) * sig2)))
      * ((x - mu) * (1 / sqrt ((1 + 1) * sig2)))))
      * -((1 + 1) * ((x - mu) * (1 / sqrt ((1 + 1) * sig2) * (1 / sqrt ((1 + 1) * sig2))))))
    0 x (hasDerivAt_scaledKernel mu (1 / sqrt ((1 + 1) * sig2)) x)
    (HasDerivAt_const (1 / (sqrt pi * sqrt ((1 + 1) * sig2))) x)
  rw [gaussianDensity_eq_kernel_mul mu sig2 hsig2]
  rw [stein_coeff_key
    (Real.exp (-(((x - mu) * (1 / sqrt ((1 + 1) * sig2)))
      * ((x - mu) * (1 / sqrt ((1 + 1) * sig2))))))
    (1 / (sqrt pi * sqrt ((1 + 1) * sig2))) (x - mu)
    (1 / sqrt ((1 + 1) * sig2) * (1 / sqrt ((1 + 1) * sig2))) (1 / sig2) (two_k_sq_eq hsig2),
    show -((x - mu) * (1 / sig2)) = -((x - mu) / sig2) from by
      rw [div_def (x - mu) sig2 (ne_of_gt hsig2)]] at hmul
  exact hmul

/-! ## §7 — tail decay: `(x-μ)·gaussianDensity μ σ² x → 0` as `|x| → ∞` (S4)

The boundary term of the variance formula's integration by parts. Reduces to `u·exp(-u²) → 0`
(`u := (x-μ)/√(2σ²)`), which follows from `exp(u²) > u²` (`exp_grows_strictly`). -/

private theorem u_exp_neg_sq_small (ε : Real) (hε : 0 < ε) :
    ∃ U : Real, 0 < U ∧ ∀ u : Real, U ≤ u → u * Real.exp (-(u * u)) < ε := by
  refine ⟨1 / ε, one_div_pos_of_pos hε, ?_⟩
  intro u hu
  have hupos : 0 < u := lt_of_lt_of_le (one_div_pos_of_pos hε) hu
  have heu : 1 ≤ ε * u := by
    have h := mul_le_mul_of_nonneg_left hu (le_of_lt hε)
    rwa [mul_inv ε (ne_of_gt hε)] at h
  have hule : u ≤ ε * (u * u) := by
    have h := mul_le_mul_of_nonneg_right heu (le_of_lt hupos)
    rwa [one_mul_thm, show ε * u * u = ε * (u * u) from by mach_mpoly [ε, u]] at h
  have hlt : u < ε * Real.exp (u * u) :=
    lt_of_le_of_lt hule (mul_lt_mul_of_pos_left (exp_grows_strictly (u * u)) hε)
  rw [exp_neg_inv, ← div_def u (Real.exp (u * u)) (ne_of_gt (exp_pos _))]
  exact div_lt_of_lt_mul hlt (exp_pos _)

/-- Two-sided version: `|u·exp(-u²)| < ε` once `|u| ≥ U`. -/
private theorem abs_u_exp_neg_sq_small (ε : Real) (hε : 0 < ε) :
    ∃ U : Real, 0 < U ∧ ∀ u : Real, U ≤ abs u → abs (u * Real.exp (-(u * u))) < ε := by
  obtain ⟨U, hU, hUspec⟩ := u_exp_neg_sq_small ε hε
  refine ⟨U, hU, ?_⟩
  intro u hu
  rw [abs_mul, abs_of_nonneg (le_of_lt (exp_pos _))]
  have huu : u * u = abs u * abs u := by
    rw [← abs_mul]; exact (abs_of_nonneg (mul_self_nonneg u)).symm
  rw [huu]
  exact hUspec (abs u) hu

/-- Abstract identity `zmu·(E/(spi·c)) = (zmu·k)·E·(1/spi)` given `c·k = 1` — reduces the density
tail `(z-μ)·gaussianDensity(z)` to `w·exp(-w²)/√π` with `w = (z-μ)·k`. Abstract atoms so `mach_ring`
avoids the shared-`sqrt` overlapping-atom bug. -/
private theorem density_tail_id (zmu E c k spi : Real) (hc : c ≠ 0) (hspi : spi ≠ 0)
    (hck : c * k = 1) :
    zmu * (E * (1 / (spi * c))) = zmu * k * E * (1 / spi) := by
  have hspic : spi * c ≠ 0 := mul_ne_zero hspi hc
  apply mul_right_cancel' hspic
  rw [show zmu * (E * (1 / (spi * c))) * (spi * c) = zmu * E * (1 / (spi * c) * (spi * c)) from by
      mach_ring, div_mul_cancel hspic, mul_one_ax,
    show zmu * k * E * (1 / spi) * (spi * c) = zmu * k * E * c * (1 / spi * spi) from by mach_ring,
    div_mul_cancel hspi, mul_one_ax,
    show zmu * k * E * c = zmu * E * (c * k) from by mach_ring, hck, mul_one_ax]

/-- Tail decay of `(z-μ)·gaussianDensity μ σ² z`: `< ε` once `|(z-μ)/√(2σ²)| ≥ D`. -/
private theorem abs_xmu_gaussianDensity_small (mu sig2 : Real) (hsig2 : 0 < sig2) (ε : Real)
    (hε : 0 < ε) : ∃ D : Real, 0 < D ∧
      ∀ z : Real, D ≤ abs ((z - mu) * (1 / sqrt ((1 + 1) * sig2))) →
        abs ((z - mu) * gaussianDensity mu sig2 z) < ε := by
  have hc : 0 < sqrt ((1 + 1) * sig2) := sqrt_pos (two_sig2_pos hsig2)
  have hspi : 0 < sqrt pi := sqrt_pos pi_pos
  obtain ⟨U, hU, hUspec⟩ := abs_u_exp_neg_sq_small (ε * sqrt pi) (mul_pos hε hspi)
  refine ⟨U, hU, ?_⟩
  intro z hz
  rw [gaussianDensity_eq_kernel_mul mu sig2 hsig2,
    density_tail_id (z - mu)
      (Real.exp (-(((z - mu) * (1 / sqrt ((1 + 1) * sig2)))
        * ((z - mu) * (1 / sqrt ((1 + 1) * sig2))))))
      (sqrt ((1 + 1) * sig2)) (1 / sqrt ((1 + 1) * sig2)) (sqrt pi) (ne_of_gt hc) (ne_of_gt hspi)
      (mul_inv _ (ne_of_gt hc))]
  -- goal: |w·exp(-w²)·(1/√π)| < ε, w = (z-μ)·k
  rw [abs_mul, abs_of_nonneg (le_of_lt (one_div_pos_of_pos hspi))]
  have hw := hUspec ((z - mu) * (1 / sqrt ((1 + 1) * sig2))) hz
  -- |w·exp(-w²)| < ε·√π ⟹ |w·exp(-w²)|·(1/√π) < ε
  have hlt := mul_lt_mul_of_pos_right hw (one_div_pos_of_pos hspi)
  rwa [show ε * sqrt pi * (1 / sqrt pi) = ε from by
    rw [show ε * sqrt pi * (1 / sqrt pi) = ε * (sqrt pi * (1 / sqrt pi)) from by mach_ring,
      mul_inv (sqrt pi) (ne_of_gt hspi), mul_one_ax]] at hlt

/-! ## §8 — the variance formula `∫(x-μ)²·gaussianDensity μ σ² dx = σ²` (S6, second milestone)

Integration by parts: `G(x) := -σ²·(x-μ)·gaussianDensity(x)` has, via the product rule + the Stein
derivative (S5), `G'(x) = (x-μ)²·gaussianDensity(x) - σ²·gaussianDensity(x)`. So `(x-μ)²·dens =
G' + σ²·dens`, and integrating `[-R,R]`: `∫(x-μ)²dens = (G(R)-G(-R)) + σ²·∫dens` (S0 additivity +
`riemann_integral_mul_const` + `ftc_riemann`). As `R→∞`: `G(±R)→0` (tail decay S4), `∫dens→1` (S3),
so the variance is `σ²`. -/

/-- Abstract coefficient identity for `G`'s derivative (`σ²·(1/σ²)=1` via `hinv`; abstract atoms
avoid the overlapping-atom bug). -/
private theorem Gderiv_coeff (d xm sig2 invsig A : Real) (hinv : sig2 * invsig = 1) :
    -(0 * A + sig2 * (1 * d + xm * (-(xm * invsig) * d))) = xm * xm * d - d * sig2 := by
  rw [show -(0 * A + sig2 * (1 * d + xm * (-(xm * invsig) * d)))
      = xm * xm * d * (sig2 * invsig) - d * sig2 from by mach_mpoly [d, xm, sig2, invsig, A],
    hinv, mul_one_ax]

theorem hasDerivAt_Gfn (mu sig2 : Real) (hsig2 : 0 < sig2) (x : Real) :
    HasDerivAt (fun y => -(sig2 * ((y - mu) * gaussianDensity mu sig2 y)))
      ((x - mu) * (x - mu) * gaussianDensity mu sig2 x - gaussianDensity mu sig2 x * sig2) x := by
  have hsub : HasDerivAt (fun y => y - mu) (1 - 0) x :=
    HasDerivAt_sub (fun y => y) (fun _ => mu) 1 0 x (HasDerivAt_id x) (HasDerivAt_const mu x)
  rw [sub_zero] at hsub
  have hprod := HasDerivAt_mul (fun y => y - mu) (gaussianDensity mu sig2) 1
    (-((x - mu) / sig2) * gaussianDensity mu sig2 x) x hsub
    (hasDerivAt_gaussianDensity mu sig2 hsig2 x)
  have hsig := HasDerivAt_mul (fun _ => sig2) (fun y => (y - mu) * gaussianDensity mu sig2 y)
    0 (1 * gaussianDensity mu sig2 x
      + (x - mu) * (-((x - mu) / sig2) * gaussianDensity mu sig2 x)) x
    (HasDerivAt_const sig2 x) hprod
  have hneg := HasDerivAt_neg (fun y => sig2 * ((y - mu) * gaussianDensity mu sig2 y))
    (0 * ((x - mu) * gaussianDensity mu sig2 x)
      + sig2 * (1 * gaussianDensity mu sig2 x
        + (x - mu) * (-((x - mu) / sig2) * gaussianDensity mu sig2 x))) x hsig
  rw [div_def (x - mu) sig2 (ne_of_gt hsig2),
    Gderiv_coeff (gaussianDensity mu sig2 x) (x - mu) sig2 (1 / sig2)
      ((x - mu) * gaussianDensity mu sig2 x) (mul_inv sig2 (ne_of_gt hsig2))] at hneg
  exact hneg

private theorem continuousAt_xmu (mu x : Real) : ContinuousAt (fun y => y - mu) x :=
  hasDerivAt_continuousAt
    (HasDerivAt_sub (fun y => y) (fun _ => mu) 1 0 x (HasDerivAt_id x) (HasDerivAt_const mu x))

private theorem continuousAt_varInt (mu sig2 : Real) (hsig2 : 0 < sig2) (x : Real) :
    ContinuousAt (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y) x :=
  continuousAt_mul (continuousAt_mul (continuousAt_xmu mu x) (continuousAt_xmu mu x))
    (continuousAt_gaussianDensity mu sig2 hsig2 x)

private theorem continuousAt_densSig2 (mu sig2 : Real) (hsig2 : 0 < sig2) (x : Real) :
    ContinuousAt (fun y => gaussianDensity mu sig2 y * sig2) x :=
  continuousAt_mul (continuousAt_gaussianDensity mu sig2 hsig2 x) (continuousAt_const sig2 x)

private theorem continuousAt_Gderiv (mu sig2 : Real) (hsig2 : 0 < sig2) (x : Real) :
    ContinuousAt (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y
      - gaussianDensity mu sig2 y * sig2) x := by
  rw [show (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y
        - gaussianDensity mu sig2 y * sig2)
      = (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y
        + -(gaussianDensity mu sig2 y * sig2)) from by funext y; exact sub_def _ _]
  exact continuousAt_add (continuousAt_varInt mu sig2 hsig2 x)
    (continuousAt_neg (continuousAt_densSig2 mu sig2 hsig2 x))

private theorem varInt_split (xm d sig2 : Real) : xm * xm * d = xm * xm * d - d * sig2 + d * sig2 := by
  mach_mpoly [xm, d, sig2]

/-- `∫_{-R}^R (x-μ)²·gaussianDensity μ σ² dx` as a total function (`0` off `R > 0`). -/
noncomputable def gaussianVarSymInt (mu sig2 : Real) (hsig2 : 0 < sig2) (R : Real) : Real :=
  if h : 0 < R then
    Classical.choose (continuous_riemann_integrable
      (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y) (-R) R
      (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun z _ _ => continuousAt_varInt mu sig2 hsig2 z))
  else 0

private theorem gaussianVarSymInt_eq (mu sig2 : Real) (hsig2 : 0 < sig2) {R : Real} (hR : 0 < R) :
    gaussianVarSymInt mu sig2 hsig2 R
      = -(sig2 * ((R - mu) * gaussianDensity mu sig2 R))
          - -(sig2 * ((-R - mu) * gaussianDensity mu sig2 (-R)))
        + gaussianDensitySymInt mu sig2 hsig2 R * sig2 := by
  have hab : -R < R := lt_trans_ax (neg_neg_of_pos hR) hR
  have hgd : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y
        - gaussianDensity mu sig2 y * sig2) z :=
    fun z _ _ => continuousAt_Gderiv mu sig2 hsig2 z
  have hds : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => gaussianDensity mu sig2 y * sig2) z :=
    fun z _ _ => continuousAt_densSig2 mu sig2 hsig2 z
  have hd : ∀ z : Real, -R ≤ z → z ≤ R → ContinuousAt (gaussianDensity mu sig2) z :=
    fun z _ _ => continuousAt_gaussianDensity mu sig2 hsig2 z
  have hsum : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => ((y - mu) * (y - mu) * gaussianDensity mu sig2 y
        - gaussianDensity mu sig2 y * sig2) + gaussianDensity mu sig2 y * sig2) z :=
    fun z hz0 hz1 => continuousAt_add (hgd z hz0 hz1) (hds z hz0 hz1)
  have hvar : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y) z :=
    fun z _ _ => continuousAt_varInt mu sig2 hsig2 z
  have hfeq : (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y)
      = (fun y => ((y - mu) * (y - mu) * gaussianDensity mu sig2 y
        - gaussianDensity mu sig2 y * sig2) + gaussianDensity mu sig2 y * sig2) := by
    funext y; exact varInt_split (y - mu) (gaussianDensity mu sig2 y) sig2
  show (if h : 0 < R then Classical.choose (continuous_riemann_integrable
      (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y) (-R) R
      (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun z _ _ => continuousAt_varInt mu sig2 hsig2 z)) else 0) = _
  rw [dif_pos hR]
  rw [cri_congr hfeq (le_of_lt hab) hvar hsum]
  rw [riemann_integral_add (le_of_lt hab) hgd hds hsum]
  -- ∫Gderiv = Gfn R - Gfn(-R) via FTC
  have hspecG := Classical.choose_spec (continuous_riemann_integrable
    (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y
      - gaussianDensity mu sig2 y * sig2) (-R) R (le_of_lt hab) hgd)
  rw [ftc_riemann (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y
      - gaussianDensity mu sig2 y * sig2) (fun y => -(sig2 * ((y - mu) * gaussianDensity mu sig2 y)))
    (-R) R hab hgd (fun z _ _ => hasDerivAt_Gfn mu sig2 hsig2 z) _
    (fun k => (hspecG.1 k).1) (fun k => (hspecG.1 k).2) hspecG.2]
  -- ∫(dens·sig2) = (∫dens)·sig2 via mul_const; ∫dens = gaussianDensitySymInt
  rw [riemann_integral_mul_const (le_of_lt hab) hd hds]
  rw [show gaussianDensitySymInt mu sig2 hsig2 R = Classical.choose (continuous_riemann_integrable
      (gaussianDensity mu sig2) (-R) R (le_of_lt hab) hd) from by
    show (if h : 0 < R then Classical.choose (continuous_riemann_integrable (gaussianDensity mu sig2)
        (-R) R (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
        (fun z _ _ => continuousAt_gaussianDensity mu sig2 hsig2 z)) else 0)
      = Classical.choose (continuous_riemann_integrable (gaussianDensity mu sig2) (-R) R
        (le_of_lt hab) hd)
    rw [dif_pos hR]]

private theorem abs_arg_lower_pos {D mu R c : Real} (hc : 0 < c) (hcinv : c * (1 / c) = 1)
    (hD : 0 < D) (h : mu + D * c ≤ R) : D ≤ abs ((R - mu) * (1 / c)) := by
  have h1 : D ≤ (R - mu) * (1 / c) := arg_lower_helper hc hcinv h
  rwa [abs_of_nonneg (le_trans (le_of_lt hD) h1)]

private theorem abs_arg_lower_neg {D mu R c : Real} (hc : 0 < c) (hcinv : c * (1 / c) = 1)
    (hD : 0 < D) (h : -mu + D * c ≤ R) : D ≤ abs ((-R - mu) * (1 / c)) := by
  have h1 : D ≤ (R - -mu) * (1 / c) := arg_lower_helper hc hcinv h
  rw [show (-R - mu) * (1 / c) = -((R - -mu) * (1 / c)) from by
      mach_mpoly [R, mu, (1 / c : Real)], abs_neg, abs_of_nonneg (le_trans (le_of_lt hD) h1)]
  exact h1

private theorem third_add_third_add_third (ε : Real) :
    ε / (1 + 1 + 1) + ε / (1 + 1 + 1) + ε / (1 + 1 + 1) = ε := by
  rw [show ε / (1 + 1 + 1) + ε / (1 + 1 + 1) + ε / (1 + 1 + 1) = (1 + 1 + 1) * (ε / (1 + 1 + 1))
      from by mach_mpoly [ε / (1 + 1 + 1)],
    mul_div_cancel' (ne_of_gt (add_pos_of_nonneg_pos (le_of_lt two_pos) one_pos))]

private theorem var_final_bound (GR GnR Wsig sig2 ε : Real)
    (hGR : abs GR < ε / (1 + 1 + 1)) (hGnR : abs GnR < ε / (1 + 1 + 1))
    (hW : abs (Wsig - sig2) < ε / (1 + 1 + 1)) : abs (GR - GnR + Wsig - sig2) < ε := by
  rw [show GR - GnR + Wsig - sig2 = GR - GnR + (Wsig - sig2) from by
    mach_mpoly [GR, GnR, Wsig, sig2]]
  have h1 : abs (GR - GnR + (Wsig - sig2)) ≤ abs GR + abs GnR + abs (Wsig - sig2) := by
    have t1 := abs_add (GR - GnR) (Wsig - sig2)
    have t2 := abs_add GR (-GnR)
    rw [show GR + -GnR = GR - GnR from by mach_mpoly [GR, GnR], abs_neg] at t2
    exact le_trans t1 (add_le_add_both t2 (le_refl (abs (Wsig - sig2))))
  have h2 : abs GR + abs GnR + abs (Wsig - sig2) < ε := by
    have h := add_lt_add_both (add_lt_add_both hGR hGnR) hW
    rwa [third_add_third_add_third ε] at h
  exact lt_of_le_of_lt h1 h2

/-- **`∫_{-∞}^∞ (x-μ)²·gaussianDensity μ σ² dx = σ²`** — the variance of `N(μ,σ²)` is `σ²`. Stated as
an ε–R₀ limit of the symmetric finite integral (S6, the arc's second milestone). -/
theorem gaussianVarSymInt_tendsto_sigma2 (mu sig2 : Real) (hsig2 : 0 < sig2) :
    ∀ ε : Real, 0 < ε → ∃ R₀ : Real, 0 < R₀ ∧
      ∀ R : Real, R₀ ≤ R → abs (gaussianVarSymInt mu sig2 hsig2 R - sig2) < ε := by
  intro ε hε
  have hc : 0 < sqrt ((1 + 1) * sig2) := sqrt_pos (two_sig2_pos hsig2)
  have hcinv : sqrt ((1 + 1) * sig2) * (1 / sqrt ((1 + 1) * sig2)) = 1 := mul_inv _ (ne_of_gt hc)
  have hε3 : 0 < ε / (1 + 1 + 1) := div_pos_of_pos_pos hε
    (add_pos_of_nonneg_pos (le_of_lt two_pos) one_pos)
  have hε3s : 0 < ε / (1 + 1 + 1) / sig2 := div_pos_of_pos_pos hε3 hsig2
  obtain ⟨D, hD, hDspec⟩ := abs_xmu_gaussianDensity_small mu sig2 hsig2 (ε / (1 + 1 + 1) / sig2) hε3s
  obtain ⟨R1, hR1pos, hR1⟩ :=
    gaussianDensity_symInt_tendsto_one mu sig2 hsig2 (ε / (1 + 1 + 1) / sig2) hε3s
  refine ⟨max (max (mu + D * sqrt ((1 + 1) * sig2)) (-mu + D * sqrt ((1 + 1) * sig2)))
    (max R1 1), lt_of_lt_of_le one_pos (le_trans (le_max_right R1 1) (le_max_right _ _)), ?_⟩
  intro R hR
  have hRpos : 0 < R :=
    lt_of_lt_of_le one_pos (le_trans (le_trans (le_max_right R1 1) (le_max_right _ _)) hR)
  have hRp : mu + D * sqrt ((1 + 1) * sig2) ≤ R :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hR
  have hRm : -mu + D * sqrt ((1 + 1) * sig2) ≤ R :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hR
  have hRR1 : R1 ≤ R := le_trans (le_trans (le_max_left R1 1) (le_max_right _ _)) hR
  rw [gaussianVarSymInt_eq mu sig2 hsig2 hRpos]
  -- bound the two boundary terms via tail decay + the density term via S3
  have hGR : abs (-(sig2 * ((R - mu) * gaussianDensity mu sig2 R))) < ε / (1 + 1 + 1) := by
    rw [abs_neg, abs_mul, abs_of_nonneg (le_of_lt hsig2)]
    have h := mul_lt_mul_of_pos_left (hDspec R (abs_arg_lower_pos hc hcinv hD hRp)) hsig2
    rwa [mul_div_cancel_left (ne_of_gt hsig2)] at h
  have hGnR : abs (-(sig2 * ((-R - mu) * gaussianDensity mu sig2 (-R)))) < ε / (1 + 1 + 1) := by
    rw [abs_neg, abs_mul, abs_of_nonneg (le_of_lt hsig2)]
    have h := mul_lt_mul_of_pos_left (hDspec (-R) (abs_arg_lower_neg hc hcinv hD hRm)) hsig2
    rwa [mul_div_cancel_left (ne_of_gt hsig2)] at h
  have hW : abs (gaussianDensitySymInt mu sig2 hsig2 R * sig2 - sig2) < ε / (1 + 1 + 1) := by
    rw [show gaussianDensitySymInt mu sig2 hsig2 R * sig2 - sig2
        = (gaussianDensitySymInt mu sig2 hsig2 R - 1) * sig2 from by
      mach_mpoly [gaussianDensitySymInt mu sig2 hsig2 R, sig2], abs_mul,
      abs_of_nonneg (le_of_lt hsig2)]
    have h := mul_lt_mul_of_pos_right (hR1 R hRR1) hsig2
    rwa [div_mul_cancel (ne_of_gt hsig2)] at h
  exact var_final_bound (-(sig2 * ((R - mu) * gaussianDensity mu sig2 R)))
    (-(sig2 * ((-R - mu) * gaussianDensity mu sig2 (-R))))
    (gaussianDensitySymInt mu sig2 hsig2 R * sig2) sig2 ε hGR hGnR hW

/-! ## §9 — the parallel-axis theorem `∫(x-c)²·gaussianDensity μ σ² dx = σ² + (c-μ)²` (S7)

Generalizes the variance (S6, the `c=μ` case). Expand `(x-c)² = (x-μ)² + 2(x-μ)(μ-c) + (μ-c)²` and
integrate: the mean term `∫(x-μ)·dens = 0` (its antiderivative `-σ²·dens` is elementary, and
`dens → 0` at ±∞), plus `∫(x-μ)²·dens = σ²` (S6) and `∫dens = 1` (S3). The key MMSE-optimality
inner-integral fact: the mean-squared error of a constant estimator `c` is `σ² + (bias)²`. -/

private theorem abs_exp_neg_sq_small (ε : Real) (hε : 0 < ε) :
    ∃ W : Real, 0 < W ∧ ∀ w : Real, W ≤ abs w → Real.exp (-(w * w)) < ε := by
  obtain ⟨x0, hx0, hx0e⟩ := exp_neg_sq_small ε hε
  refine ⟨x0, hx0, ?_⟩
  intro w hw
  have hww : x0 * x0 ≤ w * w := by
    have h := mul_le_mul' (le_of_lt hx0) hw (le_of_lt hx0) hw
    rwa [← abs_mul, abs_of_nonneg (mul_self_nonneg w)] at h
  exact lt_of_le_of_lt (exp_monotone (neg_le_neg hww)) hx0e

/-- `gaussianDensity μ σ² z → 0` as `|(z-μ)/√(2σ²)| → ∞`. -/
private theorem gaussianDensity_small (mu sig2 : Real) (hsig2 : 0 < sig2) (ε : Real) (hε : 0 < ε) :
    ∃ D : Real, 0 < D ∧ ∀ z : Real,
      D ≤ abs ((z - mu) * (1 / sqrt ((1 + 1) * sig2))) → gaussianDensity mu sig2 z < ε := by
  have hc : 0 < sqrt ((1 + 1) * sig2) := sqrt_pos (two_sig2_pos hsig2)
  have hspi : 0 < sqrt pi := sqrt_pos pi_pos
  have hN : 0 < sqrt pi * sqrt ((1 + 1) * sig2) := mul_pos hspi hc
  obtain ⟨W, hW, hWspec⟩ := abs_exp_neg_sq_small (ε * (sqrt pi * sqrt ((1 + 1) * sig2))) (mul_pos hε hN)
  refine ⟨W, hW, ?_⟩
  intro z hz
  rw [gaussianDensity]
  rw [div_def _ _ (ne_of_gt hN)]
  have hexp := hWspec ((z - mu) * (1 / sqrt ((1 + 1) * sig2))) hz
  have hlt := mul_lt_mul_of_pos_right hexp (one_div_pos_of_pos hN)
  rwa [mul_assoc ε (sqrt pi * sqrt ((1 + 1) * sig2)) (1 / (sqrt pi * sqrt ((1 + 1) * sig2))),
    mul_inv _ (ne_of_gt hN), mul_one_ax] at hlt

private theorem meanAnti_coeff (d xm sig2 invsig : Real) (hinv : sig2 * invsig = 1) :
    -(0 * d + sig2 * (-(xm * invsig) * d)) = xm * d := by
  rw [show -(0 * d + sig2 * (-(xm * invsig) * d)) = xm * d * (sig2 * invsig) from by
    mach_mpoly [d, xm, sig2, invsig], hinv, mul_one_ax]

/-- Elementary antiderivative of `(x-μ)·gaussianDensity`: `-σ²·gaussianDensity(x)` (Stein again). -/
theorem hasDerivAt_meanAnti (mu sig2 : Real) (hsig2 : 0 < sig2) (x : Real) :
    HasDerivAt (fun y => -(sig2 * gaussianDensity mu sig2 y))
      ((x - mu) * gaussianDensity mu sig2 x) x := by
  have hmul := HasDerivAt_mul (fun _ => sig2) (gaussianDensity mu sig2) 0
    (-((x - mu) / sig2) * gaussianDensity mu sig2 x) x (HasDerivAt_const sig2 x)
    (hasDerivAt_gaussianDensity mu sig2 hsig2 x)
  have hneg := HasDerivAt_neg (fun y => sig2 * gaussianDensity mu sig2 y)
    (0 * gaussianDensity mu sig2 x
      + sig2 * (-((x - mu) / sig2) * gaussianDensity mu sig2 x)) x hmul
  rw [div_def (x - mu) sig2 (ne_of_gt hsig2),
    meanAnti_coeff (gaussianDensity mu sig2 x) (x - mu) sig2 (1 / sig2)
      (mul_inv sig2 (ne_of_gt hsig2))] at hneg
  exact hneg

private theorem continuousAt_meanInt (mu sig2 : Real) (hsig2 : 0 < sig2) (x : Real) :
    ContinuousAt (fun y => (y - mu) * gaussianDensity mu sig2 y) x :=
  continuousAt_mul (continuousAt_xmu mu x) (continuousAt_gaussianDensity mu sig2 hsig2 x)

/-- `∫_{-R}^R (x-μ)·gaussianDensity μ σ² dx` as a total function (`0` off `R > 0`). -/
noncomputable def gaussianMeanSymInt (mu sig2 : Real) (hsig2 : 0 < sig2) (R : Real) : Real :=
  if h : 0 < R then
    Classical.choose (continuous_riemann_integrable
      (fun y => (y - mu) * gaussianDensity mu sig2 y) (-R) R
      (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun z _ _ => continuousAt_meanInt mu sig2 hsig2 z))
  else 0

private theorem gaussianMeanSymInt_eq (mu sig2 : Real) (hsig2 : 0 < sig2) {R : Real} (hR : 0 < R) :
    gaussianMeanSymInt mu sig2 hsig2 R
      = -(sig2 * gaussianDensity mu sig2 R) - -(sig2 * gaussianDensity mu sig2 (-R)) := by
  have hab : -R < R := lt_trans_ax (neg_neg_of_pos hR) hR
  have hspec := Classical.choose_spec (continuous_riemann_integrable
    (fun y => (y - mu) * gaussianDensity mu sig2 y) (-R) R (le_of_lt hab)
    (fun z _ _ => continuousAt_meanInt mu sig2 hsig2 z))
  show (if h : 0 < R then Classical.choose (continuous_riemann_integrable
      (fun y => (y - mu) * gaussianDensity mu sig2 y) (-R) R
      (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun z _ _ => continuousAt_meanInt mu sig2 hsig2 z)) else 0) = _
  rw [dif_pos hR]
  exact ftc_riemann (fun y => (y - mu) * gaussianDensity mu sig2 y)
    (fun y => -(sig2 * gaussianDensity mu sig2 y)) (-R) R hab
    (fun z _ _ => continuousAt_meanInt mu sig2 hsig2 z)
    (fun z _ _ => hasDerivAt_meanAnti mu sig2 hsig2 z) _
    (fun k => (hspec.1 k).1) (fun k => (hspec.1 k).2) hspec.2

private theorem mean_final_bound (A B ε : Real) (hA : abs A < ε / (1 + 1))
    (hB : abs B < ε / (1 + 1)) : abs (-A - -B) < ε := by
  rw [show -A - -B = -A + B from by mach_mpoly [A, B]]
  have h1 : abs (-A + B) ≤ abs A + abs B := by
    have h := abs_add (-A) B; rwa [abs_neg] at h
  have h2 : abs A + abs B < ε := by
    have h := add_lt_add_both hA hB; rwa [half_add_half ε] at h
  exact lt_of_le_of_lt h1 h2

/-- **`∫_{-∞}^∞ (x-μ)·gaussianDensity μ σ² dx = 0`** — the mean of `N(μ,σ²)` is `μ`. Stated as an
ε–R₀ limit; the antiderivative `-σ²·dens` is elementary and vanishes at ±∞. -/
theorem gaussianMeanSymInt_tendsto_zero (mu sig2 : Real) (hsig2 : 0 < sig2) :
    ∀ ε : Real, 0 < ε → ∃ R₀ : Real, 0 < R₀ ∧
      ∀ R : Real, R₀ ≤ R → abs (gaussianMeanSymInt mu sig2 hsig2 R) < ε := by
  intro ε hε
  have hc : 0 < sqrt ((1 + 1) * sig2) := sqrt_pos (two_sig2_pos hsig2)
  have hcinv : sqrt ((1 + 1) * sig2) * (1 / sqrt ((1 + 1) * sig2)) = 1 := mul_inv _ (ne_of_gt hc)
  have hε2 : 0 < ε / (1 + 1) := div_pos_of_pos_pos hε two_pos
  have hε2s : 0 < ε / (1 + 1) / sig2 := div_pos_of_pos_pos hε2 hsig2
  obtain ⟨D, hD, hDspec⟩ := gaussianDensity_small mu sig2 hsig2 (ε / (1 + 1) / sig2) hε2s
  refine ⟨max (max (mu + D * sqrt ((1 + 1) * sig2)) (-mu + D * sqrt ((1 + 1) * sig2))) 1,
    lt_of_lt_of_le one_pos (le_max_right _ 1), ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_trans (le_max_right _ 1) hR)
  have hRp : mu + D * sqrt ((1 + 1) * sig2) ≤ R :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ 1)) hR
  have hRm : -mu + D * sqrt ((1 + 1) * sig2) ≤ R :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ 1)) hR
  rw [gaussianMeanSymInt_eq mu sig2 hsig2 hRpos]
  have hbnd : ∀ z : Real, D ≤ abs ((z - mu) * (1 / sqrt ((1 + 1) * sig2))) →
      abs (sig2 * gaussianDensity mu sig2 z) < ε / (1 + 1) := by
    intro z hz
    rw [abs_of_nonneg (le_of_lt (mul_pos hsig2 (gaussianDensity_pos mu sig2 hsig2 z)))]
    have h := mul_lt_mul_of_pos_left (hDspec z hz) hsig2
    rwa [mul_div_cancel_left (ne_of_gt hsig2)] at h
  exact mean_final_bound (sig2 * gaussianDensity mu sig2 R)
    (sig2 * gaussianDensity mu sig2 (-R))
    ε (hbnd R (abs_arg_lower_pos hc hcinv hD hRp)) (hbnd (-R) (abs_arg_lower_neg hc hcinv hD hRm))

/-! ### The full parallel-axis theorem, via the mean/variance/normalization tendsto's. -/

private theorem varC_split (x c mu d : Real) :
    (x - c) * (x - c) * d
      = (x - mu) * (x - mu) * d + (x - mu) * d * ((1 + 1) * (mu - c)) + d * ((mu - c) * (mu - c)) := by
  mach_mpoly [x, c, mu, d]

private theorem continuousAt_meanIntC (mu sig2 : Real) (hsig2 : 0 < sig2) (cc : Real) (x : Real) :
    ContinuousAt (fun y => (y - mu) * gaussianDensity mu sig2 y * cc) x :=
  continuousAt_mul (continuousAt_meanInt mu sig2 hsig2 x) (continuousAt_const cc x)

private theorem continuousAt_densC (mu sig2 : Real) (hsig2 : 0 < sig2) (cc : Real) (x : Real) :
    ContinuousAt (fun y => gaussianDensity mu sig2 y * cc) x :=
  continuousAt_mul (continuousAt_gaussianDensity mu sig2 hsig2 x) (continuousAt_const cc x)

private theorem continuousAt_varCInt (mu sig2 : Real) (hsig2 : 0 < sig2) (c : Real) (x : Real) :
    ContinuousAt (fun y => (y - c) * (y - c) * gaussianDensity mu sig2 y) x :=
  continuousAt_mul (continuousAt_mul (continuousAt_xmu c x) (continuousAt_xmu c x))
    (continuousAt_gaussianDensity mu sig2 hsig2 x)

/-- `∫_{-R}^R (x-c)²·gaussianDensity μ σ² dx` as a total function (`0` off `R > 0`). -/
noncomputable def gaussianVarCSymInt (mu sig2 : Real) (hsig2 : 0 < sig2) (c R : Real) : Real :=
  if h : 0 < R then
    Classical.choose (continuous_riemann_integrable
      (fun y => (y - c) * (y - c) * gaussianDensity mu sig2 y) (-R) R
      (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun z _ _ => continuousAt_varCInt mu sig2 hsig2 c z))
  else 0

private theorem gaussianVarCSymInt_eq (mu sig2 : Real) (hsig2 : 0 < sig2) (c : Real) {R : Real}
    (hR : 0 < R) :
    gaussianVarCSymInt mu sig2 hsig2 c R
      = gaussianVarSymInt mu sig2 hsig2 R
          + gaussianMeanSymInt mu sig2 hsig2 R * ((1 + 1) * (mu - c))
        + gaussianDensitySymInt mu sig2 hsig2 R * ((mu - c) * (mu - c)) := by
  have hab : -R < R := lt_trans_ax (neg_neg_of_pos hR) hR
  have hle := le_of_lt hab
  -- continuity witnesses
  have hV : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y) z :=
    fun z _ _ => continuousAt_varInt mu sig2 hsig2 z
  have hM : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => (y - mu) * gaussianDensity mu sig2 y * ((1 + 1) * (mu - c))) z :=
    fun z _ _ => continuousAt_meanIntC mu sig2 hsig2 ((1 + 1) * (mu - c)) z
  have hDc : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => gaussianDensity mu sig2 y * ((mu - c) * (mu - c))) z :=
    fun z _ _ => continuousAt_densC mu sig2 hsig2 ((mu - c) * (mu - c)) z
  have hVM : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y
        + (y - mu) * gaussianDensity mu sig2 y * ((1 + 1) * (mu - c))) z :=
    fun z hz0 hz1 => continuousAt_add (hV z hz0 hz1) (hM z hz0 hz1)
  have hVMD : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => ((y - mu) * (y - mu) * gaussianDensity mu sig2 y
        + (y - mu) * gaussianDensity mu sig2 y * ((1 + 1) * (mu - c)))
        + gaussianDensity mu sig2 y * ((mu - c) * (mu - c))) z :=
    fun z hz0 hz1 => continuousAt_add (hVM z hz0 hz1) (hDc z hz0 hz1)
  have hVC : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => (y - c) * (y - c) * gaussianDensity mu sig2 y) z :=
    fun z _ _ => continuousAt_varCInt mu sig2 hsig2 c z
  -- dens & meanInt continuity for mul_const
  have hd : ∀ z : Real, -R ≤ z → z ≤ R → ContinuousAt (gaussianDensity mu sig2) z :=
    fun z _ _ => continuousAt_gaussianDensity mu sig2 hsig2 z
  have hmi : ∀ z : Real, -R ≤ z → z ≤ R →
      ContinuousAt (fun y => (y - mu) * gaussianDensity mu sig2 y) z :=
    fun z _ _ => continuousAt_meanInt mu sig2 hsig2 z
  have hfeq : (fun y => (y - c) * (y - c) * gaussianDensity mu sig2 y)
      = (fun y => ((y - mu) * (y - mu) * gaussianDensity mu sig2 y
          + (y - mu) * gaussianDensity mu sig2 y * ((1 + 1) * (mu - c)))
        + gaussianDensity mu sig2 y * ((mu - c) * (mu - c))) := by
    funext y; exact varC_split y c mu (gaussianDensity mu sig2 y)
  show (if h : 0 < R then Classical.choose (continuous_riemann_integrable
      (fun y => (y - c) * (y - c) * gaussianDensity mu sig2 y) (-R) R
      (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
      (fun z _ _ => continuousAt_varCInt mu sig2 hsig2 c z)) else 0) = _
  have e1 : gaussianVarSymInt mu sig2 hsig2 R = Classical.choose (continuous_riemann_integrable
      (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y) (-R) R hle hV) := by
    show (if h : 0 < R then Classical.choose (continuous_riemann_integrable
        (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y) (-R) R
        (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
        (fun z _ _ => continuousAt_varInt mu sig2 hsig2 z)) else 0)
      = Classical.choose (continuous_riemann_integrable
        (fun y => (y - mu) * (y - mu) * gaussianDensity mu sig2 y) (-R) R hle hV)
    rw [dif_pos hR]
  have e2 : gaussianMeanSymInt mu sig2 hsig2 R = Classical.choose (continuous_riemann_integrable
      (fun y => (y - mu) * gaussianDensity mu sig2 y) (-R) R hle hmi) := by
    show (if h : 0 < R then Classical.choose (continuous_riemann_integrable
        (fun y => (y - mu) * gaussianDensity mu sig2 y) (-R) R
        (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
        (fun z _ _ => continuousAt_meanInt mu sig2 hsig2 z)) else 0)
      = Classical.choose (continuous_riemann_integrable
        (fun y => (y - mu) * gaussianDensity mu sig2 y) (-R) R hle hmi)
    rw [dif_pos hR]
  have e3 : gaussianDensitySymInt mu sig2 hsig2 R = Classical.choose (continuous_riemann_integrable
      (gaussianDensity mu sig2) (-R) R hle hd) := by
    show (if h : 0 < R then Classical.choose (continuous_riemann_integrable (gaussianDensity mu sig2)
        (-R) R (le_of_lt (lt_trans_ax (neg_neg_of_pos h) h))
        (fun z _ _ => continuousAt_gaussianDensity mu sig2 hsig2 z)) else 0)
      = Classical.choose (continuous_riemann_integrable (gaussianDensity mu sig2) (-R) R hle hd)
    rw [dif_pos hR]
  rw [dif_pos hR, cri_congr hfeq hle hVC hVMD, riemann_integral_add hle hVM hDc hVMD,
    riemann_integral_add hle hV hM hVM, riemann_integral_mul_const hle hmi hM,
    riemann_integral_mul_const hle hd hDc, ← e1, ← e2, ← e3]

private theorem varC_final_bound (V M Dn sig2 mc ε : Real) (hV : abs (V - sig2) < ε / (1 + 1 + 1))
    (hM : abs M * (abs ((1 + 1) * mc) + 1) < ε / (1 + 1 + 1))
    (hDn : abs (Dn - 1) * (mc * mc + 1) < ε / (1 + 1 + 1)) :
    abs (V + M * ((1 + 1) * mc) + Dn * (mc * mc) - (sig2 + mc * mc)) < ε := by
  rw [show V + M * ((1 + 1) * mc) + Dn * (mc * mc) - (sig2 + mc * mc)
      = V - sig2 + M * ((1 + 1) * mc) + (Dn - 1) * (mc * mc) from by
    mach_mpoly [V, M, Dn, sig2, mc]]
  have hMb : abs (M * ((1 + 1) * mc)) < ε / (1 + 1 + 1) := by
    rw [abs_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (le_of_lt one_pos))
      (abs_nonneg M)) hM
  have hDnb : abs ((Dn - 1) * (mc * mc)) < ε / (1 + 1 + 1) := by
    rw [abs_mul, abs_of_nonneg (mul_self_nonneg mc)]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (le_of_lt one_pos))
      (abs_nonneg (Dn - 1))) hDn
  have htri : abs (V - sig2 + M * ((1 + 1) * mc) + (Dn - 1) * (mc * mc))
      ≤ abs (V - sig2) + abs (M * ((1 + 1) * mc)) + abs ((Dn - 1) * (mc * mc)) := by
    have t1 := abs_add (V - sig2 + M * ((1 + 1) * mc)) ((Dn - 1) * (mc * mc))
    have t2 := abs_add (V - sig2) (M * ((1 + 1) * mc))
    exact le_trans t1 (add_le_add_both t2 (le_refl _))
  have hsum : abs (V - sig2) + abs (M * ((1 + 1) * mc)) + abs ((Dn - 1) * (mc * mc)) < ε := by
    have h := add_lt_add_both (add_lt_add_both hV hMb) hDnb
    rwa [third_add_third_add_third ε] at h
  exact lt_of_le_of_lt htri hsum

/-- **`∫_{-∞}^∞ (x-c)²·gaussianDensity μ σ² dx = σ² + (c-μ)²`** — the parallel-axis / bias-variance
decomposition for `N(μ,σ²)` (S7). The mean-squared error of the constant estimator `c` is the
variance plus the squared bias. This is the MMSE-optimality inner-integral fact. -/
theorem gaussianVarCSymInt_tendsto (mu sig2 c : Real) (hsig2 : 0 < sig2) :
    ∀ ε : Real, 0 < ε → ∃ R₀ : Real, 0 < R₀ ∧
      ∀ R : Real, R₀ ≤ R →
        abs (gaussianVarCSymInt mu sig2 hsig2 c R - (sig2 + (c - mu) * (c - mu))) < ε := by
  intro ε hε
  have hε3 : 0 < ε / (1 + 1 + 1) := div_pos_of_pos_pos hε
    (add_pos_of_nonneg_pos (le_of_lt two_pos) one_pos)
  have hcoef1 : 0 < abs ((1 + 1) * (mu - c)) + 1 := add_pos_of_nonneg_pos (abs_nonneg _) one_pos
  have hcoef2 : 0 < (mu - c) * (mu - c) + 1 := add_pos_of_nonneg_pos (mul_self_nonneg _) one_pos
  obtain ⟨R1, hR1p, hR1⟩ := gaussianVarSymInt_tendsto_sigma2 mu sig2 hsig2 (ε / (1 + 1 + 1)) hε3
  obtain ⟨R2, hR2p, hR2⟩ := gaussianMeanSymInt_tendsto_zero mu sig2 hsig2
    (ε / (1 + 1 + 1) / (abs ((1 + 1) * (mu - c)) + 1)) (div_pos_of_pos_pos hε3 hcoef1)
  obtain ⟨R3, hR3p, hR3⟩ := gaussianDensity_symInt_tendsto_one mu sig2 hsig2
    (ε / (1 + 1 + 1) / ((mu - c) * (mu - c) + 1)) (div_pos_of_pos_pos hε3 hcoef2)
  refine ⟨max (max R1 R2) (max R3 1), lt_of_lt_of_le one_pos
    (le_trans (le_max_right R3 1) (le_max_right _ _)), ?_⟩
  intro R hR
  have hRpos : 0 < R :=
    lt_of_lt_of_le one_pos (le_trans (le_trans (le_max_right R3 1) (le_max_right _ _)) hR)
  have hRR1 : R1 ≤ R := le_trans (le_trans (le_max_left R1 R2) (le_max_left _ _)) hR
  have hRR2 : R2 ≤ R := le_trans (le_trans (le_max_right R1 R2) (le_max_left _ _)) hR
  have hRR3 : R3 ≤ R := le_trans (le_trans (le_max_left R3 1) (le_max_right _ _)) hR
  rw [gaussianVarCSymInt_eq mu sig2 hsig2 c hRpos,
    show (c - mu) * (c - mu) = (mu - c) * (mu - c) from by mach_mpoly [c, mu]]
  refine varC_final_bound (gaussianVarSymInt mu sig2 hsig2 R) (gaussianMeanSymInt mu sig2 hsig2 R)
    (gaussianDensitySymInt mu sig2 hsig2 R) sig2 (mu - c) ε (hR1 R hRR1) ?_ ?_
  · have h := mul_lt_mul_of_pos_right (hR2 R hRR2) hcoef1
    rwa [div_mul_cancel (ne_of_gt hcoef1)] at h
  · have h := mul_lt_mul_of_pos_right (hR3 R hRR3) hcoef2
    rwa [div_mul_cancel (ne_of_gt hcoef2)] at h

end Real
end MachLib
