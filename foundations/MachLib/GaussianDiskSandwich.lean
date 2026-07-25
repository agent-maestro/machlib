/-
`GaussianDiskSandwich.lean` — Stage 4/5 of the √π project: the disk/square sandwich.

Why: `gaussianImproperIntegral` (Stage 2) gives `I := ∫₀^∞exp(-t²)dt` as a real number, but not its
VALUE. Poisson's classical trick pins the value by comparing `S(R):=(∫₀ᴿexp(-t²)dt)²` (a SQUARE,
via Fubini) to `D(R):=` the same Gaussian kernel integrated over a QUARTER-DISK of radius `R` (via
polar coordinates) — `Disk(R) ⊆ Square(R) ⊆ Disk(R√2)`, and both disk integrals converge to `π/4`,
squeezing `I²` to `π/4`.

This file starts with prerequisites the sandwich needs before it can even be STATED: continuity of
`sqrt` (needed to express the quarter-disk's Cartesian boundary `y=√(R²-x²)`), general composition
of `ContinuousAt` functions, and continuity of `gaussianIntegral` as a function of ITS OWN upper
limit (needed so the disk integral `∫₀ᴿexp(-x²)·gaussianIntegral(√(R²-x²))dx` is itself a
well-defined Riemann integral) — including at the boundary point `t=0`, which `ftc_part1` alone
does not cover (it only gives continuity at INTERIOR points `0<t<c`).

Design worked out on paper first (see the `project_sqrtpi_disk_sandwich_design_2026_07_24` memory
note): the sandwich comparison itself needs NO new geometry (pure 1D interval-additivity +
integrand-monotonicity, both already built); the one genuinely new piece is pinning `lim D(R)` to
`π/4`, deferred to a later file once these prerequisites are in place.

`sorryAx`-free, no new axioms (so far).
-/
import MachLib.GaussianRadialIntegral
import MachLib.RiemannIntegralFTCPart1

namespace MachLib
namespace Real

/-! ## §1 — `sqrt` is continuous everywhere on `[0,∞)` -/

private theorem mul_le_mul_both_nonneg {a b c d : Real} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c)
    (hcd : c ≤ d) : a * c ≤ b * d :=
  mul_le_mul' ha hab hc hcd

/-- `y < ε² ⟹ √y < ε`, for `ε>0` — the `x0=0` case of `sqrt`'s continuity, proven directly (no
Lipschitz bound available AT `0`, where `sqrt`'s "derivative" blows up). -/
theorem sqrt_lt_of_lt_sq {y ε : Real} (hε : 0 < ε) (hy : y < ε * ε) : sqrt y < ε := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hge : ε ≤ sqrt y := le_of_not_lt_mono hcon
  by_cases hy0 : 0 ≤ y
  · have hsq : sqrt y * sqrt y = y := sqrt_sq_nonneg y hy0
    have hmul : ε * ε ≤ sqrt y * sqrt y := mul_le_mul_both_nonneg (le_of_lt hε) hge (le_of_lt hε) hge
    rw [hsq] at hmul
    exact lt_irrefl_ax (ε * ε) (lt_of_le_of_lt hmul hy)
  · have hyneg : y < 0 := lt_of_not_le_mono hy0
    have hsqz : sqrt y = 0 := sqrt_neg_zero y hyneg
    rw [hsqz] at hge
    exact lt_irrefl_ax 0 (lt_of_lt_of_le hε hge)

theorem sqrt_continuousAt_zero : ContinuousAt sqrt 0 := by
  intro ε hε
  refine ⟨ε * ε, mul_pos hε hε, ?_⟩
  intro y hy
  show abs (sqrt y - sqrt 0) < ε
  rw [sqrt_zero, sub_zero_local (sqrt y)]
  have hyabs : abs (y - 0) < ε * ε := hy
  rw [sub_zero_local y] at hyabs
  have hsy_nn : 0 ≤ sqrt y := sqrt_nonneg y
  rw [abs_of_nonneg hsy_nn]
  by_cases hy0 : 0 ≤ y
  · rw [abs_of_nonneg hy0] at hyabs
    exact sqrt_lt_of_lt_sq hε hyabs
  · have hyneg : y < 0 := lt_of_not_le_mono hy0
    rw [sqrt_neg_zero y hyneg]
    exact hε

private theorem sq_sum_expand (X Y : Real) : (X + Y) * (X + Y) = X * X + Y * Y + (1 + 1) * (X * Y) := by
  mach_mpoly [X, Y]

private theorem add_sub_self_local (a b : Real) : b + (a - b) = a := by mach_mpoly [a, b]

private theorem cancel_add_neg_local (a b : Real) : a + b + -a = b := by mach_mpoly [a, b]

private theorem add_neg_self_local2 (a : Real) : a + -a = 0 := by mach_mpoly [a]

/-- `a≥b≥0 ⟹ √a-√b ≤ √(a-b)` — the key algebraic step behind `sqrt`'s local Hölder-1/2 bound. -/
private theorem sqrt_sub_le_sqrt_of_ge {a b : Real} (hb : 0 ≤ b) (hab : b ≤ a) :
    sqrt a - sqrt b ≤ sqrt (a - b) := by
  have hab0 : 0 ≤ a - b := sub_nonneg_of_le hab
  have hsum_nn : 0 ≤ sqrt b + sqrt (a - b) := add_nonneg (sqrt_nonneg b) (sqrt_nonneg (a - b))
  have hexpand := sq_sum_expand (sqrt b) (sqrt (a - b))
  rw [sqrt_sq_nonneg b hb, sqrt_sq_nonneg (a - b) hab0, add_sub_self_local a b] at hexpand
  have hcross_nn : 0 ≤ (1 + 1) * (sqrt b * sqrt (a - b)) :=
    mul_nonneg (le_of_lt two_pos) (mul_nonneg (sqrt_nonneg b) (sqrt_nonneg (a - b)))
  have hage : a ≤ (sqrt b + sqrt (a - b)) * (sqrt b + sqrt (a - b)) := by
    rw [hexpand]; exact le_add_of_nonneg_right hcross_nn
  have hsqrt_a_le : sqrt a ≤ sqrt b + sqrt (a - b) := sqrt_le_of_le_sq hsum_nn hage
  have h1 := add_le_add_both hsqrt_a_le (le_refl (-sqrt b))
  rwa [cancel_add_neg_local (sqrt b) (sqrt (a - b)), ← sub_def (sqrt a) (sqrt b)] at h1

private theorem le_total_local3 (a b : Real) : a ≤ b ∨ b ≤ a := by
  obtain h | h | h := lt_total a b
  · exact Or.inl (le_of_lt h)
  · exact Or.inl (le_of_eq h)
  · exact Or.inr (le_of_lt h)

/-- `a,b≥0 ⟹ |√a-√b| ≤ √|a-b|` — `sqrt` is 1-Hölder in the square root of its argument's gap,
uniformly on nonnegatives. -/
private theorem sqrt_abs_diff_bound (a b : Real) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    abs (sqrt a - sqrt b) ≤ sqrt (abs (a - b)) := by
  obtain hab | hba := le_total_local3 a b
  · have hle : sqrt a ≤ sqrt b := sqrt_le_sqrt ha hab
    have h1 : sqrt b - sqrt a ≤ sqrt (b - a) := sqrt_sub_le_sqrt_of_ge ha hab
    have habsab : abs (a - b) = b - a := by
      rw [abs_of_nonpos (sub_nonpos_of_le hab)]; mach_mpoly [a, b]
    have habssub : abs (sqrt a - sqrt b) = sqrt b - sqrt a := by
      rw [abs_of_nonpos (sub_nonpos_of_le hle)]; mach_mpoly [sqrt a, sqrt b]
    rw [habsab, habssub]; exact h1
  · have hle : sqrt b ≤ sqrt a := sqrt_le_sqrt hb hba
    have h1 : sqrt a - sqrt b ≤ sqrt (a - b) := sqrt_sub_le_sqrt_of_ge hb hba
    have habsab : abs (a - b) = a - b := abs_of_nonneg (sub_nonneg_of_le hba)
    have habssub : abs (sqrt a - sqrt b) = sqrt a - sqrt b := abs_of_nonneg (sub_nonneg_of_le hle)
    rw [habsab, habssub]; exact h1

theorem sqrt_continuousAt_pos (x0 : Real) (hx0 : 0 < x0) : ContinuousAt sqrt x0 := by
  intro ε hε
  refine ⟨min x0 (ε * ε), lt_min_of_lt_of_lt hx0 (mul_pos hε hε), ?_⟩
  intro y hy
  have hyδ1 : abs (y - x0) < x0 := lt_of_lt_of_le hy (min_le_left x0 (ε * ε))
  have hyδ2 : abs (y - x0) < ε * ε := lt_of_lt_of_le hy (min_le_right x0 (ε * ε))
  have hylb : -x0 < y - x0 := (abs_lt_split hyδ1).2
  have hypos : 0 < y := by
    have h1 := add_lt_add_left hylb x0
    rwa [add_neg_self_local2 x0, add_sub_self_local y x0] at h1
  exact lt_of_le_of_lt (sqrt_abs_diff_bound y x0 (le_of_lt hypos) (le_of_lt hx0))
    (sqrt_lt_of_lt_sq hε hyδ2)

theorem sqrt_continuousAt (x0 : Real) (hx0 : 0 ≤ x0) : ContinuousAt sqrt x0 := by
  obtain hx0pos | hx0eq := (le_iff_lt_or_eq 0 x0).mp hx0
  · exact sqrt_continuousAt_pos x0 hx0pos
  · rw [← hx0eq]
    exact sqrt_continuousAt_zero

/-! ## §2 — composition of continuous functions is continuous -/

/-- Standard ε-δ composition: if `g` is continuous at `x` and `f` is continuous at `g x`, then
`f∘g` is continuous at `x`. -/
theorem continuousAt_comp {f g : Real → Real} {x : Real} (hg : ContinuousAt g x)
    (hf : ContinuousAt f (g x)) : ContinuousAt (fun y => f (g y)) x := by
  intro ε hε
  obtain ⟨δf, hδfpos, hδf⟩ := hf ε hε
  obtain ⟨δg, hδgpos, hδg⟩ := hg δf hδfpos
  exact ⟨δg, hδgpos, fun y hy => hδf (g y) (hδg y hy)⟩

/-! ## §3 — `gaussianIntegral` is continuous in its own upper limit, everywhere on `[0,∞)` -/

theorem gaussian_le_one (z : Real) : Real.exp (-(z * z)) ≤ 1 := by
  have h1 : -(z * z) ≤ 0 := neg_nonpos_of_nonneg (mul_self_nonneg z)
  have h2 := exp_monotone h1
  rwa [Real.exp_zero] at h2

theorem gaussianIntegral_zero_eq : gaussianIntegral 0 (le_refl 0) = 0 := by
  have hgspec := Classical.choose_spec (gaussian_integral_exists 0 (le_refl 0))
  have hupz : upperSumCont (fun t => Real.exp (-(t * t))) 0 0 (le_refl 0)
      (fun z _ _ => gaussian_continuous z) (2 ^ 0) (two_pow_pos 0) = 0 := by
    show partialSum (maxSub (fun t => Real.exp (-(t * t))) 0 0 (le_refl 0)
        (fun z _ _ => gaussian_continuous z) (2 ^ 0) (two_pow_pos 0)) (2 ^ 0)
        * meshWidth 0 0 (2 ^ 0) = 0
    have hw0 : meshWidth 0 0 (2 ^ 0) = 0 := by
      show ((0:Real) - 0) / natCast (2 ^ 0) = 0
      rw [sub_self, zero_div]
    rw [hw0, mul_zero]
  have hlowz : lowerSumCont (fun t => Real.exp (-(t * t))) 0 0 (le_refl 0)
      (fun z _ _ => gaussian_continuous z) (2 ^ 0) (two_pow_pos 0) = 0 := by
    show partialSum (minSub (fun t => Real.exp (-(t * t))) 0 0 (le_refl 0)
        (fun z _ _ => gaussian_continuous z) (2 ^ 0) (two_pow_pos 0)) (2 ^ 0)
        * meshWidth 0 0 (2 ^ 0) = 0
    have hw0 : meshWidth 0 0 (2 ^ 0) = 0 := by
      show ((0:Real) - 0) / natCast (2 ^ 0) = 0
      rw [sub_self, zero_div]
    rw [hw0, mul_zero]
  have h1 : lowerSumCont (fun t => Real.exp (-(t * t))) 0 0 (le_refl 0)
      (fun z _ _ => gaussian_continuous z) (2 ^ 0) (two_pow_pos 0)
      ≤ gaussianIntegral 0 (le_refl 0) := (hgspec.1 0).1
  have h2 : gaussianIntegral 0 (le_refl 0)
      ≤ upperSumCont (fun t => Real.exp (-(t * t))) 0 0 (le_refl 0)
        (fun z _ _ => gaussian_continuous z) (2 ^ 0) (two_pow_pos 0) := (hgspec.1 0).2
  rw [hupz] at h2
  rw [hlowz] at h1
  exact le_antisymm h2 h1

private theorem div_one_local (t : Real) : t / 1 = t := by
  have h := div_mul_cancel (a := t) (b := (1:Real)) one_ne_zero
  rwa [mul_one_ax] at h

theorem meshWidth_zero_one_pow (t : Real) : meshWidth 0 t (2 ^ 0) = t := by
  rw [meshWidth_zero_base]
  show t / natCast 1 = t
  rw [natCast_one_local2]
  exact div_one_local t

/-- `gaussianIntegral t ht ≤ t` — the `n=1` upper Darboux sum, using the uniform bound
`exp(-s²)≤1`. Gives a direct Lipschitz-style estimate near `t=0`. -/
theorem gaussianIntegral_le_self (t : Real) (ht : 0 ≤ t) : gaussianIntegral t ht ≤ t := by
  have hgspec := Classical.choose_spec (gaussian_integral_exists t ht)
  have h1 : gaussianIntegral t ht
      ≤ upperSumCont (fun s => Real.exp (-(s * s))) 0 t ht (fun z _ _ => gaussian_continuous z)
        (2 ^ 0) (two_pow_pos 0) := (hgspec.1 0).2
  have hmaxle : maxSub (fun s => Real.exp (-(s * s))) 0 t ht (fun z _ _ => gaussian_continuous z)
      (2 ^ 0) (two_pow_pos 0) 0 ≤ 1 :=
    maxSub_le_global_bound (fun s => Real.exp (-(s * s))) 0 t ht
      (fun z _ _ => gaussian_continuous z) 1 (fun z _ _ => gaussian_le_one z) (2 ^ 0)
      (two_pow_pos 0) 0
  have hus : upperSumCont (fun s => Real.exp (-(s * s))) 0 t ht (fun z _ _ => gaussian_continuous z)
      (2 ^ 0) (two_pow_pos 0)
      = maxSub (fun s => Real.exp (-(s * s))) 0 t ht (fun z _ _ => gaussian_continuous z)
        (2 ^ 0) (two_pow_pos 0) 0 * meshWidth 0 t (2 ^ 0) := by
    show partialSum (maxSub (fun s => Real.exp (-(s * s))) 0 t ht
        (fun z _ _ => gaussian_continuous z) (2 ^ 0) (two_pow_pos 0)) (2 ^ 0) * meshWidth 0 t (2 ^ 0)
      = maxSub (fun s => Real.exp (-(s * s))) 0 t ht (fun z _ _ => gaussian_continuous z)
        (2 ^ 0) (two_pow_pos 0) 0 * meshWidth 0 t (2 ^ 0)
    rw [partialSum_one]
  rw [meshWidth_zero_one_pow] at hus
  rw [hus] at h1
  have hbound : maxSub (fun s => Real.exp (-(s * s))) 0 t ht (fun z _ _ => gaussian_continuous z)
      (2 ^ 0) (two_pow_pos 0) 0 * t ≤ 1 * t :=
    mul_le_mul_of_nonneg_right hmaxle ht
  rw [one_mul_thm] at hbound
  exact le_trans h1 hbound

theorem gaussianIntegral_nonneg (t : Real) (ht : 0 ≤ t) : 0 ≤ gaussianIntegral t ht := by
  have hgspec := Classical.choose_spec (gaussian_integral_exists t ht)
  have h1 : lowerSumCont (fun s => Real.exp (-(s * s))) 0 t ht (fun z _ _ => gaussian_continuous z)
      (2 ^ 0) (two_pow_pos 0) ≤ gaussianIntegral t ht := (hgspec.1 0).1
  have hminge : 0 ≤ minSub (fun s => Real.exp (-(s * s))) 0 t ht (fun z _ _ => gaussian_continuous z)
      (2 ^ 0) (two_pow_pos 0) 0 :=
    minSub_ge_global_bound (fun s => Real.exp (-(s * s))) 0 t ht
      (fun z _ _ => gaussian_continuous z) 0 (fun z _ _ => le_of_lt (exp_pos _)) (2 ^ 0)
      (two_pow_pos 0) 0
  have hls : lowerSumCont (fun s => Real.exp (-(s * s))) 0 t ht (fun z _ _ => gaussian_continuous z)
      (2 ^ 0) (two_pow_pos 0)
      = minSub (fun s => Real.exp (-(s * s))) 0 t ht (fun z _ _ => gaussian_continuous z)
        (2 ^ 0) (two_pow_pos 0) 0 * meshWidth 0 t (2 ^ 0) := by
    show partialSum (minSub (fun s => Real.exp (-(s * s))) 0 t ht
        (fun z _ _ => gaussian_continuous z) (2 ^ 0) (two_pow_pos 0)) (2 ^ 0) * meshWidth 0 t (2 ^ 0)
      = minSub (fun s => Real.exp (-(s * s))) 0 t ht (fun z _ _ => gaussian_continuous z)
        (2 ^ 0) (two_pow_pos 0) 0 * meshWidth 0 t (2 ^ 0)
    rw [partialSum_one]
  rw [hls] at h1
  have hbound : (0:Real) ≤ minSub (fun s => Real.exp (-(s * s))) 0 t ht
      (fun z _ _ => gaussian_continuous z) (2 ^ 0) (two_pow_pos 0) 0 * meshWidth 0 t (2 ^ 0) :=
    mul_nonneg hminge (meshWidth_nonneg ht (2 ^ 0))
  exact le_trans hbound h1

/-- Total-function wrapper for `gaussianIntegral`, extended by `0` off `[0,∞)`, so it can be used
as an `I : Real → Real` argument to `ftc_part1` (which needs a genuine total function, with the
sandwich hypotheses only pinning its behavior on the relevant range). -/
noncomputable def gaussianI (t : Real) : Real :=
  if h : 0 ≤ t then gaussianIntegral t h else 0

theorem gaussianI_eq (t : Real) (ht : 0 ≤ t) : gaussianI t = gaussianIntegral t ht := by
  show (if h : 0 ≤ t then gaussianIntegral t h else 0) = gaussianIntegral t ht
  rw [dif_pos ht]

theorem gaussianI_continuousAt_zero : ContinuousAt gaussianI 0 := by
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy
  show abs (gaussianI y - gaussianI 0) < ε
  rw [gaussianI_eq 0 (le_refl 0), gaussianIntegral_zero_eq, sub_zero_local (gaussianI y)]
  by_cases hy0 : 0 ≤ y
  · rw [gaussianI_eq y hy0, abs_of_nonneg (gaussianIntegral_nonneg y hy0)]
    have hyabs : abs (y - 0) < ε := hy
    rw [sub_zero_local y] at hyabs
    rw [abs_of_nonneg hy0] at hyabs
    exact lt_of_le_of_lt (gaussianIntegral_le_self y hy0) hyabs
  · have hyneg : y < 0 := lt_of_not_le_mono hy0
    show (if h : 0 ≤ y then gaussianIntegral y h else 0).abs < ε
    rw [dif_neg hy0, abs_zero]
    exact hε

theorem gaussianI_continuousAt_pos (t0 : Real) (ht0 : 0 < t0) : ContinuousAt gaussianI t0 := by
  have hc0 : (0:Real) ≤ t0 + 1 := le_trans (le_of_lt ht0) (le_add_of_nonneg_right (le_of_lt one_pos))
  have hcont_x : ∀ x : Real, 0 ≤ x → x ≤ t0 + 1 → ∀ z : Real, 0 ≤ z → z ≤ x →
      ContinuousAt (fun s => Real.exp (-(s * s))) z := fun _ _ _ z _ _ => gaussian_continuous z
  have hIlow : ∀ x : Real, ∀ hx0 : 0 ≤ x, ∀ hxc : x ≤ t0 + 1, ∀ k : Nat,
      lowerSumCont (fun s => Real.exp (-(s * s))) 0 x hx0 (hcont_x x hx0 hxc) (2 ^ k) (two_pow_pos k)
        ≤ gaussianI x := by
    intro x hx0 hxc k
    rw [gaussianI_eq x hx0]
    exact (Classical.choose_spec (gaussian_integral_exists x hx0)).1 k |>.1
  have hIup : ∀ x : Real, ∀ hx0 : 0 ≤ x, ∀ hxc : x ≤ t0 + 1, ∀ k : Nat,
      gaussianI x ≤ upperSumCont (fun s => Real.exp (-(s * s))) 0 x hx0 (hcont_x x hx0 hxc)
        (2 ^ k) (two_pow_pos k) := by
    intro x hx0 hxc k
    rw [gaussianI_eq x hx0]
    exact (Classical.choose_spec (gaussian_integral_exists x hx0)).1 k |>.2
  have hIgap : ∀ x : Real, ∀ hx0 : 0 ≤ x, ∀ hxc : x ≤ t0 + 1, ∀ ε : Real, 0 < ε → ∃ k : Nat,
      upperSumCont (fun s => Real.exp (-(s * s))) 0 x hx0 (hcont_x x hx0 hxc) (2 ^ k) (two_pow_pos k)
        - lowerSumCont (fun s => Real.exp (-(s * s))) 0 x hx0 (hcont_x x hx0 hxc) (2 ^ k)
          (two_pow_pos k) < ε :=
    fun x hx0 _ ε hε => (Classical.choose_spec (gaussian_integral_exists x hx0)).2 ε hε
  have ht0_lt : t0 < t0 + 1 := by
    have h := add_lt_add_left one_pos t0
    rwa [add_zero] at h
  have hderiv := ftc_part1 (fun s => Real.exp (-(s * s))) (t0 + 1) hc0
    (fun z _ _ => gaussian_continuous z) hcont_x (fun z _ _ => le_of_lt (exp_pos _))
    gaussianI hIlow hIup hIgap t0 ht0 ht0_lt
  exact hasDerivAt_continuousAt hderiv

theorem gaussianI_continuousAt (t0 : Real) (ht0 : 0 ≤ t0) : ContinuousAt gaussianI t0 := by
  obtain ht0pos | ht0eq := (le_iff_lt_or_eq 0 t0).mp ht0
  · exact gaussianI_continuousAt_pos t0 ht0pos
  · rw [← ht0eq]
    exact gaussianI_continuousAt_zero

end Real
end MachLib
