/-
`RiemannIntegralFTCPart1.lean` — Fundamental Theorem of Calculus, part 1: the Riemann integral
`I(x) := ∫₀ˣf`, as a function of its upper limit, has derivative `f(x)` at every interior point
`x` of `f`'s domain of continuity.

Why: designing the √π project's disk/square sandwich needs a quantitative interval bound on the
Riemann integral, which is most naturally obtained via FTC part 1 (differentiate, then bound the
derivative) rather than re-deriving the bound from scratch. This is the actual reason interval
additivity (`RiemannIntegralAdditivity.lean`) was built.

Proof idea: fix ε>0 and use continuity of `f` at `x₀` to get `δ` such that `f` stays within `ε` of
`f(x₀)` throughout `(x₀-δ,x₀+δ)`. For `y` in that neighborhood, `I(y)-I(x₀)` equals the integral of
`f` over the (possibly reversed) interval between `x₀` and `y` — via `riemann_integral_additivity`
— and that integral is within `ε·|y-x₀|` of `f(x₀)·(y-x₀)`, since `f` stays within `ε` of `f(x₀)`
on the whole sub-interval (`integral_close_to_const`). This is exactly `HasDerivAt`'s
epsilon-delta linear-approximation characterization (`HasDerivAt_of_eps_delta`).

`sorryAx`-free, no new axioms.
-/
import MachLib.RiemannIntegralAdditivity
import MachLib.Differentiation

namespace MachLib
namespace Real

/-! ## §1 — small abs-value helpers -/

private theorem neg_le_self_of_nonneg {t : Real} (h : 0 ≤ t) : -t ≤ t := by
  have h1 := add_le_add_both h h
  have h2 := add_le_add_both h1 (le_refl (-t))
  rwa [show (0:Real) + 0 + (-t) = -t from by mach_mpoly [t],
      show t + t + (-t) = t from by mach_mpoly [t]] at h2

private theorem neg_le_abs_self (t : Real) : -t ≤ abs t := by
  by_cases h : 0 ≤ t
  · rw [abs_of_nonneg h]
    exact neg_le_self_of_nonneg h
  · have hneg : t < 0 := by
      obtain h1 | h1 | h1 := lt_total t 0
      · exact h1
      · exact absurd (h1 ▸ le_refl (0:Real)) h
      · exact absurd (le_of_lt h1) h
    rw [abs_of_nonpos (le_of_lt hneg)]
    exact le_refl (-t)

/-- The two one-sided bounds packed inside `abs t < B`. -/
private theorem abs_lt_split {t B : Real} (h : abs t < B) : t < B ∧ -B < t := by
  refine ⟨lt_of_abs_lt h, ?_⟩
  have h1 : -t < B := lt_of_le_of_lt (neg_le_abs_self t) h
  have h2 := add_lt_add_left h1 t
  rw [show t + -t = (0:Real) from by mach_mpoly [t]] at h2
  have h3 := add_lt_add_left h2 (-B)
  rwa [show -B + 0 = -B from by mach_mpoly [B],
      show -B + (t + B) = t from by mach_mpoly [t, B]] at h3

/-! ## §2 — strict positivity of a `min` -/

private theorem lt_min_of_lt_of_lt {a b c : Real} (h1 : c < a) (h2 : c < b) : c < min a b := by
  unfold min
  by_cases h : a ≤ b
  · rw [if_pos h]; exact h1
  · rw [if_neg h]; exact h2

/-! ## §3 — a global LOWER bound transfers to `minSub`, and `meshWidth` at a 1-cell offset
partition equals the width exactly -/

/-- `minSub` (any base interval) is never BELOW a global lower bound valid on a larger interval
containing it. Mirrors `minSub_le_global_bound` (upper bound), flipped. -/
theorem minSub_ge_global_bound (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (m : Real) (hmlb : ∀ x : Real, a ≤ x → x ≤ b → m ≤ f x) (n : Nat) (hn : 0 < n) (i : Nat) :
    m ≤ minSub f a b hab hcont n hn i := by
  by_cases hi : i < n
  · rw [minSub_eq f a b hab hcont n hn i hi]
    have hmem := minSub_mem f a b hab hcont n hn i hi
    apply hmlb
    · exact le_trans (meshPoint_mem a b n i hab hn (Nat.le_of_lt hi)).1 hmem.1
    · exact le_trans hmem.2 (meshPoint_mem a b n (i + 1) hab hn hi).2
  · unfold minSub
    rw [dif_neg hi]
    exact hmlb a (le_refl a) hab

/-- `meshWidth p (p+w) 1 = w` — the trivial single-cell partition's one cell spans the whole
interval. -/
theorem meshWidth_offset_one (p w : Real) : meshWidth p (p + w) 1 = w := by
  have heq := natCast_mul_meshWidth p (p + w) 1 (by omega)
  rw [show p + w - p = w from by mach_mpoly [p, w], natCast_one_local2] at heq
  rwa [show (1:Real) * meshWidth p (p + w) 1 = meshWidth p (p + w) 1
      from by mach_mpoly [meshWidth p (p + w) 1]] at heq

private theorem partialSum_one (g : Nat → Real) : partialSum g 1 = g 0 := by
  show (0:Real) + g 0 = g 0
  rw [zero_add]

/-! ## §4 — an integral of a function that stays within `ε` of a constant `M` is itself within
`ε·w` of `M·w` -/

/-- If `f` stays within `ε` of a constant `M` throughout `[p,p+w]`, any value `J` sandwiched by
`f`'s dyadic Darboux sums over `[p,p+w]` satisfies `(M-ε)·w ≤ J ≤ (M+ε)·w`. Only the trivial
1-cell partition is needed — the bound is EXACT there, not just in the limit. -/
theorem integral_close_to_const (f : Real → Real) (p w : Real) (hp0 : 0 ≤ p) (hw : 0 ≤ w)
    (hcont_p : ∀ z : Real, p ≤ z → z ≤ p + w → ContinuousAt f z)
    (M ε : Real) (hub : ∀ z : Real, p ≤ z → z ≤ p + w → f z ≤ M + ε)
    (hlb : ∀ z : Real, p ≤ z → z ≤ p + w → M - ε ≤ f z)
    (J : Real)
    (hJlow : lowerSumCont f p (p + w) (le_add_of_nonneg_right hw) hcont_p 1 (by omega) ≤ J)
    (hJup : J ≤ upperSumCont f p (p + w) (le_add_of_nonneg_right hw) hcont_p 1 (by omega)) :
    (M - ε) * w ≤ J ∧ J ≤ (M + ε) * w := by
  constructor
  · have hminge : M - ε ≤ minSub f p (p + w) (le_add_of_nonneg_right hw) hcont_p 1 (by omega) 0 :=
      minSub_ge_global_bound f p (p + w) (le_add_of_nonneg_right hw) hcont_p (M - ε) hlb 1 (by omega) 0
    have hls : lowerSumCont f p (p + w) (le_add_of_nonneg_right hw) hcont_p 1 (by omega)
        = minSub f p (p + w) (le_add_of_nonneg_right hw) hcont_p 1 (by omega) 0 * w := by
      show partialSum (minSub f p (p + w) (le_add_of_nonneg_right hw) hcont_p 1 (by omega)) 1
          * meshWidth p (p + w) 1 = minSub f p (p + w) (le_add_of_nonneg_right hw) hcont_p 1 (by omega) 0 * w
      rw [partialSum_one, meshWidth_offset_one]
    have hbound : (M - ε) * w
        ≤ minSub f p (p + w) (le_add_of_nonneg_right hw) hcont_p 1 (by omega) 0 * w :=
      mul_le_mul_of_nonneg_right hminge hw
    rw [← hls] at hbound
    exact le_trans hbound hJlow
  · have hmaxle : maxSub f p (p + w) (le_add_of_nonneg_right hw) hcont_p 1 (by omega) 0 ≤ M + ε :=
      maxSub_le_global_bound f p (p + w) (le_add_of_nonneg_right hw) hcont_p (M + ε) hub 1 (by omega) 0
    have hus : upperSumCont f p (p + w) (le_add_of_nonneg_right hw) hcont_p 1 (by omega)
        = maxSub f p (p + w) (le_add_of_nonneg_right hw) hcont_p 1 (by omega) 0 * w := by
      show partialSum (maxSub f p (p + w) (le_add_of_nonneg_right hw) hcont_p 1 (by omega)) 1
          * meshWidth p (p + w) 1 = maxSub f p (p + w) (le_add_of_nonneg_right hw) hcont_p 1 (by omega) 0 * w
      rw [partialSum_one, meshWidth_offset_one]
    have hbound : maxSub f p (p + w) (le_add_of_nonneg_right hw) hcont_p 1 (by omega) 0 * w
        ≤ (M + ε) * w :=
      mul_le_mul_of_nonneg_right hmaxle hw
    rw [← hus] at hbound
    exact le_trans hJup hbound

/-! ## §5 — remaining small helpers for the main assembly -/

private theorem le_total_local (a b : Real) : a ≤ b ∨ b ≤ a := by
  obtain h | h | h := lt_total a b
  · exact Or.inl (le_of_lt h)
  · exact Or.inl (le_of_eq h)
  · exact Or.inr (le_of_lt h)

private theorem sub_le_sub_right_ftc {a b : Real} (h : a ≤ b) (c : Real) : a - c ≤ b - c := by
  have h1 := add_le_add_both h (le_refl (-c))
  rwa [← sub_def a c, ← sub_def b c] at h1

private theorem add_eq_to_sub (A B C : Real) (h : A + B = C) : B = C - A := by
  rw [← h]; mach_mpoly [A, B]

/-- `a+(b-a)=b`. Hoisted (not inline) because the main proof below hits `mach_mpoly` failures deep
inside a hypothesis-heavy context that don't match the established "have/let-bound atom" gotcha —
same underlying issue (mach_mpoly apparently inspects more of the local context than just its
atom list), different trigger (context SIZE, not atom complexity). Confirms the house rule
generalizes: once a proof accumulates enough hypotheses, hoist EVERY remaining ring step
proactively, don't wait for a specific failure to diagnose. -/
private theorem add_sub_cancel_local (a b : Real) : a + (b - a) = b := by mach_mpoly [a, b]

private theorem add_neg_self_local (a : Real) : a + -a = 0 := by mach_mpoly [a]

private theorem mul_expand_ub (M ε w : Real) : (M + ε) * w + -(M * w) = ε * w := by
  mach_mpoly [M, ε, w]

private theorem mul_expand_lb (M ε w : Real) : (M - ε) * w + -(M * w) = -(ε * w) := by
  mach_mpoly [M, ε, w]

private theorem sub_eq_neg_of_add_eq (A B C : Real) (h : A + B = C) : A - C = -B := by
  rw [← h]; mach_mpoly [A, B]

private theorem sub_le_sub_left_ftc {a b : Real} (h : a ≤ b) (c : Real) : c - b ≤ c - a := by
  have h1 := add_le_add_both (le_refl c) (neg_le_neg h)
  rwa [← sub_def c b, ← sub_def c a] at h1

private theorem sub_nonpos_of_le_ftc {a b : Real} (h : a ≤ b) : a - b ≤ 0 := by
  have h1 := add_le_add_both h (le_refl (-b))
  rwa [← sub_def a b, add_neg_self_local b] at h1

/-- `-J - M*(y-x0) = -(J - M*(x0-y))` — the sign-flip identity connecting `I y - I x0` (via
`-J'`) to the "closeness to constant" bound, which is naturally stated for the interval `[y,x0]`
(width `x0-y`), not `[x0,y]`. -/
private theorem neg_sub_flip (J M x0 y : Real) : -J - M * (y - x0) = -(J - M * (x0 - y)) := by
  mach_mpoly [J, M, x0, y]

private theorem neg_neg_local (a : Real) : -(-a) = a := by mach_mpoly [a]

private theorem neg_sub_eq_local (a b : Real) : -(a - b) = b - a := by mach_mpoly [a, b]

private theorem abs_neg_local (t : Real) : abs (-t) = abs t := by
  by_cases h : 0 ≤ t
  · have hnegt : -t ≤ 0 := by
      have h1 := neg_le_neg h
      rwa [neg_zero] at h1
    rw [abs_of_nonneg h, abs_of_nonpos hnegt]
    mach_mpoly [t]
  · have hneg : t < 0 := by
      obtain h1 | h1 | h1 := lt_total t 0
      · exact h1
      · exact absurd (h1 ▸ le_refl (0:Real)) h
      · exact absurd (le_of_lt h1) h
    have hnegtnn : (0:Real) ≤ -t := by
      have h1 := neg_le_neg (le_of_lt hneg)
      rwa [neg_zero] at h1
    rw [abs_of_nonpos (le_of_lt hneg), abs_of_nonneg hnegtnn]

/-- `abs t ≤ B` from `t≤B` and `-B≤t` (as opposed to the library's `abs_le_of`, which wants
`-t≤B` — equivalent, but a different literal shape than what falls out of this proof). -/
private theorem abs_le_of_bounds {t B : Real} (h1 : t ≤ B) (h2 : -B ≤ t) : abs t ≤ B := by
  apply abs_le_of h1
  have h3 := neg_le_neg h2
  rwa [show -(-B) = B from by mach_mpoly [B]] at h3

/-- Given `f` stays within `ε` of `f x0` on a `δ`-neighborhood of `x0`, and `z` is within `δ` of
`x0`, both one-sided bounds `f z < f x0 + ε` and `f x0 - ε < f z` follow. -/
private theorem near_const_bounds (f : Real → Real) (x0 δ ε : Real)
    (hδ : ∀ y : Real, abs (y - x0) < δ → abs (f y - f x0) < ε) (z : Real) (hz : abs (z - x0) < δ) :
    f z < f x0 + ε ∧ f x0 - ε < f z := by
  obtain ⟨h1, h2⟩ := abs_lt_split (hδ z hz)
  refine ⟨?_, ?_⟩
  · have h3 := add_lt_add_left h1 (f x0)
    rwa [show f x0 + (f z - f x0) = f z from by mach_mpoly [f x0, f z]] at h3
  · have h3 := add_lt_add_left h2 (f x0)
    rwa [show f x0 + -ε = f x0 - ε from by mach_mpoly [f x0, ε],
        show f x0 + (f z - f x0) = f z from by mach_mpoly [f x0, f z]] at h3

/-! ## §6 — the headline: FTC part 1 -/

/-- **Fundamental Theorem of Calculus, part 1.** `I(x) := ∫₀ˣf` has derivative `f(x₀)` at any
interior point `x₀` of `[0,c]` (`0<x₀<c`), for `f` continuous and nonnegative on `[0,c]`. `I` is
taken as any function satisfying the Riemann-integral sandwich at every `x∈[0,c]` (matching this
whole arc's style of never committing to a specific choice function). -/
theorem ftc_part1 (f : Real → Real) (c : Real) (hc0 : 0 ≤ c)
    (hcont : ∀ z : Real, 0 ≤ z → z ≤ c → ContinuousAt f z)
    (hcont_x : ∀ x : Real, 0 ≤ x → x ≤ c → ∀ z : Real, 0 ≤ z → z ≤ x → ContinuousAt f z)
    (hnonneg : ∀ z : Real, 0 ≤ z → z ≤ c → 0 ≤ f z)
    (I : Real → Real)
    (hIlow : ∀ x : Real, ∀ hx0 : 0 ≤ x, ∀ hxc : x ≤ c, ∀ k : Nat,
        lowerSumCont f 0 x hx0 (hcont_x x hx0 hxc) (2 ^ k) (two_pow_pos k) ≤ I x)
    (hIup : ∀ x : Real, ∀ hx0 : 0 ≤ x, ∀ hxc : x ≤ c, ∀ k : Nat,
        I x ≤ upperSumCont f 0 x hx0 (hcont_x x hx0 hxc) (2 ^ k) (two_pow_pos k))
    (hIgap : ∀ x : Real, ∀ hx0 : 0 ≤ x, ∀ hxc : x ≤ c, ∀ ε : Real, 0 < ε → ∃ k : Nat,
        upperSumCont f 0 x hx0 (hcont_x x hx0 hxc) (2 ^ k) (two_pow_pos k)
          - lowerSumCont f 0 x hx0 (hcont_x x hx0 hxc) (2 ^ k) (two_pow_pos k) < ε)
    (x0 : Real) (hx0pos : 0 < x0) (hx0c : x0 < c) :
    HasDerivAt I (f x0) x0 := by
  apply HasDerivAt_of_eps_delta
  intro ε hε
  obtain ⟨δc, hδcpos, hδc⟩ := hcont x0 (le_of_lt hx0pos) (le_of_lt hx0c) ε hε
  have hcxpos : 0 < c - x0 := sub_pos_of_lt hx0c
  have hδ2pos : 0 < min x0 (c - x0) := lt_min_of_lt_of_lt hx0pos hcxpos
  have hδpos : 0 < min δc (min x0 (c - x0)) := lt_min_of_lt_of_lt hδcpos hδ2pos
  refine ⟨min δc (min x0 (c - x0)), hδpos, ?_⟩
  intro y hy
  have hyδc : abs (y - x0) < δc := lt_of_lt_of_le hy (min_le_left δc (min x0 (c - x0)))
  have hyδ2 : abs (y - x0) < min x0 (c - x0) := lt_of_lt_of_le hy (min_le_right δc (min x0 (c - x0)))
  have hyx0lt : abs (y - x0) < x0 := lt_of_lt_of_le hyδ2 (min_le_left x0 (c - x0))
  have hycxlt : abs (y - x0) < c - x0 := lt_of_lt_of_le hyδ2 (min_le_right x0 (c - x0))
  obtain ⟨_, hlt2⟩ := abs_lt_split hyx0lt
  obtain ⟨hlt3, _⟩ := abs_lt_split hycxlt
  have hypos : 0 < y := by
    have h1 := add_lt_add_left hlt2 x0
    rwa [add_neg_self_local x0, add_sub_cancel_local x0 y] at h1
  have hyc : y < c := by
    have h1 := add_lt_add_left hlt3 x0
    rwa [add_sub_cancel_local x0 y, add_sub_cancel_local x0 c] at h1
  obtain hxy | hyx := le_total_local x0 y
  · -- x0 ≤ y
    have hcont_y : ∀ z : Real, 0 ≤ z → z ≤ y → ContinuousAt f z :=
      fun z hz1 hz2 => hcont z hz1 (le_trans hz2 (le_of_lt hyc))
    have hcont_a : ∀ z : Real, 0 ≤ z → z ≤ x0 → ContinuousAt f z :=
      hcont_x x0 (le_of_lt hx0pos) (le_of_lt hx0c)
    have hcont_xy : ∀ z : Real, x0 ≤ z → z ≤ y → ContinuousAt f z :=
      fun z hz1 hz2 => hcont z (le_trans (le_of_lt hx0pos) hz1) (le_trans hz2 (le_of_lt hyc))
    have hnonneg_y : ∀ z : Real, 0 ≤ z → z ≤ y → 0 ≤ f z :=
      fun z hz1 hz2 => hnonneg z hz1 (le_trans hz2 (le_of_lt hyc))
    obtain ⟨J, hJsw, hJgap⟩ := continuous_riemann_integrable f x0 y hxy hcont_xy
    have hadd : I x0 + J = I y :=
      riemann_integral_additivity f x0 y (le_of_lt hx0pos) hxy (le_of_lt hypos) hcont_y hcont_a
        hcont_xy hnonneg_y (I x0) J (I y)
        (hIlow x0 (le_of_lt hx0pos) (le_of_lt hx0c)) (hIup x0 (le_of_lt hx0pos) (le_of_lt hx0c))
        (hIgap x0 (le_of_lt hx0pos) (le_of_lt hx0c))
        (fun k => (hJsw k).1) (fun k => (hJsw k).2) hJgap
        (hIlow y (le_of_lt hypos) (le_of_lt hyc)) (hIup y (le_of_lt hypos) (le_of_lt hyc))
        (hIgap y (le_of_lt hypos) (le_of_lt hyc))
    have hJeq : J = I y - I x0 := add_eq_to_sub (I x0) J (I y) hadd
    have hwnn : (0:Real) ≤ y - x0 := sub_nonneg_of_le hxy
    have hpweq : x0 + (y - x0) = y := add_sub_cancel_local x0 y
    have hcont_xy' : ∀ z : Real, x0 ≤ z → z ≤ x0 + (y - x0) → ContinuousAt f z :=
      fun z hz1 hz2 => hcont_xy z hz1 (by rwa [hpweq] at hz2)
    have hub : ∀ z : Real, x0 ≤ z → z ≤ x0 + (y - x0) → f z ≤ f x0 + ε := by
      intro z hz1 hz2
      have hzy : z ≤ y := by rwa [hpweq] at hz2
      have hzx0nn : (0:Real) ≤ z - x0 := sub_nonneg_of_le hz1
      have hzx0le : z - x0 ≤ y - x0 := sub_le_sub_right_ftc hzy x0
      have hzδ : abs (z - x0) < δc := by
        rw [abs_of_nonneg hzx0nn]
        exact lt_of_le_of_lt hzx0le (by rwa [abs_of_nonneg hwnn] at hyδc)
      exact le_of_lt (near_const_bounds f x0 δc ε hδc z hzδ).1
    have hlb : ∀ z : Real, x0 ≤ z → z ≤ x0 + (y - x0) → f x0 - ε ≤ f z := by
      intro z hz1 hz2
      have hzy : z ≤ y := by rwa [hpweq] at hz2
      have hzx0nn : (0:Real) ≤ z - x0 := sub_nonneg_of_le hz1
      have hzx0le : z - x0 ≤ y - x0 := sub_le_sub_right_ftc hzy x0
      have hzδ : abs (z - x0) < δc := by
        rw [abs_of_nonneg hzx0nn]
        exact lt_of_le_of_lt hzx0le (by rwa [abs_of_nonneg hwnn] at hyδc)
      exact le_of_lt (near_const_bounds f x0 δc ε hδc z hzδ).2
    have hcongr_lo := lowerSumCont_congr_val f x0 hpweq.symm hxy (le_add_of_nonneg_right hwnn)
      hcont_xy hcont_xy' (2 ^ 0) (two_pow_pos 0)
    have hcongr_up := upperSumCont_congr_val f x0 hpweq.symm hxy (le_add_of_nonneg_right hwnn)
      hcont_xy hcont_xy' (2 ^ 0) (two_pow_pos 0)
    have hJlow' : lowerSumCont f x0 (x0 + (y - x0)) (le_add_of_nonneg_right hwnn) hcont_xy'
        (2 ^ 0) (two_pow_pos 0) ≤ J := hcongr_lo ▸ (hJsw 0).1
    have hJup' : J ≤ upperSumCont f x0 (x0 + (y - x0)) (le_add_of_nonneg_right hwnn) hcont_xy'
        (2 ^ 0) (two_pow_pos 0) := hcongr_up ▸ (hJsw 0).2
    obtain ⟨hJgelb, hJleub⟩ :=
      integral_close_to_const f x0 (y - x0) (le_of_lt hx0pos) hwnn hcont_xy' (f x0) ε hub hlb J
        hJlow' hJup'
    have hgoal1 : I y - I x0 - f x0 * (y - x0) ≤ ε * (y - x0) := by
      rw [← hJeq]
      have h1 := add_le_add_both hJleub (le_refl (-(f x0 * (y - x0))))
      rwa [← sub_def J (f x0 * (y - x0)), mul_expand_ub (f x0) ε (y - x0)] at h1
    have hgoal2 : -(ε * (y - x0)) ≤ I y - I x0 - f x0 * (y - x0) := by
      rw [← hJeq]
      have h1 := add_le_add_both hJgelb (le_refl (-(f x0 * (y - x0))))
      rw [← sub_def J (f x0 * (y - x0)), mul_expand_lb (f x0) ε (y - x0)] at h1
      exact h1
    have habsy : abs (y - x0) = y - x0 := abs_of_nonneg hwnn
    rw [habsy]
    exact abs_le_of_bounds hgoal1 hgoal2
  · -- y ≤ x0
    have hcont_x0 : ∀ z : Real, 0 ≤ z → z ≤ x0 → ContinuousAt f z :=
      hcont_x x0 (le_of_lt hx0pos) (le_of_lt hx0c)
    have hcont_y' : ∀ z : Real, 0 ≤ z → z ≤ y → ContinuousAt f z :=
      fun z hz1 hz2 => hcont z hz1 (le_trans hz2 (le_of_lt hyc))
    have hcont_yx : ∀ z : Real, y ≤ z → z ≤ x0 → ContinuousAt f z :=
      fun z hz1 hz2 => hcont z (le_trans (le_of_lt hypos) hz1) (le_trans hz2 (le_of_lt hx0c))
    have hnonneg_x0 : ∀ z : Real, 0 ≤ z → z ≤ x0 → 0 ≤ f z :=
      fun z hz1 hz2 => hnonneg z hz1 (le_trans hz2 (le_of_lt hx0c))
    obtain ⟨J', hJsw', hJgap'⟩ := continuous_riemann_integrable f y x0 hyx hcont_yx
    have hadd' : I y + J' = I x0 :=
      riemann_integral_additivity f y x0 (le_of_lt hypos) hyx (le_of_lt hx0pos) hcont_x0 hcont_y'
        hcont_yx hnonneg_x0 (I y) J' (I x0)
        (hIlow y (le_of_lt hypos) (le_of_lt hyc)) (hIup y (le_of_lt hypos) (le_of_lt hyc))
        (hIgap y (le_of_lt hypos) (le_of_lt hyc))
        (fun k => (hJsw' k).1) (fun k => (hJsw' k).2) hJgap'
        (hIlow x0 (le_of_lt hx0pos) (le_of_lt hx0c)) (hIup x0 (le_of_lt hx0pos) (le_of_lt hx0c))
        (hIgap x0 (le_of_lt hx0pos) (le_of_lt hx0c))
    have hIeq' : I y - I x0 = -J' := sub_eq_neg_of_add_eq (I y) J' (I x0) hadd'
    have hwnn' : (0:Real) ≤ x0 - y := sub_nonneg_of_le hyx
    have hpweq' : y + (x0 - y) = x0 := add_sub_cancel_local y x0
    have hcont_yx' : ∀ z : Real, y ≤ z → z ≤ y + (x0 - y) → ContinuousAt f z :=
      fun z hz1 hz2 => hcont_yx z hz1 (by rwa [hpweq'] at hz2)
    have hub' : ∀ z : Real, y ≤ z → z ≤ y + (x0 - y) → f z ≤ f x0 + ε := by
      intro z hz1 hz2
      have hzx0 : z ≤ x0 := by rwa [hpweq'] at hz2
      have hzx0nonpos : z - x0 ≤ 0 := sub_nonpos_of_le_ftc hzx0
      have hx0zle : x0 - z ≤ x0 - y := sub_le_sub_left_ftc hz1 x0
      have hzδ : abs (z - x0) < δc := by
        rw [abs_of_nonpos hzx0nonpos, neg_sub_eq_local z x0]
        have hyx0nonpos : y - x0 ≤ 0 := sub_nonpos_of_le_ftc hyx
        have hyδc' : x0 - y < δc := by rw [abs_of_nonpos hyx0nonpos, neg_sub_eq_local y x0] at hyδc; exact hyδc
        exact lt_of_le_of_lt hx0zle hyδc'
      exact le_of_lt (near_const_bounds f x0 δc ε hδc z hzδ).1
    have hlb' : ∀ z : Real, y ≤ z → z ≤ y + (x0 - y) → f x0 - ε ≤ f z := by
      intro z hz1 hz2
      have hzx0 : z ≤ x0 := by rwa [hpweq'] at hz2
      have hzx0nonpos : z - x0 ≤ 0 := sub_nonpos_of_le_ftc hzx0
      have hx0zle : x0 - z ≤ x0 - y := sub_le_sub_left_ftc hz1 x0
      have hzδ : abs (z - x0) < δc := by
        rw [abs_of_nonpos hzx0nonpos, neg_sub_eq_local z x0]
        have hyx0nonpos : y - x0 ≤ 0 := sub_nonpos_of_le_ftc hyx
        have hyδc' : x0 - y < δc := by rw [abs_of_nonpos hyx0nonpos, neg_sub_eq_local y x0] at hyδc; exact hyδc
        exact lt_of_le_of_lt hx0zle hyδc'
      exact le_of_lt (near_const_bounds f x0 δc ε hδc z hzδ).2
    have hcongr_lo' := lowerSumCont_congr_val f y hpweq'.symm hyx (le_add_of_nonneg_right hwnn')
      hcont_yx hcont_yx' (2 ^ 0) (two_pow_pos 0)
    have hcongr_up' := upperSumCont_congr_val f y hpweq'.symm hyx (le_add_of_nonneg_right hwnn')
      hcont_yx hcont_yx' (2 ^ 0) (two_pow_pos 0)
    have hJlow'' : lowerSumCont f y (y + (x0 - y)) (le_add_of_nonneg_right hwnn') hcont_yx'
        (2 ^ 0) (two_pow_pos 0) ≤ J' := hcongr_lo' ▸ (hJsw' 0).1
    have hJup'' : J' ≤ upperSumCont f y (y + (x0 - y)) (le_add_of_nonneg_right hwnn') hcont_yx'
        (2 ^ 0) (two_pow_pos 0) := hcongr_up' ▸ (hJsw' 0).2
    obtain ⟨hJ'gelb, hJ'leub⟩ :=
      integral_close_to_const f y (x0 - y) (le_of_lt hypos) hwnn' hcont_yx' (f x0) ε hub' hlb' J'
        hJlow'' hJup''
    have hexpand : I y - I x0 - f x0 * (y - x0) = -(J' - f x0 * (x0 - y)) := by
      rw [hIeq']
      exact neg_sub_flip J' (f x0) x0 y
    have hdiff_ub : J' - f x0 * (x0 - y) ≤ ε * (x0 - y) := by
      have h1 := add_le_add_both hJ'leub (le_refl (-(f x0 * (x0 - y))))
      rwa [← sub_def J' (f x0 * (x0 - y)), mul_expand_ub (f x0) ε (x0 - y)] at h1
    have hdiff_lb : -(ε * (x0 - y)) ≤ J' - f x0 * (x0 - y) := by
      have h1 := add_le_add_both hJ'gelb (le_refl (-(f x0 * (x0 - y))))
      rw [← sub_def J' (f x0 * (x0 - y)), mul_expand_lb (f x0) ε (x0 - y)] at h1
      exact h1
    have hgoal2' : -(ε * (x0 - y)) ≤ I y - I x0 - f x0 * (y - x0) := by
      rw [hexpand]
      exact neg_le_neg hdiff_ub
    have hgoal1' : I y - I x0 - f x0 * (y - x0) ≤ ε * (x0 - y) := by
      rw [hexpand]
      have h1 := neg_le_neg hdiff_lb
      rwa [neg_neg_local (ε * (x0 - y))] at h1
    have hyx0nonpos : y - x0 ≤ 0 := sub_nonpos_of_le_ftc hyx
    have habsy' : abs (y - x0) = x0 - y := by rw [abs_of_nonpos hyx0nonpos, neg_sub_eq_local y x0]
    rw [habsy']
    exact abs_le_of_bounds hgoal1' hgoal2'

end Real
end MachLib
