import MachLib.InverseTrig
import MachLib.InverseTrigBounded
import MachLib.SinTaylorRemainder
import MachLib.NatCastArith
import MachLib.DivisionError
import MachLib.SignTactic
import MachLib.SturmNonOscillation
import MachLib.TanTaylorRemainder

/-!
# `arcsin` Taylor-remainder bound — a genuinely different chain from `tan`/`tanh`/`atan`

`eml_asin.v` computes the 4-term Maclaurin truncation `arcsin(x) ≈ x + x³/6 + 3x⁵/40 + 15x⁷/336`,
valid only for `|x| ≤ 0.5` (the RTL's own comment: convergence is too slow outside this band).
`arcsin' = 1/√(1−x²)` is neither polynomial-in-itself (like `tan`/`tanh`) nor rational-in-`x`
(like `atan`) — every further derivative involves a GROWING ODD POWER of `1/√(1−y²)` composed with
a growing-degree polynomial in `y`. Verified symbolically (sympy) before encoding: writing
`h(y) := 1/√(1−y²)` and `f^(k)(y) = N_k(y)·h(y)^(2k−1)` for a polynomial `N_k`, the numerators obey
the CLEAN recursion `N_1 = 1`, `N_{k+1}(y) = N_k'(y)·(1−y²) + (2k−1)·y·N_k(y)` — cross-checked
numerically against `sympy`'s direct 8th-order symbolic differentiation of `asin` at `y = 0.3`
(all 8 levels match to 1e-9).

**New axiom**: `MachLib.Real` had no derivative rule for `sqrt` at all (`Trig.lean` only gives its
algebraic properties) — `HasDerivAt_arcsin` itself was already a standalone axiom not derived from
one. Reaching the 2nd derivative and beyond needs differentiating THROUGH the `sqrt`, so
`InverseTrig.lean` gained one new axiom, `HasDerivAt_sqrt` (the standard `d/dx √x = 1/(2√x)` for
`x > 0`), added after explicit user sign-off (the "general axiom, reusable by `acos` too" option)
rather than a narrower one-off. Every level below composes it via the EXISTING `HasDerivAt_comp`/
`HasDerivAt_inv` combinators — no further axioms.

**Domain**: `[0, 0.5]` (matching `eml_asin.v`'s own documented valid range), since `h(y)` blows up
as `y → 1` — the `Rasin_k` bound below is NOT flat like `tanh`'s, but grows with the (bounded, on
this domain) irrational constant `h(0.5) = 1/√(3/4) = 2/√3`.
-/

namespace MachLib.Real

/-- `arcsin`'s derivative, as its own named function — `h(y) := 1/√(1−y²) = arcsin'(y)`. -/
noncomputable def hAsin (y : Real) : Real := 1 / sqrt (1 - y * y)

/-- `h(y)^n`, built by plain recursion (`h^0 = 1`, `h^(n+1) = h · h^n`) — the odd powers
(`hAsinPow 1, 3, 5, ..., 15`) are exactly the `h`-factor in `arcsin`'s `1st..8th` derivatives. -/
noncomputable def hAsinPow (n : Nat) (y : Real) : Real :=
  match n with
  | 0 => 1
  | m + 1 => hAsin y * hAsinPow m y

theorem hAsinPow_zero (y : Real) : hAsinPow 0 y = 1 := rfl
theorem hAsinPow_succ (n : Nat) (y : Real) : hAsinPow (n + 1) y = hAsin y * hAsinPow n y := rfl

theorem hAsinPow_add (a b : Nat) (y : Real) :
    hAsinPow (a + b) y = hAsinPow a y * hAsinPow b y := by
  induction b with
  | zero => rw [hAsinPow_zero]; mach_ring
  | succ m ih =>
    rw [show a + (m + 1) = (a + m) + 1 from by omega, hAsinPow_succ, ih, hAsinPow_succ]
    mach_ring

/-- `x·x < 1` from `abs x < 1` (`abs_mul_self` + the existing `sq_lt_one_of_abs_le_lt_one`,
instantiated at its own bound `R := abs x`). -/
theorem sq_lt_one_of_abs_lt_one {x : Real} (hx : abs x < 1) : x * x < 1 := by
  rw [← abs_mul_self x]
  exact sq_lt_one_of_abs_le_lt_one hx (le_refl (abs x))

theorem one_sub_sq_pos {x : Real} (hx : abs x < 1) : 0 < 1 - x * x :=
  sub_pos_of_lt (sq_lt_one_of_abs_lt_one hx)

/-- **The key identity**: `h(x)·h(x)·(1−x²) = 1` — the `sqrt`-analogue of `tan`/`tanh`'s
`sec²`/`sech²` identities, from `sqrt_sq_nonneg` (`s·s = 1−x²` for `s := √(1−x²)`) plus
`h := 1/s`. -/
theorem hAsin_sq_mul_one_sub_sq {x : Real} (hx : abs x < 1) :
    hAsin x * hAsin x * (1 - x * x) = 1 := by
  have hpos : 0 < 1 - x * x := one_sub_sq_pos hx
  have hsne : sqrt (1 - x * x) ≠ 0 := ne_of_gt (sqrt_pos hpos)
  have hs2 : sqrt (1 - x * x) * sqrt (1 - x * x) = 1 - x * x :=
    sqrt_sq_nonneg (1 - x * x) (le_of_lt hpos)
  calc hAsin x * hAsin x * (1 - x * x)
      = hAsin x * hAsin x * (sqrt (1 - x * x) * sqrt (1 - x * x)) :=
        congrArg (fun t => hAsin x * hAsin x * t) hs2.symm
    _ = (hAsin x * sqrt (1 - x * x)) * (hAsin x * sqrt (1 - x * x)) := by mach_ring
    _ = 1 * 1 := by
        rw [show hAsin x * sqrt (1 - x * x) = 1 from by
          unfold hAsin; rw [mul_comm, mul_inv (sqrt (1 - x * x)) hsne]]
    _ = 1 := by mach_ring

/-- **The base derivative fact**: `h'(x) = x·h(x)^3` (`h := arcsin'`). Built from the new
`HasDerivAt_sqrt` axiom composed via `HasDerivAt_comp`/`HasDerivAt_inv` — the ONLY place the new
axiom is invoked; every level of the `Rasin_k` chain below reuses this single fact via
`hD_hAsinPow`'s induction, never touching `HasDerivAt_sqrt` again. -/
theorem hD_hAsin (x : Real) (hx : abs x < 1) : HasDerivAt hAsin (x * hAsinPow 3 x) x := by
  have hpos : 0 < 1 - x * x := one_sub_sq_pos hx
  have hspos : 0 < sqrt (1 - x * x) := sqrt_pos hpos
  have hsne : sqrt (1 - x * x) ≠ 0 := ne_of_gt hspos
  have hu : HasDerivAt (fun y => 1 - y * y) (0 - (x + x)) x :=
    HasDerivAt_sub (fun _ => (1 : Real)) (fun y => y * y) 0 (x + x) x
      (HasDerivAt_const 1 x) (hD_y2 x)
  have hs := HasDerivAt_sqrt (1 - x * x) hpos
  have hcomp : HasDerivAt (fun y => sqrt (1 - y * y))
      ((1 / (sqrt (1 - x * x) + sqrt (1 - x * x))) * (0 - (x + x))) x :=
    HasDerivAt_comp sqrt (fun y => 1 - y * y) (0 - (x + x))
      (1 / (sqrt (1 - x * x) + sqrt (1 - x * x))) x hu hs
  have hinv := HasDerivAt_inv (fun y => sqrt (1 - y * y))
    ((1 / (sqrt (1 - x * x) + sqrt (1 - x * x))) * (0 - (x + x))) x hsne hcomp
  refine hasDerivAt_congr_val hinv ?_
  have hs2ne : sqrt (1 - x * x) + sqrt (1 - x * x) ≠ 0 :=
    ne_of_gt (add_pos hspos hspos)
  have hfrac2 : (1 + 1 : Real) * (1 / (sqrt (1 - x * x) + sqrt (1 - x * x)))
      = 1 / sqrt (1 - x * x) :=
    frac_reduce (1 + 1) (sqrt (1 - x * x)) (sqrt (1 - x * x) + sqrt (1 - x * x)) hsne hs2ne
      (by mach_ring)
  have hkey : (1 / (sqrt (1 - x * x) + sqrt (1 - x * x))) * (x + x)
      = x * (1 / sqrt (1 - x * x)) := by
    calc (1 / (sqrt (1 - x * x) + sqrt (1 - x * x))) * (x + x)
        = x * ((1 + 1) * (1 / (sqrt (1 - x * x) + sqrt (1 - x * x)))) := by mach_ring
      _ = x * (1 / sqrt (1 - x * x)) := by rw [hfrac2]
  have hpow2 : (1 / sqrt (1 - x * x)) * (1 / sqrt (1 - x * x))
      = 1 / (sqrt (1 - x * x) * sqrt (1 - x * x)) := one_div_mul_one_div hspos
  show -((1 / (sqrt (1 - x * x) + sqrt (1 - x * x))) * (0 - (x + x)))
      / (sqrt (1 - x * x) * sqrt (1 - x * x)) = x * hAsinPow 3 x
  unfold hAsinPow hAsin
  calc -((1 / (sqrt (1 - x * x) + sqrt (1 - x * x))) * (0 - (x + x)))
        / (sqrt (1 - x * x) * sqrt (1 - x * x))
      = ((1 / (sqrt (1 - x * x) + sqrt (1 - x * x))) * (x + x))
          / (sqrt (1 - x * x) * sqrt (1 - x * x)) := by mach_ring
    _ = (x * (1 / sqrt (1 - x * x))) / (sqrt (1 - x * x) * sqrt (1 - x * x)) := by rw [hkey]
    _ = x * ((1 / sqrt (1 - x * x)) * (1 / (sqrt (1 - x * x) * sqrt (1 - x * x)))) := by
        rw [div_def _ _ (mul_ne_zero hsne hsne)]; mach_ring
    _ = x * ((1 / sqrt (1 - x * x)) * ((1 / sqrt (1 - x * x)) * (1 / sqrt (1 - x * x)))) := by
        rw [← hpow2]
    _ = x * (1 / sqrt (1 - x * x) * (1 / sqrt (1 - x * x) * (1 / sqrt (1 - x * x) * 1))) := by
        rw [mul_one_ax]

/-- **`hAsinPow`'s general derivative** — by induction on `n`, reusing `hD_hAsin` as the ONLY base
case and `hAsinPow_add` to recombine, so no further `sqrt`-specific reasoning is needed at any
level: `d/dy[h^n] = n·y·h^(n+2)`. -/
theorem hD_hAsinPow (n : Nat) (x : Real) (hx : abs x < 1) :
    HasDerivAt (fun y => hAsinPow n y) (natCast n * x * hAsinPow (n + 2) x) x := by
  induction n with
  | zero =>
    refine hasDerivAt_congr_val (HasDerivAt_const (1 : Real) x) ?_
    rw [natCast_zero]
    mach_ring
  | succ m ih =>
    have hstep := HasDerivAt_mul hAsin (fun y => hAsinPow m y) (x * hAsinPow 3 x)
      (natCast m * x * hAsinPow (m + 2) x) x (hD_hAsin x hx) ih
    refine hasDerivAt_congr_val hstep ?_
    have e2 : hAsinPow (m + 3) x = hAsinPow 3 x * hAsinPow m x := by
      rw [show m + 3 = 3 + m from by omega]; exact hAsinPow_add 3 m x
    have e3 : hAsinPow (m + 3) x = hAsin x * hAsinPow (m + 2) x := hAsinPow_succ (m + 2) x
    have e4 : hAsin x * hAsinPow (m + 2) x = hAsinPow 3 x * hAsinPow m x := e3.symm.trans e2
    rw [show m + 1 + 2 = m + 3 from by omega, e2,
      show hAsin x * (natCast m * x * hAsinPow (m + 2) x)
          = natCast m * x * (hAsin x * hAsinPow (m + 2) x) from by mach_ring,
      e4, natCast_succ]
    mach_ring

/-! ## Monotonicity + a flat domain bound on `[0, R]`, `R := 1/2` — matching `eml_asin.v`'s own
documented valid range. Since `h` blows up only as `y → ±1` (not within our fixed, bounded-away-
from-1 domain), a single flat constant `Hmax := h(R)` bounds `h` throughout `[0,R]` — exactly
`tanh`'s flat-bound situation, not `tan`'s growing-`Mtan(x)` one, even though `h` itself is
irrational-valued. -/

/-- `arcsin`/`arcsin''`/etc.'s certified domain radius, matching `eml_asin.v`'s own `|x| ≤ 0.5`. -/
noncomputable def asinR : Real := 1 / (1 + 1)

theorem asinR_abs_lt_one : abs asinR < 1 := by
  unfold asinR
  rw [abs_of_nonneg (one_div_nonneg_of_pos my_two_pos)]
  exact div_lt_one_of_pos_lt my_two_pos (by
    have h := add_lt_add_left zero_lt_one_ax 1
    rwa [add_zero] at h)

/-- **`Hmax`**: `h` evaluated at the domain's right edge — the flat bound for `h` on `[0, R]`. -/
noncomputable def Hmax : Real := hAsin asinR

theorem hAsin_mono {y x : Real} (hy0 : 0 ≤ y) (hyx : y ≤ x) (hx1 : abs x < 1) :
    hAsin y ≤ hAsin x := by
  have hyy_le_xx : y * y ≤ x * x := mul_le_mul' hy0 hyx hy0 hyx
  have hxx1 : x * x < 1 := sq_lt_one_of_abs_lt_one hx1
  have h1mxx_pos : 0 < 1 - x * x := sub_pos_of_lt hxx1
  have h1sub : 1 - x * x ≤ 1 - y * y := sub_le_sub_left hyy_le_xx 1
  have hsm : sqrt (1 - x * x) ≤ sqrt (1 - y * y) := sqrt_mono (le_of_lt h1mxx_pos) h1sub
  unfold hAsin
  exact div_le_div_pos (le_of_lt zero_lt_one_ax) (le_refl 1) (sqrt_pos h1mxx_pos) hsm

theorem hAsin_nonneg {y : Real} (hy : abs y < 1) : 0 ≤ hAsin y :=
  one_div_nonneg_of_pos (sqrt_pos (one_sub_sq_pos hy))

theorem hAsin_le_Hmax {y : Real} (hy0 : 0 ≤ y) (hyR : y ≤ asinR) : hAsin y ≤ Hmax :=
  hAsin_mono hy0 hyR asinR_abs_lt_one

theorem hAsinPow_nonneg (n : Nat) {y : Real} (hy : abs y < 1) : 0 ≤ hAsinPow n y := by
  induction n with
  | zero => exact le_of_lt zero_lt_one_ax
  | succ m ih =>
    rw [hAsinPow_succ]
    exact mul_nonneg (hAsin_nonneg hy) ih

theorem hAsinPow_mono (n : Nat) {y x : Real} (hy0 : 0 ≤ y) (hyx : y ≤ x) (hx1 : abs x < 1) :
    hAsinPow n y ≤ hAsinPow n x := by
  have hx0 : 0 ≤ x := le_trans hy0 hyx
  have hx_lt1 : x < 1 := by rw [← abs_of_nonneg hx0]; exact hx1
  have hy_lt1 : y < 1 := lt_of_le_of_lt hyx hx_lt1
  have hy1 : abs y < 1 := by rw [abs_of_nonneg hy0]; exact hy_lt1
  induction n with
  | zero => exact le_refl 1
  | succ m ih =>
    rw [hAsinPow_succ, hAsinPow_succ]
    exact mul_le_mul' (hAsin_nonneg hy1) (hAsin_mono hy0 hyx hx1) (hAsinPow_nonneg m hy1) ih

/-- **The shift identity**: `h(x)^(n+2)·(1−x²) = h(x)^n` — the reusable bridge every `Rasin_k_deriv`
below needs to fold `N_k'(y)·h(y)^(2k−1)` back into a SINGLE `h(y)^(2k+1)` factor (the `sqrt`-chain
analogue of `tan`/`tanh`'s `sec²`/`sech²` coefficient bridging, but as ONE lemma reused at every
level instead of re-derived). -/
theorem hAsinPow_shift2 (n : Nat) {x : Real} (hx : abs x < 1) :
    hAsinPow (n + 2) x * (1 - x * x) = hAsinPow n x := by
  have hkey := hAsin_sq_mul_one_sub_sq hx
  have hadd : hAsinPow (n + 2) x = hAsinPow n x * hAsinPow 2 x := hAsinPow_add n 2 x
  have h2 : hAsinPow 2 x = hAsin x * (hAsin x * 1) := rfl
  calc hAsinPow (n + 2) x * (1 - x * x)
      = (hAsinPow n x * hAsinPow 2 x) * (1 - x * x) := by rw [hadd]
    _ = hAsinPow n x * (hAsin x * hAsin x * (1 - x * x)) := by rw [h2]; mach_ring
    _ = hAsinPow n x * 1 := by rw [hkey]
    _ = hAsinPow n x := by mach_ring

/-! ## `gAsin8` — the base level (`Rasin7' = gAsin8`), analogous to `tanh`'s `g8h`. `P^(8) = 0`
(the truncation's own 8th derivative vanishes, degree 7), so `gAsin8 = N_8(y)·h(y)^15` with no
correction term. Unlike `tanh`'s FLAT bound (`|tanh| ≤ 1` everywhere), the bound here is flat
ONLY because the domain `[0, asinR]` is fixed and bounded away from `h`'s singularity at `1` — the
same mechanism `tan`'s `Mtan(x)` needed, but since our domain never approaches `1`, a single
constant (`h` evaluated at the domain's own edge `asinR`) suffices, no `x`-dependent quantity
needed. -/

noncomputable def gAsin8 (y : Real) : Real :=
  (natCast 5040 * (y * y * y * y * y * y * y) + natCast 52920 * (y * y * y * y * y)
    + natCast 66150 * (y * y * y) + natCast 11025 * y) * hAsinPow 15 y

/-- `N_8` evaluated at the domain's right edge `asinR` — the flat polynomial-part bound. -/
noncomputable def NTop : Real :=
  natCast 5040 * (asinR * asinR * asinR * asinR * asinR * asinR * asinR)
    + natCast 52920 * (asinR * asinR * asinR * asinR * asinR)
    + natCast 66150 * (asinR * asinR * asinR) + natCast 11025 * asinR

theorem gAsin8_bound (t : Real) (ht0 : 0 ≤ t) (htR : t ≤ asinR) :
    abs (gAsin8 t) ≤ NTop * hAsinPow 15 asinR := by
  have hasinR0 : 0 ≤ asinR := le_trans ht0 htR
  have hasinR_lt1 : asinR < 1 := by rw [← abs_of_nonneg hasinR0]; exact asinR_abs_lt_one
  have ht_lt1 : t < 1 := lt_of_le_of_lt htR hasinR_lt1
  have ht1 : abs t < 1 := by rw [abs_of_nonneg ht0]; exact ht_lt1
  -- t^j ≤ asinR^j, j = 2..7, plus nonnegativity of each power.
  have tnn2 : 0 ≤ t * t := mul_nonneg ht0 ht0
  have tnn3 : 0 ≤ t * t * t := mul_nonneg tnn2 ht0
  have tnn4 : 0 ≤ t * t * t * t := mul_nonneg tnn3 ht0
  have tnn5 : 0 ≤ t * t * t * t * t := mul_nonneg tnn4 ht0
  have tnn6 : 0 ≤ t * t * t * t * t * t := mul_nonneg tnn5 ht0
  have tnn7 : 0 ≤ t * t * t * t * t * t * t := mul_nonneg tnn6 ht0
  have m2 : t * t ≤ asinR * asinR := mul_le_mul' ht0 htR ht0 htR
  have m3 : t * t * t ≤ asinR * asinR * asinR := mul_le_mul' tnn2 m2 ht0 htR
  have m4 : t * t * t * t ≤ asinR * asinR * asinR * asinR := mul_le_mul' tnn3 m3 ht0 htR
  have m5 : t * t * t * t * t ≤ asinR * asinR * asinR * asinR * asinR :=
    mul_le_mul' tnn4 m4 ht0 htR
  have m6 : t * t * t * t * t * t ≤ asinR * asinR * asinR * asinR * asinR * asinR :=
    mul_le_mul' tnn5 m5 ht0 htR
  have m7 : t * t * t * t * t * t * t ≤ asinR * asinR * asinR * asinR * asinR * asinR * asinR :=
    mul_le_mul' tnn6 m6 ht0 htR
  have hNnn : (0 : Real) ≤ natCast 5040 * (t * t * t * t * t * t * t)
      + natCast 52920 * (t * t * t * t * t) + natCast 66150 * (t * t * t) + natCast 11025 * t :=
    add_nonneg (add_nonneg (add_nonneg (mul_nonneg (natCast_nonneg 5040) tnn7)
      (mul_nonneg (natCast_nonneg 52920) tnn5)) (mul_nonneg (natCast_nonneg 66150) tnn3))
      (mul_nonneg (natCast_nonneg 11025) ht0)
  have hNle : natCast 5040 * (t * t * t * t * t * t * t) + natCast 52920 * (t * t * t * t * t)
      + natCast 66150 * (t * t * t) + natCast 11025 * t ≤ NTop := by
    unfold NTop
    exact add_le_add_both (add_le_add_both (add_le_add_both
      (mul_le_mul_of_nonneg_left m7 (natCast_nonneg 5040))
      (mul_le_mul_of_nonneg_left m5 (natCast_nonneg 52920)))
      (mul_le_mul_of_nonneg_left m3 (natCast_nonneg 66150)))
      (mul_le_mul_of_nonneg_left htR (natCast_nonneg 11025))
  have hHle : hAsinPow 15 t ≤ hAsinPow 15 asinR := hAsinPow_mono 15 ht0 htR asinR_abs_lt_one
  have hHnn : 0 ≤ hAsinPow 15 t := hAsinPow_nonneg 15 ht1
  unfold gAsin8
  rw [abs_of_nonneg (mul_nonneg hNnn hHnn)]
  exact mul_le_mul' hNnn hNle hHnn hHle

/-- `h(0) = 1` (`sqrt(1-0)=sqrt 1=1`, then `1/1=1`) — the base case every `Rasin_k_zero` below
needs (`hAsinPow n 0 = 1` for any `n`, since `hAsinPow` is just repeated multiplication by `h`). -/
theorem hAsin_zero : hAsin 0 = 1 := by
  unfold hAsin
  rw [show (1 : Real) - 0 * 0 = 1 from by mach_ring, sqrt_one]
  have h := mul_inv (1 : Real) one_ne_zero
  rwa [one_mul_thm] at h

theorem hAsinPow_zero_pt (n : Nat) : hAsinPow n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ m ih => rw [hAsinPow_succ, hAsin_zero, ih]; mach_ring

/-! ## `Rasin7` (`Rasin6' = Rasin7`, `Rasin7' = gAsin8`). -/

noncomputable def Rasin7 (y : Real) : Real :=
  (natCast 720 * (y * y * y * y * y * y) + natCast 5400 * (y * y * y * y) + natCast 4050 * (y * y)
    + natCast 225) * hAsinPow 13 y - natCast 225

set_option maxHeartbeats 1000000 in
theorem Rasin7_deriv (c : Real) (hx : abs c < 1) : HasDerivAt Rasin7 (gAsin8 c) c := by
  have h6 := HasDerivAt_mul (fun _ => natCast 720) (fun y => y * y * y * y * y * y) 0 _ c
    (HasDerivAt_const (natCast 720) c) (hD_y6 c)
  have h4 := HasDerivAt_mul (fun _ => natCast 5400) (fun y => y * y * y * y) 0 _ c
    (HasDerivAt_const (natCast 5400) c) (hD_y4 c)
  have h2 := HasDerivAt_mul (fun _ => natCast 4050) (fun y => y * y) 0 _ c
    (HasDerivAt_const (natCast 4050) c) (hD_y2 c)
  have hc0 := HasDerivAt_const (natCast 225) c
  have hadd1 := HasDerivAt_add (fun y => natCast 720 * (y * y * y * y * y * y))
    (fun y => natCast 5400 * (y * y * y * y)) _ _ c h6 h4
  have hadd2 := HasDerivAt_add _ (fun y => natCast 4050 * (y * y)) _ _ c hadd1 h2
  have hN7 := HasDerivAt_add _ (fun _ => natCast 225) _ _ c hadd2 hc0
  have hMain := HasDerivAt_mul
    (fun y => natCast 720 * (y * y * y * y * y * y) + natCast 5400 * (y * y * y * y)
      + natCast 4050 * (y * y) + natCast 225)
    (fun y => hAsinPow 13 y) _ _ c hN7 (hD_hAsinPow 13 c hx)
  have hfull := HasDerivAt_sub _ (fun _ => natCast 225) _ _ c hMain (HasDerivAt_const (natCast 225) c)
  refine hasDerivAt_congr_val hfull ?_
  simp only []
  unfold gAsin8
  rw [← hAsinPow_shift2 13 hx]
  have e6 : natCast 4320 = (1 + 1 + 1 + 1 + 1 + 1) * natCast 720 := (six_mul_natCast 720).symm
  have e4 : natCast 21600 = (1 + 1 + 1 + 1) * natCast 5400 := (four_mul_natCast 5400).symm
  have e2 : natCast 8100 = (1 + 1) * natCast 4050 := (two_mul_natCast 4050).symm
  have eB7 : natCast 9360 = natCast 13 * natCast 720 := by rw [← natCast_mul]
  have eB5 : natCast 70200 = natCast 13 * natCast 5400 := by rw [← natCast_mul]
  have eB3 : natCast 52650 = natCast 13 * natCast 4050 := by rw [← natCast_mul]
  have eB1 : natCast 2925 = natCast 13 * natCast 225 := by rw [← natCast_mul]
  have hsum7 : natCast 5040 + natCast 4320 = natCast 9360 := by rw [← natCast_add]
  have hsum5 : natCast 52920 + natCast 21600 = natCast 4320 + natCast 70200 := by
    rw [← natCast_add, ← natCast_add]
  have hsum3 : natCast 66150 + natCast 8100 = natCast 21600 + natCast 52650 := by
    rw [← natCast_add, ← natCast_add]
  have hsum1 : natCast 11025 = natCast 8100 + natCast 2925 := by rw [← natCast_add]
  rw [show natCast 5040 = natCast 9360 - natCast 4320 from by rw [← hsum7]; mach_ring,
    show natCast 52920 = natCast 4320 + natCast 70200 - natCast 21600 from by
      rw [← hsum5]; mach_ring,
    show natCast 66150 = natCast 21600 + natCast 52650 - natCast 8100 from by
      rw [← hsum3]; mach_ring,
    hsum1, eB7, eB5, eB3, eB1, e6, e4, e2]
  mach_mpoly [c, hAsinPow 15 c, natCast 720, natCast 5400, natCast 4050, natCast 225, natCast 13]

theorem Rasin7_zero : Rasin7 0 = 0 := by
  unfold Rasin7
  rw [hAsinPow_zero_pt]
  mach_ring

theorem asinR_nonneg : 0 ≤ asinR := le_of_lt (one_div_pos_of_pos my_two_pos)

theorem asinR_lt_one : asinR < 1 := by rw [← abs_of_nonneg asinR_nonneg]; exact asinR_abs_lt_one

theorem NTop_nonneg : 0 ≤ NTop := by
  have a0 := asinR_nonneg
  have a2 : 0 ≤ asinR * asinR := mul_nonneg a0 a0
  have a3 : 0 ≤ asinR * asinR * asinR := mul_nonneg a2 a0
  have a5 : 0 ≤ asinR * asinR * asinR * asinR * asinR := mul_nonneg (mul_nonneg a3 a0) a0
  have a7 : 0 ≤ asinR * asinR * asinR * asinR * asinR * asinR * asinR :=
    mul_nonneg (mul_nonneg a5 a0) a0
  unfold NTop
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (natCast_nonneg 5040) a7)
    (mul_nonneg (natCast_nonneg 52920) a5))
    (mul_nonneg (natCast_nonneg 66150) a3))
    (mul_nonneg (natCast_nonneg 11025) a0)

theorem hAsinPow15_asinR_nonneg : 0 ≤ hAsinPow 15 asinR := hAsinPow_nonneg 15 asinR_abs_lt_one

theorem Rasin7_bound (x : Real) (hx0 : 0 ≤ x) (hxR : x ≤ asinR) :
    abs (Rasin7 x) ≤ NTop * hAsinPow 15 asinR * x := by
  have hxR1 : x < 1 := lt_of_le_of_lt hxR asinR_lt_one
  apply abs_mvt_step_bounded Rasin7 gAsin8 x (NTop * hAsinPow 15 asinR) 1 hx0 hxR1
    (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg)
    (fun c hc0 hcR => Rasin7_deriv c (by rw [abs_of_nonneg hc0]; exact hcR))
    Rasin7_zero
    (fun t ht0 htx => gAsin8_bound t ht0 (le_trans htx hxR))

/-! ## `Rasin6` (`Rasin5' = Rasin6`, `Rasin6' = Rasin7`). -/

noncomputable def Rasin6 (y : Real) : Real :=
  (natCast 120 * (y * y * y * y * y) + natCast 600 * (y * y * y) + natCast 225 * y)
    * hAsinPow 11 y - natCast 225 * y

set_option maxHeartbeats 1000000 in
theorem Rasin6_deriv (c : Real) (hx : abs c < 1) : HasDerivAt Rasin6 (Rasin7 c) c := by
  have h5 := HasDerivAt_mul (fun _ => natCast 120) (fun y => y * y * y * y * y) 0 _ c
    (HasDerivAt_const (natCast 120) c) (hD_y5 c)
  have h3 := HasDerivAt_mul (fun _ => natCast 600) (fun y => y * y * y) 0 _ c
    (HasDerivAt_const (natCast 600) c) (hD_y3 c)
  have h1 := HasDerivAt_mul (fun _ => natCast 225) (fun y => y) 0 1 c
    (HasDerivAt_const (natCast 225) c) (HasDerivAt_id c)
  have hadd1 := HasDerivAt_add (fun y => natCast 120 * (y * y * y * y * y))
    (fun y => natCast 600 * (y * y * y)) _ _ c h5 h3
  have hN6 := HasDerivAt_add _ (fun y => natCast 225 * y) _ _ c hadd1 h1
  have hMain := HasDerivAt_mul
    (fun y => natCast 120 * (y * y * y * y * y) + natCast 600 * (y * y * y) + natCast 225 * y)
    (fun y => hAsinPow 11 y) _ _ c hN6 (hD_hAsinPow 11 c hx)
  have hy1 := HasDerivAt_mul (fun _ => natCast 225) (fun y => y) 0 1 c
    (HasDerivAt_const (natCast 225) c) (HasDerivAt_id c)
  have hfull := HasDerivAt_sub _ (fun y => natCast 225 * y) _ _ c hMain hy1
  refine hasDerivAt_congr_val hfull ?_
  simp only []
  unfold Rasin7
  rw [← hAsinPow_shift2 11 hx]
  have e5 : natCast 600 = (1 + 1 + 1 + 1 + 1) * natCast 120 := (five_mul_natCast 120).symm
  have e3 : natCast 1800 = (1 + 1 + 1) * natCast 600 := (three_mul_natCast 600).symm
  have eB6 : natCast 1320 = natCast 11 * natCast 120 := by rw [← natCast_mul]
  have eB4 : natCast 6600 = natCast 11 * natCast 600 := by rw [← natCast_mul]
  have eB2 : natCast 2475 = natCast 11 * natCast 225 := by rw [← natCast_mul]
  have hsum6 : natCast 720 + natCast 600 = natCast 1320 := by rw [← natCast_add]
  have hsum4 : natCast 600 + natCast 6600 = natCast 5400 + natCast 1800 := by
    rw [← natCast_add, ← natCast_add]
  have hsum2 : natCast 1800 + natCast 2475 = natCast 4050 + natCast 225 := by
    rw [← natCast_add, ← natCast_add]
  rw [show natCast 720 = natCast 1320 - natCast 600 from by rw [← hsum6]; mach_ring,
    show natCast 5400 = natCast 600 + natCast 6600 - natCast 1800 from by rw [hsum4]; mach_ring,
    show natCast 4050 = natCast 1800 + natCast 2475 - natCast 225 from by rw [hsum2]; mach_ring,
    eB6, eB4, eB2, e3, e5]
  mach_mpoly [c, hAsinPow 13 c, natCast 120, natCast 225, natCast 11]

theorem Rasin6_zero : Rasin6 0 = 0 := by
  unfold Rasin6
  rw [hAsinPow_zero_pt]
  mach_ring

theorem Rasin6_bound (x : Real) (hx0 : 0 ≤ x) (hxR : x ≤ asinR) :
    abs (Rasin6 x) ≤ NTop * hAsinPow 15 asinR * x * x := by
  have hxR1 : x < 1 := lt_of_le_of_lt hxR asinR_lt_one
  apply abs_mvt_step_bounded Rasin6 Rasin7 x (NTop * hAsinPow 15 asinR * x) 1 hx0 hxR1
    (mul_nonneg (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) hx0)
    (fun c hc0 hcR => Rasin6_deriv c (by rw [abs_of_nonneg hc0]; exact hcR))
    Rasin6_zero
    (fun t ht0 htx => le_trans (Rasin7_bound t ht0 (le_trans htx hxR))
      (mul_le_mul_of_nonneg_left htx (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg)))

/-! ## `Rasin5` (`Rasin4' = Rasin5`, `Rasin5' = Rasin6`). -/

noncomputable def Rasin5 (y : Real) : Real :=
  (natCast 24 * (y * y * y * y) + natCast 72 * (y * y) + natCast 9) * hAsinPow 9 y
    - natCast 225 * (1 / (1 + 1)) * (y * y) - natCast 9

set_option maxHeartbeats 1000000 in
theorem Rasin5_deriv (c : Real) (hx : abs c < 1) : HasDerivAt Rasin5 (Rasin6 c) c := by
  have h4 := HasDerivAt_mul (fun _ => natCast 24) (fun y => y * y * y * y) 0 _ c
    (HasDerivAt_const (natCast 24) c) (hD_y4 c)
  have h2 := HasDerivAt_mul (fun _ => natCast 72) (fun y => y * y) 0 _ c
    (HasDerivAt_const (natCast 72) c) (hD_y2 c)
  have hc0 := HasDerivAt_const (natCast 9) c
  have hadd1 := HasDerivAt_add (fun y => natCast 24 * (y * y * y * y)) (fun y => natCast 72 * (y * y))
    _ _ c h4 h2
  have hN5 := HasDerivAt_add _ (fun _ => natCast 9) _ _ c hadd1 hc0
  have hMain := HasDerivAt_mul
    (fun y => natCast 24 * (y * y * y * y) + natCast 72 * (y * y) + natCast 9)
    (fun y => hAsinPow 9 y) _ _ c hN5 (hD_hAsinPow 9 c hx)
  have hy2 := HasDerivAt_mul (fun _ => natCast 225 * (1 / (1 + 1))) (fun y => y * y) 0 (c + c) c
    (HasDerivAt_const (natCast 225 * (1 / (1 + 1))) c) (hD_y2 c)
  have hy2' : HasDerivAt (fun y => natCast 225 * (1 / (1 + 1)) * (y * y)) (natCast 225 * c) c :=
    hasDerivAt_congr_val hy2 (by
      have hfrac : (1 + 1 : Real) * (1 / (1 + 1)) = 1 := mul_inv (1 + 1) (ne_of_gt my_two_pos)
      rw [show (0 : Real) * (c * c) + natCast 225 * (1 / (1 + 1)) * (c + c)
          = natCast 225 * ((1 + 1) * (1 / (1 + 1))) * c from by mach_ring, hfrac]
      mach_ring)
  have hfull0 := HasDerivAt_sub _ (fun y => natCast 225 * (1 / (1 + 1)) * (y * y)) _ _ c hMain hy2'
  have hfull := HasDerivAt_sub _ (fun _ => natCast 9) _ _ c hfull0 (HasDerivAt_const (natCast 9) c)
  refine hasDerivAt_congr_val hfull ?_
  simp only []
  unfold Rasin6
  rw [← hAsinPow_shift2 9 hx]
  have e4 : natCast 96 = (1 + 1 + 1 + 1) * natCast 24 := (four_mul_natCast 24).symm
  have e2 : natCast 144 = (1 + 1) * natCast 72 := (two_mul_natCast 72).symm
  have eB5 : natCast 216 = natCast 9 * natCast 24 := by rw [← natCast_mul]
  have eB3 : natCast 648 = natCast 9 * natCast 72 := by rw [← natCast_mul]
  have eB1 : natCast 81 = natCast 9 * natCast 9 := by rw [← natCast_mul]
  have hsum5 : natCast 120 + natCast 96 = natCast 216 := by rw [← natCast_add]
  have hsum3 : natCast 96 + natCast 648 = natCast 600 + natCast 144 := by
    rw [← natCast_add, ← natCast_add]
  have hsum1 : natCast 225 = natCast 144 + natCast 81 := by rw [← natCast_add]
  rw [show natCast 120 = natCast 216 - natCast 96 from by rw [← hsum5]; mach_ring,
    show natCast 600 = natCast 96 + natCast 648 - natCast 144 from by rw [hsum3]; mach_ring,
    hsum1, eB5, eB3, eB1, e4, e2]
  mach_mpoly [c, hAsinPow 11 c, natCast 24, natCast 72, natCast 9]

theorem Rasin5_zero : Rasin5 0 = 0 := by
  unfold Rasin5
  rw [hAsinPow_zero_pt]
  mach_ring

theorem Rasin5_bound (x : Real) (hx0 : 0 ≤ x) (hxR : x ≤ asinR) :
    abs (Rasin5 x) ≤ NTop * hAsinPow 15 asinR * x * x * x := by
  have hxR1 : x < 1 := lt_of_le_of_lt hxR asinR_lt_one
  apply abs_mvt_step_bounded Rasin5 Rasin6 x (NTop * hAsinPow 15 asinR * x * x) 1 hx0 hxR1
    (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) hx0) hx0)
    (fun c hc0 hcR => Rasin5_deriv c (by rw [abs_of_nonneg hc0]; exact hcR))
    Rasin5_zero
    (fun t ht0 htx => le_trans (Rasin6_bound t ht0 (le_trans htx hxR))
      (mul_le_mul' (mul_nonneg (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) ht0)
        (mul_le_mul_of_nonneg_left htx (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg))
        ht0 htx))

/-! ## `Rasin4` (`Rasin3' = Rasin4`, `Rasin4' = Rasin5`). -/

noncomputable def Rasin4 (y : Real) : Real :=
  (natCast 6 * (y * y * y) + natCast 9 * y) * hAsinPow 7 y
    - natCast 75 * (1 / (1 + 1)) * (y * y * y) - natCast 9 * y

set_option maxHeartbeats 1000000 in
theorem Rasin4_deriv (c : Real) (hx : abs c < 1) : HasDerivAt Rasin4 (Rasin5 c) c := by
  have h3 := HasDerivAt_mul (fun _ => natCast 6) (fun y => y * y * y) 0 _ c
    (HasDerivAt_const (natCast 6) c) (hD_y3 c)
  have h1 := HasDerivAt_mul (fun _ => natCast 9) (fun y => y) 0 1 c
    (HasDerivAt_const (natCast 9) c) (HasDerivAt_id c)
  have hN4 := HasDerivAt_add (fun y => natCast 6 * (y * y * y)) (fun y => natCast 9 * y) _ _ c h3 h1
  have hMain := HasDerivAt_mul (fun y => natCast 6 * (y * y * y) + natCast 9 * y)
    (fun y => hAsinPow 7 y) _ _ c hN4 (hD_hAsinPow 7 c hx)
  have hy3 := HasDerivAt_mul (fun _ => natCast 75 * (1 / (1 + 1))) (fun y => y * y * y)
    0 (c * c + c * c + c * c) c (HasDerivAt_const (natCast 75 * (1 / (1 + 1))) c) (hD_y3 c)
  have hy3' : HasDerivAt (fun y => natCast 75 * (1 / (1 + 1)) * (y * y * y))
      (natCast 225 * (1 / (1 + 1)) * (c * c)) c :=
    hasDerivAt_congr_val hy3 (by
      rw [show (0 : Real) * (c * c * c) + natCast 75 * (1 / (1 + 1)) * (c * c + c * c + c * c)
          = ((1 + 1 + 1) * natCast 75) * ((1 / (1 + 1)) * (c * c)) from by mach_ring,
        three_mul_natCast]
      mach_ring)
  have hy1 := HasDerivAt_mul (fun _ => natCast 9) (fun y => y) 0 1 c
    (HasDerivAt_const (natCast 9) c) (HasDerivAt_id c)
  have hfull0 := HasDerivAt_sub _ (fun y => natCast 75 * (1 / (1 + 1)) * (y * y * y)) _ _ c hMain hy3'
  have hfull := HasDerivAt_sub _ (fun y => natCast 9 * y) _ _ c hfull0 hy1
  refine hasDerivAt_congr_val hfull ?_
  simp only []
  unfold Rasin5
  rw [← hAsinPow_shift2 7 hx]
  have e3 : natCast 18 = (1 + 1 + 1) * natCast 6 := (three_mul_natCast 6).symm
  have eB4 : natCast 42 = natCast 7 * natCast 6 := by rw [← natCast_mul]
  have eB2 : natCast 63 = natCast 7 * natCast 9 := by rw [← natCast_mul]
  have hsum4 : natCast 24 + natCast 18 = natCast 42 := by rw [← natCast_add]
  have hsum2 : natCast 18 + natCast 63 = natCast 72 + natCast 9 := by
    rw [← natCast_add, ← natCast_add]
  rw [show natCast 24 = natCast 42 - natCast 18 from by rw [← hsum4]; mach_ring,
    show natCast 72 = natCast 18 + natCast 63 - natCast 9 from by rw [hsum2]; mach_ring,
    eB4, eB2, e3]
  mach_mpoly [c, hAsinPow 9 c, natCast 6, natCast 9, natCast 7]

theorem Rasin4_zero : Rasin4 0 = 0 := by
  unfold Rasin4
  rw [hAsinPow_zero_pt]
  mach_ring

theorem Rasin4_bound (x : Real) (hx0 : 0 ≤ x) (hxR : x ≤ asinR) :
    abs (Rasin4 x) ≤ NTop * hAsinPow 15 asinR * x * x * x * x := by
  have hxR1 : x < 1 := lt_of_le_of_lt hxR asinR_lt_one
  apply abs_mvt_step_bounded Rasin4 Rasin5 x (NTop * hAsinPow 15 asinR * x * x * x) 1 hx0 hxR1
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) hx0) hx0) hx0)
    (fun c hc0 hcR => Rasin4_deriv c (by rw [abs_of_nonneg hc0]; exact hcR))
    Rasin4_zero
    (fun t ht0 htx => le_trans (Rasin5_bound t ht0 (le_trans htx hxR))
      (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) ht0) ht0)
        (mul_le_mul' (mul_nonneg (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) ht0)
          (mul_le_mul_of_nonneg_left htx (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg))
          ht0 htx)
        ht0 htx))

/-! ## `Rasin3` (`Rasin2' = Rasin3`, `Rasin3' = Rasin4`). -/

noncomputable def Rasin3 (y : Real) : Real :=
  (natCast 2 * (y * y) + 1) * hAsinPow 5 y
    - 1 - natCast 9 * (1 / (1 + 1)) * (y * y) - natCast 75 * (1 / natCast 8) * (y * y * y * y)

set_option maxHeartbeats 1000000 in
theorem Rasin3_deriv (c : Real) (hx : abs c < 1) : HasDerivAt Rasin3 (Rasin4 c) c := by
  have h2 := HasDerivAt_mul (fun _ => natCast 2) (fun y => y * y) 0 _ c
    (HasDerivAt_const (natCast 2) c) (hD_y2 c)
  have hc1 := HasDerivAt_const (1 : Real) c
  have hN3 := HasDerivAt_add (fun y => natCast 2 * (y * y)) (fun _ => (1 : Real)) _ _ c h2 hc1
  have hMain := HasDerivAt_mul (fun y => natCast 2 * (y * y) + 1) (fun y => hAsinPow 5 y) _ _ c
    hN3 (hD_hAsinPow 5 c hx)
  have hc1' := HasDerivAt_const (1 : Real) c
  have hy2 := HasDerivAt_mul (fun _ => natCast 9 * (1 / (1 + 1))) (fun y => y * y) 0 (c + c) c
    (HasDerivAt_const (natCast 9 * (1 / (1 + 1))) c) (hD_y2 c)
  have hy2' : HasDerivAt (fun y => natCast 9 * (1 / (1 + 1)) * (y * y)) (natCast 9 * c) c :=
    hasDerivAt_congr_val hy2 (by
      rw [show (0 : Real) * (c * c) + natCast 9 * (1 / (1 + 1)) * (c + c)
          = natCast 9 * ((1 + 1) * (1 / (1 + 1))) * c from by mach_ring,
        mul_inv (1 + 1) (ne_of_gt my_two_pos)]
      mach_ring)
  have hfrac48 : (1 + 1 + 1 + 1 : Real) * (1 / natCast 8) = 1 / (1 + 1) := by
    have hnd : (1 + 1 + 1 + 1 : Real) * (1 + 1) = natCast 8 := by
      rw [← natCast_four, ← natCast_two, ← natCast_mul]
    exact frac_reduce (1 + 1 + 1 + 1) (1 + 1) (natCast 8) (ne_of_gt my_two_pos)
      (natCast_ne_zero (by decide)) hnd
  have hy4 := HasDerivAt_mul (fun _ => natCast 75 * (1 / natCast 8)) (fun y => y * y * y * y)
    0 ((c + c) * (c * c) + c * c * (c + c)) c (HasDerivAt_const (natCast 75 * (1 / natCast 8)) c)
    (hD_y4 c)
  have hy4' : HasDerivAt (fun y => natCast 75 * (1 / natCast 8) * (y * y * y * y))
      (natCast 75 * (1 / (1 + 1)) * (c * c * c)) c :=
    hasDerivAt_congr_val hy4 (by
      rw [show (0 : Real) * (c * c * c * c) + natCast 75 * (1 / natCast 8)
            * ((c + c) * (c * c) + c * c * (c + c))
          = natCast 75 * ((1 + 1 + 1 + 1) * (1 / natCast 8)) * (c * c * c) from by mach_ring,
        hfrac48]
      mach_ring)
  have hfull0 := HasDerivAt_sub _ (fun _ => (1 : Real)) _ _ c hMain hc1'
  have hfull1 := HasDerivAt_sub _ (fun y => natCast 9 * (1 / (1 + 1)) * (y * y)) _ _ c hfull0 hy2'
  have hfull := HasDerivAt_sub _ (fun y => natCast 75 * (1 / natCast 8) * (y * y * y * y)) _ _ c
    hfull1 hy4'
  refine hasDerivAt_congr_val hfull ?_
  simp only []
  unfold Rasin4
  rw [← hAsinPow_shift2 5 hx]
  have e2 : natCast 4 = (1 + 1) * natCast 2 := (two_mul_natCast 2).symm
  have eB3 : natCast 10 = natCast 5 * natCast 2 := by rw [← natCast_mul]
  have hsum3 : natCast 6 + natCast 4 = natCast 10 := by rw [← natCast_add]
  have hsum1 : natCast 9 = natCast 4 + natCast 5 := by rw [← natCast_add]
  rw [show natCast 6 = natCast 10 - natCast 4 from by rw [← hsum3]; mach_ring,
    hsum1, eB3, e2]
  mach_mpoly [c, hAsinPow 7 c, natCast 2, natCast 5]

theorem Rasin3_zero : Rasin3 0 = 0 := by
  unfold Rasin3
  rw [hAsinPow_zero_pt]
  mach_ring

theorem Rasin3_bound (x : Real) (hx0 : 0 ≤ x) (hxR : x ≤ asinR) :
    abs (Rasin3 x) ≤ NTop * hAsinPow 15 asinR * x * x * x * x * x := by
  have hxR1 : x < 1 := lt_of_le_of_lt hxR asinR_lt_one
  apply abs_mvt_step_bounded Rasin3 Rasin4 x (NTop * hAsinPow 15 asinR * x * x * x * x) 1 hx0 hxR1
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg
      hAsinPow15_asinR_nonneg) hx0) hx0) hx0) hx0)
    (fun c hc0 hcR => Rasin3_deriv c (by rw [abs_of_nonneg hc0]; exact hcR))
    Rasin3_zero
    (fun t ht0 htx => le_trans (Rasin4_bound t ht0 (le_trans htx hxR))
      (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg
          hAsinPow15_asinR_nonneg) ht0) ht0) ht0)
        (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) ht0) ht0)
          (mul_le_mul' (mul_nonneg (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) ht0)
            (mul_le_mul_of_nonneg_left htx (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg))
            ht0 htx)
          ht0 htx)
        ht0 htx))

/-! ## `Rasin2` (`Rasin1' = Rasin2`, `Rasin2' = Rasin3`). -/

noncomputable def Rasin2 (y : Real) : Real :=
  y * hAsinPow 3 y - y - natCast 3 * (1 / (1 + 1)) * (y * y * y)
    - natCast 15 * (1 / natCast 8) * (y * y * y * y * y)

set_option maxHeartbeats 1000000 in
theorem Rasin2_deriv (c : Real) (hx : abs c < 1) : HasDerivAt Rasin2 (Rasin3 c) c := by
  have hMain := HasDerivAt_mul (fun y => y) (fun y => hAsinPow 3 y) 1 _ c
    (HasDerivAt_id c) (hD_hAsinPow 3 c hx)
  have hy1 := HasDerivAt_id c
  have hy3 := HasDerivAt_mul (fun _ => natCast 3 * (1 / (1 + 1))) (fun y => y * y * y)
    0 (c * c + c * c + c * c) c (HasDerivAt_const (natCast 3 * (1 / (1 + 1))) c) (hD_y3 c)
  have hy3' : HasDerivAt (fun y => natCast 3 * (1 / (1 + 1)) * (y * y * y))
      (natCast 9 * (1 / (1 + 1)) * (c * c)) c :=
    hasDerivAt_congr_val hy3 (by
      rw [show (0 : Real) * (c * c * c) + natCast 3 * (1 / (1 + 1)) * (c * c + c * c + c * c)
          = ((1 + 1 + 1) * natCast 3) * ((1 / (1 + 1)) * (c * c)) from by mach_ring,
        three_mul_natCast]
      mach_ring)
  have hy5 := HasDerivAt_mul (fun _ => natCast 15 * (1 / natCast 8)) (fun y => y * y * y * y * y)
    0 ((c + c) * (c * c * c) + c * c * (c * c + c * c + c * c)) c
    (HasDerivAt_const (natCast 15 * (1 / natCast 8)) c) (hD_y5 c)
  have hy5' : HasDerivAt (fun y => natCast 15 * (1 / natCast 8) * (y * y * y * y * y))
      (natCast 75 * (1 / natCast 8) * (c * c * c * c)) c :=
    hasDerivAt_congr_val hy5 (by
      rw [show (0 : Real) * (c * c * c * c * c) + natCast 15 * (1 / natCast 8)
            * ((c + c) * (c * c * c) + c * c * (c * c + c * c + c * c))
          = ((1 + 1 + 1 + 1 + 1) * natCast 15) * ((1 / natCast 8) * (c * c * c * c))
          from by mach_ring,
        five_mul_natCast]
      mach_ring)
  have hfull0 := HasDerivAt_sub _ (fun y => y) _ _ c hMain hy1
  have hfull1 := HasDerivAt_sub _ (fun y => natCast 3 * (1 / (1 + 1)) * (y * y * y)) _ _ c
    hfull0 hy3'
  have hfull := HasDerivAt_sub _ (fun y => natCast 15 * (1 / natCast 8) * (y * y * y * y * y)) _ _ c
    hfull1 hy5'
  refine hasDerivAt_congr_val hfull ?_
  simp only []
  unfold Rasin3
  rw [← hAsinPow_shift2 3 hx]
  have hsum2 : natCast 2 + 1 = natCast 3 := by
    rw [show natCast 3 = natCast 2 + natCast 1 from by rw [← natCast_add], natCast_one]
  rw [show natCast 2 = natCast 3 - 1 from by rw [← hsum2]; mach_ring]
  mach_mpoly [c, hAsinPow 5 c]

theorem Rasin2_zero : Rasin2 0 = 0 := by
  unfold Rasin2
  rw [hAsinPow_zero_pt]
  mach_ring

theorem Rasin2_bound (x : Real) (hx0 : 0 ≤ x) (hxR : x ≤ asinR) :
    abs (Rasin2 x) ≤ NTop * hAsinPow 15 asinR * x * x * x * x * x * x := by
  have hxR1 : x < 1 := lt_of_le_of_lt hxR asinR_lt_one
  apply abs_mvt_step_bounded Rasin2 Rasin3 x
    (NTop * hAsinPow 15 asinR * x * x * x * x * x) 1 hx0 hxR1
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg
      hAsinPow15_asinR_nonneg) hx0) hx0) hx0) hx0) hx0)
    (fun c hc0 hcR => Rasin2_deriv c (by rw [abs_of_nonneg hc0]; exact hcR))
    Rasin2_zero
    (fun t ht0 htx => le_trans (Rasin3_bound t ht0 (le_trans htx hxR))
      (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg
          hAsinPow15_asinR_nonneg) ht0) ht0) ht0) ht0)
        (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg
            hAsinPow15_asinR_nonneg) ht0) ht0) ht0)
          (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) ht0) ht0)
            (mul_le_mul' (mul_nonneg (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) ht0)
              (mul_le_mul_of_nonneg_left htx (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg))
              ht0 htx)
            ht0 htx)
          ht0 htx)
        ht0 htx))

/-! ## `Rasin1` (`Rasin0' = Rasin1`, `Rasin1' = Rasin2`). `N_1 = 1` is constant (`N_1' = 0`), so this
level's "main" term is literally `h` itself — `hD_hAsin` already gives exactly the right shape, no
`hAsinPow_shift2` step needed (the induction bottoms out here). -/

noncomputable def Rasin1 (y : Real) : Real :=
  hAsin y - 1 - (1 / (1 + 1)) * (y * y) - natCast 3 * (1 / natCast 8) * (y * y * y * y)
    - natCast 5 * (1 / natCast 16) * (y * y * y * y * y * y)

set_option maxHeartbeats 1000000 in
theorem Rasin1_deriv (c : Real) (hx : abs c < 1) : HasDerivAt Rasin1 (Rasin2 c) c := by
  have hMain := hD_hAsin c hx
  have hc1 := HasDerivAt_const (1 : Real) c
  have hy2 := HasDerivAt_mul (fun _ => (1 : Real) / (1 + 1)) (fun y => y * y) 0 (c + c) c
    (HasDerivAt_const ((1 : Real) / (1 + 1)) c) (hD_y2 c)
  have hy2' : HasDerivAt (fun y => (1 / (1 + 1)) * (y * y)) c c :=
    hasDerivAt_congr_val hy2 (by
      rw [show (0 : Real) * (c * c) + 1 / (1 + 1) * (c + c) = (1 + 1) * (1 / (1 + 1)) * c
          from by mach_ring, mul_inv (1 + 1) (ne_of_gt my_two_pos)]
      mach_ring)
  have hfrac48 : (1 + 1 + 1 + 1 : Real) * (1 / natCast 8) = 1 / (1 + 1) := by
    have hnd : (1 + 1 + 1 + 1 : Real) * (1 + 1) = natCast 8 := by
      rw [← natCast_four, ← natCast_two, ← natCast_mul]
    exact frac_reduce (1 + 1 + 1 + 1) (1 + 1) (natCast 8) (ne_of_gt my_two_pos)
      (natCast_ne_zero (by decide)) hnd
  have hy4 := HasDerivAt_mul (fun _ => natCast 3 * (1 / natCast 8)) (fun y => y * y * y * y)
    0 ((c + c) * (c * c) + c * c * (c + c)) c (HasDerivAt_const (natCast 3 * (1 / natCast 8)) c)
    (hD_y4 c)
  have hy4' : HasDerivAt (fun y => natCast 3 * (1 / natCast 8) * (y * y * y * y))
      (natCast 3 * (1 / (1 + 1)) * (c * c * c)) c :=
    hasDerivAt_congr_val hy4 (by
      rw [show (0 : Real) * (c * c * c * c) + natCast 3 * (1 / natCast 8)
            * ((c + c) * (c * c) + c * c * (c + c))
          = natCast 3 * ((1 + 1 + 1 + 1) * (1 / natCast 8)) * (c * c * c) from by mach_ring,
        hfrac48]
      mach_ring)
  have hfrac2_16 : natCast 2 * (1 / natCast 16) = 1 / natCast 8 :=
    frac_reduce (natCast 2) (natCast 8) (natCast 16) (natCast_ne_zero (by decide))
      (natCast_ne_zero (by decide)) (by rw [← natCast_mul])
  have hy6 := HasDerivAt_mul (fun _ => natCast 5 * (1 / natCast 16))
    (fun y => y * y * y * y * y * y) 0
    ((c * c + c * c + c * c) * (c * c * c) + c * c * c * (c * c + c * c + c * c)) c
    (HasDerivAt_const (natCast 5 * (1 / natCast 16)) c) (hD_y6 c)
  have hy6' : HasDerivAt (fun y => natCast 5 * (1 / natCast 16) * (y * y * y * y * y * y))
      (natCast 15 * (1 / natCast 8) * (c * c * c * c * c)) c := by
    refine hasDerivAt_congr_val hy6 ?_
    have hstep1 : natCast 2 * natCast 15 = (1 + 1 + 1 + 1 + 1 + 1) * natCast 5 := by
      rw [six_mul_natCast, ← natCast_mul]
    have hstep2 : (natCast 2 * natCast 15) * (1 / natCast 16) = natCast 15 * (1 / natCast 8) := by
      rw [show natCast 2 * natCast 15 * (1 / natCast 16)
          = natCast 15 * (natCast 2 * (1 / natCast 16)) from by mach_ring, hfrac2_16]
    rw [show (0 : Real) * (c * c * c * c * c * c) + natCast 5 * (1 / natCast 16)
          * ((c * c + c * c + c * c) * (c * c * c) + c * c * c * (c * c + c * c + c * c))
        = (natCast 2 * natCast 15) * ((1 / natCast 16) * (c * c * c * c * c)) from by
      rw [hstep1]; mach_ring]
    rw [show (natCast 2 * natCast 15) * ((1 / natCast 16) * (c * c * c * c * c))
        = ((natCast 2 * natCast 15) * (1 / natCast 16)) * (c * c * c * c * c) from by mach_ring,
      hstep2]
    mach_ring
  have hfull0 := HasDerivAt_sub hAsin (fun _ => (1 : Real)) _ _ c hMain hc1
  have hfull1 := HasDerivAt_sub _ (fun y => (1 / (1 + 1)) * (y * y)) _ _ c hfull0 hy2'
  have hfull2 := HasDerivAt_sub _ (fun y => natCast 3 * (1 / natCast 8) * (y * y * y * y)) _ _ c
    hfull1 hy4'
  have hfull := HasDerivAt_sub _ (fun y => natCast 5 * (1 / natCast 16) * (y * y * y * y * y * y))
    _ _ c hfull2 hy6'
  refine hasDerivAt_congr_val hfull ?_
  unfold Rasin2
  mach_mpoly [c, hAsinPow 3 c]

theorem Rasin1_zero : Rasin1 0 = 0 := by
  unfold Rasin1
  rw [hAsin_zero]
  mach_ring

theorem Rasin1_bound (x : Real) (hx0 : 0 ≤ x) (hxR : x ≤ asinR) :
    abs (Rasin1 x) ≤ NTop * hAsinPow 15 asinR * x * x * x * x * x * x * x := by
  have hxR1 : x < 1 := lt_of_le_of_lt hxR asinR_lt_one
  apply abs_mvt_step_bounded Rasin1 Rasin2 x
    (NTop * hAsinPow 15 asinR * x * x * x * x * x * x) 1 hx0 hxR1
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg
      hAsinPow15_asinR_nonneg) hx0) hx0) hx0) hx0) hx0) hx0)
    (fun c hc0 hcR => Rasin1_deriv c (by rw [abs_of_nonneg hc0]; exact hcR))
    Rasin1_zero
    (fun t ht0 htx => le_trans (Rasin2_bound t ht0 (le_trans htx hxR))
      (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg
          hAsinPow15_asinR_nonneg) ht0) ht0) ht0) ht0) ht0)
        (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg
            hAsinPow15_asinR_nonneg) ht0) ht0) ht0) ht0)
          (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg
              hAsinPow15_asinR_nonneg) ht0) ht0) ht0)
            (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg
                hAsinPow15_asinR_nonneg) ht0) ht0)
              (mul_le_mul' (mul_nonneg (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) ht0)
                (mul_le_mul_of_nonneg_left htx (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg))
                ht0 htx)
              ht0 htx)
            ht0 htx)
          ht0 htx)
        ht0 htx))

/-! ## `Rasin0` — THE TARGET. `Rasin0(y) = arcsin(y) − (y + y³/6 + 3y⁵/40 + 15y⁷/336)`, exactly
`eml_asin.v`'s claimed 4-term Maclaurin truncation, subtracted from the true `arcsin`. -/

noncomputable def Rasin0 (y : Real) : Real :=
  arcsin y - y - y * y * y * (1 / natCast 6)
    - natCast 3 * (1 / natCast 40) * (y * y * y * y * y)
    - natCast 15 * (1 / natCast 336) * (y * y * y * y * y * y * y)

set_option maxHeartbeats 1000000 in
theorem Rasin0_deriv (c : Real) (hx : abs c < 1) : HasDerivAt Rasin0 (Rasin1 c) c := by
  have hMain := HasDerivAt_arcsin c hx
  have hy1 := HasDerivAt_id c
  have hy3 := HasDerivAt_mul (fun y => y * y * y) (fun _ => (1 : Real) / natCast 6)
    (c * c + c * c + c * c) 0 c (hD_y3 c) (HasDerivAt_const ((1 : Real) / natCast 6) c)
  have hfrac3_6 : (1 + 1 + 1 : Real) * (1 / natCast 6) = 1 / (1 + 1) := by
    have hnd : (1 + 1 + 1 : Real) * (1 + 1) = natCast 6 := by
      rw [show (1 + 1 + 1 : Real) * (1 + 1) = 1 + 1 + 1 + 1 + 1 + 1 from by mach_ring,
        ← natCast_six]
    exact frac_reduce (1 + 1 + 1) (1 + 1) (natCast 6) (ne_of_gt my_two_pos)
      (natCast_ne_zero (by decide)) hnd
  have hy3' : HasDerivAt (fun y => y * y * y * (1 / natCast 6)) ((1 / (1 + 1)) * (c * c)) c :=
    hasDerivAt_congr_val hy3 (by
      rw [show (c * c + c * c + c * c) * (1 / natCast 6) + (c * c * c) * 0
          = ((1 + 1 + 1) * (1 / natCast 6)) * (c * c) from by mach_ring, hfrac3_6])
  have hy5 := HasDerivAt_mul (fun _ => natCast 3 * (1 / natCast 40)) (fun y => y * y * y * y * y)
    0 ((c + c) * (c * c * c) + c * c * (c * c + c * c + c * c)) c
    (HasDerivAt_const (natCast 3 * (1 / natCast 40)) c) (hD_y5 c)
  have hfrac5_40 : natCast 5 * (1 / natCast 40) = 1 / natCast 8 :=
    frac_reduce (natCast 5) (natCast 8) (natCast 40) (natCast_ne_zero (by decide))
      (natCast_ne_zero (by decide)) (by rw [← natCast_mul])
  have hy5' : HasDerivAt (fun y => natCast 3 * (1 / natCast 40) * (y * y * y * y * y))
      (natCast 3 * (1 / natCast 8) * (c * c * c * c)) c :=
    hasDerivAt_congr_val hy5 (by
      rw [show (0 : Real) * (c * c * c * c * c) + natCast 3 * (1 / natCast 40)
            * ((c + c) * (c * c * c) + c * c * (c * c + c * c + c * c))
          = natCast 3 * ((1 + 1 + 1 + 1 + 1) * (1 / natCast 40)) * (c * c * c * c) from by mach_ring,
        ← natCast_five, hfrac5_40]
      mach_ring)
  have hy7 := HasDerivAt_mul (fun _ => natCast 15 * (1 / natCast 336))
    (fun y => y * y * y * y * y * y * y) 0
    ((c * c + c * c + c * c) * (c * c * c * c) + c * c * c * ((c + c) * (c * c) + c * c * (c + c))) c
    (HasDerivAt_const (natCast 15 * (1 / natCast 336)) c) (hD_y7 c)
  have hfrac21_336 : natCast 21 * (1 / natCast 336) = 1 / natCast 16 :=
    frac_reduce (natCast 21) (natCast 16) (natCast 336) (natCast_ne_zero (by decide))
      (natCast_ne_zero (by decide)) (by rw [← natCast_mul])
  have hcombine15_7 : natCast 15 * (natCast 7 * (1 / natCast 336)) = natCast 5 * (1 / natCast 16) := by
    rw [show natCast 15 * (natCast 7 * (1 / natCast 336)) = (natCast 15 * natCast 7) * (1 / natCast 336)
        from by mach_ring,
      show natCast 15 * natCast 7 = natCast 5 * natCast 21 from by rw [← natCast_mul, ← natCast_mul],
      show natCast 5 * natCast 21 * (1 / natCast 336) = natCast 5 * (natCast 21 * (1 / natCast 336))
        from by mach_ring,
      hfrac21_336]
  have hy7' : HasDerivAt (fun y => natCast 15 * (1 / natCast 336) * (y * y * y * y * y * y * y))
      (natCast 5 * (1 / natCast 16) * (c * c * c * c * c * c)) c :=
    hasDerivAt_congr_val hy7 (by
      rw [show (0 : Real) * (c * c * c * c * c * c * c) + natCast 15 * (1 / natCast 336)
            * ((c * c + c * c + c * c) * (c * c * c * c)
              + c * c * c * ((c + c) * (c * c) + c * c * (c + c)))
          = natCast 15 * ((1 + 1 + 1 + 1 + 1 + 1 + 1) * (1 / natCast 336))
            * (c * c * c * c * c * c) from by mach_ring,
        ← natCast_seven, hcombine15_7]
      mach_ring)
  have hfull0 := HasDerivAt_sub arcsin (fun y => y) _ _ c hMain hy1
  have hfull1 := HasDerivAt_sub _ (fun y => y * y * y * (1 / natCast 6)) _ _ c hfull0 hy3'
  have hfull2 := HasDerivAt_sub _ (fun y => natCast 3 * (1 / natCast 40) * (y * y * y * y * y)) _ _ c
    hfull1 hy5'
  have hfull := HasDerivAt_sub _
    (fun y => natCast 15 * (1 / natCast 336) * (y * y * y * y * y * y * y)) _ _ c hfull2 hy7'
  refine hasDerivAt_congr_val hfull ?_
  unfold Rasin1
  mach_mpoly [c, hAsin c]

theorem Rasin0_zero : Rasin0 0 = 0 := by
  unfold Rasin0
  rw [arcsin_zero]
  mach_ring

/-- **THE MAIN RESULT**: `|arcsin(x) − (x + x³/6 + 3x⁵/40 + 15x⁷/336)| ≤ NTop·h(R)^15·x^8` for
`x ∈ [0, R]`, `R = 1/2` — matching `eml_asin.v`'s own documented valid range exactly. Unlike
`tanh`'s flat bound, the constant here (`NTop * hAsinPow 15 asinR`) is irrational (involves
`√3`), reflecting `arcsin`'s derivative genuinely blowing up as `y → ±1` — but since the domain is
fixed and bounded away from that singularity, the bound is still flat in `x` up to the final
`x^8` factor, exactly like `tanh`'s. -/
theorem Rasin0_bound (x : Real) (hx0 : 0 ≤ x) (hxR : x ≤ asinR) :
    abs (Rasin0 x) ≤ NTop * hAsinPow 15 asinR * x * x * x * x * x * x * x * x := by
  have hxR1 : x < 1 := lt_of_le_of_lt hxR asinR_lt_one
  apply abs_mvt_step_bounded Rasin0 Rasin1 x
    (NTop * hAsinPow 15 asinR * x * x * x * x * x * x * x) 1 hx0 hxR1
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) hx0) hx0) hx0) hx0) hx0) hx0) hx0)
    (fun c hc0 hcR => Rasin0_deriv c (by rw [abs_of_nonneg hc0]; exact hcR))
    Rasin0_zero
    (fun t ht0 htx => le_trans (Rasin1_bound t ht0 (le_trans htx hxR))
      (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
          (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) ht0) ht0) ht0) ht0) ht0) ht0)
        (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
            (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) ht0) ht0) ht0) ht0) ht0)
          (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
              (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) ht0) ht0) ht0) ht0)
            (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg
                (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) ht0) ht0) ht0)
              (mul_le_mul' (mul_nonneg (mul_nonneg (mul_nonneg NTop_nonneg
                  hAsinPow15_asinR_nonneg) ht0) ht0)
                (mul_le_mul' (mul_nonneg (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg) ht0)
                  (mul_le_mul_of_nonneg_left htx (mul_nonneg NTop_nonneg hAsinPow15_asinR_nonneg))
                  ht0 htx)
                ht0 htx)
              ht0 htx)
            ht0 htx)
          ht0 htx)
        ht0 htx))

end MachLib.Real
