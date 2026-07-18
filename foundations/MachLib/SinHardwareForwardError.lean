import MachLib.Forge
import MachLib.Ring
import MachLib.FixedPoint
import MachLib.SinTaylorRemainder

/-!
# `eml_sin.v` hardware forward-error certificate — the fixed-point ↔ real leg

The composed answer to "does the Arty A7 bitstream actually compute `sin`, and how far off can
it be": combines `FixedPoint`'s `qmul_err_loose` (fixed-point truncation, derived from `floor`,
not assumed) with `SinTaylorRemainder.R0_bound` (the real-valued Taylor-remainder bound) into one
certificate against the exact hardware pipeline read off `hardware/modules/transcendental/eml_sin.v`.

## What `eml_sin.v` actually computes (ground truth, read off the RTL)

Q<WIDTH-FRAC>.<FRAC> fixed-point (`WIDTH=32`, `FRAC=16`), `qmul a b := (a*b) >>> FRAC` (arithmetic
right shift = floor division on the scaled product). A 4-stage pipeline evaluates
`x − x³/6 + x⁵/120` via **six** `qmul`s: `x2=qmul(x1,x1)`, `x3=qmul(x2,x1)`,
`x4=qmul(x2,x2)`, `x5=qmul(x4,x1)`, `t3=qmul(x3,ONE_SIXTH)`, `t5=qmul(x5,ONE_120TH)`, then
`acc = x1 − t3 + t5` (add/sub are exact integer ops, no further rounding). `ONE_SIXTH`/`ONE_120TH`
are themselves `⌊ONE/6⌋`/`⌊ONE/120⌋` computed at elaboration time — i.e. exactly
`quantize (1/6) D` / `quantize (1/120) D`, so they carry the *same* `1/D` grid error as a runtime
`qmul`, not a separate constant.

## Method

Each `qmul` stage is bounded via `qmul_err_loose`, which needs the *exact* operand magnitudes
bounded by `1` — hence the `x ∈ [0,1]` restriction (the physically meaningful range-reduced-input
regime; a kernel calling this would range-reduce its argument first). Composing all six stages
by hand (rather than via a generic "propagate through a DAG" combinator, which MachLib does not
yet have) gives clean integer coefficients in units of `1/D`:

| stage | operation         | error (× `1/D`) |
|-------|-------------------|------------------|
| `x2`  | `qmul(x,x)`       | 1                |
| `x3`  | `qmul(x2,x)`      | 2                |
| `x4`  | `qmul(x2,x2)`     | 4                |
| `x5`  | `qmul(x4,x)`      | 5                |
| `t3`  | `qmul(x3,1/6)`    | 6                |
| `t5`  | `qmul(x5,1/120)`  | 12               |

giving a fixed-point-only error of `18/D` against the exact `x − x³/6 + x⁵/120`, combined via the
triangle inequality with `R0_bound`'s `x⁶` Taylor-truncation term for the full certificate.

## A `mach_ring`/`mach_mpoly` gotcha hit while building this

Blind `mach_ring` calls on identities mentioning `1/onetwenty` (where `onetwenty` is itself a
`noncomputable def := five*twentyfour`) hit deterministic timeouts (200000 heartbeats) —
apparently from `mach_ring`'s normalizer trying to unfold `onetwenty`'s internal product structure
while simultaneously normalizing the surrounding polynomial, echoing the earlier
"`mach_ring` can't handle large flat sums" wall from `SinTaylorRemainder`. Fixed by using
`mach_mpoly` with an **explicit atom list** naming `(1/(1+1+1+1+1+1) : Real)` and
`(1/onetwenty : Real)` directly (so they're treated as opaque leaves, never unfolded) rather than
letting the tactic's default term collection decide.

`sorryAx`-free throughout. Companion: `FixedPoint` (the general `quantize`/`qmul_err_loose`
machinery lives there now), `SinTaylorRemainder` (`R0_bound`).
-/

namespace MachLib.Real

/-! ## Magnitude bounds for `x ∈ [0,1]` — the operand-boundedness `qmul_err_loose` needs -/

theorem mul_le_one {a b : Real} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    a * b ≤ 1 := by
  have h1 : a * b ≤ a * 1 := mul_le_mul_of_nonneg_left hb1 ha0
  rw [mul_one_ax] at h1
  exact le_trans h1 ha1

theorem hxx_nn (x : Real) (hx0 : 0 ≤ x) : 0 ≤ x * x := mul_nonneg hx0 hx0
theorem hxx_le1 (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x * x ≤ 1 :=
  mul_le_one hx0 hx1 hx0 hx1
theorem habsx_le1 (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : abs x ≤ 1 := by
  rw [abs_of_nonneg hx0]; exact hx1
theorem habsxx_le1 (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : abs (x * x) ≤ 1 := by
  rw [abs_of_nonneg (hxx_nn x hx0)]; exact hxx_le1 x hx0 hx1

theorem hx3_nn (x : Real) (hx0 : 0 ≤ x) : 0 ≤ (x * x) * x := mul_nonneg (hxx_nn x hx0) hx0
theorem hx3_le1 (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (x * x) * x ≤ 1 :=
  mul_le_one (hxx_nn x hx0) (hxx_le1 x hx0 hx1) hx0 hx1
theorem habsx3_le1 (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : abs ((x * x) * x) ≤ 1 := by
  rw [abs_of_nonneg (hx3_nn x hx0)]; exact hx3_le1 x hx0 hx1

theorem hx4_nn (x : Real) (hx0 : 0 ≤ x) : 0 ≤ (x * x) * (x * x) :=
  mul_nonneg (hxx_nn x hx0) (hxx_nn x hx0)
theorem hx4_le1 (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (x * x) * (x * x) ≤ 1 :=
  mul_le_one (hxx_nn x hx0) (hxx_le1 x hx0 hx1) (hxx_nn x hx0) (hxx_le1 x hx0 hx1)
theorem habsx4_le1 (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    abs ((x * x) * (x * x)) ≤ 1 := by
  rw [abs_of_nonneg (hx4_nn x hx0)]; exact hx4_le1 x hx0 hx1

theorem hx5_nn (x : Real) (hx0 : 0 ≤ x) : 0 ≤ (x * x) * (x * x) * x :=
  mul_nonneg (hx4_nn x hx0) hx0
theorem hx5_le1 (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (x * x) * (x * x) * x ≤ 1 :=
  mul_le_one (hx4_nn x hx0) (hx4_le1 x hx0 hx1) hx0 hx1
theorem habsx5_le1 (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    abs ((x * x) * (x * x) * x) ≤ 1 := by
  rw [abs_of_nonneg (hx5_nn x hx0)]; exact hx5_le1 x hx0 hx1

theorem nonneg_add_ge_one {a b : Real} (ha1 : 1 ≤ a) (hb0 : 0 ≤ b) : 1 ≤ a + b := by
  have h := add_le_add_both ha1 hb0
  rwa [show (1:Real)+0 = 1 from by mach_ring] at h

theorem one_le_mul {a b : Real} (ha1 : 1 ≤ a) (hb1 : 1 ≤ b) : 1 ≤ a * b := by
  have ha0 : (0:Real) ≤ a := le_trans (le_of_lt zero_lt_one_ax) ha1
  have step1 : (1:Real) * 1 ≤ a * 1 := mul_le_mul_of_nonneg_right ha1 (le_of_lt zero_lt_one_ax)
  have step2 : a * 1 ≤ a * b := mul_le_mul_of_nonneg_left hb1 ha0
  simp only [mul_one_ax] at step1 step2
  exact le_trans step1 step2

theorem two_ge1 : (1 : Real) ≤ 1 + 1 := nonneg_add_ge_one (le_refl 1) (le_of_lt zero_lt_one_ax)
theorem three_ge1 : (1 : Real) ≤ 1 + 1 + 1 := nonneg_add_ge_one two_ge1 (le_of_lt zero_lt_one_ax)
theorem four_ge1 : (1 : Real) ≤ 1 + 1 + 1 + 1 := nonneg_add_ge_one three_ge1 (le_of_lt zero_lt_one_ax)
theorem five_ge1 : (1 : Real) ≤ 1 + 1 + 1 + 1 + 1 :=
  nonneg_add_ge_one four_ge1 (le_of_lt zero_lt_one_ax)
theorem six_ge1 : (1 : Real) ≤ 1 + 1 + 1 + 1 + 1 + 1 :=
  nonneg_add_ge_one five_ge1 (le_of_lt zero_lt_one_ax)

theorem hsixth_le1 : (1 : Real) / (1 + 1 + 1 + 1 + 1 + 1) ≤ 1 :=
  div_le_one_of_le_of_pos my_six_pos six_ge1
theorem hsixth_nn : (0 : Real) ≤ 1 / (1 + 1 + 1 + 1 + 1 + 1) :=
  one_div_nonneg_of_pos my_six_pos
theorem habssixth_le1 : abs ((1 : Real) / (1 + 1 + 1 + 1 + 1 + 1)) ≤ 1 := by
  rw [abs_of_nonneg hsixth_nn]; exact hsixth_le1

theorem honetwenty_pos : (0 : Real) < onetwenty := by
  unfold onetwenty
  exact mul_pos my_five_pos (by unfold twentyfour; exact mul_pos my_four_pos my_six_pos)

theorem htwentyfour_ge1 : (1 : Real) ≤ twentyfour := by
  unfold twentyfour; exact one_le_mul four_ge1 six_ge1

theorem honetwenty_ge1 : (1 : Real) ≤ onetwenty := by
  unfold onetwenty; exact one_le_mul five_ge1 htwentyfour_ge1

theorem h120th_le1 : (1 : Real) / onetwenty ≤ 1 :=
  div_le_one_of_le_of_pos honetwenty_pos honetwenty_ge1
theorem h120th_nn : (0 : Real) ≤ 1 / onetwenty := one_div_nonneg_of_pos honetwenty_pos
theorem habs120th_le1 : abs ((1 : Real) / onetwenty) ≤ 1 := by
  rw [abs_of_nonneg h120th_nn]; exact h120th_le1

/-! ## The `eml_sin.v` pipeline, encoded stage-by-stage -/

noncomputable def x2f (x D : Real) : Real := qmul_real x x D
noncomputable def x3f (x D : Real) : Real := qmul_real (x2f x D) x D
noncomputable def x4f (x D : Real) : Real := qmul_real (x2f x D) (x2f x D) D
noncomputable def x5f (x D : Real) : Real := qmul_real (x4f x D) x D
noncomputable def sixth_fx (D : Real) : Real := quantize (1 / (1+1+1+1+1+1)) D
noncomputable def onetwenty_fx (D : Real) : Real := quantize (1 / onetwenty) D
noncomputable def t3f (x D : Real) : Real := qmul_real (x3f x D) (sixth_fx D) D
noncomputable def t5f (x D : Real) : Real := qmul_real (x5f x D) (onetwenty_fx D) D

/-- **The RTL pipeline**, definitionally: six `qmul`s feeding two exact accumulate steps. -/
noncomputable def eml_sin_rtl (x D : Real) : Real := x - t3f x D + t5f x D

theorem hexact_err (v D : Real) : abs (v - v) ≤ 0 * (1/D) := by
  rw [sub_self, zero_mul, abs_zero]
  exact le_refl 0

theorem E2_bound (x D : Real) (hD : 0 < D) :
    abs (x2f x D - x * x) ≤ 1 * (1/D) := by
  unfold x2f; rw [one_mul_thm]; exact qmul_trunc_err x x D hD

theorem E3_bound (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (x3f x D - (x * x) * x) ≤ (1 + 1) * (1/D) := by
  unfold x3f
  have hraw := qmul_err_loose hD hD1 (habsxx_le1 x hx0 hx1) (habsx_le1 x hx0 hx1)
    (le_of_lt zero_lt_one_ax) (le_refl (0:Real))
    (E2_bound x D hD) (hexact_err x D) (qmul_trunc_err (x2f x D) x D hD)
  rwa [show (1 + 1 + 0 + 1 * 0 : Real) = 1 + 1 from by mach_ring] at hraw

theorem E4_bound (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (x4f x D - (x * x) * (x * x)) ≤ (1 + 1 + 1 + 1) * (1/D) := by
  unfold x4f
  have hraw := qmul_err_loose hD hD1 (habsxx_le1 x hx0 hx1) (habsxx_le1 x hx0 hx1)
    (le_of_lt zero_lt_one_ax) (le_of_lt zero_lt_one_ax)
    (E2_bound x D hD) (E2_bound x D hD) (qmul_trunc_err (x2f x D) (x2f x D) D hD)
  rwa [show (1 + 1 + 1 + 1 * 1 : Real) = 1 + 1 + 1 + 1 from by mach_ring] at hraw

theorem E5_bound (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (x5f x D - ((x * x) * (x * x)) * x) ≤ (1 + 1 + 1 + 1 + 1) * (1/D) := by
  unfold x5f
  have hraw := qmul_err_loose hD hD1 (habsx4_le1 x hx0 hx1) (habsx_le1 x hx0 hx1)
    (by mach_linarith : (0:Real) ≤ 1 + 1 + 1 + 1) (le_refl (0:Real))
    (E4_bound x D hx0 hx1 hD hD1) (hexact_err x D) (qmul_trunc_err (x4f x D) x D hD)
  rwa [show (1 + (1+1+1+1) + 0 + (1+1+1+1) * 0 : Real) = 1 + 1 + 1 + 1 + 1
    from by mach_ring] at hraw

theorem Esixth_bound (D : Real) (hD : 0 < D) :
    abs (sixth_fx D - 1 / (1+1+1+1+1+1)) ≤ 1 * (1/D) := by
  unfold sixth_fx; rw [one_mul_thm]; exact quantize_err _ D hD

theorem E120th_bound (D : Real) (hD : 0 < D) :
    abs (onetwenty_fx D - 1 / onetwenty) ≤ 1 * (1/D) := by
  unfold onetwenty_fx; rw [one_mul_thm]; exact quantize_err _ D hD

theorem Et3_bound (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (t3f x D - ((x * x) * x) * (1 / (1+1+1+1+1+1))) ≤ (1+1+1+1+1+1) * (1/D) := by
  unfold t3f
  have hraw := qmul_err_loose hD hD1 (habsx3_le1 x hx0 hx1) habssixth_le1
    (by mach_linarith : (0:Real) ≤ 1 + 1) (le_of_lt zero_lt_one_ax)
    (E3_bound x D hx0 hx1 hD hD1) (Esixth_bound D hD) (qmul_trunc_err (x3f x D) (sixth_fx D) D hD)
  rwa [show (1 + (1+1) + 1 + (1+1) * 1 : Real) = 1+1+1+1+1+1 from by mach_ring] at hraw

theorem Et5_bound (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (t5f x D - (((x * x) * (x * x)) * x) * (1 / onetwenty)) ≤
      (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold t5f
  have hraw := qmul_err_loose hD hD1 (habsx5_le1 x hx0 hx1) habs120th_le1
    (by mach_linarith : (0:Real) ≤ 1+1+1+1+1) (le_of_lt zero_lt_one_ax)
    (E5_bound x D hx0 hx1 hD hD1) (E120th_bound D hD) (qmul_trunc_err (x5f x D) (onetwenty_fx D) D hD)
  rwa [show (1 + (1+1+1+1+1) + 1 + (1+1+1+1+1) * 1 : Real) = 1+1+1+1+1+1+1+1+1+1+1+1
    from by mach_ring] at hraw

/-! ## Full composition against `R0` -/

theorem eml_sin_fx_vs_acc_exact (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_sin_rtl x D -
      (x - ((x * x) * x) * (1 / (1+1+1+1+1+1)) + (((x * x) * (x * x)) * x) * (1 / onetwenty)))
      ≤ (1+1+1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold eml_sin_rtl
  have hsplit : (x - t3f x D + t5f x D)
      - (x - ((x * x) * x) * (1 / (1+1+1+1+1+1)) + (((x * x) * (x * x)) * x) * (1 / onetwenty))
      = -(t3f x D - ((x * x) * x) * (1 / (1+1+1+1+1+1)))
        + (t5f x D - (((x * x) * (x * x)) * x) * (1 / onetwenty)) := by
    mach_mpoly [x, t3f x D, t5f x D,
      (((x * x) * x) * (1 / (1+1+1+1+1+1)) : Real),
      ((((x * x) * (x * x)) * x) * (1 / onetwenty) : Real)]
  rw [hsplit]
  refine le_trans (abs_add _ _) ?_
  rw [abs_neg]
  exact add_le_add_both (Et3_bound x D hx0 hx1 hD hD1) (Et5_bound x D hx0 hx1 hD hD1)

/-- **The full `eml_sin.v` hardware forward-error certificate.** The fixed-point RTL pipeline's
output is within `18/D` (fixed-point truncation, 6 `qmul`s) `+ x⁶` (Taylor truncation,
`R0_bound`) of the true `sin x`, for `x ∈ [0,1]` and any grid `D ≥ 1`. Instantiate at
`D = 2¹⁶` (Q16.16, `eml_sin.v`'s actual format) for the concrete hardware claim. `sorryAx`-free —
this is a real proof, not an assumed spec. -/
theorem eml_sin_full_fwd_error (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_sin_rtl x D - sin x)
      ≤ ((1+1+1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D))
        + ((((x * x) * x) * x) * x) * x := by
  have hstep1 := eml_sin_fx_vs_acc_exact x D hx0 hx1 hD hD1
  have hstep2 : abs
      ((x - ((x * x) * x) * (1 / (1+1+1+1+1+1)) + (((x * x) * (x * x)) * x) * (1 / onetwenty))
        - sin x) ≤ ((((x * x) * x) * x) * x) * x := by
    have hR0 := R0_bound x hx0
    have heq : (x - ((x * x) * x) * (1 / (1+1+1+1+1+1))
        + (((x * x) * (x * x)) * x) * (1 / onetwenty)) - sin x = -(R0 x) := by
      unfold R0
      mach_mpoly [x, (1 / (1+1+1+1+1+1) : Real), (1 / onetwenty : Real), sin x]
    rw [heq, abs_neg]
    exact hR0
  have hsplit : eml_sin_rtl x D - sin x
      = (eml_sin_rtl x D -
          (x - ((x * x) * x) * (1 / (1+1+1+1+1+1)) + (((x * x) * (x * x)) * x) * (1 / onetwenty)))
        + ((x - ((x * x) * x) * (1 / (1+1+1+1+1+1)) + (((x * x) * (x * x)) * x) * (1 / onetwenty))
          - sin x) := by
    mach_mpoly [eml_sin_rtl x D, sin x,
      (x - ((x * x) * x) * (1 / (1+1+1+1+1+1)) + (((x * x) * (x * x)) * x) * (1 / onetwenty)
        : Real)]
  rw [hsplit]
  exact le_trans (abs_add _ _) (add_le_add_both hstep1 hstep2)

end MachLib.Real
