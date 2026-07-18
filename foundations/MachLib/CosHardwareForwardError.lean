import MachLib.SinHardwareForwardError
import MachLib.CosTaylorRemainder

/-!
# `eml_cos.v` hardware forward-error certificate — reusing the sin file's fixed-point machinery

The "breadth" companion to `SinHardwareForwardError`: `eml_cos.v` computes the 4-term
Maclaurin truncation `1 − x²/2 + x⁴/24 − x⁶/720` via a 6-`qmul` pipeline (`x2,x4,x6`, then
three constant-multiplies), one degree past `eml_sin.v`. Almost everything needed already
exists — `x2f`/`x4f`/`E2_bound`/`E4_bound` and the `x`/`x²`/`x⁴` magnitude bounds are literally
the SAME definitions `eml_cos.v`'s pipeline needs (`x4 = qmul(x2,x2)` is identical in both
primitives), reused directly from `SinHardwareForwardError` rather than redefined. Only `x6`
(`qmul(x4,x2)` — different from sin's `x5 = qmul(x4,x1)`) and the three constant-quantizations
(`1/2`, `1/24`, `1/720`, vs sin's `1/6`, `1/120`) are new.

## Per-stage error coefficients (units of `1/D`)

| stage | operation           | error |
|-------|---------------------|-------|
| `x2`  | `qmul(x,x)`         | 1 (= sin's `E2_bound`) |
| `x4`  | `qmul(x2,x2)`       | 4 (= sin's `E4_bound`) |
| `x6`  | `qmul(x4,x2)`       | 10 |
| `t2`  | `qmul(x2,1/2)`      | 4 |
| `t4`  | `qmul(x4,1/24)`     | 10 |
| `t6`  | `qmul(x6,1/720)`    | 22 |

Total fixed-point error `36/D` (vs sin's `18/D` — makes sense, this pipeline goes one degree
further). Combined with `Rcos_bound`'s `x⁷` Taylor term for the full certificate.

`sorryAx`-free. Companion: `SinHardwareForwardError`, `CosTaylorRemainder`.
-/

namespace MachLib.Real

theorem twentyfour_pos : (0 : Real) < twentyfour := by
  unfold twentyfour; exact mul_pos my_four_pos my_six_pos

theorem sevenhundredtwenty_pos : (0 : Real) < sevenhundredtwenty := by
  unfold sevenhundredtwenty; exact mul_pos my_six_pos honetwenty_pos

theorem sevenhundredtwenty_ge1 : (1 : Real) ≤ sevenhundredtwenty := by
  unfold sevenhundredtwenty; exact one_le_mul six_ge1 honetwenty_ge1

theorem hhalf_le1 : (1 : Real) / (1 + 1) ≤ 1 := div_le_one_of_le_of_pos my_two_pos two_ge1
theorem hhalf_nn : (0 : Real) ≤ 1 / (1 + 1) := one_div_nonneg_of_pos my_two_pos
theorem habshalf_le1 : abs ((1 : Real) / (1 + 1)) ≤ 1 := by
  rw [abs_of_nonneg hhalf_nn]; exact hhalf_le1

theorem h24th_le1 : (1 : Real) / twentyfour ≤ 1 := div_le_one_of_le_of_pos twentyfour_pos htwentyfour_ge1
theorem h24th_nn : (0 : Real) ≤ 1 / twentyfour := one_div_nonneg_of_pos twentyfour_pos
theorem habs24th_le1 : abs ((1 : Real) / twentyfour) ≤ 1 := by
  rw [abs_of_nonneg h24th_nn]; exact h24th_le1

theorem h720th_le1 : (1 : Real) / sevenhundredtwenty ≤ 1 :=
  div_le_one_of_le_of_pos sevenhundredtwenty_pos sevenhundredtwenty_ge1
theorem h720th_nn : (0 : Real) ≤ 1 / sevenhundredtwenty := one_div_nonneg_of_pos sevenhundredtwenty_pos
theorem habs720th_le1 : abs ((1 : Real) / sevenhundredtwenty) ≤ 1 := by
  rw [abs_of_nonneg h720th_nn]; exact h720th_le1

/-! ## x⁶ magnitude bound (extends `SinHardwareForwardError`'s x/x²/x³/x⁴/x⁵ bounds) -/

theorem hx6_nn (x : Real) (hx0 : 0 ≤ x) : 0 ≤ (x * x) * (x * x) * (x * x) :=
  mul_nonneg (hx4_nn x hx0) (hxx_nn x hx0)
theorem hx6_le1 (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (x * x) * (x * x) * (x * x) ≤ 1 :=
  mul_le_one (hx4_nn x hx0) (hx4_le1 x hx0 hx1) (hxx_nn x hx0) (hxx_le1 x hx0 hx1)
theorem habsx6_le1 (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    abs ((x * x) * (x * x) * (x * x)) ≤ 1 := by
  rw [abs_of_nonneg (hx6_nn x hx0)]; exact hx6_le1 x hx0 hx1

/-! ## The `eml_cos.v` pipeline, reusing `x2f`/`x4f`/`E2_bound`/`E4_bound` from the sin file -/

noncomputable def x6f (x D : Real) : Real := qmul_real (x4f x D) (x2f x D) D
noncomputable def half_fx (D : Real) : Real := quantize (1 / (1 + 1)) D
noncomputable def c24th_fx (D : Real) : Real := quantize (1 / twentyfour) D
noncomputable def c720th_fx (D : Real) : Real := quantize (1 / sevenhundredtwenty) D
noncomputable def ct2f (x D : Real) : Real := qmul_real (x2f x D) (half_fx D) D
noncomputable def ct4f (x D : Real) : Real := qmul_real (x4f x D) (c24th_fx D) D
noncomputable def ct6f (x D : Real) : Real := qmul_real (x6f x D) (c720th_fx D) D

/-- **The RTL pipeline**, definitionally: six `qmul`s (`x2,x4,x6` and three constant-multiplies)
feeding three exact accumulate steps. -/
noncomputable def eml_cos_rtl (x D : Real) : Real := 1 - ct2f x D + ct4f x D - ct6f x D

theorem E6_bound (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (x6f x D - (x * x) * (x * x) * (x * x)) ≤ (1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold x6f
  have hraw := qmul_err_loose hD hD1 (habsx4_le1 x hx0 hx1) (habsxx_le1 x hx0 hx1)
    (by mach_linarith : (0:Real) ≤ 1+1+1+1) (le_of_lt zero_lt_one_ax)
    (E4_bound x D hx0 hx1 hD hD1) (E2_bound x D hD) (qmul_trunc_err (x4f x D) (x2f x D) D hD)
  rwa [show (1 + (1+1+1+1) + 1 + (1+1+1+1) * 1 : Real) = 1+1+1+1+1+1+1+1+1+1 from by mach_ring] at hraw

theorem Ehalf_bound (D : Real) (hD : 0 < D) :
    abs (half_fx D - 1 / (1 + 1)) ≤ 1 * (1/D) := by
  unfold half_fx; rw [one_mul_thm]; exact quantize_err _ D hD

theorem E24th_bound (D : Real) (hD : 0 < D) :
    abs (c24th_fx D - 1 / twentyfour) ≤ 1 * (1/D) := by
  unfold c24th_fx; rw [one_mul_thm]; exact quantize_err _ D hD

theorem E720th_bound (D : Real) (hD : 0 < D) :
    abs (c720th_fx D - 1 / sevenhundredtwenty) ≤ 1 * (1/D) := by
  unfold c720th_fx; rw [one_mul_thm]; exact quantize_err _ D hD

theorem Et2_bound (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (ct2f x D - (x * x) * (1 / (1 + 1))) ≤ (1+1+1+1) * (1/D) := by
  unfold ct2f
  have hraw := qmul_err_loose hD hD1 (habsxx_le1 x hx0 hx1) habshalf_le1
    (le_of_lt zero_lt_one_ax) (le_of_lt zero_lt_one_ax)
    (E2_bound x D hD) (Ehalf_bound D hD) (qmul_trunc_err (x2f x D) (half_fx D) D hD)
  rwa [show (1 + 1 + 1 + 1 * 1 : Real) = 1+1+1+1 from by mach_ring] at hraw

theorem Et4_bound (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (ct4f x D - ((x * x) * (x * x)) * (1 / twentyfour)) ≤ (1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold ct4f
  have hraw := qmul_err_loose hD hD1 (habsx4_le1 x hx0 hx1) habs24th_le1
    (by mach_linarith : (0:Real) ≤ 1+1+1+1) (le_of_lt zero_lt_one_ax)
    (E4_bound x D hx0 hx1 hD hD1) (E24th_bound D hD) (qmul_trunc_err (x4f x D) (c24th_fx D) D hD)
  rwa [show (1 + (1+1+1+1) + 1 + (1+1+1+1) * 1 : Real) = 1+1+1+1+1+1+1+1+1+1 from by mach_ring] at hraw

theorem Et6_bound (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (ct6f x D - ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty)) ≤
      (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold ct6f
  have hraw := qmul_err_loose hD hD1 (habsx6_le1 x hx0 hx1) habs720th_le1
    (by mach_linarith : (0:Real) ≤ 1+1+1+1+1+1+1+1+1+1) (le_of_lt zero_lt_one_ax)
    (E6_bound x D hx0 hx1 hD hD1) (E720th_bound D hD) (qmul_trunc_err (x6f x D) (c720th_fx D) D hD)
  rwa [show (1 + (1+1+1+1+1+1+1+1+1+1) + 1 + (1+1+1+1+1+1+1+1+1+1) * 1 : Real)
      = 1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1 from by mach_ring] at hraw

/-! ## Full composition against `Rcos` -/

theorem eml_cos_fx_vs_acc_exact (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_cos_rtl x D -
      (1 - (x * x) * (1 / (1 + 1)) + ((x * x) * (x * x)) * (1 / twentyfour)
        - ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty)))
      ≤ (1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1) * (1/D)
        + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold eml_cos_rtl
  have hsplit : (1 - ct2f x D + ct4f x D - ct6f x D)
      - (1 - (x * x) * (1 / (1 + 1)) + ((x * x) * (x * x)) * (1 / twentyfour)
        - ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty))
      = -(ct2f x D - (x * x) * (1 / (1 + 1)))
        + (ct4f x D - ((x * x) * (x * x)) * (1 / twentyfour))
        + -(ct6f x D - ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty)) := by
    mach_mpoly [(1 : Real), ct2f x D, ct4f x D, ct6f x D,
      ((x * x) * (1 / (1 + 1)) : Real),
      (((x * x) * (x * x)) * (1 / twentyfour) : Real),
      (((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty) : Real)]
  rw [hsplit]
  have hEA : abs (ct2f x D - (x * x) * (1 / (1 + 1))) ≤ (1+1+1+1) * (1/D) :=
    Et2_bound x D hx0 hx1 hD hD1
  have hEB : abs (ct4f x D - ((x * x) * (x * x)) * (1 / twentyfour)) ≤
      (1+1+1+1+1+1+1+1+1+1) * (1/D) := Et4_bound x D hx0 hx1 hD hD1
  have hEC : abs (ct6f x D - ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty)) ≤
      (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := Et6_bound x D hx0 hx1 hD hD1
  have hnegA := abs_neg (ct2f x D - (x * x) * (1 / (1 + 1)))
  have hnegC := abs_neg (ct6f x D - ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty))
  refine le_trans (abs_add _ _) ?_
  refine le_trans (add_le_add_both (abs_add _ _) (le_refl _)) ?_
  rw [hnegA, hnegC]
  exact add_le_add_both (add_le_add_both hEA hEB) hEC

/-- **The full `eml_cos.v` hardware forward-error certificate.** The fixed-point RTL pipeline's
output is within `36/D` (fixed-point truncation, 6 `qmul`s) `+ x⁷` (Taylor truncation,
`Rcos_bound`) of the true `cos x`, for `x ∈ [0,1]` and any grid `D ≥ 1`. `sorryAx`-free. -/
theorem eml_cos_full_fwd_error (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_cos_rtl x D - cos x)
      ≤ ((1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1) * (1/D)
          + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D))
        + ((((((x * x) * x) * x) * x) * x) * x) := by
  have hstep1 := eml_cos_fx_vs_acc_exact x D hx0 hx1 hD hD1
  have hstep2 : abs
      ((1 - (x * x) * (1 / (1 + 1)) + ((x * x) * (x * x)) * (1 / twentyfour)
        - ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty)) - cos x)
      ≤ ((((((x * x) * x) * x) * x) * x) * x) := by
    have hRcos := Rcos_bound x hx0
    have heq : (1 - (x * x) * (1 / (1 + 1)) + ((x * x) * (x * x)) * (1 / twentyfour)
        - ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty)) - cos x = -(Rcos x) := by
      unfold Rcos R1
      mach_mpoly [x, (1 / (1 + 1) : Real), (1 / twentyfour : Real),
        (1 / sevenhundredtwenty : Real), cos x]
    rw [heq, abs_neg]
    exact hRcos
  have hsplit : eml_cos_rtl x D - cos x
      = (eml_cos_rtl x D -
          (1 - (x * x) * (1 / (1 + 1)) + ((x * x) * (x * x)) * (1 / twentyfour)
            - ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty)))
        + ((1 - (x * x) * (1 / (1 + 1)) + ((x * x) * (x * x)) * (1 / twentyfour)
            - ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty)) - cos x) := by
    mach_mpoly [eml_cos_rtl x D, cos x,
      (1 - (x * x) * (1 / (1 + 1)) + ((x * x) * (x * x)) * (1 / twentyfour)
        - ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty) : Real)]
  rw [hsplit]
  exact le_trans (abs_add _ _) (add_le_add_both hstep1 hstep2)

end MachLib.Real
