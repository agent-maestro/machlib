import MachLib.SinHardwareForwardError
import MachLib.TanTaylorRemainder

/-!
# `eml_tan.v` hardware forward-error certificate — the fixed-point ↔ real leg

Combines `Rtan0_bound` (the real-valued Taylor-remainder bound, `MachLib.TanTaylorRemainder`) with
`FixedPoint`'s `qmul_err_loose`/`quantize_err` (already used by `SinHardwareForwardError`, reused
here rather than redefined) into a certificate against the exact pipeline read off
`hardware/modules/transcendental/eml_tan.v`.

## What `eml_tan.v` actually computes (ground truth, read off the RTL)

Same Q16.16 `qmul` discipline as `eml_sin.v`, but one degree further: `x2=qmul(x,x)`,
`x3=qmul(x2,x1)`, `x4=qmul(x2,x2)`, `x5=qmul(x4,x1)`, `x7=qmul(x4,x3)`, then THREE constant
multiplies (`ONE_THIRD`, `TWO_15THS`, `SEVNTN_315TH` — each `⌊coefficient·D⌋` at elaboration time,
i.e. `quantize` of the true fraction, same phenomenon `eml_sin.v`'s `ONE_SIXTH` had) and a
FOUR-term accumulate `acc = x1 + t3 + t5 + t7`. `x2,x3,x4,x5` and their error bounds are reused
directly from `SinHardwareForwardError` (`x4=qmul(x2,x2)` is the identical computation in both
primitives) — only `x7` (`qmul(x4,x3)`, new) and the three constant-quantizations are new.

## Per-stage error coefficients (units of `1/D`)

| stage | operation             | error |
|-------|-----------------------|-------|
| `x2`  | `qmul(x,x)`           | 1  (= sin's `E2_bound`) |
| `x3`  | `qmul(x2,x1)`         | 2  (= sin's `E3_bound`) |
| `x4`  | `qmul(x2,x2)`         | 4  (= sin's `E4_bound`) |
| `x5`  | `qmul(x4,x1)`         | 5  (= sin's `E5_bound`) |
| `x7`  | `qmul(x4,x3)`         | 15 |
| `t3`  | `qmul(x3,1/3)`        | 6  |
| `t5`  | `qmul(x5,2/15)`       | 12 |
| `t7`  | `qmul(x7,17/315)`     | 32 |

Total fixed-point error `50/D`. Combined with `Rtan0_bound`'s `354560·Mtan(x)^9·x^8` Taylor term
for the full certificate. `sorryAx`-free.
-/

namespace MachLib.Real

/-! ## `natCast`-fraction magnitude bounds — `1/3`, `2/15`, `17/315` are all `≤ 1`, needed for
`qmul_err_loose`'s operand-boundedness hypothesis. -/

theorem natCast_le_of_nat_le {a b : Nat} (h : a ≤ b) : natCast a ≤ natCast b := by
  obtain ⟨d, hd⟩ := Nat.le.dest h
  rw [← hd, natCast_add]
  exact le_add_of_nonneg_right (natCast_nonneg d)

theorem natCast_frac_nonneg {b : Nat} (hb : 0 < b) (a : Nat) :
    (0 : Real) ≤ natCast a * (1 / natCast b) :=
  mul_nonneg (natCast_nonneg a) (one_div_nonneg_of_pos (natCast_pos hb))

theorem natCast_frac_le_one {a b : Nat} (hb : 0 < b) (h : a ≤ b) :
    natCast a * (1 / natCast b) ≤ 1 := by
  have hbpos : 0 < natCast b := natCast_pos hb
  have hbne : natCast b ≠ 0 := ne_of_gt hbpos
  have step : natCast a * (1 / natCast b) ≤ natCast b * (1 / natCast b) :=
    mul_le_mul_of_nonneg_right (natCast_le_of_nat_le h) (le_of_lt (one_div_pos_of_pos hbpos))
  rwa [mul_inv (natCast b) hbne] at step

/-! ## `x⁷` magnitude bound and pipeline stage — extends `SinHardwareForwardError`'s `x,x²,x³,x⁴,x⁵`
bounds (`x7 = qmul(x4,x3)`, new to `eml_tan.v`). -/

theorem hx7_nn (x : Real) (hx0 : 0 ≤ x) : 0 ≤ ((x * x) * (x * x)) * ((x * x) * x) :=
  mul_nonneg (hx4_nn x hx0) (hx3_nn x hx0)
theorem hx7_le1 (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : ((x * x) * (x * x)) * ((x * x) * x) ≤ 1 :=
  mul_le_one (hx4_nn x hx0) (hx4_le1 x hx0 hx1) (hx3_nn x hx0) (hx3_le1 x hx0 hx1)
theorem habsx7_le1 (x : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    abs (((x * x) * (x * x)) * ((x * x) * x)) ≤ 1 := by
  rw [abs_of_nonneg (hx7_nn x hx0)]; exact hx7_le1 x hx0 hx1

noncomputable def x7f (x D : Real) : Real := qmul_real (x4f x D) (x3f x D) D

theorem E7_bound (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (x7f x D - ((x * x) * (x * x)) * ((x * x) * x))
      ≤ (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold x7f
  have hraw := qmul_err_loose hD hD1 (habsx4_le1 x hx0 hx1) (habsx3_le1 x hx0 hx1)
    (by mach_linarith : (0:Real) ≤ 1+1+1+1) (by mach_linarith : (0:Real) ≤ 1+1)
    (E4_bound x D hx0 hx1 hD hD1) (E3_bound x D hx0 hx1 hD hD1)
    (qmul_trunc_err (x4f x D) (x3f x D) D hD)
  rwa [show (1 + (1+1+1+1) + (1+1) + (1+1+1+1) * (1+1) : Real)
      = 1+1+1+1+1+1+1+1+1+1+1+1+1+1+1 from by mach_ring] at hraw

/-! ## The three constant quantizations — `ONE_THIRD`, `TWO_15THS`, `SEVNTN_315TH` in the RTL,
each `⌊coefficient·D⌋` at elaboration time, i.e. `quantize` of the true fraction (same phenomenon
`eml_sin.v`'s `ONE_SIXTH` had). -/

noncomputable def third_fx (D : Real) : Real := quantize (1 / natCast 3) D
noncomputable def fifteenths_fx (D : Real) : Real := quantize (natCast 2 * (1 / natCast 15)) D
noncomputable def threefifteenths_fx (D : Real) : Real :=
  quantize (natCast 17 * (1 / natCast 315)) D

theorem Ethird_bound (D : Real) (hD : 0 < D) :
    abs (third_fx D - 1 / natCast 3) ≤ 1 * (1/D) := by
  unfold third_fx; rw [one_mul_thm]; exact quantize_err _ D hD
theorem Efifteenths_bound (D : Real) (hD : 0 < D) :
    abs (fifteenths_fx D - natCast 2 * (1 / natCast 15)) ≤ 1 * (1/D) := by
  unfold fifteenths_fx; rw [one_mul_thm]; exact quantize_err _ D hD
theorem Ethreefifteenths_bound (D : Real) (hD : 0 < D) :
    abs (threefifteenths_fx D - natCast 17 * (1 / natCast 315)) ≤ 1 * (1/D) := by
  unfold threefifteenths_fx; rw [one_mul_thm]; exact quantize_err _ D hD

theorem habsthird_le1 : abs ((1 : Real) / natCast 3) ≤ 1 := by
  rw [abs_of_nonneg (one_div_nonneg_of_pos (natCast_pos (n := 3) (by decide)))]
  have h3ge1 : (1 : Real) ≤ natCast 3 := by
    rw [show (3 : Nat) = 1 + 2 from rfl, natCast_add, natCast_one]
    exact le_add_of_nonneg_right (natCast_nonneg 2)
  exact div_le_one_of_le_of_pos (natCast_pos (n := 3) (by decide)) h3ge1
theorem habsfifteenths_le1 : abs (natCast 2 * (1 / natCast 15) : Real) ≤ 1 := by
  rw [abs_of_nonneg (natCast_frac_nonneg (b := 15) (by decide) 2)]
  exact natCast_frac_le_one (by decide) (by decide)
theorem habsthreefifteenths_le1 : abs (natCast 17 * (1 / natCast 315) : Real) ≤ 1 := by
  rw [abs_of_nonneg (natCast_frac_nonneg (b := 315) (by decide) 17)]
  exact natCast_frac_le_one (by decide) (by decide)

/-! ## The three constant-multiply stages (`t3,t5,t7`) and the full pipeline -/

noncomputable def t3f_tan (x D : Real) : Real := qmul_real (x3f x D) (third_fx D) D
noncomputable def t5f_tan (x D : Real) : Real := qmul_real (x5f x D) (fifteenths_fx D) D
noncomputable def t7f_tan (x D : Real) : Real := qmul_real (x7f x D) (threefifteenths_fx D) D

theorem Et3_bound_tan (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (t3f_tan x D - ((x * x) * x) * (1 / natCast 3)) ≤ (1+1+1+1+1+1) * (1/D) := by
  unfold t3f_tan
  have hraw := qmul_err_loose hD hD1 (habsx3_le1 x hx0 hx1) habsthird_le1
    (by mach_linarith : (0:Real) ≤ 1+1) (le_of_lt zero_lt_one_ax)
    (E3_bound x D hx0 hx1 hD hD1) (Ethird_bound D hD) (qmul_trunc_err (x3f x D) (third_fx D) D hD)
  rwa [show (1 + (1+1) + 1 + (1+1) * 1 : Real) = 1+1+1+1+1+1 from by mach_ring] at hraw

theorem Et5_bound_tan (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (t5f_tan x D - (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15)))
      ≤ (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold t5f_tan
  have hraw := qmul_err_loose hD hD1 (habsx5_le1 x hx0 hx1) habsfifteenths_le1
    (by mach_linarith : (0:Real) ≤ 1+1+1+1+1) (le_of_lt zero_lt_one_ax)
    (E5_bound x D hx0 hx1 hD hD1) (Efifteenths_bound D hD)
    (qmul_trunc_err (x5f x D) (fifteenths_fx D) D hD)
  rwa [show (1 + (1+1+1+1+1) + 1 + (1+1+1+1+1) * 1 : Real) = 1+1+1+1+1+1+1+1+1+1+1+1
      from by mach_ring] at hraw

theorem Et7_bound_tan (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (t7f_tan x D - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315)))
      ≤ (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold t7f_tan
  have hraw := qmul_err_loose hD hD1 (habsx7_le1 x hx0 hx1) habsthreefifteenths_le1
    (by mach_linarith : (0:Real) ≤ 1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (le_of_lt zero_lt_one_ax)
    (E7_bound x D hx0 hx1 hD hD1) (Ethreefifteenths_bound D hD)
    (qmul_trunc_err (x7f x D) (threefifteenths_fx D) D hD)
  rwa [show (1 + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) + 1 + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * 1 : Real)
      = 1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1 from by mach_ring] at hraw

/-- **The RTL pipeline**, definitionally: eight `qmul`s (`x2,x3,x4,x5,x7` and three
constant-multiplies) feeding a four-term exact accumulate. -/
noncomputable def eml_tan_rtl (x D : Real) : Real := x + t3f_tan x D + t5f_tan x D + t7f_tan x D

/-! ## Full composition against `Rtan0` -/

theorem eml_tan_fx_vs_acc_exact (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_tan_rtl x D -
      (x + ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15))
        + (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315))))
      ≤ (1+1+1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D)
        + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold eml_tan_rtl
  have hsplit : (x + t3f_tan x D + t5f_tan x D + t7f_tan x D)
      - (x + ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15))
        + (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315)))
      = (t3f_tan x D - ((x * x) * x) * (1 / natCast 3))
        + (t5f_tan x D - (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15)))
        + (t7f_tan x D
            - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315))) := by
    mach_mpoly [x, t3f_tan x D, t5f_tan x D, t7f_tan x D,
      (((x * x) * x) * (1 / natCast 3) : Real),
      ((((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15)) : Real),
      ((((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315)) : Real)]
  rw [hsplit]
  refine le_trans (abs_add _ _) (add_le_add_both ?_ (Et7_bound_tan x D hx0 hx1 hD hD1))
  exact le_trans (abs_add _ _)
    (add_le_add_both (Et3_bound_tan x D hx0 hx1 hD hD1) (Et5_bound_tan x D hx0 hx1 hD hD1))

/-- **The full `eml_tan.v` hardware forward-error certificate.** The fixed-point RTL pipeline's
output is within `50/D` (fixed-point truncation, 8 `qmul`s) `+ 354560·Mtan(x)^9·x^8` (Taylor
truncation, `Rtan0_bound`) of the true `tan x`, for `x ∈ [0,1]` and any grid `D ≥ 1`. `sorryAx`-free
— matches `eml_tan.v`'s own documented valid range `[-π/4,π/4]` (`π/4 < 1`) as a special case. -/
theorem eml_tan_full_fwd_error (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_tan_rtl x D - tan x)
      ≤ ((1+1+1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D)
          + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D))
        + (((((((natCast 354560
          * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
          * x) * x * x) * x) * x) * x) * x) := by
  have hxpi : x < pi / (1 + 1) := lt_of_le_of_lt hx1 one_lt_pi_div_two
  have hstep1 := eml_tan_fx_vs_acc_exact x D hx0 hx1 hD hD1
  have hstep2 : abs
      ((x + ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15))
        + (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315))) - tan x)
      ≤ (((((((natCast 354560
          * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
          * x) * x * x) * x) * x) * x) * x) := by
    have hR0 := Rtan0_bound x hx0 hxpi
    have heq : (x + ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15))
        + (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315))) - tan x
        = -(Rtan0 x) := by
      unfold Rtan0
      mach_mpoly [x, tan x, natCast 2, natCast 17, (1 / natCast 3 : Real),
        (1 / natCast 15 : Real), (1 / natCast 315 : Real)]
    rw [heq, abs_neg]
    exact hR0
  have hsplit : eml_tan_rtl x D - tan x
      = (eml_tan_rtl x D -
          (x + ((x * x) * x) * (1 / natCast 3)
            + (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15))
            + (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315))))
        + ((x + ((x * x) * x) * (1 / natCast 3)
            + (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15))
            + (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315))) - tan x) := by
    mach_mpoly [eml_tan_rtl x D, tan x,
      (x + ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15))
        + (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315)) : Real)]
  rw [hsplit]
  exact le_trans (abs_add _ _) (add_le_add_both hstep1 hstep2)

end MachLib.Real
