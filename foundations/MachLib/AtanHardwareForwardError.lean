import MachLib.SinHardwareForwardError
import MachLib.TanHardwareForwardError
import MachLib.AtanTaylorRemainder

/-!
# `eml_atan.v` hardware forward-error certificate — the fixed-point ↔ real leg

Combines `R0atan_bound` (the real-valued Taylor-remainder bound, `MachLib.AtanTaylorRemainder`) with
`FixedPoint`'s `qmul_err_loose`/`quantize_err` into a certificate against the exact pipeline read
off `hardware/modules/transcendental/eml_atan.v`.

## What `eml_atan.v` actually computes (ground truth, read off the RTL)

The SAME `x2,x3,x4,x5,x7` pipeline as `eml_tan.v` (`x7f`/`E7_bound`, reused directly from
`MachLib.TanHardwareForwardError` — it's an identical computation, not atan-specific), then THREE
constant multiplies (`ONE_THIRD`, `ONE_FIFTH`, `ONE_SEVENTH`) and a four-term accumulate
`acc = x1 - t3 + t5 - t7`. `ONE_THIRD`/`third_fx`/`Ethird_bound`/`habsthird_le1` are ALSO reused
directly from `TanHardwareForwardError` (`tan`'s own first coefficient is `1/3` too). Only the
`1/5`, `1/7` constant quantizations are new.

## Per-stage error coefficients (units of `1/D`)

| stage | operation             | error |
|-------|-----------------------|-------|
| `x2,x3,x4,x5,x7` | (shared with `eml_tan.v`) | `1,2,4,5,15` |
| `t3`  | `qmul(x3,1/3)`        | 6  |
| `t5`  | `qmul(x5,1/5)`        | 6  |
| `t7`  | `qmul(x7,1/7)`        | 16 |

Total fixed-point error `28/D`. Combined with `R0atan_bound`'s `x⁹` Taylor term for the full
certificate. `sorryAx`-free.
-/

namespace MachLib.Real

/-! ## The two new constant quantizations — `ONE_FIFTH`, `ONE_SEVENTH` in the RTL. -/

noncomputable def fifth_fx (D : Real) : Real := quantize (1 / natCast 5) D
noncomputable def seventh_fx (D : Real) : Real := quantize (1 / natCast 7) D

theorem Efifth_bound (D : Real) (hD : 0 < D) :
    abs (fifth_fx D - 1 / natCast 5) ≤ 1 * (1/D) := by
  unfold fifth_fx; rw [one_mul_thm]; exact quantize_err _ D hD
theorem Eseventh_bound (D : Real) (hD : 0 < D) :
    abs (seventh_fx D - 1 / natCast 7) ≤ 1 * (1/D) := by
  unfold seventh_fx; rw [one_mul_thm]; exact quantize_err _ D hD

theorem habsfifth_le1 : abs ((1 : Real) / natCast 5) ≤ 1 := by
  rw [abs_of_nonneg (one_div_nonneg_of_pos (natCast_pos (n := 5) (by decide)))]
  have h5ge1 : (1 : Real) ≤ natCast 5 := by
    rw [show (5 : Nat) = 1 + 4 from rfl, natCast_add, natCast_one]
    exact le_add_of_nonneg_right (natCast_nonneg 4)
  exact div_le_one_of_le_of_pos (natCast_pos (n := 5) (by decide)) h5ge1
theorem habsseventh_le1 : abs ((1 : Real) / natCast 7) ≤ 1 := by
  rw [abs_of_nonneg (one_div_nonneg_of_pos (natCast_pos (n := 7) (by decide)))]
  have h7ge1 : (1 : Real) ≤ natCast 7 := by
    rw [show (7 : Nat) = 1 + 6 from rfl, natCast_add, natCast_one]
    exact le_add_of_nonneg_right (natCast_nonneg 6)
  exact div_le_one_of_le_of_pos (natCast_pos (n := 7) (by decide)) h7ge1

/-! ## The three constant-multiply stages (`t3,t5,t7`) and the full pipeline -/

noncomputable def t3f_atan (x D : Real) : Real := qmul_real (x3f x D) (third_fx D) D
noncomputable def t5f_atan (x D : Real) : Real := qmul_real (x5f x D) (fifth_fx D) D
noncomputable def t7f_atan (x D : Real) : Real := qmul_real (x7f x D) (seventh_fx D) D

theorem Et3_bound_atan (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (t3f_atan x D - ((x * x) * x) * (1 / natCast 3)) ≤ (1+1+1+1+1+1) * (1/D) := by
  unfold t3f_atan
  have hraw := qmul_err_loose hD hD1 (habsx3_le1 x hx0 hx1) habsthird_le1
    (by mach_linarith : (0:Real) ≤ 1+1) (le_of_lt zero_lt_one_ax)
    (E3_bound x D hx0 hx1 hD hD1) (Ethird_bound D hD) (qmul_trunc_err (x3f x D) (third_fx D) D hD)
  rwa [show (1 + (1+1) + 1 + (1+1) * 1 : Real) = 1+1+1+1+1+1 from by mach_ring] at hraw

theorem Et5_bound_atan (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (t5f_atan x D - (((x * x) * (x * x)) * x) * (1 / natCast 5))
      ≤ (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold t5f_atan
  have hraw := qmul_err_loose hD hD1 (habsx5_le1 x hx0 hx1) habsfifth_le1
    (by mach_linarith : (0:Real) ≤ 1+1+1+1+1) (le_of_lt zero_lt_one_ax)
    (E5_bound x D hx0 hx1 hD hD1) (Efifth_bound D hD)
    (qmul_trunc_err (x5f x D) (fifth_fx D) D hD)
  rwa [show (1 + (1+1+1+1+1) + 1 + (1+1+1+1+1) * 1 : Real) = 1+1+1+1+1+1+1+1+1+1+1+1
      from by mach_ring] at hraw

theorem Et7_bound_atan (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (t7f_atan x D - (((x * x) * (x * x)) * ((x * x) * x)) * (1 / natCast 7))
      ≤ (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold t7f_atan
  have hraw := qmul_err_loose hD hD1 (habsx7_le1 x hx0 hx1) habsseventh_le1
    (by mach_linarith : (0:Real) ≤ 1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (le_of_lt zero_lt_one_ax)
    (E7_bound x D hx0 hx1 hD hD1) (Eseventh_bound D hD)
    (qmul_trunc_err (x7f x D) (seventh_fx D) D hD)
  rwa [show (1 + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) + 1 + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * 1 : Real)
      = 1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1 from by mach_ring] at hraw

/-- **The RTL pipeline**, definitionally: `eml_atan.v`'s eight `qmul`s (`x2,x3,x4,x5,x7` and three
constant-multiplies) feeding a four-term exact accumulate, `x1 - t3 + t5 - t7`. -/
noncomputable def eml_atan_rtl (x D : Real) : Real := x - t3f_atan x D + t5f_atan x D - t7f_atan x D

/-! ## Full composition against `R0atan` -/

/-- `abs(-a + b - c) ≤ abs a + abs b + abs c` — the sign-mixed triangle inequality every
composition proof below needs (`eml_atan.v`'s accumulate has real minus signs, unlike
`eml_tan.v`'s all-plus one). -/
theorem abs_neg_add_sub (a b c : Real) : abs (-a + b - c) ≤ abs a + abs b + abs c := by
  have hrw : -a + b - c = (-a + b) + -c := by mach_ring
  rw [hrw]
  refine le_trans (abs_add _ _) ?_
  rw [abs_neg]
  have h1 : abs (-a + b) ≤ abs a + abs b := by
    refine le_trans (abs_add _ _) ?_
    rw [abs_neg]
    exact le_refl _
  exact add_le_add_both h1 (le_refl (abs c))

theorem eml_atan_fx_vs_acc_exact (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_atan_rtl x D -
      (x - ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (1 / natCast 5)
        - (((x * x) * (x * x)) * ((x * x) * x)) * (1 / natCast 7)))
      ≤ (1+1+1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D)
        + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold eml_atan_rtl
  have hsplit : (x - t3f_atan x D + t5f_atan x D - t7f_atan x D)
      - (x - ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (1 / natCast 5)
        - (((x * x) * (x * x)) * ((x * x) * x)) * (1 / natCast 7))
      = -(t3f_atan x D - ((x * x) * x) * (1 / natCast 3))
        + (t5f_atan x D - (((x * x) * (x * x)) * x) * (1 / natCast 5))
        - (t7f_atan x D - (((x * x) * (x * x)) * ((x * x) * x)) * (1 / natCast 7)) := by
    mach_mpoly [x, t3f_atan x D, t5f_atan x D, t7f_atan x D,
      (((x * x) * x) * (1 / natCast 3) : Real),
      ((((x * x) * (x * x)) * x) * (1 / natCast 5) : Real),
      ((((x * x) * (x * x)) * ((x * x) * x)) * (1 / natCast 7) : Real)]
  rw [hsplit]
  refine le_trans (abs_neg_add_sub _ _ _) ?_
  exact add_le_add_both (add_le_add_both (Et3_bound_atan x D hx0 hx1 hD hD1)
    (Et5_bound_atan x D hx0 hx1 hD hD1)) (Et7_bound_atan x D hx0 hx1 hD hD1)

/-- **The full `eml_atan.v` hardware forward-error certificate.** The fixed-point RTL pipeline's
output is within `50/D` (fixed-point truncation) `+ x⁹` (Taylor truncation, `R0atan_bound`) of the
true `atan x`, for `x ∈ [0,1]` and any grid `D ≥ 1`. `sorryAx`-free — matches `eml_atan.v`'s own
documented valid range `[-1,1]` exactly. -/
theorem eml_atan_full_fwd_error (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_atan_rtl x D - atan x)
      ≤ ((1+1+1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D)
          + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D))
        + (x * x * x * x * x * x * x * x) * x := by
  have hstep1 := eml_atan_fx_vs_acc_exact x D hx0 hx1 hD hD1
  have hstep2 : abs
      ((x - ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (1 / natCast 5)
        - (((x * x) * (x * x)) * ((x * x) * x)) * (1 / natCast 7)) - atan x)
      ≤ (x * x * x * x * x * x * x * x) * x := by
    have hR0 := R0atan_bound x hx0
    have heq : (x - ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (1 / natCast 5)
        - (((x * x) * (x * x)) * ((x * x) * x)) * (1 / natCast 7)) - atan x
        = -(R0atan x) := by
      unfold R0atan Patan
      rw [natCast_three, natCast_five, natCast_seven]
      mach_mpoly [x, atan x, (1 / (1 + 1 + 1) : Real), (1 / (1 + 1 + 1 + 1 + 1) : Real),
        (1 / (1 + 1 + 1 + 1 + 1 + 1 + 1) : Real)]
    rw [heq, abs_neg]
    exact hR0
  have hsplit : eml_atan_rtl x D - atan x
      = (eml_atan_rtl x D -
          (x - ((x * x) * x) * (1 / natCast 3)
            + (((x * x) * (x * x)) * x) * (1 / natCast 5)
            - (((x * x) * (x * x)) * ((x * x) * x)) * (1 / natCast 7)))
        + ((x - ((x * x) * x) * (1 / natCast 3)
            + (((x * x) * (x * x)) * x) * (1 / natCast 5)
            - (((x * x) * (x * x)) * ((x * x) * x)) * (1 / natCast 7)) - atan x) := by
    mach_mpoly [eml_atan_rtl x D, atan x,
      (x - ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (1 / natCast 5)
        - (((x * x) * (x * x)) * ((x * x) * x)) * (1 / natCast 7) : Real)]
  rw [hsplit]
  exact le_trans (abs_add _ _) (add_le_add_both hstep1 hstep2)

end MachLib.Real
