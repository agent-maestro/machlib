import MachLib.SinHardwareForwardError
import MachLib.TanHardwareForwardError
import MachLib.AsinTaylorRemainder

/-!
# `eml_asin.v` hardware forward-error certificate — the fixed-point ↔ real leg

Combines `Rasin0_bound` (the real-valued Taylor-remainder bound, `MachLib.AsinTaylorRemainder`)
with `FixedPoint`'s `qmul_err_loose`/`quantize_err` into a certificate against the exact pipeline
read off `hardware/modules/transcendental/eml_asin.v`.

## What `eml_asin.v` actually computes (ground truth, read off the RTL)

The SAME `x2,x3,x4,x5,x7` pipeline as `eml_tan.v`/`eml_tanh.v` (`x7f`/`E7_bound` reused directly
from `MachLib.TanHardwareForwardError`), then THREE new constant multiplies (`ONE_SIXTH`,
`THREE_40TH`, `FIFT_336TH`) and a four-term ALL-PLUS accumulate `acc = x1 + t3 + t5 + t7` — matching
`tan`'s own sign pattern (not `tanh`'s alternating one), since `arcsin`'s Maclaurin series has every
coefficient positive.

## Per-stage error coefficients (units of `1/D`)

| stage | operation             | error |
|-------|-----------------------|-------|
| `x2,x3,x4,x5,x7` | (shared with `eml_tan.v`) | `1,2,4,5,15` |
| `t3`  | `qmul(x3,1/6)`        | 6  |
| `t5`  | `qmul(x5,3/40)`       | 12 |
| `t7`  | `qmul(x7,15/336)`     | 32 |

Total fixed-point error `50/D`. Combined with `Rasin0_bound`'s `NTop·h(R)^15·x^8` Taylor term
(domain `x ∈ [0, R]`, `R = 1/2`, matching `eml_asin.v`'s own documented valid range exactly) for
the full certificate. `sorryAx`-free.
-/

namespace MachLib.Real

/-! ## The three new constant quantizations — `ONE_SIXTH`, `THREE_40TH`, `FIFT_336TH` in the RTL.
`sixth_fx`/`Esixth_bound`/`habssixth_le1` are reused directly from `SinHardwareForwardError`
(`sin`'s own `1/6` coefficient, stated in flat-sum form) rather than redefined. -/

noncomputable def three40th_fx (D : Real) : Real := quantize (natCast 3 * (1 / natCast 40)) D
noncomputable def fift336th_fx (D : Real) : Real := quantize (natCast 15 * (1 / natCast 336)) D

theorem Ethree40th_bound (D : Real) (hD : 0 < D) :
    abs (three40th_fx D - natCast 3 * (1 / natCast 40)) ≤ 1 * (1 / D) := by
  unfold three40th_fx; rw [one_mul_thm]; exact quantize_err _ D hD
theorem Efift336th_bound (D : Real) (hD : 0 < D) :
    abs (fift336th_fx D - natCast 15 * (1 / natCast 336)) ≤ 1 * (1 / D) := by
  unfold fift336th_fx; rw [one_mul_thm]; exact quantize_err _ D hD

theorem habsthree40th_le1 : abs (natCast 3 * (1 / natCast 40) : Real) ≤ 1 := by
  rw [abs_of_nonneg (natCast_frac_nonneg (b := 40) (by decide) 3)]
  exact natCast_frac_le_one (by decide) (by decide)
theorem habsfift336th_le1 : abs (natCast 15 * (1 / natCast 336) : Real) ≤ 1 := by
  rw [abs_of_nonneg (natCast_frac_nonneg (b := 336) (by decide) 15)]
  exact natCast_frac_le_one (by decide) (by decide)

/-! ## The three constant-multiply stages (`t3,t5,t7`) and the full pipeline -/

noncomputable def t3f_asin (x D : Real) : Real := qmul_real (x3f x D) (sixth_fx D) D
noncomputable def t5f_asin (x D : Real) : Real := qmul_real (x5f x D) (three40th_fx D) D
noncomputable def t7f_asin (x D : Real) : Real := qmul_real (x7f x D) (fift336th_fx D) D

theorem Et3_bound_asin (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (t3f_asin x D - ((x * x) * x) * (1 / (1+1+1+1+1+1))) ≤ (1+1+1+1+1+1) * (1/D) := by
  unfold t3f_asin
  have hraw := qmul_err_loose hD hD1 (habsx3_le1 x hx0 hx1) habssixth_le1
    (by mach_linarith : (0:Real) ≤ 1+1) (le_of_lt zero_lt_one_ax)
    (E3_bound x D hx0 hx1 hD hD1) (Esixth_bound D hD) (qmul_trunc_err (x3f x D) (sixth_fx D) D hD)
  rwa [show (1 + (1+1) + 1 + (1+1) * 1 : Real) = 1+1+1+1+1+1 from by mach_ring] at hraw

theorem Et5_bound_asin (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (t5f_asin x D - (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40)))
      ≤ (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold t5f_asin
  have hraw := qmul_err_loose hD hD1 (habsx5_le1 x hx0 hx1) habsthree40th_le1
    (by mach_linarith : (0:Real) ≤ 1+1+1+1+1) (le_of_lt zero_lt_one_ax)
    (E5_bound x D hx0 hx1 hD hD1) (Ethree40th_bound D hD)
    (qmul_trunc_err (x5f x D) (three40th_fx D) D hD)
  rwa [show (1 + (1+1+1+1+1) + 1 + (1+1+1+1+1) * 1 : Real) = 1+1+1+1+1+1+1+1+1+1+1+1
      from by mach_ring] at hraw

theorem Et7_bound_asin (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (t7f_asin x D - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336)))
      ≤ (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold t7f_asin
  have hraw := qmul_err_loose hD hD1 (habsx7_le1 x hx0 hx1) habsfift336th_le1
    (by mach_linarith : (0:Real) ≤ 1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (le_of_lt zero_lt_one_ax)
    (E7_bound x D hx0 hx1 hD hD1) (Efift336th_bound D hD)
    (qmul_trunc_err (x7f x D) (fift336th_fx D) D hD)
  rwa [show (1 + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) + 1 + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * 1 : Real)
      = 1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1 from by mach_ring] at hraw

/-- **The RTL pipeline**, definitionally: `eml_asin.v`'s eight `qmul`s (`x2,x3,x4,x5,x7` and three
constant-multiplies) feeding a four-term ALL-PLUS exact accumulate, matching `eml_tan.v`'s sign
pattern (not `eml_tanh.v`'s alternating one). -/
noncomputable def eml_asin_rtl (x D : Real) : Real := x + t3f_asin x D + t5f_asin x D + t7f_asin x D

/-! ## Full composition against `Rasin0` -/

theorem eml_asin_fx_vs_acc_exact (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_asin_rtl x D -
      (x + ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
        + (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40))
        + (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336))))
      ≤ (1+1+1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D)
        + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold eml_asin_rtl
  have hsplit : (x + t3f_asin x D + t5f_asin x D + t7f_asin x D)
      - (x + ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
        + (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40))
        + (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336)))
      = (t3f_asin x D - ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1)))
        + (t5f_asin x D - (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40)))
        + (t7f_asin x D
            - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336))) := by
    mach_mpoly [x, t3f_asin x D, t5f_asin x D, t7f_asin x D,
      (((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1)) : Real),
      ((((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40)) : Real),
      ((((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336)) : Real)]
  rw [hsplit]
  refine le_trans (abs_add _ _) (add_le_add_both ?_ (Et7_bound_asin x D hx0 hx1 hD hD1))
  exact le_trans (abs_add _ _)
    (add_le_add_both (Et3_bound_asin x D hx0 hx1 hD hD1) (Et5_bound_asin x D hx0 hx1 hD hD1))

/-- **The full `eml_asin.v` hardware forward-error certificate.** The fixed-point RTL pipeline's
output is within `50/D` (fixed-point truncation, 8 `qmul`s, identical count to `tan`/`tanh`)
`+ NTop·h(R)^15·x^8` (Taylor truncation, `Rasin0_bound`) of the true `arcsin x`, for `x ∈ [0, R]`
(`R = 1/2`) and any grid `D ≥ 1` — matches `eml_asin.v`'s own documented valid range exactly.
`sorryAx`-free. -/
theorem eml_asin_full_fwd_error (x D : Real) (hx0 : 0 ≤ x) (hxR : x ≤ asinR)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_asin_rtl x D - arcsin x)
      ≤ ((1+1+1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D)
          + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D))
        + NTop * hAsinPow 15 asinR * x * x * x * x * x * x * x * x := by
  have hx1 : x ≤ 1 := le_trans hxR (le_of_lt asinR_lt_one)
  have hstep1 := eml_asin_fx_vs_acc_exact x D hx0 hx1 hD hD1
  have hstep2 : abs
      ((x + ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
        + (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40))
        + (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336))) - arcsin x)
      ≤ NTop * hAsinPow 15 asinR * x * x * x * x * x * x * x * x := by
    have hR0 := Rasin0_bound x hx0 hxR
    have heq : (x + ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
        + (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40))
        + (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336))) - arcsin x
        = -(Rasin0 x) := by
      unfold Rasin0
      rw [natCast_six]
      mach_mpoly [x, arcsin x, natCast 3, natCast 15, (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real),
        (1 / natCast 40 : Real), (1 / natCast 336 : Real)]
    rw [heq, abs_neg]
    exact hR0
  have hsplit : eml_asin_rtl x D - arcsin x
      = (eml_asin_rtl x D -
          (x + ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
            + (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40))
            + (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336))))
        + ((x + ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
            + (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40))
            + (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336))) - arcsin x) := by
    mach_mpoly [eml_asin_rtl x D, arcsin x,
      (x + ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
        + (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40))
        + (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336)) : Real)]
  rw [hsplit]
  exact le_trans (abs_add _ _) (add_le_add_both hstep1 hstep2)

end MachLib.Real
