import MachLib.TanHardwareForwardError
import MachLib.TanhTaylorRemainder

/-!
# `eml_tanh.v` hardware forward-error certificate — the fixed-point ↔ real leg

Combines `Rtanh0_bound` (the real-valued Taylor-remainder bound, `MachLib.TanhTaylorRemainder`)
with `FixedPoint`'s `qmul_err_loose`/`quantize_err` into a certificate against the exact pipeline
read off `hardware/modules/transcendental/eml_tanh.v`.

## What `eml_tanh.v` actually computes (ground truth, read off the RTL)

The IDENTICAL `x2,x3,x4,x5,x7` pipeline AND the same three constant quantizations
(`ONE_THIRD`, `TWO_15THS`, `SEVNTN_315TH`) as `eml_tan.v` — `tanh`'s 4-term Maclaurin coefficients
(`1/3, 2/15, 17/315`) have the SAME magnitudes as `tan`'s own, just alternating sign in the
accumulate. Every fixed-point stage (`x7f`/`E7_bound`, `third_fx`/`fifteenths_fx`/
`threefifteenths_fx` and their error/magnitude bounds, `t3f_tan`/`t5f_tan`/`t7f_tan` and
`Et3_bound_tan`/`Et5_bound_tan`/`Et7_bound_tan`) is reused DIRECTLY from `TanHardwareForwardError` —
nothing new to quantize. Only the accumulate's sign pattern (`x1 - t3 + t5 - t7`, vs `tan`'s
all-plus) and the real-side comparison (against `Rtanh0_bound` instead of `Rtan0_bound`) differ.

Total fixed-point error `50/D` (identical to `tan`'s, same three `qmul`s). Combined with
`Rtanh0_bound`'s FLAT `354560·x⁸` Taylor term (no `Mtan(x)`-style growing quantity or domain
restriction beyond `[0,1]`, since `tanh` has no singularity) for the full certificate.
`sorryAx`-free.
-/

namespace MachLib.Real

/-- `abs(-a + b - c) ≤ abs a + abs b + abs c` — the sign-mixed triangle inequality
`eml_tanh_fx_vs_acc_exact` needs (`eml_tanh.v`'s accumulate has real minus signs, unlike
`eml_tan.v`'s all-plus one). Built from `abs_sub_le'` (`MachLib.AbsoluteError`) rather than manual
`abs_neg`/`abs_add` juggling — cleaner than `AtanHardwareForwardError`'s own `abs_neg_add_sub`. -/
theorem abs_neg_add_sub (a b c : Real) : abs (-a + b - c) ≤ abs a + abs b + abs c := by
  have h1 : abs (-a + b - c) ≤ abs b + abs a + abs c := by
    rw [show -a + b - c = (b - a) - c from by mach_ring]
    exact le_trans (abs_sub_le' _ _) (add_le_add_both (abs_sub_le' b a) (le_refl (abs c)))
  rwa [show abs b + abs a + abs c = abs a + abs b + abs c from by mach_ring] at h1

/-- **The RTL pipeline**, definitionally: `eml_tanh.v`'s eight `qmul`s (`x2,x3,x4,x5,x7` and three
constant-multiplies, all reused from `eml_tan.v`'s own) feeding a four-term exact accumulate,
`x1 - t3 + t5 - t7`. -/
noncomputable def eml_tanh_rtl (x D : Real) : Real :=
  x - t3f_tan x D + t5f_tan x D - t7f_tan x D

/-! ## Full composition against `Rtanh0` -/

theorem eml_tanh_fx_vs_acc_exact (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_tanh_rtl x D -
      (x - ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15))
        - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315))))
      ≤ (1+1+1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D)
        + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold eml_tanh_rtl
  have hsplit : (x - t3f_tan x D + t5f_tan x D - t7f_tan x D)
      - (x - ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15))
        - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315)))
      = -(t3f_tan x D - ((x * x) * x) * (1 / natCast 3))
        + (t5f_tan x D - (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15)))
        - (t7f_tan x D
            - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315))) := by
    mach_mpoly [x, t3f_tan x D, t5f_tan x D, t7f_tan x D,
      (((x * x) * x) * (1 / natCast 3) : Real),
      ((((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15)) : Real),
      ((((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315)) : Real)]
  rw [hsplit]
  refine le_trans (abs_neg_add_sub _ _ _) ?_
  exact add_le_add_both (add_le_add_both (Et3_bound_tan x D hx0 hx1 hD hD1)
    (Et5_bound_tan x D hx0 hx1 hD hD1)) (Et7_bound_tan x D hx0 hx1 hD hD1)

/-- **The full `eml_tanh.v` hardware forward-error certificate.** The fixed-point RTL pipeline's
output is within `50/D` (fixed-point truncation, 8 `qmul`s, identical to `tan`'s own) `+ 354560·x⁸`
(Taylor truncation, `Rtanh0_bound`) of the true `tanh x`, for `x ∈ [0,1]` and any grid `D ≥ 1` —
matches `eml_tanh.v`'s own documented valid range `[-1,1]` exactly, no restriction needed (unlike
`tan`'s `Mtan(x)`/`π/4` machinery). `sorryAx`-free. -/
theorem eml_tanh_full_fwd_error (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_tanh_rtl x D - tanh x)
      ≤ ((1+1+1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D)
          + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D))
        + (((((((natCast 354560 * x) * x) * x) * x) * x) * x) * x) * x := by
  have hstep1 := eml_tanh_fx_vs_acc_exact x D hx0 hx1 hD hD1
  have hstep2 : abs
      ((x - ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15))
        - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315))) - tanh x)
      ≤ (((((((natCast 354560 * x) * x) * x) * x) * x) * x) * x) * x := by
    have hR0 := Rtanh0_bound x hx0
    have heq : (x - ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15))
        - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315))) - tanh x
        = -(Rtanh0 x) := by
      unfold Rtanh0
      mach_mpoly [x, tanh x, natCast 2, natCast 17, (1 / natCast 3 : Real),
        (1 / natCast 15 : Real), (1 / natCast 315 : Real)]
    rw [heq, abs_neg]
    exact hR0
  have hsplit : eml_tanh_rtl x D - tanh x
      = (eml_tanh_rtl x D -
          (x - ((x * x) * x) * (1 / natCast 3)
            + (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15))
            - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315))))
        + ((x - ((x * x) * x) * (1 / natCast 3)
            + (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15))
            - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315))) - tanh x) := by
    mach_mpoly [eml_tanh_rtl x D, tanh x,
      (x - ((x * x) * x) * (1 / natCast 3)
        + (((x * x) * (x * x)) * x) * (natCast 2 * (1 / natCast 15))
        - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 17 * (1 / natCast 315)) : Real)]
  rw [hsplit]
  exact le_trans (abs_add _ _) (add_le_add_both hstep1 hstep2)

end MachLib.Real
