import MachLib.CosHardwareForwardError
import MachLib.CoshTaylorRemainder

/-!
# `eml_cosh.v` hardware forward-error certificate — reusing `eml_cos.v`'s fixed-point layer wholesale

`hardware/modules/transcendental/eml_cosh.v` computes the **identical** six-`qmul` Q16.16
pipeline as `eml_cos.v` (`x2=qmul(x,x)`, `x4=qmul(x2,x2)`, `x6=qmul(x4,x2)`, three
constant-multiplies by `1/2`, `1/24`, `1/720`) — the ONLY RTL difference is the accumulate
sign: `acc = ONE + t2 + t4 + t6` (all `+`, matching `cosh`'s series) instead of
`1 − t2 + t4 − t6`. Every fixed-point bound in `CosHardwareForwardError`
(`E6_bound`..`Et6_bound`) is about `qmul` magnitude alone, independent of the final sign
combination, so they transfer verbatim — this file only rewires the accumulate step and
composes with `CoshTaylorRemainder.Rch0_bound` in place of `Rcos_bound`. `sorryAx`-free.
-/

namespace MachLib.Real

/-- **The RTL pipeline**, definitionally: the same six `qmul`s as `eml_cos_rtl`, accumulated
with `+` throughout (matching `cosh`'s all-positive Maclaurin series). -/
noncomputable def eml_cosh_rtl (x D : Real) : Real := 1 + ct2f x D + ct4f x D + ct6f x D

theorem eml_cosh_fx_vs_acc_exact (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_cosh_rtl x D -
      (1 + (x * x) * (1 / (1 + 1)) + ((x * x) * (x * x)) * (1 / twentyfour)
        + ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty)))
      ≤ (1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1) * (1/D)
        + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold eml_cosh_rtl
  have hsplit : (1 + ct2f x D + ct4f x D + ct6f x D)
      - (1 + (x * x) * (1 / (1 + 1)) + ((x * x) * (x * x)) * (1 / twentyfour)
        + ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty))
      = (ct2f x D - (x * x) * (1 / (1 + 1)))
        + (ct4f x D - ((x * x) * (x * x)) * (1 / twentyfour))
        + (ct6f x D - ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty)) := by
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
  exact le_trans (abs_add _ _) (add_le_add_both (le_trans (abs_add _ _) (add_le_add_both hEA hEB)) hEC)

/-- **The full `eml_cosh.v` hardware forward-error certificate.** The fixed-point RTL pipeline's
output is within `36/D` (fixed-point truncation, the same 6 `qmul`s as `eml_cos.v`)
`+ sinh(x)·x⁷` (Taylor truncation, `Rch0_bound`) of the true `cosh x`, for `x ∈ [0,1]` and any
grid `D ≥ 1`. Instantiate at `D = 2¹⁶` (Q16.16, `eml_cosh.v`'s actual format) for the concrete
hardware claim. `sorryAx`-free. -/
theorem eml_cosh_full_fwd_error (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_cosh_rtl x D - cosh x)
      ≤ ((1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1) * (1/D)
          + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D))
        + ((((((sinh x * x) * x) * x) * x) * x) * x) * x := by
  have hstep1 := eml_cosh_fx_vs_acc_exact x D hx0 hx1 hD hD1
  have hstep2 : abs
      ((1 + (x * x) * (1 / (1 + 1)) + ((x * x) * (x * x)) * (1 / twentyfour)
        + ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty)) - cosh x)
      ≤ ((((((sinh x * x) * x) * x) * x) * x) * x) * x := by
    have hRch0 := Rch0_bound x hx0
    have heq : (1 + (x * x) * (1 / (1 + 1)) + ((x * x) * (x * x)) * (1 / twentyfour)
        + ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty)) - cosh x = -(Rch0 x) := by
      unfold Rch0 Rsh1
      mach_mpoly [x, (1 / (1 + 1) : Real), (1 / twentyfour : Real),
        (1 / sevenhundredtwenty : Real), cosh x]
    rw [heq, abs_neg]
    exact hRch0
  have hsplit : eml_cosh_rtl x D - cosh x
      = (eml_cosh_rtl x D -
          (1 + (x * x) * (1 / (1 + 1)) + ((x * x) * (x * x)) * (1 / twentyfour)
            + ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty)))
        + ((1 + (x * x) * (1 / (1 + 1)) + ((x * x) * (x * x)) * (1 / twentyfour)
            + ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty)) - cosh x) := by
    mach_mpoly [eml_cosh_rtl x D, cosh x,
      (1 + (x * x) * (1 / (1 + 1)) + ((x * x) * (x * x)) * (1 / twentyfour)
        + ((x * x) * (x * x) * (x * x)) * (1 / sevenhundredtwenty) : Real)]
  rw [hsplit]
  exact le_trans (abs_add _ _) (add_le_add_both hstep1 hstep2)

end MachLib.Real
