import MachLib.SinHardwareForwardError
import MachLib.SinhTaylorRemainder

/-!
# `eml_sinh.v` hardware forward-error certificate — reusing `eml_sin.v`'s fixed-point layer wholesale

`hardware/modules/transcendental/eml_sinh.v` computes the **identical** six-`qmul` Q16.16 pipeline
as `eml_sin.v` (`x2=qmul(x,x)`, `x3=qmul(x2,x1)`, `x5=qmul(qmul(x2,x2),x1)`,
`t3=qmul(x3,ONE_SIXTH)`, `t5=qmul(x5,ONE_120TH)`) — the ONLY RTL difference is the final
accumulate sign: `acc = x1 + t3 + t5` (all `+`, matching `sinh`'s series) instead of
`x1 − t3 + t5`. Since every fixed-point error bound in `SinHardwareForwardError`
(`E2_bound`..`Et5_bound`) is about `qmul` magnitude alone, independent of how the terms are later
combined, they transfer verbatim — this file adds only the new accumulate wiring and composes
with `SinhTaylorRemainder.Rsh0_bound` in place of `R0_bound`. `sorryAx`-free.
-/

namespace MachLib.Real

/-- **The RTL pipeline**, definitionally: the same six `qmul`s as `eml_sin_rtl`, accumulated with
`+` throughout (matching `sinh`'s all-positive Maclaurin series). -/
noncomputable def eml_sinh_rtl (x D : Real) : Real := x + t3f x D + t5f x D

theorem eml_sinh_fx_vs_acc_exact (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_sinh_rtl x D -
      (x + ((x * x) * x) * (1 / (1+1+1+1+1+1)) + (((x * x) * (x * x)) * x) * (1 / onetwenty)))
      ≤ (1+1+1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold eml_sinh_rtl
  have hsplit : (x + t3f x D + t5f x D)
      - (x + ((x * x) * x) * (1 / (1+1+1+1+1+1)) + (((x * x) * (x * x)) * x) * (1 / onetwenty))
      = (t3f x D - ((x * x) * x) * (1 / (1+1+1+1+1+1)))
        + (t5f x D - (((x * x) * (x * x)) * x) * (1 / onetwenty)) := by
    mach_mpoly [x, t3f x D, t5f x D,
      (((x * x) * x) * (1 / (1+1+1+1+1+1)) : Real),
      ((((x * x) * (x * x)) * x) * (1 / onetwenty) : Real)]
  rw [hsplit]
  exact le_trans (abs_add _ _) (add_le_add_both (Et3_bound x D hx0 hx1 hD hD1) (Et5_bound x D hx0 hx1 hD hD1))

/-- **The full `eml_sinh.v` hardware forward-error certificate.** The fixed-point RTL pipeline's
output is within `18/D` (fixed-point truncation, the same 6 `qmul`s as `eml_sin.v`)
`+ sinh(x)·x⁶` (Taylor truncation, `Rsh0_bound`) of the true `sinh x`, for `x ∈ [0,1]` and any
grid `D ≥ 1`. Instantiate at `D = 2¹⁶` (Q16.16, `eml_sinh.v`'s actual format) for the concrete
hardware claim. `sorryAx`-free. -/
theorem eml_sinh_full_fwd_error (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_sinh_rtl x D - sinh x)
      ≤ ((1+1+1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D))
        + (((((sinh x * x) * x) * x) * x) * x) * x := by
  have hstep1 := eml_sinh_fx_vs_acc_exact x D hx0 hx1 hD hD1
  have hstep2 : abs
      ((x + ((x * x) * x) * (1 / (1+1+1+1+1+1)) + (((x * x) * (x * x)) * x) * (1 / onetwenty))
        - sinh x) ≤ (((((sinh x * x) * x) * x) * x) * x) * x := by
    have hRsh0 := Rsh0_bound x hx0
    have heq : (x + ((x * x) * x) * (1 / (1+1+1+1+1+1))
        + (((x * x) * (x * x)) * x) * (1 / onetwenty)) - sinh x = -(Rsh0 x) := by
      unfold Rsh0
      mach_mpoly [x, (1 / (1+1+1+1+1+1) : Real), (1 / onetwenty : Real), sinh x]
    rw [heq, abs_neg]
    exact hRsh0
  have hsplit : eml_sinh_rtl x D - sinh x
      = (eml_sinh_rtl x D -
          (x + ((x * x) * x) * (1 / (1+1+1+1+1+1)) + (((x * x) * (x * x)) * x) * (1 / onetwenty)))
        + ((x + ((x * x) * x) * (1 / (1+1+1+1+1+1)) + (((x * x) * (x * x)) * x) * (1 / onetwenty))
          - sinh x) := by
    mach_mpoly [eml_sinh_rtl x D, sinh x,
      (x + ((x * x) * x) * (1 / (1+1+1+1+1+1)) + (((x * x) * (x * x)) * x) * (1 / onetwenty)
        : Real)]
  rw [hsplit]
  exact le_trans (abs_add _ _) (add_le_add_both hstep1 hstep2)

end MachLib.Real
