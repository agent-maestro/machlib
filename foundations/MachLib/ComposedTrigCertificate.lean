import MachLib.CosHardwareForwardError

/-!
# Composed certificate: the hardware sin/cos stay on the (approximate) unit circle

The "depth" companion to `SinHardwareForwardError`/`CosHardwareForwardError`: a genuinely
COMPOSED forward-error result, not just two primitives certified in isolation. Real EML
kernels chain transcendentals together (rotations, orientation, control laws using both `sin`
and `cos` of the same angle); this file certifies the simplest, most structurally meaningful
composition — squaring and adding the two certified hardware outputs via two more `qmul`s
lands within a computable bound of the exact Pythagorean identity `sin²x + cos²x = 1`.

## Method

`qmul_err` (the general two-erroneous-operand composition from `FixedPoint`, NOT the
`_loose` unit-of-`1/D` specialization) applies directly: `Es x D`/`Ec x D` — the exact RHS
expressions of `eml_sin_full_fwd_error`/`eml_cos_full_fwd_error` — are the error bounds `Ex`/`Ey`
on `eml_sin_rtl`/`eml_cos_rtl` against `sin x`/`cos x`. Squaring each via one more `qmul`
(`qmul_trunc_err` for the leaf rounding fact) and combining via `qmul_err` gives a bound on
`|sin_sq - sin²x|` and `|cos_sq - cos²x|`; the triangle inequality plus `pythagorean`
(`sin²x + cos²x = 1`, pre-existing in `MachLib.Trig`) finishes it. The bound is left in terms
of `abs (sin x)`/`abs (cos x)` rather than simplified to a pure polynomial in `x`/`1/D` — both
are individually `≤ 1` (`abs_sin_le_one`/`abs_cos_le_one`) if a caller needs that, but leaving
them in is both simpler to prove and slightly tighter.

`sorryAx`-free.
-/

namespace MachLib.Real

/-- The exact RHS of `eml_sin_full_fwd_error`, named for reuse. -/
noncomputable def Es (x D : Real) : Real :=
  ((1+1+1+1+1+1)*(1/D) + (1+1+1+1+1+1+1+1+1+1+1+1)*(1/D)) + ((((x*x)*x)*x)*x)*x

/-- The exact RHS of `eml_cos_full_fwd_error`, named for reuse. -/
noncomputable def Ec (x D : Real) : Real :=
  ((1+1+1+1)*(1/D) + (1+1+1+1+1+1+1+1+1+1)*(1/D) + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1)*(1/D))
    + ((((((x*x)*x)*x)*x)*x)*x)

theorem hEs (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_sin_rtl x D - sin x) ≤ Es x D := eml_sin_full_fwd_error x D hx0 hx1 hD hD1

theorem hEc (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_cos_rtl x D - cos x) ≤ Ec x D := eml_cos_full_fwd_error x D hx0 hx1 hD hD1

/-- **Composed certificate: `qmul(sin_hw,sin_hw) + qmul(cos_hw,cos_hw)` stays close to `1`.**
Chains `qmul_err` on top of the two primitive certificates (`eml_sin_full_fwd_error`,
`eml_cos_full_fwd_error`) plus the exact Pythagorean identity — the first result in this arc
about a genuinely composed hardware kernel rather than a single certified primitive.
`sorryAx`-free. -/
theorem sin_cos_sq_sum_fwd_error (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (qmul_real (eml_sin_rtl x D) (eml_sin_rtl x D) D
      + qmul_real (eml_cos_rtl x D) (eml_cos_rtl x D) D - 1)
      ≤ (1/D + ((abs (sin x) + Es x D) * Es x D + Es x D * abs (sin x)))
        + (1/D + ((abs (cos x) + Ec x D) * Ec x D + Ec x D * abs (cos x))) := by
  have hsinsq := qmul_err (hEs x D hx0 hx1 hD hD1) (hEs x D hx0 hx1 hD hD1)
    (qmul_trunc_err (eml_sin_rtl x D) (eml_sin_rtl x D) D hD)
  have hcossq := qmul_err (hEc x D hx0 hx1 hD hD1) (hEc x D hx0 hx1 hD hD1)
    (qmul_trunc_err (eml_cos_rtl x D) (eml_cos_rtl x D) D hD)
  have hsplit : (qmul_real (eml_sin_rtl x D) (eml_sin_rtl x D) D
      + qmul_real (eml_cos_rtl x D) (eml_cos_rtl x D) D) - 1
      = (qmul_real (eml_sin_rtl x D) (eml_sin_rtl x D) D - sin x * sin x)
        + (qmul_real (eml_cos_rtl x D) (eml_cos_rtl x D) D - cos x * cos x) := by
    rw [← pythagorean x]
    mach_mpoly [qmul_real (eml_sin_rtl x D) (eml_sin_rtl x D) D,
      qmul_real (eml_cos_rtl x D) (eml_cos_rtl x D) D, sin x, cos x]
  rw [hsplit]
  exact le_trans (abs_add _ _) (add_le_add_both hsinsq hcossq)

end MachLib.Real
