import MachLib.Matrix2InverseFixedPoint

/-!
# 2×2 Joseph covariance update — structural PSD + full-width dot bound

The proof spine for the scheduled-linear-algebra / Joseph arc (Forge:
`docs/scheduled_linear_algebra.md`). Two obligations the RTL side needs certified before
the datapath:

**(1) Full-width dot forward-error bound.** The scheduled MAC (`seq_mac_fw`) keeps the
products EXACT (full width) and truncates ONCE per dot, so its forward error is a *single*
rounding `sa` (≤ 2⁻ᶠ) — a factor-`K` improvement over the per-product engine's `K·2⁻ᶠ`.
`fxerr_dot2_fullwidth` is exactly `fxerr_dot2` with the truncation moved off the products
(`s0 = s1 = 0`) onto the final add, so for exact-leaf operands the error collapses to `sa`.

**(2) Joseph PSD preservation.** The Joseph form `P⁺ = (I−K)P(I−K)ᵀ + K R Kᵀ` stays
symmetric positive-semidefinite for *any* gain `K` — the reason real filters use it (round-off
cannot drive the covariance indefinite). Scoped to 2×2 with explicit entries and a
Mathlib-free PSD predicate (the quadratic form on entries): a congruence `G X Gᵀ` preserves
PSD (its quadratic form at `v` is `X`'s at `Gᵀv`), and a sum of PSD is PSD, so
`kalman2_joseph_psd` is `psd2_add` of two `psd2_congruence`s.

`sorryAx`-free, zero new axioms — Real arithmetic + `mach_mpoly` + the existing FxErr algebra.
(`Real` exposes `OfNat` only for `0`/`1`, so the coefficient `2` is written `(1 + 1)`.)
-/

namespace MachLib.Real

/-- An exact (full-width, un-truncated) value is a zero-width truncation of itself. -/
theorem truncw_exact (v : Real) : TruncW 0 v v := by
  unfold TruncW; rw [sub_self, abs_zero]; exact le_refl 0

/-- **Full-width fixed-point dot product** (the scheduled-LA / Joseph arithmetic). The two
products are kept EXACT (`s0 = s1 = 0`) and a SINGLE truncation `sa` is applied to the
accumulated exact sum — vs `fxerr_dot2`'s per-product truncation. For exact-leaf operands
(`Ex = Ey = 0`) the forward error is just the one final rounding `sa` (≤ 2⁻ᶠ), a factor-`K`
improvement on the per-product `K·2⁻ᶠ`. It is the same `fxerr_dot2` fold with the truncation
moved from the products onto the final add. -/
theorem fxerr_dot2_fullwidth
    {sa Mx0 vx0 My0 vy0 Mx1 vx1 My1 vy1 pa : Real}
    (hsa : 0 ≤ sa)
    (hx0 : FxErr Mx0 0 vx0 vx0) (hy0 : FxErr My0 0 vy0 vy0)
    (hx1 : FxErr Mx1 0 vx1 vx1) (hy1 : FxErr My1 0 vy1 vy1)
    (hpa : TruncW sa pa (vx0 * vy0 + vx1 * vy1)) :
    FxErr (Mx0 * My0 + Mx1 * My1) sa pa (vx0 * vy0 + vx1 * vy1) :=
  ⟨(fxerr_dot2 (le_refl 0) (le_refl 0) hsa
      hx0 hy0 (truncw_exact _) hx1 hy1 (truncw_exact _) hpa).1, hpa⟩

/-- A symmetric 2×2 matrix `[[a, b], [b, d]]` is **positive-semidefinite** iff its quadratic
form `a x² + 2b xy + d y²` is nonnegative everywhere. Mathlib-free: written on entries. -/
abbrev Psd2 (a b d : Real) : Prop :=
  ∀ x y : Real, 0 ≤ a * (x * x) + (1 + 1) * b * (x * y) + d * (y * y)

/-- **Congruence preserves PSD.** For any 2×2 `G = [[g00,g01],[g10,g11]]` and symmetric PSD
`X = [[p,q],[q,r]]`, the (symmetric) product `G X Gᵀ` is PSD: its quadratic form at `(x,y)`
equals `X`'s at `Gᵀ(x,y) = (g00 x + g10 y, g01 x + g11 y)`, hence nonnegative. The entry
formulas below are the `G X Gᵀ` entries. -/
theorem psd2_congruence {p q r g00 g01 g10 g11 : Real} (h : Psd2 p q r) :
    Psd2 (g00 * g00 * p + (1 + 1) * (g00 * g01) * q + g01 * g01 * r)
         (g00 * g10 * p + (g00 * g11 + g01 * g10) * q + g01 * g11 * r)
         (g10 * g10 * p + (1 + 1) * (g10 * g11) * q + g11 * g11 * r) := by
  intro x y
  have key := h (g00 * x + g10 * y) (g01 * x + g11 * y)
  have hid :
      (g00 * g00 * p + (1 + 1) * (g00 * g01) * q + g01 * g01 * r) * (x * x)
        + (1 + 1) * (g00 * g10 * p + (g00 * g11 + g01 * g10) * q + g01 * g11 * r) * (x * y)
        + (g10 * g10 * p + (1 + 1) * (g10 * g11) * q + g11 * g11 * r) * (y * y)
      = p * ((g00 * x + g10 * y) * (g00 * x + g10 * y))
        + (1 + 1) * q * ((g00 * x + g10 * y) * (g01 * x + g11 * y))
        + r * ((g01 * x + g11 * y) * (g01 * x + g11 * y)) := by
    mach_ring
  rw [hid]; exact key

/-- **A sum of PSD matrices is PSD.** Entrywise addition; the quadratic form is additive. -/
theorem psd2_add {a1 b1 d1 a2 b2 d2 : Real}
    (h1 : Psd2 a1 b1 d1) (h2 : Psd2 a2 b2 d2) :
    Psd2 (a1 + a2) (b1 + b2) (d1 + d2) := by
  intro x y
  have k1 := h1 x y
  have k2 := h2 x y
  have hid :
      (a1 + a2) * (x * x) + (1 + 1) * (b1 + b2) * (x * y) + (d1 + d2) * (y * y)
      = (a1 * (x * x) + (1 + 1) * b1 * (x * y) + d1 * (y * y))
        + (a2 * (x * x) + (1 + 1) * b2 * (x * y) + d2 * (y * y)) := by
    mach_ring
  rw [hid]; exact add_nonneg k1 k2

/-- **2×2 Joseph covariance update stays PSD, for any gain.** For symmetric PSD prior `P =
[[pa,pb],[pb,pd]]` and measurement noise `R = [[ra,rb],[rb,rd]]`, and any gain
`K = [[k00,k01],[k10,k11]]`, the Joseph-form posterior
`P⁺ = (I−K) P (I−K)ᵀ + K R Kᵀ` is symmetric PSD — a sum of two congruences of PSD matrices
(`G₁ = I−K`, `G₂ = K`). This is the numerical-robustness guarantee: no gain, and no rounding
in the gain, can make the covariance indefinite. -/
theorem kalman2_joseph_psd
    {k00 k01 k10 k11 pa pb pd ra rb rd : Real}
    (hP : Psd2 pa pb pd) (hR : Psd2 ra rb rd) :
    Psd2
      -- A⁺ = A(term1) + A(term2)
      (((1 - k00) * (1 - k00) * pa + (1 + 1) * ((1 - k00) * (-k01)) * pb + (-k01) * (-k01) * pd)
        + (k00 * k00 * ra + (1 + 1) * (k00 * k01) * rb + k01 * k01 * rd))
      -- B⁺
      (((1 - k00) * (-k10) * pa + ((1 - k00) * (1 - k11) + (-k01) * (-k10)) * pb
          + (-k01) * (1 - k11) * pd)
        + (k00 * k10 * ra + (k00 * k11 + k01 * k10) * rb + k01 * k11 * rd))
      -- D⁺
      (((-k10) * (-k10) * pa + (1 + 1) * ((-k10) * (1 - k11)) * pb + (1 - k11) * (1 - k11) * pd)
        + (k10 * k10 * ra + (1 + 1) * (k10 * k11) * rb + k11 * k11 * rd)) :=
  psd2_add
    (psd2_congruence (g00 := 1 - k00) (g01 := -k01) (g10 := -k10) (g11 := 1 - k11) hP)
    (psd2_congruence (g00 := k00) (g01 := k01) (g10 := k10) (g11 := k11) hR)

end MachLib.Real
