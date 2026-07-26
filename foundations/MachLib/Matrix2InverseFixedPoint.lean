import MachLib.KalmanUpdateFixedPoint
import MachLib.FixedPointCertifier

/-!
# Fixed-point stability of the 2×2 symmetric matrix inverse

Scaling the scalar Kalman flagship toward matrices, the scoped-honest first step: a
**fixed-size** inverse (no dynamic loops, no general Cholesky/LDLT machinery — it fits the
FPGA substrate). 2×2 symmetric is exactly the dimension the existing matrix Kalman uses —
the EKF innovation covariance `S = H·P·Hᵀ + R` and the `kalman2d` covariance are 2×2 — so
its gain needs a 2×2 inverse.

For a symmetric `A = [[a,b],[b,d]]`, `det = a·d − b²` and

    A⁻¹ = (1/det) · [[d, −b], [−b, a]].

The whole inverse is therefore **one reciprocal** (of `det`) **plus qmuls** — so its
fixed-point error composes exactly like the scalar reciprocal forward-error already proven
(`kalman_update_1d_fwd_error`), with `w := 1/det` carried abstractly so `mach_mpoly` never
touches a `1/(·)` atom.

Proven here (sorryAx-free, no new axioms):

* `matrix2_inv_entry_fwd_error`  — one inverse entry `qmul(e, recip)` is within
  `s + |e|·Erec` of the exact `e/det` (`s` = qmul truncation, `Erec` = the reciprocal's
  error as an approximation of `1/det`).
* `matrix2_sym_inverse_fwd_error` — all three distinct entries of the symmetric inverse at
  once.
* `matrix2_inverse_conditioning` — the **divergence bound**: the reciprocal is really an
  approximation of `1/det_fx` (the *computed* determinant); as an approximation of the exact
  `1/det` its error is `≤ Erec0 + Edet·|wf|·|w|`, where `|wf|·|w| = 1/(|det_fx|·|det|)`. So
  the inverse error blows up as `det → 0` (ill-conditioned) and is bounded exactly when the
  matrix is well-conditioned (`|det|` away from 0). This is the precise sense in which
  fixed-point rounding does not make the filter diverge — the numerical-stability companion
  to the existing `kalman2d_joseph_psd` structural-stability (PSD) proof.

The general n×n inversion-stability (Cholesky/LDLT, dynamic size) remains the larger arc;
at fixed 2×2 the closed form is equivalent and lands on the current substrate.
-/

namespace MachLib.Real

/-- **Forward error of one inverse entry.** With `recip ≈ w = 1/det` to `Erec` and the
`qmul` truncating within `s`, the computed entry `e_fx ≈ e·recip` is within `s + |e|·Erec`
of the exact `e·w = e/det`. -/
theorem matrix2_inv_entry_fwd_error (e w recip e_fx s Erec : Real)
    (hrec : abs (recip - w) ≤ Erec)
    (hq : abs (e_fx - e * recip) ≤ s) :
    abs (e_fx - e * w) ≤ s + abs e * Erec := by
  have hsplit : e_fx - e * w = (e_fx - e * recip) + e * (recip - w) := by
    mach_mpoly [e_fx, e, recip, w]
  rw [hsplit]
  refine le_trans (abs_add _ _) ?_
  refine add_le_add_both hq ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hrec (abs_nonneg _)

/-- **Forward error of the symmetric 2×2 inverse.** `A = [[a,b],[b,d]]`, `w := 1/det`,
`A⁻¹ = w·[[d,−b],[−b,a]]`. Each computed entry (`qmul` of the cofactor with `recip ≈ w`) is
within `s + |cofactor|·Erec` of the exact inverse entry — one reciprocal error `Erec`
shared across all four entries. -/
theorem matrix2_sym_inverse_fwd_error
    (a b d w recip inv00 inv01 inv11 s Erec : Real)
    (hrec : abs (recip - w) ≤ Erec)
    (h00 : abs (inv00 - d * recip) ≤ s)
    (h01 : abs (inv01 - (-b) * recip) ≤ s)
    (h11 : abs (inv11 - a * recip) ≤ s) :
    abs (inv00 - d * w) ≤ s + abs d * Erec
      ∧ abs (inv01 - (-b) * w) ≤ s + abs b * Erec
      ∧ abs (inv11 - a * w) ≤ s + abs a * Erec := by
  refine ⟨matrix2_inv_entry_fwd_error d w recip inv00 s Erec hrec h00, ?_,
          matrix2_inv_entry_fwd_error a w recip inv11 s Erec hrec h11⟩
  have h := matrix2_inv_entry_fwd_error (-b) w recip inv01 s Erec hrec h01
  rwa [abs_neg] at h

/-- **Conditioning / divergence bound.** `recip` approximates `1/det_fx` (the *computed*
determinant) to `Erec0`; `wf := 1/det_fx`, `w := 1/det`. As an approximation of the exact
`1/det`,

    |recip − w| ≤ Erec0 + Edet · |wf| · |w|,   Edet := |det − det_fx|.

Because `|wf|·|w| = 1/(|det_fx|·|det|)`, this is bounded exactly when the matrix is
well-conditioned (`det` bounded away from 0) and diverges as `det → 0`. -/
theorem matrix2_inverse_conditioning
    (det detfx recip wf w Erec0 Edet : Real)
    (hwf : detfx * wf = 1) (hw : det * w = 1)
    (hrec0 : abs (recip - wf) ≤ Erec0)
    (hedet : abs (det - detfx) ≤ Edet) :
    abs (recip - w) ≤ Erec0 + Edet * abs wf * abs w := by
  have hid : wf - w = (det - detfx) * wf * w := by
    have e : (det - detfx) * wf * w = wf * (det * w) - w * (detfx * wf) := by
      mach_mpoly [det, detfx, wf, w]
    rw [e, hw, hwf]; mach_mpoly [wf, w]
  have hsplit : recip - w = (recip - wf) + (wf - w) := by mach_mpoly [recip, wf, w]
  rw [hsplit]
  refine le_trans (abs_add _ _) ?_
  refine add_le_add_both hrec0 ?_
  rw [hid, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hedet (abs_nonneg _)) (abs_nonneg _)

/-! ## Gain / update composition — the inverse error flows into the gain, bounded

The Kalman gain `K = P·Hᵀ·S⁻¹` is a matrix product; each gain entry is a dot product of a row
of `P·Hᵀ` with a column of `S⁻¹`. The `S⁻¹` entries carry the inversion error just bounded, so
the gain error is a fold of `FixedPointCertifier`'s `fxerr_mul`/`fxerr_add` (the additive
fixed-point error algebra) with those entries plugged in — the inversion error `Erec`
propagates into the gain boundedly. -/

/-- **Fixed-point dot product of two perturbed operands** (reusable): `p ≈ x0·y0 + x1·y1`,
each factor carrying a `FxErr`, each `qmul` and the add truncating. The forward-error fold
of two `fxerr_mul`s and one `fxerr_add`. -/
theorem fxerr_dot2
    {s0 s1 sa Mx0 Ex0 vx0 xe0 My0 Ey0 vy0 ye0 p0
     Mx1 Ex1 vx1 xe1 My1 Ey1 vy1 ye1 p1 pa : Real}
    (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1) (hsa : 0 ≤ sa)
    (hx0 : FxErr Mx0 Ex0 vx0 xe0) (hy0 : FxErr My0 Ey0 vy0 ye0) (hp0 : TruncW s0 p0 (vx0 * vy0))
    (hx1 : FxErr Mx1 Ex1 vx1 xe1) (hy1 : FxErr My1 Ey1 vy1 ye1) (hp1 : TruncW s1 p1 (vx1 * vy1))
    (hpa : TruncW sa pa (p0 + p1)) :
    FxErr (Mx0 * My0 + Mx1 * My1)
          ((Mx0 * Ey0 + My0 * Ex0 + Ex0 * Ey0 + s0)
            + (Mx1 * Ey1 + My1 * Ex1 + Ex1 * Ey1 + s1) + sa)
          pa (xe0 * ye0 + xe1 * ye1) :=
  fxerr_add hsa (fxerr_mul hs0 hx0 hy0 hp0) (fxerr_mul hs1 hx1 hy1 hp1) hpa

/-- **A symmetric-2×2 inverse entry as an `FxErr`.** Repackages `matrix2_inv_entry_fwd_error`
(error `s + |e|·Erec`) with a magnitude bound so it can feed the `FxErr` fold above. -/
theorem matrix2_inv_entry_fxerr (e w recip e_fx s Erec M : Real)
    (hrec : abs (recip - w) ≤ Erec) (hq : abs (e_fx - e * recip) ≤ s)
    (hmag : abs (e * w) ≤ M) :
    FxErr M (s + abs e * Erec) e_fx (e * w) :=
  ⟨hmag, matrix2_inv_entry_fwd_error e w recip e_fx s Erec hrec hq⟩

/-- **A gain entry, through the inverse.** `K = (row of P·Hᵀ)·(column of S⁻¹)`. The two column
entries `b0,b1` are `S⁻¹` entries built from the shared reciprocal `recip ≈ w = 1/det`
(cofactors `e0,e1`), so they carry the inversion error `Erec`; the row entries `m0,m1` carry
their own `FxErr`. The gain entry's fixed-point error is bounded — with `Erec` appearing
explicitly, i.e. the inversion error propagates into the gain and no further amplification is
hidden. -/
theorem kalman2_gain_entry_via_inverse
    {Mm0 Em0 m0 me0 Mm1 Em1 m1 me1 : Real}
    {e0 e1 w recip b0 b1 sinv Erec Mb0 Mb1 : Real}
    {s0 s1 sa p0 p1 pa : Real}
    (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1) (hsa : 0 ≤ sa)
    (hm0 : FxErr Mm0 Em0 m0 me0) (hm1 : FxErr Mm1 Em1 m1 me1)
    (hrec : abs (recip - w) ≤ Erec)
    (hq0 : abs (b0 - e0 * recip) ≤ sinv) (hmag0 : abs (e0 * w) ≤ Mb0)
    (hq1 : abs (b1 - e1 * recip) ≤ sinv) (hmag1 : abs (e1 * w) ≤ Mb1)
    (hp0 : TruncW s0 p0 (m0 * b0)) (hp1 : TruncW s1 p1 (m1 * b1))
    (hpa : TruncW sa pa (p0 + p1)) :
    FxErr (Mm0 * Mb0 + Mm1 * Mb1)
          ((Mm0 * (sinv + abs e0 * Erec) + Mb0 * Em0 + Em0 * (sinv + abs e0 * Erec) + s0)
            + (Mm1 * (sinv + abs e1 * Erec) + Mb1 * Em1 + Em1 * (sinv + abs e1 * Erec) + s1) + sa)
          pa (me0 * (e0 * w) + me1 * (e1 * w)) :=
  fxerr_dot2 hs0 hs1 hsa hm0
    (matrix2_inv_entry_fxerr e0 w recip b0 sinv Erec Mb0 hrec hq0 hmag0) hp0
    hm1 (matrix2_inv_entry_fxerr e1 w recip b1 sinv Erec Mb1 hrec hq1 hmag1) hp1 hpa

end MachLib.Real
