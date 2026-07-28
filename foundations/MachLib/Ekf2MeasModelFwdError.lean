import MachLib.FixedPointCertifier
import MachLib.SqrtNode
import MachLib.InverseTrig
import MachLib.DivisionError

/-!
# EKF measurement-model forward error — the range/bearing chain in fixed point

**Part 1 of the pre-registered 2×2 EKF forward-error bound**
(`../EKF2_FWD_ERROR_PREREGISTRATION.md`, posted before any tactic here ran). This file discharges
`δ_h`: the forward error of the *measurement model*

    h(x) = ( √(x₀² + x₁²) ,  atan(x₁ / x₀) )

as computed in Q16.16 by Forge's emitted `rb_track` block, against the same `h` in exact real
arithmetic. It is the nonlinear half of the update; the Joseph/gain half is `fxerr_dot2_fullwidth`
and `kalman2_joseph_psd`, which already exist.

## D2 — the composition is LIPSCHITZ, and the two transcendentals sit at opposite ends

The kernel certificates bound each kernel **at its exact input**. In the chain, `sqrt` receives an
already-erroneous sum of squares and `atan` an already-erroneous quotient, so each stage contributes
its own certified error **plus its derivative bound times the upstream error**. The pre-registration
committed to that asymmetry being visible in the statements, and it is — compare the two nodes below:

* `fxerr_atan_global` takes **no domain hypothesis at all**. `atan` is 1-Lipschitz *everywhere*
  (`InverseTrig.atan_lipschitz`, proven by MVT from `atan_deriv_le_one`), so upstream error passes
  through **unamplified**. Note this is stronger than the pre-registration claimed: `|atan′| ≤ 1` is
  not merely machine-checked in SymPy, it is a **Lean theorem in this repo**.
* `fxerr_sqrt_local` takes **six**: `0 < lo`, and both the computed and exact argument inside
  `[lo, hi]`. `d√s/ds = 1/(2√s)` blows up at the origin, so the amplification factor
  `1/(√lo + √lo)` only exists away from it.

**That asymmetry is physics, not slack.** Bearing is genuinely ill-conditioned at zero range; a
bound that claimed otherwise would be wrong. The domain is stated, and
`../EKF2_FWD_ERROR_PREREGISTRATION.md` §4 checks the anchor's own 8-step trajectory against it
(`r ∈ [5.000, 5.491]` vs `r_min = 4.0`), which is what makes the silicon evidence *an instance of
this theorem's hypotheses* rather than a separate claim.

## D4 — kernel bounds are HYPOTHESES, never axioms

Every node takes its kernel's error as a hypothesis (`hker : |impl v − exact v| ≤ c`) and is proven
unconditionally as composition. Nothing about `eml_sqrt_wide`'s structural ULP bound or
`eml_atan_wide`'s *enumerated* certificate enters MachLib as an axiom — which is the whole point,
since the latter is enumerated-plus-composition rather than derived, and importing its constant would
have killed the zero-new-axioms property in the first EKF file. If that certificate is ever upgraded
to derived, **these theorems do not change — only their instantiation does.**

Precedent, not a novel dodge: `KalmanUpdateFixedPoint.kalman_update_1d_fwd_error` already takes the
reciprocal's `Erec` as a hypothesis rather than importing a constant.

## Scope

Compares **fixed-point `h`** against **exact-real `h`**. It does *not* bound linearisation error,
distance to the true bearing, or anything statistical. Per the pre-registration, those are different
quantities and are deliberately not folded in here.

`sorryAx`-free, zero new axioms.
-/

namespace MachLib.Real

/-! ## Nodes the fold was missing -/

/-- **Propagated error of an exact division**, denominators bounded below by `m > 0`:

    |vx/vy − xe/ye|  ≤  Ex/m + Mx·Ey/(m·m)

Extracted so both the rounding models can share it. `DivisionError.aerr_div` proves exactly this
inline for the *relative*-rounding (`RoundsW`) carrier; `fxerr_div` below needs it for the
*absolute*-truncation (`TruncW`) carrier, which is the fixed-point one. Refactoring `aerr_div` onto
this lemma is a mechanical follow-up, kept out of this commit because `DivisionError` is widely
imported and this file is a leaf. -/
theorem div_prop_abs_error {Mx Ex vx xe My Ey vy ye m : Real}
    (hx : FxErr Mx Ex vx xe) (hy : FxErr My Ey vy ye)
    (hm : 0 < m) (hmvy : m ≤ vy) (hmye : m ≤ ye) :
    abs (vx / vy - xe / ye) ≤ Ex / m + Mx * Ey / (m * m) := by
  have hvy : 0 < vy := lt_of_lt_of_le hm hmvy
  have hye : 0 < ye := lt_of_lt_of_le hm hmye
  have hvyye : 0 < vy * ye := mul_pos hvy hye
  have hmm : 0 < m * m := mul_pos hm hm
  have hMx0 : 0 ≤ Mx := le_trans (abs_nonneg xe) hx.1
  have hEx0 : 0 ≤ Ex := le_trans (abs_nonneg (vx - xe)) hx.2
  have hEy0 : 0 ≤ Ey := le_trans (abs_nonneg (vy - ye)) hy.2
  rw [div_sub_div (ne_of_gt hvy) (ne_of_gt hye), abs_div_pos hvyye]
  have hnum : abs (vx * ye - xe * vy) ≤ Ex * ye + Mx * Ey := by
    rw [show vx * ye - xe * vy = (vx - xe) * ye + xe * (ye - vy) from by
          mach_mpoly [vx, ye, xe, vy]]
    have hA : abs ((vx - xe) * ye) ≤ Ex * ye := by
      rw [abs_mul, abs_of_nonneg (le_of_lt hye)]
      exact mul_le_mul_of_nonneg_right hx.2 (le_of_lt hye)
    have hB : abs (xe * (ye - vy)) ≤ Mx * Ey := by
      rw [abs_mul, show ye - vy = -(vy - ye) from by mach_ring, abs_neg]
      exact mul_le_mul' (abs_nonneg xe) hx.1 (abs_nonneg (vy - ye)) hy.2
    exact le_trans (abs_add _ _) (add_le_add_both hA hB)
  have hstep : abs (vx * ye - xe * vy) / (vy * ye) ≤ (Ex * ye + Mx * Ey) / (vy * ye) :=
    div_le_div_pos (abs_nonneg _) hnum hvyye (le_refl _)
  have hP : Ex * ye / (vy * ye) ≤ Ex / m := by
    rw [div_le_div_iff hvyye hm, show Ex * (vy * ye) = Ex * ye * vy from by
          mach_mpoly [Ex, vy, ye]]
    exact mul_le_mul_of_nonneg_left hmvy (mul_nonneg hEx0 (le_of_lt hye))
  have hQ : Mx * Ey / (vy * ye) ≤ Mx * Ey / (m * m) :=
    div_le_div_pos (mul_nonneg hMx0 hEy0) (le_refl _) hmm
      (mul_le_mul' (le_of_lt hm) hmvy (le_of_lt hm) hmye)
  have hcomb : (Ex * ye + Mx * Ey) / (vy * ye) ≤ Ex / m + Mx * Ey / (m * m) := by
    rw [show (Ex * ye + Mx * Ey) / (vy * ye)
          = Ex * ye / (vy * ye) + Mx * Ey / (vy * ye) from
          (div_add_div_same (ne_of_gt hvyye)).symm]
    exact add_le_add_both hP hQ
  exact le_trans hstep hcomb

/-- **Truncating divide, bounded against the TRUE quotient.** The quotient's own error is one
absolute truncation `s`, not a relative rounding. Denominator bounded below by `m > 0` on **both**
the computed and the exact value — the side condition division alone needs, since `1/y` is unbounded
near `0`.

**NOT a duplicate of `NewtonReciprocalDivision.fxerr_div`, and the difference is the whole point.**
That one is `fxerr_mul` with the NR reciprocal as second operand, and `fxerr_recip` places the
*exact* reciprocal `1/b` in the computed slot and the *NR output* `recip_e` in the exact slot. Its
conclusion therefore bounds `p` against `xe * rr` — exact dividend times **the hardware's own
reciprocal output**. That is a fine statement (and `|·|` is symmetric, so the error side is sound),
but it is a **hybrid reference**, not exact real arithmetic. A forward-error bound whose reference
contains the hardware's own output does not bound distance to the mathematics, which is precisely
what this file exists to do — hence a separate theorem against `xe / ye`. Whether the slot inversion
in `fxerr_recip` is deliberate is not adjudicated here; it is flagged, not fixed. -/
theorem fxerr_div_vs_exact {s Mx Ex vx xe My Ey vy ye p m : Real}
    (hx : FxErr Mx Ex vx xe) (hy : FxErr My Ey vy ye)
    (hm : 0 < m) (hmvy : m ≤ vy) (hmye : m ≤ ye) (hp : TruncW s p (vx / vy)) :
    FxErr (Mx / m) (s + (Ex / m + Mx * Ey / (m * m))) p (xe / ye) := by
  have hye : 0 < ye := lt_of_lt_of_le hm hmye
  refine ⟨?_, ?_⟩
  · rw [abs_div_pos hye]
    exact div_le_div_pos (abs_nonneg xe) hx.1 hm hmye
  · rw [show p - xe / ye = (p - vx / vy) + (vx / vy - xe / ye) from by
          mach_mpoly [p, vx / vy, xe / ye]]
    exact le_trans (abs_add _ _)
      (add_le_add_both hp (div_prop_abs_error hx hy hm hmvy hmye))

/-- **Hardware-faithful bridge to `TruncW`.** The silicon does not divide: it computes
`qq = qmul(v1, recip(v0))`. This turns that into the `TruncW s qq (v1/v0)` hypothesis
`fxerr_div_vs_exact` wants, and shows what the `s` there actually *is* — **not just the truncation,
but truncation plus dividend-magnitude times the reciprocal's certified error**. This is the join to
`nr_reciprocal_2stage`, which is the one kernel constant in this chain that is Lean-DERIVED rather
than enumerated or structural. -/
theorem trunc_quotient_via_recip {s M1 Er v1 v0 rr qq : Real}
    (hv0 : v0 ≠ 0) (hM1 : abs v1 ≤ M1) (hEr : abs (rr - 1 / v0) ≤ Er)
    (hq : TruncW s qq (v1 * rr)) :
    TruncW (s + M1 * Er) qq (v1 / v0) := by
  unfold TruncW at hq ⊢
  rw [div_def v1 v0 hv0,
      show qq - v1 * (1 / v0) = (qq - v1 * rr) + (v1 * rr - v1 * (1 / v0)) from by
        mach_mpoly [qq, v1, rr, (1 / v0 : Real)]]
  refine le_trans (abs_add _ _) (add_le_add_both hq ?_)
  rw [show v1 * rr - v1 * (1 / v0) = v1 * (rr - 1 / v0) from by
        mach_mpoly [v1, rr, (1 / v0 : Real)], abs_mul]
  exact mul_le_mul' (abs_nonneg v1) hM1 (abs_nonneg (rr - 1 / v0)) hEr

/-- **The `sqrt` node — LOCAL, six domain hypotheses.** Kernel error `c` at the *computed* argument,
plus `1/(√lo+√lo)` times the upstream error. The amplification factor is `sup |d√s/ds|` on `[lo,hi]`
and it is why `lo > 0` cannot be dropped: at the origin the derivative is unbounded and no such
constant exists. `Ms` is the caller's magnitude bound on the exact output (`√hi` in practice). -/
theorem fxerr_sqrt_local {M E v ve r lo hi c Ms : Real}
    (hlo : 0 < lo) (h : FxErr M E v ve)
    (hvlo : lo ≤ v) (hvhi : v ≤ hi) (helo : lo ≤ ve) (hehi : ve ≤ hi)
    (hker : abs (r - sqrt v) ≤ c)
    (hMs : abs (sqrt ve) ≤ Ms) :
    FxErr Ms (c + 1 / (sqrt lo + sqrt lo) * E) r (sqrt ve) := by
  refine ⟨hMs, ?_⟩
  have hL : abs (sqrt v - sqrt ve) ≤ 1 / (sqrt lo + sqrt lo) * abs (v - ve) :=
    sqrt_lip_local lo hi hlo v ve hvlo hvhi helo hehi
  have hLE : 1 / (sqrt lo + sqrt lo) * abs (v - ve) ≤ 1 / (sqrt lo + sqrt lo) * E :=
    mul_le_mul_of_nonneg_left h.2
      (le_of_lt (one_div_pos_of_pos (add_pos (sqrt_pos hlo) (sqrt_pos hlo))))
  rw [show r - sqrt ve = (r - sqrt v) + (sqrt v - sqrt ve) from by
        mach_mpoly [r, sqrt v, sqrt ve]]
  exact le_trans (abs_add _ _) (add_le_add_both hker (le_trans hL hLE))

/-- **The `atan` node — GLOBAL, no domain hypothesis whatsoever.** `atan` is 1-Lipschitz on all of
`ℝ` (`atan_lipschitz`, MVT from `atan_deriv_le_one`), so upstream error passes through
**unamplified** and the bound is a plain sum `c + E`. This is the structural contrast with
`fxerr_sqrt_local` that the pre-registration organised D2 around — and it is the reason the bearing
branch of the range-bearing model costs nothing in conditioning *at the atan itself*, only at the
division feeding it. -/
theorem fxerr_atan_global {M E v ve t c Mt : Real}
    (h : FxErr M E v ve) (hker : abs (t - atan v) ≤ c) (hMt : abs (atan ve) ≤ Mt) :
    FxErr Mt (c + E) t (atan ve) := by
  refine ⟨hMt, ?_⟩
  rw [show t - atan ve = (t - atan v) + (atan v - atan ve) from by
        mach_mpoly [t, atan v, atan ve]]
  exact le_trans (abs_add _ _)
    (add_le_add_both hker (le_trans (atan_lipschitz v ve) h.2))

/-! ## The measurement model

Naming: `v₀ v₁` are the Q16.16 state words, `x₀ x₁` the exact reals they encode. `ESq` is the error
of one truncating square, `ESumSq` of the truncated sum of two. Everything is explicit on entries —
no `‖·‖`, no matrices — matching `Matrix2JosephPSD`'s Mathlib-free style. -/

/-- Forward error of one truncating square `v·v` (from `fxerr_mul` at `x = y`). -/
noncomputable abbrev ESq (M E s : Real) : Real := M * E + M * E + E * E + s

/-- Forward error of the truncated sum of two squares. -/
noncomputable abbrev ESumSq (M0 E0 M1 E1 s : Real) : Real := ESq M0 E0 s + ESq M1 E1 s + s

/-- **RANGE branch: `√(x₀² + x₁²)` in fixed point.** Two truncating squares, one truncating add, one
certified `sqrt` kernel. The `lo`/`hi` hypotheses are the range-bounded-away-from-the-origin domain
of D2; `c_sqrt` is `eml_sqrt_wide`'s structural sub-ULP bound, supplied as a hypothesis. -/
theorem ekf2_range_fwd_error
    {v0 v1 x0 x1 q0 q1 ss r s M0 E0 M1 E1 lo hi c_sqrt Mr : Real}
    (hs : 0 ≤ s)
    (hx0 : FxErr M0 E0 v0 x0) (hx1 : FxErr M1 E1 v1 x1)
    (hq0 : TruncW s q0 (v0 * v0)) (hq1 : TruncW s q1 (v1 * v1))
    (hss : TruncW s ss (q0 + q1))
    (hlo : 0 < lo)
    (hvlo : lo ≤ ss) (hvhi : ss ≤ hi)
    (helo : lo ≤ x0 * x0 + x1 * x1) (hehi : x0 * x0 + x1 * x1 ≤ hi)
    (hker : abs (r - sqrt ss) ≤ c_sqrt)
    (hMr : abs (sqrt (x0 * x0 + x1 * x1)) ≤ Mr) :
    abs (r - sqrt (x0 * x0 + x1 * x1))
      ≤ c_sqrt + 1 / (sqrt lo + sqrt lo) * ESumSq M0 E0 M1 E1 s :=
  (fxerr_sqrt_local hlo
    (fxerr_add hs (fxerr_mul hs hx0 hx0 hq0) (fxerr_mul hs hx1 hx1 hq1) hss)
    hvlo hvhi helo hehi hker hMr).2

/-- **BEARING branch: `atan(x₁/x₀)` in fixed point.** One truncating divide (denominator bounded
below by `m > 0` — the `x₀ = 0` axis is where the quotient, not the `atan`, is ill-conditioned) then
one certified `atan` kernel, whose upstream error passes through **unamplified**.

`c_atan` is `eml_atan_wide`'s ENUMERATED certificate, a hypothesis (D4). Instantiated at the anchor's
own folded-argument range it is `5.75e-03 rad` rather than the kernel's worst case `6.16e-02` — see
the pre-registration §4, and note that improvement is legitimate *only* because the domain is a
stated hypothesis the artifact is then checked against.

The `0 < m ≤ x₀` hypothesis also records that this is the `x₀ > 0` half-plane model: the emitted
`atan(x₁/x₀)` is the correct bearing only there, which is a property of the model, not of this
bound. -/
theorem ekf2_bearing_fwd_error
    {v0 v1 x0 x1 qq th s M0 E0 M1 E1 m c_atan Mth : Real}
    (hx0 : FxErr M0 E0 v0 x0) (hx1 : FxErr M1 E1 v1 x1)
    (hm : 0 < m) (hmv0 : m ≤ v0) (hmx0 : m ≤ x0)
    (hq : TruncW s qq (v1 / v0))
    (hker : abs (th - atan qq) ≤ c_atan)
    (hMth : abs (atan (x1 / x0)) ≤ Mth) :
    abs (th - atan (x1 / x0))
      ≤ c_atan + (s + (E1 / m + M1 * E0 / (m * m))) :=
  (fxerr_atan_global (fxerr_div_vs_exact hx1 hx0 hm hmv0 hmx0 hq) hker hMth).2

/-- **`δ_h` — both components of the measurement model at once.** This is the `δ_h` row of the
pre-registration's error-decomposition table, discharged. The remaining rows (`δ_H`, `δ_S`, `δ_K`,
`δ_x⁺`) build on it.

Read the two bounds side by side and D2 is visible in the arithmetic: the range error carries an
**amplification factor** `1/(√lo+√lo)` that only exists because `lo > 0`, while the bearing error
carries a bare `+` because `|atan′| ≤ 1` everywhere. -/
theorem ekf2_h_fwd_error
    {v0 v1 x0 x1 q0 q1 ss r qq th s M0 E0 M1 E1 lo hi m c_sqrt c_atan Mr Mth : Real}
    (hs : 0 ≤ s)
    (hx0 : FxErr M0 E0 v0 x0) (hx1 : FxErr M1 E1 v1 x1)
    (hq0 : TruncW s q0 (v0 * v0)) (hq1 : TruncW s q1 (v1 * v1))
    (hss : TruncW s ss (q0 + q1))
    (hlo : 0 < lo) (hvlo : lo ≤ ss) (hvhi : ss ≤ hi)
    (helo : lo ≤ x0 * x0 + x1 * x1) (hehi : x0 * x0 + x1 * x1 ≤ hi)
    (hkerS : abs (r - sqrt ss) ≤ c_sqrt) (hMr : abs (sqrt (x0 * x0 + x1 * x1)) ≤ Mr)
    (hm : 0 < m) (hmv0 : m ≤ v0) (hmx0 : m ≤ x0)
    (hq : TruncW s qq (v1 / v0))
    (hkerA : abs (th - atan qq) ≤ c_atan)
    (hMth : abs (atan (x1 / x0)) ≤ Mth) :
    abs (r - sqrt (x0 * x0 + x1 * x1))
        ≤ c_sqrt + 1 / (sqrt lo + sqrt lo) * ESumSq M0 E0 M1 E1 s
    ∧ abs (th - atan (x1 / x0))
        ≤ c_atan + (s + (E1 / m + M1 * E0 / (m * m))) :=
  ⟨ekf2_range_fwd_error hs hx0 hx1 hq0 hq1 hss hlo hvlo hvhi helo hehi hkerS hMr,
   ekf2_bearing_fwd_error hx0 hx1 hm hmv0 hmx0 hq hkerA hMth⟩

end MachLib.Real
