import MachLib.KalmanUpdateFixedPoint
import MachLib.Iteration

/-!
# The scalar Kalman update at chip 2's format — Q8.8

**Bar B of the chip-2 pre-registration.** The pre-registration priced this at *"near-zero by the
no-numerals architecture — CHECKED, not assumed."*

**Checked. The cost is ZERO for the theorems themselves.** `KalmanUpdateFixedPoint.lean` contains
**no numerals in any statement or proof**: `s` (the per-`qmul` truncation bound) and `B` (the
monitored residual) are free variables throughout, and every mention of `Q16.16` in that file is a
**docstring**, not a hypothesis. Nothing is re-proved here; the format is instantiated.

**Q8.8 has grid step `2⁻⁸`**, so `s := 1 / 2⁸`, written `1 / npow 8 (1+1)`.

**The no-numerals architecture is enforced by the TYPE SYSTEM, not by convention:** `MachLib.Real`
has no `OfNat` instance for `256`, so the literal *cannot be written*. The format constant is built
from `1` and `+`. That is a stronger guarantee than a coding standard — a numeral cannot leak into a
statement even by accident.

**Why the `_via_nr` form is the one chip 2 needs:** its hypothesis is
`|1 − (p+r)·recip_e| ≤ B` — **exactly the predicate a conclusion-shaped monitor computes on die**
(`S = p+r`, `recip_e = Kinv`). The certificate therefore turns *monitor silence* directly into an
end-to-end forward-error bound, with no conversion step. That is the certificate design rule
(*state the conclusion on the quantity a monitor would witness*) already satisfied, before the rule
was written.
-/

namespace MachLib
namespace Real

/-- Q8.8's grid step, `2⁻⁸`, built from `1` because no numeral literal exists at `Real`. -/
noncomputable def q88step : Real := 1 / npow 8 (1 + 1)

theorem q88step_pos : 0 < q88step := one_div_pos_of_pos (npow_pos my_two_pos 8)

/-- **Chip 2's certificate.** Q8.8 truncation (`s = 1/256`) plus a monitored reciprocal residual
`B` gives an end-to-end bound on the fixed-point Kalman update's forward error.

`B` is **the monitor's threshold**: the die witnesses `|1 − S·Kinv| ≤ B` per operation, and this
turns that witness into a bound on the estimate. -/
theorem kalman_update_1d_at_q88
    {x p z r recip_e k_hw kd_hw B : Real}
    (hpr : p + r ≠ 0) (hpos : 0 < abs (p + r))
    (hscaled : abs (1 - (p + r) * recip_e) ≤ B)
    (hk  : abs (k_hw - p * recip_e) ≤ q88step)
    (hkd : abs (kd_hw - k_hw * (z - x)) ≤ q88step) :
    abs ((x + kd_hw) - (x + p / (p + r) * (z - x)))
      ≤ q88step + abs (z - x) * (q88step + abs p * (B / abs (p + r))) :=
  kalman_update_1d_fwd_error_via_nr hpr hpos hscaled hk hkd

/-- **Chip 2's near-MMSE statement at Q8.8.** The conditional MSE of the implemented estimator is
within `ε²` of the statistical optimum, `ε` the Q8.8 forward-error bound. -/
theorem kalman_update_1d_at_q88_near_mmse
    {x_pred p_pred z r recip_e k_hw kd_hw Erec : Real}
    (hpr : p_pred + r ≠ 0) (hErec : 0 ≤ Erec)
    (hrec : abs (recip_e - 1 / (p_pred + r)) ≤ Erec)
    (hk  : abs (k_hw - p_pred * recip_e) ≤ q88step)
    (hkd : abs (kd_hw - k_hw * (z - x_pred)) ≤ q88step) :
    postVar p_pred r
        + ((x_pred + kd_hw) - postMean x_pred p_pred r z)
          * ((x_pred + kd_hw) - postMean x_pred p_pred r z)
      ≤ postVar p_pred r
        + (q88step + abs (z - x_pred) * (q88step + abs p_pred * Erec))
          * (q88step + abs (z - x_pred) * (q88step + abs p_pred * Erec)) :=
  kalman_update_1d_fx_near_mmse hpr (le_of_lt q88step_pos) hErec hrec hk hkd

end Real
end MachLib
