import MachLib.Basic
import MachLib.Forge
import MachLib.Lemmas
import MachLib.Applications.GuardedActuatorCommand
import MachLib.Applications.ActuatorCommandWithinBand
import MachLib.Applications.ActuatorCommandBandWithRateLimit
import MachLib.Applications.ActuatorCommandWithJerkLimit

/-!
# Forge kernel application — actuator-saturation guard (v4)

**v4 = v3 band + slew-rate + jerk + SNAP limit**, the discrete-time
third-difference bound on actuator motion. v0 → v1 → v2 → v3 → v4.

## The kernel (from Forge, `actuator_command_with_snap_limit.eml`)

```eml
fn actuator_command_with_snap_limit(
    error, integral, deriv, kp, ki, kd,
    u_min, u_max, rate_limit, jerk_limit, snap_limit,
    prev_result, prev_prev_result, prev_prev_prev_result) -> Real
    requires u_min <= u_max
    requires 0.0 <= rate_limit
    requires 0.0 <= jerk_limit
    requires 0.0 <= snap_limit
    requires snap_limit <= jerk_limit
    requires jerk_limit <= rate_limit
    requires u_min <= prev_result, prev_prev_result, prev_prev_prev_result <= u_max
    requires abs(prev - prev_prev) + jerk_limit <= rate_limit
    requires abs((prev - prev_prev) - (prev_prev - prev_prev_prev)) + snap_limit
              <= jerk_limit
    requires prev_result - u_min >= rate_limit
    requires u_max - prev_result >= rate_limit
    ensures  u_min <= result
    ensures  result <= u_max
    ensures  abs(result - prev) <= rate_limit
    ensures  abs((result - prev) - (prev - prev_prev)) <= jerk_limit
    ensures  abs(((result - prev) - (prev - prev_prev))
                 - ((prev - prev_prev) - (prev_prev - prev_prev_prev)))
              <= snap_limit
{
    clamp(kp*err + ki*integral + kd*deriv,
          extrap - snap_limit, extrap + snap_limit)
}
```
where `extrap := prev + (prev - prev_prev)
                      + ((prev - prev_prev) - (prev_prev - prev_prev_prev))
              = 3·prev - 3·prev_prev + prev_prev_prev`
(constant-jerk extrapolation of the last three positions).

## The single-clamp design

Like v3, v4 uses ONE clamp. Under the v4 preconditions:

  `[extrap - snap, extrap + snap]   ⊆`     (snap window)
  `[jerk_center - jerk, jerk_center + jerk]   ⊆`     (jerk window, v3-style)
  `[prev - rate, prev + rate]   ⊆`     (rate window)
  `[u_min, u_max]`                     (band)

where `jerk_center := prev + (prev - prev_prev) = 2·prev - prev_prev`
and `extrap = jerk_center + prev_jerk`, with
`prev_jerk := (prev - prev_prev) - (prev_prev - prev_prev_prev)`.

The four nested containments come from:

- `snap ⊆ jerk` :  `|prev_jerk| + snap_limit ≤ jerk_limit`  (P11)
- `jerk ⊆ rate` :  `|r_prev| + jerk_limit ≤ rate_limit`     (P10, carried from v3)
- `rate ⊆ band` :  `prev - u_min ≥ rate_limit`              (P12/P13, carried from v3)
                   `u_max - prev ≥ rate_limit`

So clamping to the snap window automatically satisfies all FIVE
ensures (band lo, band hi, rate, jerk, snap).

## Reusing v3 helpers

The "snap window ⊆ jerk window" step is STRUCTURALLY IDENTICAL to
v3's "jerk window ⊆ rate window" step — just substitute
`(prev → jerk_center, r_prev → prev_jerk, jerk → snap, rate → jerk)`.
So we reuse `prev_minus_rl_le_lo` and `hi_le_prev_plus_rl` from v3 by
straight substitution.

Likewise the "rate window ⊆ band" step reuses v3's `umin_le_lo` and
`hi_le_umax` unchanged.

The proof becomes a chain of two `le_trans` per ensures, each
discharged by one v3 helper. Total proof: ~150 lines, half of v3.

## Jerk and snap ensures forms

EML contract jerk:  `abs((result - prev) - r_prev) ≤ jerk_limit`
Lean form (assoc-normalised): `abs(result - jerk_center) ≤ jerk_limit`

EML contract snap:  `abs(((result - prev) - r_prev) - prev_jerk) ≤ snap_limit`
Lean form (assoc-normalised): `abs(result - extrap) ≤ snap_limit`

Both forms are equivalent to the EML by `(a-b)-c = a-(b+c)` (one
step of associativity), and the normalised forms match the clamp
geometry directly.
-/

namespace MachLib
namespace Forge
namespace AerospaceActuatorGuardSnap

open MachLib
open MachLib.Real
open MachLib.Forge.AerospaceActuatorGuard
  (neg_neg neg_le_neg abs_le_of_bounds)
open MachLib.Forge.AerospaceActuatorGuardBandRate
  (le_min add_nonneg sub_nonneg_le le_add_nonneg max_le)
open MachLib.Forge.AerospaceActuatorGuardJerk
  (sub_le_imp le_add_imp hi_le_umax umin_le_lo
   prev_minus_rl_le_lo hi_le_prev_plus_rl)

/-! ## The kernel body -/

/-- Single snap-window clamp centered at the constant-jerk extrapolation
of the last three positions; matches the Forge emit. -/
noncomputable def actuator_command_snap_body
    (error integral deriv kp ki kd
     u_min u_max rate_limit jerk_limit snap_limit
     prev_result prev_prev_result prev_prev_prev_result : Real) : Real :=
  MachLib.Real.min
    (MachLib.Real.max
      (kp * error + ki * integral + kd * deriv)
      (prev_result + (prev_result - prev_prev_result)
                   + ((prev_result - prev_prev_result)
                       - (prev_prev_result - prev_prev_prev_result))
                   - snap_limit))
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))
                 + snap_limit)

/-! ## Window-bound lemmas (snap clamp geometry) -/

private theorem snap_lo_le_snap_hi
    (prev_result prev_prev_result prev_prev_prev_result snap_limit : Real)
    (h_snap_nonneg : 0 ≤ snap_limit) :
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))) - snap_limit
    ≤
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))) + snap_limit :=
  le_trans (sub_nonneg_le h_snap_nonneg) (le_add_nonneg h_snap_nonneg)

/-- snap_lo ≤ result. -/
private theorem snap_lo_le_result
    (error integral deriv kp ki kd
     u_min u_max rate_limit jerk_limit snap_limit
     prev_result prev_prev_result prev_prev_prev_result : Real)
    (h_snap_nonneg : 0 ≤ snap_limit) :
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))) - snap_limit ≤
    actuator_command_snap_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      prev_result prev_prev_result prev_prev_prev_result := by
  unfold actuator_command_snap_body
  apply le_min
  · exact le_max_right _ _
  · exact snap_lo_le_snap_hi
      prev_result prev_prev_result prev_prev_prev_result snap_limit h_snap_nonneg

/-- result ≤ snap_hi. -/
private theorem result_le_snap_hi
    (error integral deriv kp ki kd
     u_min u_max rate_limit jerk_limit snap_limit
     prev_result prev_prev_result prev_prev_prev_result : Real) :
    actuator_command_snap_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      prev_result prev_prev_result prev_prev_prev_result ≤
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))) + snap_limit := by
  unfold actuator_command_snap_body
  exact min_le_right _ _

/-! ## Snap ⊆ Jerk window containment (the only v4-specific lemma)

By substitution into v3's helpers:
  (prev_result → jerk_center, r_prev → prev_jerk, rate_limit → jerk_limit,
   jerk_limit → snap_limit)

Then v3's `prev_minus_rl_le_lo` becomes `jerk_lo ≤ snap_lo`,
and v3's `hi_le_prev_plus_rl` becomes `snap_hi ≤ jerk_hi`.
-/

/-- snap_lo ≥ jerk_lo. Specialisation of v3's prev_minus_rl_le_lo. -/
theorem jerk_lo_le_snap_lo
    (prev_result prev_prev_result prev_prev_prev_result
     jerk_limit snap_limit : Real)
    (h_prev_jerk_lower :
       -((prev_result - prev_prev_result)
         - (prev_prev_result - prev_prev_prev_result)) + snap_limit ≤ jerk_limit) :
    (prev_result + (prev_result - prev_prev_result)) - jerk_limit ≤
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))) - snap_limit :=
  prev_minus_rl_le_lo
    (prev_result + (prev_result - prev_prev_result))  -- "prev" = jerk_center
    jerk_limit                                          -- "rate_limit" = jerk_limit
    snap_limit                                          -- "jerk_limit" = snap_limit
    ((prev_result - prev_prev_result)
      - (prev_prev_result - prev_prev_prev_result))     -- "r_prev" = prev_jerk
    h_prev_jerk_lower

/-- snap_hi ≤ jerk_hi. Specialisation of v3's hi_le_prev_plus_rl. -/
theorem snap_hi_le_jerk_hi
    (prev_result prev_prev_result prev_prev_prev_result
     jerk_limit snap_limit : Real)
    (h_prev_jerk_upper :
       ((prev_result - prev_prev_result)
         - (prev_prev_result - prev_prev_prev_result)) + snap_limit ≤ jerk_limit) :
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))) + snap_limit ≤
    (prev_result + (prev_result - prev_prev_result)) + jerk_limit :=
  hi_le_prev_plus_rl
    (prev_result + (prev_result - prev_prev_result))  -- "prev" = jerk_center
    jerk_limit                                          -- "rate_limit" = jerk_limit
    snap_limit                                          -- "jerk_limit" = snap_limit
    ((prev_result - prev_prev_result)
      - (prev_prev_result - prev_prev_prev_result))     -- "r_prev" = prev_jerk
    h_prev_jerk_upper

/-! ## The main verify obligation

Discharge all FIVE ensures via the containment chain
snap ⊆ jerk ⊆ rate ⊆ band, reusing v3's helpers + the new
snap-in-jerk helpers above. -/

/-- **The main verify obligation**: band + rate + jerk + snap all hold.

Preconditions unpack the EML abs constraints into two halves each
(`h_r_prev_upper/lower`, `h_prev_jerk_upper/lower`). -/
theorem actuator_command_with_snap_limit
    (error integral deriv kp ki kd
     u_min u_max rate_limit jerk_limit snap_limit
     prev_result prev_prev_result prev_prev_prev_result : Real)
    (h_snap_nonneg : 0 ≤ snap_limit)
    (h_r_prev_upper :
       (prev_result - prev_prev_result) + jerk_limit ≤ rate_limit)
    (h_r_prev_lower :
       -(prev_result - prev_prev_result) + jerk_limit ≤ rate_limit)
    (h_prev_jerk_upper :
       ((prev_result - prev_prev_result)
         - (prev_prev_result - prev_prev_prev_result)) + snap_limit ≤ jerk_limit)
    (h_prev_jerk_lower :
       -((prev_result - prev_prev_result)
         - (prev_prev_result - prev_prev_prev_result)) + snap_limit ≤ jerk_limit)
    (h_interior_lower : rate_limit ≤ prev_result - u_min)
    (h_interior_upper : rate_limit ≤ u_max - prev_result) :
    u_min ≤ actuator_command_snap_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      prev_result prev_prev_result prev_prev_prev_result ∧
    actuator_command_snap_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      prev_result prev_prev_result prev_prev_prev_result ≤ u_max ∧
    MachLib.Real.abs (actuator_command_snap_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      prev_result prev_prev_result prev_prev_prev_result - prev_result)
      ≤ rate_limit ∧
    MachLib.Real.abs (actuator_command_snap_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      prev_result prev_prev_result prev_prev_prev_result
      - (prev_result + (prev_result - prev_prev_result))) ≤ jerk_limit ∧
    MachLib.Real.abs (actuator_command_snap_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      prev_result prev_prev_result prev_prev_prev_result
      - (prev_result + (prev_result - prev_prev_result)
                     + ((prev_result - prev_prev_result)
                         - (prev_prev_result - prev_prev_prev_result))))
      ≤ snap_limit := by
  -- Key window-geometry handles.
  have h_snap_lo_le_result := snap_lo_le_result
    error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
    prev_result prev_prev_result prev_prev_prev_result h_snap_nonneg
  have h_result_le_snap_hi := result_le_snap_hi
    error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
    prev_result prev_prev_result prev_prev_prev_result
  -- Containment ladder (snap ⊆ jerk ⊆ rate ⊆ band).
  have h_jerk_lo_le_snap_lo := jerk_lo_le_snap_lo
    prev_result prev_prev_result prev_prev_prev_result jerk_limit snap_limit
    h_prev_jerk_lower
  have h_snap_hi_le_jerk_hi := snap_hi_le_jerk_hi
    prev_result prev_prev_result prev_prev_prev_result jerk_limit snap_limit
    h_prev_jerk_upper
  -- v3-style ladder up: u_min ≤ jerk_lo (via r_prev_1), jerk_hi ≤ u_max,
  -- prev - rate ≤ jerk_lo, jerk_hi ≤ prev + rate.
  have h_umin_le_jerk_lo := umin_le_lo
    prev_result u_min rate_limit jerk_limit (prev_result - prev_prev_result)
    h_r_prev_lower h_interior_lower
  have h_jerk_hi_le_umax := hi_le_umax
    prev_result u_max rate_limit jerk_limit (prev_result - prev_prev_result)
    h_r_prev_upper h_interior_upper
  have h_prev_rl_le_jerk_lo := prev_minus_rl_le_lo
    prev_result rate_limit jerk_limit (prev_result - prev_prev_result)
    h_r_prev_lower
  have h_jerk_hi_le_prev_rl := hi_le_prev_plus_rl
    prev_result rate_limit jerk_limit (prev_result - prev_prev_result)
    h_r_prev_upper
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Ensures 1: band lower (u_min ≤ result).
    -- Chain: u_min ≤ jerk_lo ≤ snap_lo ≤ result.
    exact le_trans h_umin_le_jerk_lo
         (le_trans h_jerk_lo_le_snap_lo h_snap_lo_le_result)
  · -- Ensures 2: band upper (result ≤ u_max).
    -- Chain: result ≤ snap_hi ≤ jerk_hi ≤ u_max.
    exact le_trans h_result_le_snap_hi
         (le_trans h_snap_hi_le_jerk_hi h_jerk_hi_le_umax)
  · -- Ensures 3: rate bound.
    -- Chain: prev - rate ≤ jerk_lo ≤ snap_lo ≤ result ≤ snap_hi ≤ jerk_hi ≤ prev + rate.
    have h_hi := le_trans h_result_le_snap_hi
                 (le_trans h_snap_hi_le_jerk_hi h_jerk_hi_le_prev_rl)
    have h_lo := le_trans h_prev_rl_le_jerk_lo
                 (le_trans h_jerk_lo_le_snap_lo h_snap_lo_le_result)
    exact abs_le_of_bounds (sub_le_imp h_lo) (le_add_imp h_hi)
  · -- Ensures 4: jerk bound on (result - jerk_center).
    -- Chain: jerk_lo ≤ snap_lo ≤ result ≤ snap_hi ≤ jerk_hi.
    -- jerk_lo = jerk_center - jerk_limit;  jerk_hi = jerk_center + jerk_limit.
    have h_hi := le_trans h_result_le_snap_hi h_snap_hi_le_jerk_hi
    have h_lo := le_trans h_jerk_lo_le_snap_lo h_snap_lo_le_result
    exact abs_le_of_bounds (sub_le_imp h_lo) (le_add_imp h_hi)
  · -- Ensures 5: snap bound on (result - extrap).
    -- Direct from window geometry: snap_lo ≤ result ≤ snap_hi.
    exact abs_le_of_bounds (sub_le_imp h_snap_lo_le_result)
                           (le_add_imp h_result_le_snap_hi)

/-! ## Specialisation notes

v4 strictly STRENGTHENS the contract over v3 (adds the snap ensures)
while STRENGTHENING the preconditions (adds the prev_jerk loop
invariant `|prev_jerk| + snap ≤ jerk` and the ordering
`snap ≤ jerk ≤ rate`). The operating domain shrinks accordingly.

Deployment pattern (supervisor):
  v4 → v3 → v2 → v1 → v0
as the state envelope shrinks (closer to a rail, fewer constraints
trackable). All five kernels share the band ensures, and v2/v3/v4
also share the rate ensures, so mode-switching down the ladder is
invariant-safe.

## Operational interpretation

The snap constraint protects the airframe from the THIRD derivative
of actuator position — the rate-of-change of acceleration. This is
the "snap" or "jounce" in physics notation. In flight-control terms,
it limits the rate at which the surface can change its acceleration,
which is what couples the actuator to airframe structural modes,
fatigue accumulation, and aero-elastic resonance.

Real airliners DO ship snap-limited flight-control laws for sensitive
surfaces (elevators on T-tail aircraft, all-moving stabilizers,
fly-by-wire elevons on canard designs). v4 is the structural-engineering
gold-standard guard. -/

end AerospaceActuatorGuardSnap
end Forge
end MachLib
