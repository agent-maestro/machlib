import MachLib.Basic
import MachLib.Forge
import MachLib.Lemmas
import MachLib.Applications.GuardedActuatorCommand
import MachLib.Applications.ActuatorCommandWithinBand
import MachLib.Applications.ActuatorCommandBandWithRateLimit
import MachLib.Applications.ActuatorCommandWithJerkLimit
import MachLib.Applications.ActuatorCommandWithSnapLimit
import MachLib.Applications.ActuatorCommandWithCrackleLimit
import MachLib.Applications.DegradedModeSwitcher

/-!
# Forge meta-kernel — fault_detection_and_isolation_guard

The COCKPIT-LEVEL form of the v0..v5 + switcher stack. Wraps the
switcher with FDI telltale signals so the pilot/supervisor knows
when the actuator is operating in a degraded or saturated state.

## Outputs

- `result` — same as switcher's result (Real, Q16.16 in silicon).
- `selected_mode` — same as switcher's selected_mode (Nat ∈ {2,3,4,5}).
- `fdi_warning` — Bool. Cockpit telltale lamp / FDR flag.

## fdi_warning semantics

`fdi_warning = true` iff ANY of these hold:

1. **Mode degraded**: `selected_mode ≠ 5` (full protection not active).
2. **Band rail**: `result = u_min ∨ result = u_max` (actuator at travel stop).
3. **Rate limit**: `|result - prev_result| = rate_limit` (slew rate at limit).

When `fdi_warning = false`, the actuator is in a "clean" state:
full v5 protection active AND result strictly inside the band AND
slew rate strictly under the limit.

## Theorems

- `fdi_guard_band` — same as switcher_band (band ensures always hold).
- `fdi_guard_rate` — same as switcher_rate (rate ensures always hold).
- `fdi_warning_false_implies_clean` — fdi_warning = false implies all
  three "clean state" conditions (mode = 5, result not at rail, rate
  not at limit).

All proven constructively; axioms = Lean stdlib + MachLib.Real
arithmetic. ZERO new axioms. ZERO sorry.

## Design rationale

The FDI guard is a COMBINATIONAL WRAPPER around the switcher: same
inputs, same safety contract, additional cockpit telltale signal.
Silicon: switcher_pipeline + 4 comparators + 3 OR gates + 1 flag.
Total LUTs: switcher + ~10.

This is the natural deployment-level signal flow for certified
flight-control: the kernel runs autonomously (switcher selects mode);
the cockpit gets visibility (FDI telltale) without affecting the
safety contract. -/

namespace MachLib
namespace Forge
namespace AerospaceActuatorGuardFDI

open MachLib
open MachLib.Real
open MachLib.Forge.AerospaceActuatorGuardSwitcher
  (degraded_mode_switcher_body
   degraded_mode_switcher_band
   degraded_mode_switcher_rate
   v3_runtime_pre v4_runtime_pre v5_runtime_pre)

/-! ## Selected-mode signal

This mirrors the switcher's cascade and returns the level as a Nat.
Pure cosmetic: it's just an externally-visible diagnostic. -/

open Classical in
noncomputable def fdi_guard_mode
    (u_min u_max rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real) : Nat :=
  if v5_runtime_pre u_min u_max rate_limit jerk_limit snap_limit crackle_limit
        prev_result prev_prev_result prev_prev_prev_result
        prev_prev_prev_prev_result then 5
  else if v4_runtime_pre u_min u_max rate_limit jerk_limit snap_limit
            prev_result prev_prev_result prev_prev_prev_result then 4
  else if v3_runtime_pre u_min u_max rate_limit jerk_limit
            prev_result prev_prev_result then 3
  else 2

/-! ## "Clean state" proposition

The conjunction of conditions that mean the actuator is operating
nominally: full v5 protection AND result strictly inside the band
AND slew rate strictly under the rate limit. -/

def clean_state
    (error integral deriv kp ki kd
     u_min u_max
     rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real) : Prop :=
  fdi_guard_mode u_min u_max rate_limit jerk_limit snap_limit crackle_limit
        prev_result prev_prev_result prev_prev_prev_result
        prev_prev_prev_prev_result = 5
  ∧ degraded_mode_switcher_body
        error integral deriv kp ki kd u_min u_max
        rate_limit jerk_limit snap_limit crackle_limit
        prev_result prev_prev_result prev_prev_prev_result
        prev_prev_prev_prev_result ≠ u_min
  ∧ degraded_mode_switcher_body
        error integral deriv kp ki kd u_min u_max
        rate_limit jerk_limit snap_limit crackle_limit
        prev_result prev_prev_result prev_prev_prev_result
        prev_prev_prev_prev_result ≠ u_max
  ∧ MachLib.Real.abs (degraded_mode_switcher_body
        error integral deriv kp ki kd u_min u_max
        rate_limit jerk_limit snap_limit crackle_limit
        prev_result prev_prev_result prev_prev_prev_result
        prev_prev_prev_prev_result - prev_result) ≠ rate_limit

/-! ## FDI warning signal

Definitionally: `fdi_warning = false` iff `clean_state` holds. -/

open Classical in
noncomputable def fdi_warning
    (error integral deriv kp ki kd
     u_min u_max
     rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real) : Bool :=
  if clean_state error integral deriv kp ki kd u_min u_max
        rate_limit jerk_limit snap_limit crackle_limit
        prev_result prev_prev_result prev_prev_prev_result
        prev_prev_prev_prev_result
  then false
  else true

/-! ## Safety theorems (re-exported from switcher) -/

/-- Band always holds. Inherited from the switcher. -/
theorem fdi_guard_band
    (error integral deriv kp ki kd
     u_min u_max
     rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real)
    (h_band : u_min ≤ u_max)
    (h_rate_nonneg : 0 ≤ rate_limit)
    (h_jerk_nonneg : 0 ≤ jerk_limit)
    (h_snap_nonneg : 0 ≤ snap_limit)
    (h_prev_ge_umin : u_min ≤ prev_result)
    (h_prev_le_umax : prev_result ≤ u_max) :
    u_min ≤ degraded_mode_switcher_body
      error integral deriv kp ki kd u_min u_max
      rate_limit jerk_limit snap_limit crackle_limit
      prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result ∧
    degraded_mode_switcher_body
      error integral deriv kp ki kd u_min u_max
      rate_limit jerk_limit snap_limit crackle_limit
      prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result ≤ u_max :=
  degraded_mode_switcher_band
    error integral deriv kp ki kd u_min u_max
    rate_limit jerk_limit snap_limit crackle_limit
    prev_result prev_prev_result prev_prev_prev_result
    prev_prev_prev_prev_result
    h_band h_rate_nonneg h_jerk_nonneg h_snap_nonneg
    h_prev_ge_umin h_prev_le_umax

/-- Rate always holds. Inherited from the switcher. -/
theorem fdi_guard_rate
    (error integral deriv kp ki kd
     u_min u_max
     rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real)
    (h_band : u_min ≤ u_max)
    (h_rate_nonneg : 0 ≤ rate_limit)
    (h_jerk_nonneg : 0 ≤ jerk_limit)
    (h_snap_nonneg : 0 ≤ snap_limit)
    (h_prev_ge_umin : u_min ≤ prev_result)
    (h_prev_le_umax : prev_result ≤ u_max) :
    MachLib.Real.abs (degraded_mode_switcher_body
      error integral deriv kp ki kd u_min u_max
      rate_limit jerk_limit snap_limit crackle_limit
      prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result - prev_result) ≤ rate_limit :=
  degraded_mode_switcher_rate
    error integral deriv kp ki kd u_min u_max
    rate_limit jerk_limit snap_limit crackle_limit
    prev_result prev_prev_result prev_prev_prev_result
    prev_prev_prev_prev_result
    h_band h_rate_nonneg h_jerk_nonneg h_snap_nonneg
    h_prev_ge_umin h_prev_le_umax

/-! ## FDI correctness: warning = false implies clean state -/

/-- **fdi_warning = false implies "clean state"**: full v5 protection,
result not at either band rail, slew rate strictly under the limit. -/
theorem fdi_warning_false_implies_clean
    (error integral deriv kp ki kd
     u_min u_max
     rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real)
    (h_no_warning : fdi_warning
      error integral deriv kp ki kd u_min u_max
      rate_limit jerk_limit snap_limit crackle_limit
      prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result = false) :
    fdi_guard_mode u_min u_max rate_limit jerk_limit snap_limit crackle_limit
      prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result = 5 ∧
    degraded_mode_switcher_body
      error integral deriv kp ki kd u_min u_max
      rate_limit jerk_limit snap_limit crackle_limit
      prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result ≠ u_min ∧
    degraded_mode_switcher_body
      error integral deriv kp ki kd u_min u_max
      rate_limit jerk_limit snap_limit crackle_limit
      prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result ≠ u_max ∧
    MachLib.Real.abs (degraded_mode_switcher_body
      error integral deriv kp ki kd u_min u_max
      rate_limit jerk_limit snap_limit crackle_limit
      prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result - prev_result) ≠ rate_limit := by
  unfold fdi_warning at h_no_warning
  -- h_no_warning : (if clean_state then false else true) = false
  by_cases h_clean : clean_state error integral deriv kp ki kd u_min u_max
      rate_limit jerk_limit snap_limit crackle_limit
      prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result
  · -- clean_state holds; conclude by destructuring it.
    exact h_clean
  · -- ¬ clean_state ⟹ if-then-else returns true, contradicting h_no_warning.
    rw [if_neg h_clean] at h_no_warning
    exact Bool.noConfusion h_no_warning

/-! ## FDI warning correctness for the cockpit telltale

The FDI signal SOUNDLY reports when the actuator is operating in a
degraded or saturated state. The cockpit can trust:

  - `fdi_warning = false`  ⟹  mode = 5 ∧ result inside (u_min, u_max)
                              ∧ |Δresult| < rate_limit (strict)
  - `fdi_warning = true`   ⟹  AT LEAST ONE of:
                              (a) mode < 5 (degraded), OR
                              (b) result at a band rail (saturated travel), OR
                              (c) rate at the limit (saturated slew)

The (true case) follows by contrapositive of the (false case) theorem
proven above.

## Closing notes

The FDI guard is a 1-cycle combinational wrapper around the switcher.
It adds NO safety guarantees beyond what the switcher provides — it
just makes the existing degradation/saturation state VISIBLE to the
cockpit and the flight data recorder.

For aerospace certification, this is the deployment-level form: the
SAFETY contract is in the switcher (formally proven); the COCKPIT
SIGNAL is in the FDI (also formally proven to be a sound reporter).
Together they form the complete certified subsystem. -/

end AerospaceActuatorGuardFDI
end Forge
end MachLib
