import MachLib.Basic
import MachLib.Forge
import MachLib.Lemmas
import MachLib.Applications.GuardedActuatorCommand
import MachLib.Applications.ActuatorCommandWithinBand
import MachLib.Applications.ActuatorCommandBandWithRateLimit
import MachLib.Applications.ActuatorCommandWithJerkLimit
import MachLib.Applications.ActuatorCommandWithSnapLimit
import MachLib.Applications.ActuatorCommandWithCrackleLimit

/-!
# Forge meta-kernel — degraded_mode_switcher

The DEPLOYMENT-LEVEL form of the v0..v5 ladder. The switcher checks
the runtime preconditions for each level and selects the STRONGEST
applicable kernel.

## Selection cascade

```
if v5 runtime preconditions hold:
    result = actuator_command_with_crackle_limit(...)
elif v4 runtime preconditions hold:
    result = actuator_command_with_snap_limit(...)
elif v3 runtime preconditions hold:
    result = actuator_command_with_jerk_limit(...)
else:
    result = actuator_command_band_with_rate_limit(...)    # v2 fallback
```

v2 is the unconditional fallback because the switcher requires
`u_min ≤ prev_result ≤ u_max` AND `0 ≤ rate_limit` AND
`u_min ≤ u_max` — exactly v2's preconditions. So v2 is ALWAYS
applicable, and the band+rate ensures hold.

## Guarantees

  Always:                            band, rate
  When v3 preconditions hold:        + jerk
  When v4 preconditions hold:        + snap
  When v5 preconditions hold:        + crackle

Mode-switching is invariant-safe: switching DOWN the ladder
(v5 → v4 → v3 → v2) never loses an ensures clause that the lower
kernel can also discharge.

## Proof structure

By case-analysis on the if-else cascade. In each branch, the body
equals the corresponding `actuator_command_v_k_body`, so v_k's
theorem applies. Each conditional ensures is discharged by invoking
the corresponding theorem.
-/

namespace MachLib
namespace Forge
namespace AerospaceActuatorGuardSwitcher

open MachLib
open MachLib.Real
open MachLib.Forge.AerospaceActuatorGuardBandRate
  (actuator_command_band_rate_body actuator_command_band_with_rate_limit)
open MachLib.Forge.AerospaceActuatorGuardJerk
  (actuator_command_jerk_body actuator_command_with_jerk_limit)
open MachLib.Forge.AerospaceActuatorGuardSnap
  (actuator_command_snap_body actuator_command_with_snap_limit)
open MachLib.Forge.AerospaceActuatorGuardCrackle
  (actuator_command_crackle_body actuator_command_with_crackle_limit)

/-! ## Runtime precondition predicates -/

/-- v3 runtime preconditions: r_prev loop invariant + interior. -/
def v3_runtime_pre
    (u_min u_max rate_limit jerk_limit prev_result prev_prev_result : Real) : Prop :=
  (prev_result - prev_prev_result) + jerk_limit ≤ rate_limit ∧
  -(prev_result - prev_prev_result) + jerk_limit ≤ rate_limit ∧
  rate_limit ≤ prev_result - u_min ∧
  rate_limit ≤ u_max - prev_result

/-- v4 runtime preconditions: v3 + prev_jerk loop invariant. -/
def v4_runtime_pre
    (u_min u_max rate_limit jerk_limit snap_limit
     prev_result prev_prev_result prev_prev_prev_result : Real) : Prop :=
  v3_runtime_pre u_min u_max rate_limit jerk_limit prev_result prev_prev_result ∧
  ((prev_result - prev_prev_result)
    - (prev_prev_result - prev_prev_prev_result)) + snap_limit ≤ jerk_limit ∧
  -((prev_result - prev_prev_result)
    - (prev_prev_result - prev_prev_prev_result)) + snap_limit ≤ jerk_limit

/-- v5 runtime preconditions: v4 + crackle non-neg + prev_snap loop invariant. -/
def v5_runtime_pre
    (u_min u_max rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real) : Prop :=
  v4_runtime_pre u_min u_max rate_limit jerk_limit snap_limit
                 prev_result prev_prev_result prev_prev_prev_result ∧
  0 ≤ crackle_limit ∧
  (((prev_result - prev_prev_result)
    - (prev_prev_result - prev_prev_prev_result))
   - ((prev_prev_result - prev_prev_prev_result)
      - (prev_prev_prev_result - prev_prev_prev_prev_result)))
   + crackle_limit ≤ snap_limit ∧
  -(((prev_result - prev_prev_result)
     - (prev_prev_result - prev_prev_prev_result))
    - ((prev_prev_result - prev_prev_prev_result)
       - (prev_prev_prev_result - prev_prev_prev_prev_result)))
   + crackle_limit ≤ snap_limit

/-! ## The switcher body -/

open Classical in
noncomputable def degraded_mode_switcher_body
    (error integral deriv kp ki kd
     u_min u_max
     rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real) : Real :=
  if v5_runtime_pre u_min u_max rate_limit jerk_limit snap_limit crackle_limit
        prev_result prev_prev_result prev_prev_prev_result
        prev_prev_prev_prev_result then
    actuator_command_crackle_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      crackle_limit prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result
  else if v4_runtime_pre u_min u_max rate_limit jerk_limit snap_limit
            prev_result prev_prev_result prev_prev_prev_result then
    actuator_command_snap_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      prev_result prev_prev_result prev_prev_prev_result
  else if v3_runtime_pre u_min u_max rate_limit jerk_limit
            prev_result prev_prev_result then
    actuator_command_jerk_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit
      prev_result prev_prev_result
  else
    actuator_command_band_rate_body
      error integral deriv kp ki kd u_min u_max rate_limit prev_result

/-! ## Main ensures: band always holds -/

theorem degraded_mode_switcher_band
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
      prev_prev_prev_prev_result ≤ u_max := by
  unfold degraded_mode_switcher_body
  by_cases h5 : v5_runtime_pre u_min u_max rate_limit jerk_limit snap_limit
                                crackle_limit prev_result prev_prev_result
                                prev_prev_prev_result prev_prev_prev_prev_result
  · rw [if_pos h5]
    have ⟨h_v4_pre, h_crackle_nn, h_ps_up, h_ps_lo⟩ := h5
    have ⟨h_v3_pre, h_pj_up, h_pj_lo⟩ := h_v4_pre
    have ⟨h_rp_up, h_rp_lo, h_int_lo, h_int_up⟩ := h_v3_pre
    have ⟨h_band_lo, h_band_hi, _, _, _, _⟩ :=
      actuator_command_with_crackle_limit
        error integral deriv kp ki kd u_min u_max
        rate_limit jerk_limit snap_limit crackle_limit
        prev_result prev_prev_result prev_prev_prev_result
        prev_prev_prev_prev_result h_crackle_nn
        h_rp_up h_rp_lo h_pj_up h_pj_lo h_ps_up h_ps_lo h_int_lo h_int_up
    exact ⟨h_band_lo, h_band_hi⟩
  · rw [if_neg h5]
    by_cases h4 : v4_runtime_pre u_min u_max rate_limit jerk_limit snap_limit
                                  prev_result prev_prev_result prev_prev_prev_result
    · rw [if_pos h4]
      have ⟨h_v3_pre, h_pj_up, h_pj_lo⟩ := h4
      have ⟨h_rp_up, h_rp_lo, h_int_lo, h_int_up⟩ := h_v3_pre
      have ⟨h_band_lo, h_band_hi, _, _, _⟩ :=
        actuator_command_with_snap_limit
          error integral deriv kp ki kd u_min u_max
          rate_limit jerk_limit snap_limit
          prev_result prev_prev_result prev_prev_prev_result
          h_snap_nonneg h_rp_up h_rp_lo h_pj_up h_pj_lo h_int_lo h_int_up
      exact ⟨h_band_lo, h_band_hi⟩
    · rw [if_neg h4]
      by_cases h3 : v3_runtime_pre u_min u_max rate_limit jerk_limit
                                    prev_result prev_prev_result
      · rw [if_pos h3]
        have ⟨h_rp_up, h_rp_lo, h_int_lo, h_int_up⟩ := h3
        have ⟨h_band_lo, h_band_hi, _, _⟩ :=
          actuator_command_with_jerk_limit
            error integral deriv kp ki kd u_min u_max
            rate_limit jerk_limit prev_result prev_prev_result
            h_jerk_nonneg h_rp_up h_rp_lo h_int_lo h_int_up
        exact ⟨h_band_lo, h_band_hi⟩
      · rw [if_neg h3]
        have ⟨h_band_lo, h_band_hi, _⟩ :=
          actuator_command_band_with_rate_limit
            error integral deriv kp ki kd u_min u_max rate_limit prev_result
            h_band h_rate_nonneg h_prev_ge_umin h_prev_le_umax
        exact ⟨h_band_lo, h_band_hi⟩

/-! ## Main ensures: rate always holds -/

theorem degraded_mode_switcher_rate
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
      prev_prev_prev_prev_result - prev_result) ≤ rate_limit := by
  unfold degraded_mode_switcher_body
  by_cases h5 : v5_runtime_pre u_min u_max rate_limit jerk_limit snap_limit
                                crackle_limit prev_result prev_prev_result
                                prev_prev_prev_result prev_prev_prev_prev_result
  · rw [if_pos h5]
    have ⟨h_v4_pre, h_crackle_nn, h_ps_up, h_ps_lo⟩ := h5
    have ⟨h_v3_pre, h_pj_up, h_pj_lo⟩ := h_v4_pre
    have ⟨h_rp_up, h_rp_lo, h_int_lo, h_int_up⟩ := h_v3_pre
    have ⟨_, _, h_rate, _, _, _⟩ :=
      actuator_command_with_crackle_limit
        error integral deriv kp ki kd u_min u_max
        rate_limit jerk_limit snap_limit crackle_limit
        prev_result prev_prev_result prev_prev_prev_result
        prev_prev_prev_prev_result h_crackle_nn
        h_rp_up h_rp_lo h_pj_up h_pj_lo h_ps_up h_ps_lo h_int_lo h_int_up
    exact h_rate
  · rw [if_neg h5]
    by_cases h4 : v4_runtime_pre u_min u_max rate_limit jerk_limit snap_limit
                                  prev_result prev_prev_result prev_prev_prev_result
    · rw [if_pos h4]
      have ⟨h_v3_pre, h_pj_up, h_pj_lo⟩ := h4
      have ⟨h_rp_up, h_rp_lo, h_int_lo, h_int_up⟩ := h_v3_pre
      have ⟨_, _, h_rate, _, _⟩ :=
        actuator_command_with_snap_limit
          error integral deriv kp ki kd u_min u_max
          rate_limit jerk_limit snap_limit
          prev_result prev_prev_result prev_prev_prev_result
          h_snap_nonneg h_rp_up h_rp_lo h_pj_up h_pj_lo h_int_lo h_int_up
      exact h_rate
    · rw [if_neg h4]
      by_cases h3 : v3_runtime_pre u_min u_max rate_limit jerk_limit
                                    prev_result prev_prev_result
      · rw [if_pos h3]
        have ⟨h_rp_up, h_rp_lo, h_int_lo, h_int_up⟩ := h3
        have ⟨_, _, h_rate, _⟩ :=
          actuator_command_with_jerk_limit
            error integral deriv kp ki kd u_min u_max
            rate_limit jerk_limit prev_result prev_prev_result
            h_jerk_nonneg h_rp_up h_rp_lo h_int_lo h_int_up
        exact h_rate
      · rw [if_neg h3]
        have ⟨_, _, h_rate⟩ :=
          actuator_command_band_with_rate_limit
            error integral deriv kp ki kd u_min u_max rate_limit prev_result
            h_band h_rate_nonneg h_prev_ge_umin h_prev_le_umax
        exact h_rate

/-! ## Conditional jerk ensures: when v3 preconditions hold -/

theorem degraded_mode_switcher_jerk_when_v3
    (error integral deriv kp ki kd
     u_min u_max
     rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real)
    (h_jerk_nonneg : 0 ≤ jerk_limit)
    (h_snap_nonneg : 0 ≤ snap_limit)
    (h_v3_pre : v3_runtime_pre u_min u_max rate_limit jerk_limit
                                prev_result prev_prev_result) :
    MachLib.Real.abs (degraded_mode_switcher_body
      error integral deriv kp ki kd u_min u_max
      rate_limit jerk_limit snap_limit crackle_limit
      prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result
      - (prev_result + (prev_result - prev_prev_result))) ≤ jerk_limit := by
  unfold degraded_mode_switcher_body
  by_cases h5 : v5_runtime_pre u_min u_max rate_limit jerk_limit snap_limit
                                crackle_limit prev_result prev_prev_result
                                prev_prev_prev_result prev_prev_prev_prev_result
  · rw [if_pos h5]
    have ⟨h_v4_pre, h_crackle_nn, h_ps_up, h_ps_lo⟩ := h5
    have ⟨h_v3_pre', h_pj_up, h_pj_lo⟩ := h_v4_pre
    have ⟨h_rp_up, h_rp_lo, h_int_lo, h_int_up⟩ := h_v3_pre'
    have ⟨_, _, _, h_jerk, _, _⟩ :=
      actuator_command_with_crackle_limit
        error integral deriv kp ki kd u_min u_max
        rate_limit jerk_limit snap_limit crackle_limit
        prev_result prev_prev_result prev_prev_prev_result
        prev_prev_prev_prev_result h_crackle_nn
        h_rp_up h_rp_lo h_pj_up h_pj_lo h_ps_up h_ps_lo h_int_lo h_int_up
    exact h_jerk
  · rw [if_neg h5]
    by_cases h4 : v4_runtime_pre u_min u_max rate_limit jerk_limit snap_limit
                                  prev_result prev_prev_result prev_prev_prev_result
    · rw [if_pos h4]
      have ⟨h_v3_pre', h_pj_up, h_pj_lo⟩ := h4
      have ⟨h_rp_up, h_rp_lo, h_int_lo, h_int_up⟩ := h_v3_pre'
      have ⟨_, _, _, h_jerk, _⟩ :=
        actuator_command_with_snap_limit
          error integral deriv kp ki kd u_min u_max
          rate_limit jerk_limit snap_limit
          prev_result prev_prev_result prev_prev_prev_result
          h_snap_nonneg h_rp_up h_rp_lo h_pj_up h_pj_lo h_int_lo h_int_up
      exact h_jerk
    · rw [if_neg h4]
      by_cases h3 : v3_runtime_pre u_min u_max rate_limit jerk_limit
                                    prev_result prev_prev_result
      · rw [if_pos h3]
        have ⟨h_rp_up, h_rp_lo, h_int_lo, h_int_up⟩ := h3
        have ⟨_, _, _, h_jerk⟩ :=
          actuator_command_with_jerk_limit
            error integral deriv kp ki kd u_min u_max
            rate_limit jerk_limit prev_result prev_prev_result
            h_jerk_nonneg h_rp_up h_rp_lo h_int_lo h_int_up
        exact h_jerk
      · -- ¬h3 contradicts h_v3_pre
        exact absurd h_v3_pre h3

/-! ## Conditional snap ensures: when v4 preconditions hold -/

theorem degraded_mode_switcher_snap_when_v4
    (error integral deriv kp ki kd
     u_min u_max
     rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real)
    (h_snap_nonneg : 0 ≤ snap_limit)
    (h_v4_pre : v4_runtime_pre u_min u_max rate_limit jerk_limit snap_limit
                                prev_result prev_prev_result prev_prev_prev_result) :
    MachLib.Real.abs (degraded_mode_switcher_body
      error integral deriv kp ki kd u_min u_max
      rate_limit jerk_limit snap_limit crackle_limit
      prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result
      - (prev_result + (prev_result - prev_prev_result)
                     + ((prev_result - prev_prev_result)
                         - (prev_prev_result - prev_prev_prev_result))))
      ≤ snap_limit := by
  unfold degraded_mode_switcher_body
  by_cases h5 : v5_runtime_pre u_min u_max rate_limit jerk_limit snap_limit
                                crackle_limit prev_result prev_prev_result
                                prev_prev_prev_result prev_prev_prev_prev_result
  · rw [if_pos h5]
    have ⟨h_v4_pre', h_crackle_nn, h_ps_up, h_ps_lo⟩ := h5
    have ⟨h_v3_pre', h_pj_up, h_pj_lo⟩ := h_v4_pre'
    have ⟨h_rp_up, h_rp_lo, h_int_lo, h_int_up⟩ := h_v3_pre'
    have ⟨_, _, _, _, h_snap, _⟩ :=
      actuator_command_with_crackle_limit
        error integral deriv kp ki kd u_min u_max
        rate_limit jerk_limit snap_limit crackle_limit
        prev_result prev_prev_result prev_prev_prev_result
        prev_prev_prev_prev_result h_crackle_nn
        h_rp_up h_rp_lo h_pj_up h_pj_lo h_ps_up h_ps_lo h_int_lo h_int_up
    exact h_snap
  · rw [if_neg h5]
    by_cases h4 : v4_runtime_pre u_min u_max rate_limit jerk_limit snap_limit
                                  prev_result prev_prev_result prev_prev_prev_result
    · rw [if_pos h4]
      have ⟨h_v3_pre', h_pj_up, h_pj_lo⟩ := h4
      have ⟨h_rp_up, h_rp_lo, h_int_lo, h_int_up⟩ := h_v3_pre'
      have ⟨_, _, _, _, h_snap⟩ :=
        actuator_command_with_snap_limit
          error integral deriv kp ki kd u_min u_max
          rate_limit jerk_limit snap_limit
          prev_result prev_prev_result prev_prev_prev_result
          h_snap_nonneg h_rp_up h_rp_lo h_pj_up h_pj_lo h_int_lo h_int_up
      exact h_snap
    · -- ¬h4 contradicts h_v4_pre
      exact absurd h_v4_pre h4

/-! ## Conditional crackle ensures: when v5 preconditions hold -/

theorem degraded_mode_switcher_crackle_when_v5
    (error integral deriv kp ki kd
     u_min u_max
     rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real)
    (h_v5_pre : v5_runtime_pre u_min u_max rate_limit jerk_limit snap_limit
                                crackle_limit prev_result prev_prev_result
                                prev_prev_prev_result prev_prev_prev_prev_result) :
    MachLib.Real.abs (degraded_mode_switcher_body
      error integral deriv kp ki kd u_min u_max
      rate_limit jerk_limit snap_limit crackle_limit
      prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result
      - (prev_result + (prev_result - prev_prev_result)
                     + ((prev_result - prev_prev_result)
                         - (prev_prev_result - prev_prev_prev_result))
                     + (((prev_result - prev_prev_result)
                          - (prev_prev_result - prev_prev_prev_result))
                         - ((prev_prev_result - prev_prev_prev_result)
                             - (prev_prev_prev_result - prev_prev_prev_prev_result)))))
      ≤ crackle_limit := by
  unfold degraded_mode_switcher_body
  by_cases h5 : v5_runtime_pre u_min u_max rate_limit jerk_limit snap_limit
                                crackle_limit prev_result prev_prev_result
                                prev_prev_prev_result prev_prev_prev_prev_result
  · rw [if_pos h5]
    have ⟨h_v4_pre', h_crackle_nn, h_ps_up, h_ps_lo⟩ := h5
    have ⟨h_v3_pre', h_pj_up, h_pj_lo⟩ := h_v4_pre'
    have ⟨h_rp_up, h_rp_lo, h_int_lo, h_int_up⟩ := h_v3_pre'
    have ⟨_, _, _, _, _, h_crackle⟩ :=
      actuator_command_with_crackle_limit
        error integral deriv kp ki kd u_min u_max
        rate_limit jerk_limit snap_limit crackle_limit
        prev_result prev_prev_result prev_prev_prev_result
        prev_prev_prev_prev_result h_crackle_nn
        h_rp_up h_rp_lo h_pj_up h_pj_lo h_ps_up h_ps_lo h_int_lo h_int_up
    exact h_crackle
  · -- ¬h5 contradicts h_v5_pre
    exact absurd h_v5_pre h5

/-! ## Closing notes

The switcher's 5 theorems (band, rate, jerk-conditional,
snap-conditional, crackle-conditional) cover the full v0..v5
ladder's ensures family, SELECTABLE BY RUNTIME STATE.

The supervisor can run THE SAME kernel always; the kernel SELF-
ADAPTS based on runtime state. No external mode-selection logic is
needed beyond the precondition checks already in the body.

This is the FORMAL SPECIFICATION of "supervised degradation" in
aerospace certified flight-control software: a single kernel
providing MONOTONICALLY DEGRADING guarantees as the state envelope
shrinks, with each guarantee level proven against the full DO-178C
four-corner traceability. -/

end AerospaceActuatorGuardSwitcher
end Forge
end MachLib
