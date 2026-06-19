import MachLib.Basic
import MachLib.Forge
import MachLib.Lemmas
import MachLib.Applications.GuardedActuatorCommand
import MachLib.Applications.ActuatorCommandWithinBand
import MachLib.Applications.ActuatorCommandBandWithRateLimit
import MachLib.Applications.ActuatorCommandWithJerkLimit
import MachLib.Applications.ActuatorCommandWithSnapLimit

/-!
# Forge kernel application — actuator-saturation guard (v5)

**v5 = v4 + CRACKLE limit**, the discrete-time fourth-difference
bound on actuator motion. v0 → v1 → v2 → v3 → v4 → v5.

Physics naming: position → velocity → acceleration → jerk → snap →
crackle → pop. Continuing the v3/v4 colloquial convention where
"jerk" = 2nd diff, "snap" = 3rd diff, "crackle" = 4th diff of
discrete-time actuator position.

## The kernel (from Forge, `actuator_command_with_crackle_limit.eml`)

```eml
fn actuator_command_with_crackle_limit(
    error, integral, deriv, kp, ki, kd,
    u_min, u_max, rate_limit, jerk_limit, snap_limit, crackle_limit,
    prev_result, prev_prev_result, prev_prev_prev_result, prev_prev_prev_prev_result) -> Real
    requires ... (P1-P14, see EML file)
    ensures  u_min ≤ result ≤ u_max
    ensures  abs(result - prev) ≤ rate_limit
    ensures  abs((result-prev) - r_prev_1) ≤ jerk_limit
    ensures  abs(((result-prev) - r_prev_1) - prev_jerk) ≤ snap_limit
    ensures  abs((((result-prev) - r_prev_1) - prev_jerk) - prev_snap) ≤ crackle_limit
{
    clamp(raw, extrap_v5 - crackle, extrap_v5 + crackle)
}
```
where `extrap_v5 := extrap_v4 + prev_snap = 4·prev - 6·prev_prev
                                            + 4·prev_prev_prev - prev_prev_prev_prev`
(constant-snap extrapolation of the last four positions).

## The single-clamp design (final layer)

Under v5 preconditions, the crackle window is a PROVEN subset of v4's
snap window, of v3's jerk window, of v2's rate window, of v1's band:

  `[extrap_v5 ± crackle]` (this window)
    `⊆ [extrap_v4 ± snap]`     (v4 window, by P12: `|prev_snap| + crackle ≤ snap`)
    `⊆ [jerk_center ± jerk]`   (v3 window, by P11: `|prev_jerk| + snap ≤ jerk`)
    `⊆ [prev ± rate]`          (v2 window, by P10: `|r_prev| + jerk ≤ rate`)
    `⊆ [u_min, u_max]`         (v1 band, by P13/P14 interior)

Five-level set containment; six ensures all follow from chained
`le_trans` calls of one-substitution-each v3 helpers + v4 helpers
(now publicly exported after this commit).

## Proof structure

For each ensures, a CHAIN of three `le_trans` calls:

- band lower:  `u_min ≤ jerk_lo ≤ snap_lo ≤ crackle_lo ≤ result`
- band upper:  `result ≤ crackle_hi ≤ snap_hi ≤ jerk_hi ≤ u_max`
- rate:        chain stops at `prev ± rate_limit`
- jerk:        chain stops at `jerk_center ± jerk_limit`
- snap:        chain stops at `extrap_v4 ± snap_limit`
- crackle:     direct from window geometry

The "extra layer" lemmas (`snap_lo_le_crackle_lo`,
`crackle_hi_le_snap_hi`) are one-line wrappers around v3's
`prev_minus_rl_le_lo` / `hi_le_prev_plus_rl` with the v5 substitution
`(prev → extrap_v4, r_prev → prev_snap, rate → snap_limit,
  jerk → crackle_limit)`.

## Reuse pattern across the ladder

| Layer (containment) | Substitution into v3 helper                                                       |
|---------------------|-----------------------------------------------------------------------------------|
| rate ⊆ band         | (prev → prev_result, r → r_prev_1, rate → rate, jerk → jerk_limit)                |
| jerk ⊆ rate         | (prev → prev_result, r → r_prev_1, rate → rate, jerk → jerk) — direct call        |
| snap ⊆ jerk         | (prev → jerk_center, r → prev_jerk, rate → jerk, jerk → snap)                     |
| crackle ⊆ snap      | (prev → extrap_v4, r → prev_snap, rate → snap, jerk → crackle)                    |

Same v3 helper, four substitutions, climbing the discrete-derivative
ladder. Each succeeding v_k file ADDS one wrapper lemma and chains it.
-/

namespace MachLib
namespace Forge
namespace AerospaceActuatorGuardCrackle

open MachLib
open MachLib.Real
open MachLib.Forge.AerospaceActuatorGuard
  (neg_neg neg_le_neg abs_le_of_bounds)
open MachLib.Forge.AerospaceActuatorGuardBandRate
  (le_min add_nonneg sub_nonneg_le le_add_nonneg max_le)
open MachLib.Forge.AerospaceActuatorGuardJerk
  (sub_le_imp le_add_imp hi_le_umax umin_le_lo
   prev_minus_rl_le_lo hi_le_prev_plus_rl)
open MachLib.Forge.AerospaceActuatorGuardSnap
  (jerk_lo_le_snap_lo snap_hi_le_jerk_hi)

/-! ## The kernel body

The body inlines extrap_v5 = extrap_v4 + prev_snap, where
  extrap_v4 := prev + (prev - prev_prev) + ((prev - prev_prev) - (prev_prev - prev_prev_prev))
  prev_snap := ((prev - prev_prev) - (prev_prev - prev_prev_prev))
              - ((prev_prev - prev_prev_prev) - (prev_prev_prev - prev_prev_prev_prev))
-/

noncomputable def actuator_command_crackle_body
    (error integral deriv kp ki kd
     u_min u_max rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real) : Real :=
  MachLib.Real.min
    (MachLib.Real.max
      (kp * error + ki * integral + kd * deriv)
      (prev_result + (prev_result - prev_prev_result)
                   + ((prev_result - prev_prev_result)
                       - (prev_prev_result - prev_prev_prev_result))
                   + (((prev_result - prev_prev_result)
                        - (prev_prev_result - prev_prev_prev_result))
                       - ((prev_prev_result - prev_prev_prev_result)
                           - (prev_prev_prev_result - prev_prev_prev_prev_result)))
                   - crackle_limit))
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))
                 + (((prev_result - prev_prev_result)
                      - (prev_prev_result - prev_prev_prev_result))
                     - ((prev_prev_result - prev_prev_prev_result)
                         - (prev_prev_prev_result - prev_prev_prev_prev_result)))
                 + crackle_limit)

/-! ## Window-bound lemmas (crackle clamp geometry) -/

private theorem crackle_lo_le_crackle_hi
    (prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result crackle_limit : Real)
    (h_crackle_nonneg : 0 ≤ crackle_limit) :
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))
                 + (((prev_result - prev_prev_result)
                      - (prev_prev_result - prev_prev_prev_result))
                     - ((prev_prev_result - prev_prev_prev_result)
                         - (prev_prev_prev_result - prev_prev_prev_prev_result))))
     - crackle_limit
    ≤
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))
                 + (((prev_result - prev_prev_result)
                      - (prev_prev_result - prev_prev_prev_result))
                     - ((prev_prev_result - prev_prev_prev_result)
                         - (prev_prev_prev_result - prev_prev_prev_prev_result))))
     + crackle_limit :=
  le_trans (sub_nonneg_le h_crackle_nonneg) (le_add_nonneg h_crackle_nonneg)

/-- crackle_lo ≤ result. -/
private theorem crackle_lo_le_result
    (error integral deriv kp ki kd
     u_min u_max rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real)
    (h_crackle_nonneg : 0 ≤ crackle_limit) :
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))
                 + (((prev_result - prev_prev_result)
                      - (prev_prev_result - prev_prev_prev_result))
                     - ((prev_prev_result - prev_prev_prev_result)
                         - (prev_prev_prev_result - prev_prev_prev_prev_result))))
     - crackle_limit ≤
    actuator_command_crackle_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      crackle_limit prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result := by
  unfold actuator_command_crackle_body
  apply le_min
  · exact le_max_right _ _
  · exact crackle_lo_le_crackle_hi
      prev_result prev_prev_result prev_prev_prev_result prev_prev_prev_prev_result
      crackle_limit h_crackle_nonneg

/-- result ≤ crackle_hi. -/
private theorem result_le_crackle_hi
    (error integral deriv kp ki kd
     u_min u_max rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real) :
    actuator_command_crackle_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      crackle_limit prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result ≤
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))
                 + (((prev_result - prev_prev_result)
                      - (prev_prev_result - prev_prev_prev_result))
                     - ((prev_prev_result - prev_prev_prev_result)
                         - (prev_prev_prev_result - prev_prev_prev_prev_result))))
     + crackle_limit := by
  unfold actuator_command_crackle_body
  exact min_le_right _ _

/-! ## Crackle ⊆ Snap containment (the only v5-specific containment)

By the SAME substitution into v3's helpers that v4 used for snap⊆jerk,
just one level up:

  v3 helper      | v4 substitution (snap⊆jerk)           | v5 substitution (crackle⊆snap)
  -------------- | ------------------------------------- | -----------------------------------
  prev_minus_rl  | prev→jerk_center, r→prev_jerk         | prev→extrap_v4, r→prev_snap
                 | rate→jerk_limit, jerk→snap_limit      | rate→snap_limit, jerk→crackle_limit

Same shape, one substitution up. -/

/-- snap_lo ≤ crackle_lo. -/
private theorem snap_lo_le_crackle_lo
    (prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result snap_limit crackle_limit : Real)
    (h_prev_snap_lower :
       -(((prev_result - prev_prev_result)
          - (prev_prev_result - prev_prev_prev_result))
         - ((prev_prev_result - prev_prev_prev_result)
            - (prev_prev_prev_result - prev_prev_prev_prev_result)))
       + crackle_limit ≤ snap_limit) :
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))) - snap_limit ≤
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))
                 + (((prev_result - prev_prev_result)
                      - (prev_prev_result - prev_prev_prev_result))
                     - ((prev_prev_result - prev_prev_prev_result)
                         - (prev_prev_prev_result - prev_prev_prev_prev_result))))
     - crackle_limit :=
  prev_minus_rl_le_lo
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result)))  -- "prev" = extrap_v4
    snap_limit                                                          -- "rate_limit" = snap_limit
    crackle_limit                                                       -- "jerk_limit" = crackle_limit
    (((prev_result - prev_prev_result)
       - (prev_prev_result - prev_prev_prev_result))
      - ((prev_prev_result - prev_prev_prev_result)
          - (prev_prev_prev_result - prev_prev_prev_prev_result)))      -- "r_prev" = prev_snap
    h_prev_snap_lower

/-- crackle_hi ≤ snap_hi. -/
private theorem crackle_hi_le_snap_hi
    (prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result snap_limit crackle_limit : Real)
    (h_prev_snap_upper :
       (((prev_result - prev_prev_result)
         - (prev_prev_result - prev_prev_prev_result))
        - ((prev_prev_result - prev_prev_prev_result)
           - (prev_prev_prev_result - prev_prev_prev_prev_result)))
       + crackle_limit ≤ snap_limit) :
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))
                 + (((prev_result - prev_prev_result)
                      - (prev_prev_result - prev_prev_prev_result))
                     - ((prev_prev_result - prev_prev_prev_result)
                         - (prev_prev_prev_result - prev_prev_prev_prev_result))))
     + crackle_limit ≤
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result))) + snap_limit :=
  hi_le_prev_plus_rl
    (prev_result + (prev_result - prev_prev_result)
                 + ((prev_result - prev_prev_result)
                     - (prev_prev_result - prev_prev_prev_result)))  -- "prev" = extrap_v4
    snap_limit                                                          -- "rate_limit" = snap_limit
    crackle_limit                                                       -- "jerk_limit" = crackle_limit
    (((prev_result - prev_prev_result)
       - (prev_prev_result - prev_prev_prev_result))
      - ((prev_prev_result - prev_prev_prev_result)
          - (prev_prev_prev_result - prev_prev_prev_prev_result)))      -- "r_prev" = prev_snap
    h_prev_snap_upper

/-! ## The main verify obligation -/

/-- **The main verify obligation**: band + rate + jerk + snap + crackle all hold.

Preconditions unpack each abs constraint into two halves (`*_upper`,
`*_lower`). Equivalent to the EML contract by `abs_le_iff`.

Six ensures, each discharged by a 4-link chain through window
containments. -/
theorem actuator_command_with_crackle_limit
    (error integral deriv kp ki kd
     u_min u_max rate_limit jerk_limit snap_limit crackle_limit
     prev_result prev_prev_result prev_prev_prev_result
     prev_prev_prev_prev_result : Real)
    (h_crackle_nonneg : 0 ≤ crackle_limit)
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
    (h_prev_snap_upper :
       (((prev_result - prev_prev_result)
         - (prev_prev_result - prev_prev_prev_result))
        - ((prev_prev_result - prev_prev_prev_result)
           - (prev_prev_prev_result - prev_prev_prev_prev_result)))
       + crackle_limit ≤ snap_limit)
    (h_prev_snap_lower :
       -(((prev_result - prev_prev_result)
          - (prev_prev_result - prev_prev_prev_result))
         - ((prev_prev_result - prev_prev_prev_result)
            - (prev_prev_prev_result - prev_prev_prev_prev_result)))
       + crackle_limit ≤ snap_limit)
    (h_interior_lower : rate_limit ≤ prev_result - u_min)
    (h_interior_upper : rate_limit ≤ u_max - prev_result) :
    u_min ≤ actuator_command_crackle_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      crackle_limit prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result ∧
    actuator_command_crackle_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      crackle_limit prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result ≤ u_max ∧
    MachLib.Real.abs (actuator_command_crackle_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      crackle_limit prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result - prev_result) ≤ rate_limit ∧
    MachLib.Real.abs (actuator_command_crackle_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      crackle_limit prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result
      - (prev_result + (prev_result - prev_prev_result))) ≤ jerk_limit ∧
    MachLib.Real.abs (actuator_command_crackle_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      crackle_limit prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result
      - (prev_result + (prev_result - prev_prev_result)
                     + ((prev_result - prev_prev_result)
                         - (prev_prev_result - prev_prev_prev_result))))
      ≤ snap_limit ∧
    MachLib.Real.abs (actuator_command_crackle_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
      crackle_limit prev_result prev_prev_result prev_prev_prev_result
      prev_prev_prev_prev_result
      - (prev_result + (prev_result - prev_prev_result)
                     + ((prev_result - prev_prev_result)
                         - (prev_prev_result - prev_prev_prev_result))
                     + (((prev_result - prev_prev_result)
                          - (prev_prev_result - prev_prev_prev_result))
                         - ((prev_prev_result - prev_prev_prev_result)
                             - (prev_prev_prev_result - prev_prev_prev_prev_result)))))
      ≤ crackle_limit := by
  -- Window-geometry handles
  have h_crackle_lo_le_result := crackle_lo_le_result
    error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
    crackle_limit prev_result prev_prev_result prev_prev_prev_result
    prev_prev_prev_prev_result h_crackle_nonneg
  have h_result_le_crackle_hi := result_le_crackle_hi
    error integral deriv kp ki kd u_min u_max rate_limit jerk_limit snap_limit
    crackle_limit prev_result prev_prev_result prev_prev_prev_result
    prev_prev_prev_prev_result
  -- Containment ladder (crackle ⊆ snap ⊆ jerk ⊆ rate ⊆ band)
  have h_snap_lo_le_crackle_lo := snap_lo_le_crackle_lo
    prev_result prev_prev_result prev_prev_prev_result prev_prev_prev_prev_result
    snap_limit crackle_limit h_prev_snap_lower
  have h_crackle_hi_le_snap_hi := crackle_hi_le_snap_hi
    prev_result prev_prev_result prev_prev_prev_result prev_prev_prev_prev_result
    snap_limit crackle_limit h_prev_snap_upper
  have h_jerk_lo_le_snap_lo := jerk_lo_le_snap_lo
    prev_result prev_prev_result prev_prev_prev_result jerk_limit snap_limit
    h_prev_jerk_lower
  have h_snap_hi_le_jerk_hi := snap_hi_le_jerk_hi
    prev_result prev_prev_result prev_prev_prev_result jerk_limit snap_limit
    h_prev_jerk_upper
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Ensures 1: band lower.
    -- Chain: u_min ≤ jerk_lo ≤ snap_lo ≤ crackle_lo ≤ result.
    exact le_trans h_umin_le_jerk_lo
         (le_trans h_jerk_lo_le_snap_lo
         (le_trans h_snap_lo_le_crackle_lo h_crackle_lo_le_result))
  · -- Ensures 2: band upper.
    -- Chain: result ≤ crackle_hi ≤ snap_hi ≤ jerk_hi ≤ u_max.
    exact le_trans h_result_le_crackle_hi
         (le_trans h_crackle_hi_le_snap_hi
         (le_trans h_snap_hi_le_jerk_hi h_jerk_hi_le_umax))
  · -- Ensures 3: rate bound.
    have h_hi := le_trans h_result_le_crackle_hi
                (le_trans h_crackle_hi_le_snap_hi
                (le_trans h_snap_hi_le_jerk_hi h_jerk_hi_le_prev_rl))
    have h_lo := le_trans h_prev_rl_le_jerk_lo
                (le_trans h_jerk_lo_le_snap_lo
                (le_trans h_snap_lo_le_crackle_lo h_crackle_lo_le_result))
    exact abs_le_of_bounds (sub_le_imp h_lo) (le_add_imp h_hi)
  · -- Ensures 4: jerk bound on (result - jerk_center).
    have h_hi := le_trans h_result_le_crackle_hi
                (le_trans h_crackle_hi_le_snap_hi h_snap_hi_le_jerk_hi)
    have h_lo := le_trans h_jerk_lo_le_snap_lo
                (le_trans h_snap_lo_le_crackle_lo h_crackle_lo_le_result)
    exact abs_le_of_bounds (sub_le_imp h_lo) (le_add_imp h_hi)
  · -- Ensures 5: snap bound on (result - extrap_v4).
    have h_hi := le_trans h_result_le_crackle_hi h_crackle_hi_le_snap_hi
    have h_lo := le_trans h_snap_lo_le_crackle_lo h_crackle_lo_le_result
    exact abs_le_of_bounds (sub_le_imp h_lo) (le_add_imp h_hi)
  · -- Ensures 6: crackle bound on (result - extrap_v5).
    -- Direct from window geometry.
    exact abs_le_of_bounds (sub_le_imp h_crackle_lo_le_result)
                           (le_add_imp h_result_le_crackle_hi)

/-! ## Closing notes

The v0 → v5 ladder closes the discrete-derivative chain at fourth
order. v5 has the strictest preconditions and the largest FPGA
footprint, but ALSO the strongest safety contract.

Each layer's proof is one application of v3's helpers with a
straightforward substitution. The structural pattern is:

  v_k+1 = v_k + one wrapper lemma + extra le_trans chain link

So the marginal cost per derivative order is fixed: ~80 lines of
Lean. v6 ("pop"-limit, fifth derivative) would follow the SAME
pattern with five prev registers and one more substitution layer.

The "structural decomposition" of the proof maps directly to the
hardware:  each successive derivative-order constraint adds one
adder + one register + one comparator-pair to the silicon, and one
substitution call + one `le_trans` link to the Lean proof. This is
why the ladder scales linearly in BOTH the engineering and the
mathematics: they have the same shape. -/

end AerospaceActuatorGuardCrackle
end Forge
end MachLib
