import MachLib.Basic
import MachLib.Forge
import MachLib.Applications.GuardedActuatorCommand
import MachLib.Applications.ActuatorCommandWithinBand

/-!
# Forge kernel application — actuator-saturation guard (v2)

**v2 = v1 band + slew-rate limit**, the form that ships on certified
airliners. v0 (symmetric band) → v1 (asymmetric band) → v2 (band ∧
rate). Each version a strict generalisation of the previous, each
constructive in MachLib, each zero new axioms.

## The kernel (from Forge, `actuator_command_band_with_rate_limit.eml`)

```eml
fn actuator_command_band_with_rate_limit(
    error, integral, deriv, kp, ki, kd,
    u_min, u_max, rate_limit, prev_result) -> Real
    requires u_min <= u_max
    requires 0.0 <= rate_limit
    requires u_min <= prev_result
    requires prev_result <= u_max
    ensures u_min <= result
    ensures result <= u_max
    ensures abs(result - prev_result) <= rate_limit
{
    clamp(clamp(kp * error + ki * integral + kd * deriv,
                prev_result - rate_limit,
                prev_result + rate_limit),
          u_min, u_max)
}
```

The Forge backend lowers nested clamps to nested `min (max ...) ...`.
We pin the result and prove three ensures clauses separately.

## Why the rate bound holds — case analysis

Let `raw = kp*err + ki*int + kd*deriv`, `r1 = clamp(raw, prev - Δ, prev + Δ)`,
`result = clamp(r1, u_min, u_max)`. We want `|result - prev| ≤ Δ`.

After the rate clamp, `r1 ∈ [prev - Δ, prev + Δ]`. Then the band
clamp gives `result = min(max(r1, u_min), u_max)`.

  Case 1: `r1 ∈ [u_min, u_max]`. Then `result = r1`, so
          `|result - prev| = |r1 - prev| ≤ Δ`. ✓

  Case 2: `r1 > u_max`. Then `result = u_max`. Since
          `u_max ≥ prev` (precondition), `result - prev = u_max - prev ≥ 0`.
          And `r1 ≤ prev + Δ`, so `r1 > u_max` forces `prev + Δ > u_max`,
          i.e. `u_max - prev < Δ`. ✓

  Case 3: `r1 < u_min`. Then `result = u_min`. Since
          `prev ≥ u_min` (precondition), `prev - result = prev - u_min ≥ 0`.
          And `r1 ≥ prev - Δ`, so `r1 < u_min` forces `prev - Δ < u_min`,
          i.e. `prev - u_min < Δ`. ✓

Each case relies on the SAME `u_min ≤ prev ≤ u_max` precondition that
v0/v1 ensures already establish. So v2 self-bootstraps when applied
cyclically (prev_result from cycle N satisfies the band by v1's
ensures; v2 then preserves it AND adds the rate bound).
-/

namespace MachLib
namespace Forge
namespace AerospaceActuatorGuardBandRate

open MachLib
open MachLib.Real
open MachLib.Forge.AerospaceActuatorGuard
  (neg_neg neg_le_neg abs_le_of_bounds)
-- We intentionally do NOT open AerospaceActuatorGuardBand's redundant
-- copies of `le_max_*` / `min_le_*` / `le_min` — they collide with the
-- corresponding `MachLib.Real.*` versions already in scope via
-- `open MachLib.Real` above. We use the Real-namespaced ones.
-- The `le_min` from v0/v1 is also redundant; we reprove inline below
-- using `MachLib.Real.min` and the unfold pattern.

/-! ## Local helpers

`le_min` and the rate-add nonneg helper aren't exported from
`MachLib.Real`. Reproved here against the qualified `MachLib.Real.min`
to avoid the typeclass collision documented in
`feedback_machlib_min_unfold.md`. -/

/-- `c ≤ a → c ≤ b → c ≤ min a b`. GLB intro for `MachLib.Real.min`. -/
theorem le_min {a b c : Real} (hca : c ≤ a) (hcb : c ≤ b) :
    c ≤ MachLib.Real.min a b := by
  unfold MachLib.Real.min
  by_cases h : a ≤ b
  · rw [if_pos h]; exact hca
  · rw [if_neg h]; exact hcb

/-- `0 ≤ a → 0 ≤ b → 0 ≤ a + b`. Sum of non-negatives. -/
theorem add_nonneg {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  have step := add_le_add_left hb a
  -- step: a + 0 ≤ a + b
  rw [add_zero] at step
  exact le_trans ha step

/-- `a - b ≤ a` when `0 ≤ b`. Subtraction of a non-negative
decreases. Used in band/rate proofs. -/
theorem sub_nonneg_le {a b : Real} (hb : 0 ≤ b) : a - b ≤ a := by
  have h_neg : -b ≤ 0 := by
    have := neg_le_neg hb; rwa [neg_zero] at this
  have step := add_le_add_left h_neg a
  -- step: a + -b ≤ a + 0
  rw [add_zero] at step
  rw [sub_def]
  exact step

/-- `a ≤ a + b` when `0 ≤ b`. Adding a non-negative increases. -/
theorem le_add_nonneg {a b : Real} (hb : 0 ≤ b) : a ≤ a + b := by
  have step := add_le_add_left hb a
  -- step: a + 0 ≤ a + b
  rw [add_zero] at step
  exact step

/-- LUB intro for `MachLib.Real.max`: `a ≤ c → b ≤ c → max a b ≤ c`. -/
theorem max_le {a b c : Real} (hac : a ≤ c) (hbc : b ≤ c) :
    MachLib.Real.max a b ≤ c := by
  unfold MachLib.Real.max
  by_cases h : a ≤ b
  · rw [if_pos h]; exact hbc
  · rw [if_neg h]; exact hac

/-! ## The kernel body -/

/-- The PID + nested band/rate guard, matching the Forge emit. -/
noncomputable def actuator_command_band_rate_body
    (error integral deriv kp ki kd
     u_min u_max rate_limit prev_result : Real) : Real :=
  let raw := kp * error + ki * integral + kd * deriv
  MachLib.Real.min
    (MachLib.Real.max
      (MachLib.Real.min
        (MachLib.Real.max raw (prev_result - rate_limit))
        (prev_result + rate_limit))
      u_min)
    u_max

/-! ## Ensures 1 — band lower (`u_min ≤ result`) -/

theorem band_rate_lower
    (error integral deriv kp ki kd
     u_min u_max rate_limit prev_result : Real)
    (h_band : u_min ≤ u_max) :
    u_min ≤ actuator_command_band_rate_body
      error integral deriv kp ki kd u_min u_max rate_limit prev_result := by
  -- The outer is min(max(r1, u_min), u_max). For result ≥ u_min, we need
  -- both (i) max(r1, u_min) ≥ u_min and (ii) u_max ≥ u_min.
  apply le_min
  · -- max(r1, u_min) ≥ u_min: by le_max_right.
    exact le_max_right _ _
  · -- u_max ≥ u_min: from h_band.
    exact h_band

/-! ## Ensures 2 — band upper (`result ≤ u_max`) -/

theorem band_rate_upper
    (error integral deriv kp ki kd
     u_min u_max rate_limit prev_result : Real) :
    actuator_command_band_rate_body
      error integral deriv kp ki kd u_min u_max rate_limit prev_result
      ≤ u_max := by
  -- The outer is min(max(r1, u_min), u_max), so result ≤ u_max directly.
  exact min_le_right _ _

/-! ## Ensures 3 — rate bound (`|result - prev| ≤ rate_limit`)

This is the new content. The case analysis above shows the result
stays within `prev ± rate_limit`, using `u_min ≤ prev ≤ u_max` as
the precondition.

We prove two-sided bounds: `prev - rate_limit ≤ result` and
`result ≤ prev + rate_limit`, then combine via `abs_le_of_bounds`.
-/

/-- Helper: under the band invariant on `prev`, the rate-clamped
intermediate `r1 = clamp(raw, prev - Δ, prev + Δ)` stays in
`[prev - Δ, prev + Δ]`. -/
theorem r1_bounds
    (raw rate_limit prev_result : Real)
    (h_rate_nonneg : 0 ≤ rate_limit) :
    prev_result - rate_limit ≤
      MachLib.Real.min (MachLib.Real.max raw (prev_result - rate_limit))
                       (prev_result + rate_limit) ∧
    MachLib.Real.min (MachLib.Real.max raw (prev_result - rate_limit))
                     (prev_result + rate_limit) ≤ prev_result + rate_limit := by
  refine ⟨?_, ?_⟩
  · -- (prev - Δ) ≤ min(max(raw, prev - Δ), prev + Δ).
    -- Use le_min: (prev - Δ) ≤ max(raw, prev - Δ) AND (prev - Δ) ≤ (prev + Δ).
    apply le_min
    · exact le_max_right _ _
    · -- prev - Δ ≤ prev + Δ. Chain: prev - Δ ≤ prev (sub_nonneg_le) and
      -- prev ≤ prev + Δ (le_add_nonneg).
      exact le_trans (sub_nonneg_le h_rate_nonneg)
                     (le_add_nonneg h_rate_nonneg)
  · -- min(...) ≤ prev + Δ — trivial by min_le_right.
    exact min_le_right _ _

/-- Lower rate bound: `prev_result - rate_limit ≤ result`. -/
theorem band_rate_lower_rate
    (error integral deriv kp ki kd
     u_min u_max rate_limit prev_result : Real)
    (h_rate_nonneg : 0 ≤ rate_limit)
    (h_prev_ge_umin : u_min ≤ prev_result)
    (h_prev_le_umax : prev_result ≤ u_max) :
    prev_result - rate_limit ≤
      actuator_command_band_rate_body
        error integral deriv kp ki kd u_min u_max rate_limit prev_result := by
  -- Outer is min(max(r1, u_min), u_max). Need: prev - Δ ≤ min(max(r1, u_min), u_max).
  -- Use le_min: prev - Δ ≤ max(r1, u_min) AND prev - Δ ≤ u_max.
  apply le_min
  · -- prev - Δ ≤ max(r1, u_min). Sufficient: prev - Δ ≤ r1 (then by le_max_left).
    -- Use r1_bounds.1: prev - Δ ≤ r1.
    have ⟨h_r1_lo, _⟩ := r1_bounds (kp * error + ki * integral + kd * deriv)
                                    rate_limit prev_result h_rate_nonneg
    -- Goal: prev - Δ ≤ max(r1, u_min).  By le_max_left of r1 inside max.
    exact le_trans h_r1_lo (le_max_left _ _)
  · -- prev - Δ ≤ u_max: from prev ≤ u_max and prev - Δ ≤ prev (since Δ ≥ 0).
    exact le_trans (sub_nonneg_le h_rate_nonneg) h_prev_le_umax

/-- Upper rate bound: `result ≤ prev_result + rate_limit`. -/
theorem band_rate_upper_rate
    (error integral deriv kp ki kd
     u_min u_max rate_limit prev_result : Real)
    (h_rate_nonneg : 0 ≤ rate_limit)
    (h_prev_ge_umin : u_min ≤ prev_result) :
    actuator_command_band_rate_body
      error integral deriv kp ki kd u_min u_max rate_limit prev_result
      ≤ prev_result + rate_limit := by
  -- Outer is min(max(r1, u_min), u_max). Need: that ≤ prev + Δ.
  -- Step 1: result ≤ max(r1, u_min)   (by min_le_left).
  -- Step 2: max(r1, u_min) ≤ prev + Δ — sufficient: r1 ≤ prev + Δ AND u_min ≤ prev + Δ.
  have h_r1_hi := (r1_bounds (kp * error + ki * integral + kd * deriv)
                              rate_limit prev_result h_rate_nonneg).2
  -- u_min ≤ prev (precondition); prev ≤ prev + Δ (Δ ≥ 0).
  have h_prev_le_prev_plus_Δ : prev_result ≤ prev_result + rate_limit := by
    have step := add_le_add_left h_rate_nonneg prev_result
    rw [add_zero] at step
    exact step
  have h_umin_le_prev_plus_Δ : u_min ≤ prev_result + rate_limit :=
    le_trans h_prev_ge_umin h_prev_le_prev_plus_Δ
  -- Now build: max(r1, u_min) ≤ prev + Δ using max_le.
  have h_max_le : MachLib.Real.max
      (MachLib.Real.min
        (MachLib.Real.max
          (kp * error + ki * integral + kd * deriv)
          (prev_result - rate_limit))
        (prev_result + rate_limit))
      u_min ≤ prev_result + rate_limit :=
    max_le h_r1_hi h_umin_le_prev_plus_Δ
  -- result = min(max(r1, u_min), u_max) ≤ max(r1, u_min) ≤ prev + Δ.
  exact le_trans (min_le_left _ _) h_max_le

/-! ## The main verify obligation -/

/-- **The main verify obligation**: combined band + rate bound. -/
theorem actuator_command_band_with_rate_limit
    (error integral deriv kp ki kd
     u_min u_max rate_limit prev_result : Real)
    (h_band : u_min ≤ u_max)
    (h_rate_nonneg : 0 ≤ rate_limit)
    (h_prev_ge_umin : u_min ≤ prev_result)
    (h_prev_le_umax : prev_result ≤ u_max) :
    u_min ≤ actuator_command_band_rate_body
      error integral deriv kp ki kd u_min u_max rate_limit prev_result ∧
    actuator_command_band_rate_body
      error integral deriv kp ki kd u_min u_max rate_limit prev_result
      ≤ u_max ∧
    MachLib.Real.abs (actuator_command_band_rate_body
      error integral deriv kp ki kd u_min u_max rate_limit prev_result
      - prev_result) ≤ rate_limit := by
  refine ⟨band_rate_lower _ _ _ _ _ _ _ _ _ _ h_band,
          band_rate_upper _ _ _ _ _ _ _ _ _ _,
          ?_⟩
  -- Rate bound via abs_le_of_bounds applied to (result - prev).
  -- We have:
  --   prev - rate_limit ≤ result      (band_rate_lower_rate)
  --   result            ≤ prev + rate_limit  (band_rate_upper_rate)
  -- Rewriting:
  --   -rate_limit ≤ result - prev
  --    result - prev ≤ rate_limit
  have h_lo := band_rate_lower_rate
    error integral deriv kp ki kd u_min u_max rate_limit prev_result
    h_rate_nonneg h_prev_ge_umin h_prev_le_umax
  have h_hi := band_rate_upper_rate
    error integral deriv kp ki kd u_min u_max rate_limit prev_result
    h_rate_nonneg h_prev_ge_umin
  -- h_lo:  prev_result - rate_limit ≤ result
  -- h_hi:  result ≤ prev_result + rate_limit
  -- We want abs(result - prev) ≤ rate_limit, i.e.:
  --   -rate_limit ≤ result - prev      (from h_lo by subtracting prev from both sides)
  --   result - prev ≤ rate_limit       (from h_hi)
  -- We want abs(result - prev_result) ≤ rate_limit. By abs_le_of_bounds,
  -- this follows from -rate_limit ≤ result - prev_result ≤ rate_limit.
  --
  -- The algebra is straightforward but MachLib's Real doesn't have a
  -- linear-arithmetic tactic, so we work in tiny algebraic steps via
  -- the helper `add_neg_self_eq_zero`-style identities.

  -- Helper algebraic facts we'll use:
  --   (1) x - prev ≤ rate_limit  ↔  x ≤ prev + rate_limit
  --   (2) -rate_limit ≤ x - prev ↔ prev + (-rate_limit) ≤ x
  --                            ↔  prev - rate_limit ≤ x

  -- (1): result ≤ prev + rate_limit (h_hi) ⇒ result - prev ≤ rate_limit.
  -- Add -prev_result on the LEFT of both sides of h_hi.
  have h_hi' : actuator_command_band_rate_body
      error integral deriv kp ki kd u_min u_max rate_limit prev_result
        - prev_result ≤ rate_limit := by
    have step := add_le_add_left h_hi (-prev_result)
    -- step: -prev + result ≤ -prev + (prev + Δ)
    -- Simplify RHS: -prev + (prev + Δ) = (-prev + prev) + Δ = 0 + Δ = Δ.
    rw [← add_assoc, add_comm (-prev_result) prev_result, add_neg, zero_add]
      at step
    -- step: -prev + result ≤ Δ
    -- Convert LHS to `result - prev`: result - prev = result + -prev = -prev + result
    show actuator_command_band_rate_body _ _ _ _ _ _ _ _ _ _
          - prev_result ≤ rate_limit
    rw [sub_def, add_comm (actuator_command_band_rate_body _ _ _ _ _ _ _ _ _ _)
                          (-prev_result)]
    exact step
  -- (2): prev_result - rate_limit ≤ result (h_lo) ⇒ -rate_limit ≤ result - prev.
  have h_lo' : -rate_limit ≤
      actuator_command_band_rate_body
        error integral deriv kp ki kd u_min u_max rate_limit prev_result
        - prev_result := by
    have step := add_le_add_left h_lo (-prev_result)
    -- step: -prev + (prev - Δ) ≤ -prev + result
    -- Simplify LHS: -prev + (prev - Δ) = -prev + (prev + -Δ) = (-prev + prev) + -Δ = -Δ
    rw [sub_def, ← add_assoc, add_comm (-prev_result) prev_result, add_neg,
        zero_add] at step
    -- step: -Δ ≤ -prev + result
    -- Convert RHS to `result - prev`:
    show -rate_limit ≤ actuator_command_band_rate_body _ _ _ _ _ _ _ _ _ _
                       - prev_result
    rw [sub_def, add_comm (actuator_command_band_rate_body _ _ _ _ _ _ _ _ _ _)
                          (-prev_result)]
    exact step
  exact abs_le_of_bounds h_lo' h_hi'

/-! ## v1 → v2 specialisation check

At `rate_limit → ∞` (or whenever the rate constraint is non-binding),
v2 collapses to v1 — `result` is bounded only by the band. This isn't
provable as a theorem because we can't quantify "rate_limit ≥ band
width" inside the predicate, but the band-only ensures clauses
(`band_rate_lower` and `band_rate_upper`) ARE the v1 ensures. v2
strictly adds the rate bound; v1 falls out by projection. -/

end AerospaceActuatorGuardBandRate
end Forge
end MachLib
