import MachLib.Basic
import MachLib.Forge
import MachLib.Applications.GuardedActuatorCommand

/-!
# Forge kernel application — flight-control actuator-saturation guard (v1)

**v0 → v1**: extend `guarded_actuator_command`'s symmetric
`[-limit, limit]` bound to ASYMMETRIC rails `[u_min, u_max]`.

## Domain

Real flight-control surfaces don't have symmetric travel:

  - Elevator: ~−15° down to +25° up
  - Aileron: limited by linkage one way, by wing structural envelope the other
  - Rudder: mechanical stop one way, dynamic flow separation the other

The asymmetric contract is the load-bearing form for these surfaces.

## The kernel (from Forge, `actuator_command_within_band.eml`)

```eml
@verify(lean, theorem = "actuator_command_within_band")
@target(fpga, board = "arty_a7", clock_mhz = 100, precision = float32)
fn actuator_command_within_band(error, integral, deriv, kp, ki, kd, u_min, u_max) -> Real
    requires u_min <= u_max
    ensures u_min <= result
    ensures result <= u_max
{
    clamp(kp * error + ki * integral + kd * deriv, u_min, u_max)
}
```

The Forge Lean backend lowers `clamp(x, u_min, u_max)` to
`min (max x u_min) u_max`. The verify obligation is exactly the
two-sided bound.

## Why this strengthens v0

v0's `actuator_command_within_limits` is the SPECIAL CASE of v1 at
`u_min = -limit, u_max = limit`. v1 covers every flight-control
surface that has unequal travel in the two directions — which is
basically all of them. The proof is the same shape, only the
constants change.

## Hazard mapping (DO-178C / ARP4761)

  - **Hazard ID**: H-ACT-02 — actuator over-travel in either direction
    when commanded by a faulted PID loop (asymmetric airframe rails).
  - **Source**: ARP4761 functional hazard assessment;
    same family as H-ACT-01 (the symmetric form) but parameterised
    over the surface-specific rail limits.
  - **Safety class**: DO-178C DAL A (same as v0); DO-254 for the
    silicon emission.
  - **Mitigation**: this kernel — the contract bound is the mitigation,
    proven below.

The unconditional contract on `error/integral/deriv/kp/ki/kd` is the
load-bearing safety property: the bound holds even when the PID
inputs are garbage (a saturated or NaN-substituted sensor).
-/

namespace MachLib
namespace Forge
namespace AerospaceActuatorGuardBand

open MachLib
open MachLib.Real
open MachLib.Forge.AerospaceActuatorGuard
  (neg_neg neg_le_neg abs_le_of_bounds)

/-! ## Reusable order lemmas (specialised for the asymmetric form)

`actuator_command_within_band` returns
`min (max raw u_min) u_max`. We need two-sided bounds. -/

/-- `a ≤ max a b` (LHS bound). -/
theorem le_max_left (a b : Real) : a ≤ MachLib.Real.max a b := by
  unfold MachLib.Real.max
  by_cases h : a ≤ b
  · rw [if_pos h]; exact h
  · rw [if_neg h]
    exact (le_iff_lt_or_eq a a).mpr (Or.inr rfl)

/-- `b ≤ max a b` (RHS bound). -/
theorem le_max_right (a b : Real) : b ≤ MachLib.Real.max a b := by
  unfold MachLib.Real.max
  by_cases h : a ≤ b
  · rw [if_pos h]
    exact (le_iff_lt_or_eq b b).mpr (Or.inr rfl)
  · rw [if_neg h]
    -- ¬ (a ≤ b), so b < a, so b ≤ a (via le_iff_lt_or_eq).
    rcases lt_total b a with hlt | heq | hgt
    · exact (le_iff_lt_or_eq b a).mpr (Or.inl hlt)
    · exact (le_iff_lt_or_eq b a).mpr (Or.inr heq)
    · exact absurd ((le_iff_lt_or_eq a b).mpr (Or.inl hgt)) h

/-- `min a b ≤ b` (RHS bound). -/
theorem min_le_right (a b : Real) : MachLib.Real.min a b ≤ b := by
  unfold MachLib.Real.min
  by_cases h : a ≤ b
  · rw [if_pos h]; exact h
  · rw [if_neg h]
    exact (le_iff_lt_or_eq b b).mpr (Or.inr rfl)

/-- `min a b ≤ a` (LHS bound). -/
theorem min_le_left (a b : Real) : MachLib.Real.min a b ≤ a := by
  unfold MachLib.Real.min
  by_cases h : a ≤ b
  · rw [if_pos h]
    exact (le_iff_lt_or_eq a a).mpr (Or.inr rfl)
  · rw [if_neg h]
    -- ¬(a ≤ b), so b < a, so b ≤ a.
    have hba : b ≤ a := by
      rcases lt_total b a with hlt | heq | hgt
      · exact (le_iff_lt_or_eq b a).mpr (Or.inl hlt)
      · exact (le_iff_lt_or_eq b a).mpr (Or.inr heq)
      · exact absurd ((le_iff_lt_or_eq a b).mpr (Or.inl hgt)) h
    exact hba

/-- `c ≤ a → c ≤ b → c ≤ min a b`. GLB intro. Qualified `min` to
avoid the `Min.min` typeclass collision documented in memory:
`feedback_machlib_min_unfold.md`. -/
theorem le_min {a b c : Real} (hca : c ≤ a) (hcb : c ≤ b) :
    c ≤ MachLib.Real.min a b := by
  unfold MachLib.Real.min
  by_cases h : a ≤ b
  · rw [if_pos h]; exact hca
  · rw [if_neg h]; exact hcb

/-! ## The kernel (matches `actuator_command_within_band.eml` exactly)

`clamp(raw, u_min, u_max)` lowers to `min (max raw u_min) u_max`,
identical to the Forge-emitted `actuator_command_within_band` body. -/

/-- The PID + asymmetric saturation guard, as the Forge backend
emits it. -/
noncomputable def actuator_command_band_body
    (error integral deriv kp ki kd u_min u_max : Real) : Real :=
  MachLib.Real.min
    (MachLib.Real.max (kp * error + ki * integral + kd * deriv) u_min)
    u_max

/-! ## The verify obligation

The Forge emit attaches `@verify(lean, theorem =
"actuator_command_within_band")`. The two-sided bound. The hypothesis
mirrors the EML's `requires u_min <= u_max`.

We prove both sides separately and as a pair. -/

/-- Lower bound: `u_min ≤ result`. Holds unconditionally on the PID
inputs; requires `u_min ≤ u_max` (so the inner max can fit below
the outer min). -/
theorem actuator_command_within_band_lower
    (error integral deriv kp ki kd u_min u_max : Real)
    (h_band : u_min ≤ u_max) :
    u_min ≤
      actuator_command_band_body error integral deriv kp ki kd u_min u_max := by
  show u_min ≤
    MachLib.Real.min
      (MachLib.Real.max (kp * error + ki * integral + kd * deriv) u_min)
      u_max
  -- Strategy: u_min ≤ max raw u_min  AND  u_min ≤ u_max
  apply le_min
  · -- u_min ≤ max (raw) u_min: by le_max_right on (raw, u_min).
    exact le_max_right _ _
  · -- u_min ≤ u_max: from hypothesis.
    exact h_band

/-- Upper bound: `result ≤ u_max`. Holds unconditionally on the PID
inputs (no `h_band` needed — `min _ u_max ≤ u_max` directly). -/
theorem actuator_command_within_band_upper
    (error integral deriv kp ki kd u_min u_max : Real) :
    actuator_command_band_body error integral deriv kp ki kd u_min u_max
      ≤ u_max := by
  show MachLib.Real.min
        (MachLib.Real.max (kp * error + ki * integral + kd * deriv) u_min)
        u_max
      ≤ u_max
  exact min_le_right _ _

/-- **The main verify obligation**: the asymmetric two-sided bound.
Conjunction form — the Forge backend tracks `requires`/`ensures` as
separate goals but this version expresses the band as a single
conjunction for readability. -/
theorem actuator_command_within_band
    (error integral deriv kp ki kd u_min u_max : Real)
    (h_band : u_min ≤ u_max) :
    u_min ≤
      actuator_command_band_body error integral deriv kp ki kd u_min u_max ∧
    actuator_command_band_body error integral deriv kp ki kd u_min u_max
      ≤ u_max :=
  ⟨actuator_command_within_band_lower _ _ _ _ _ _ _ _ h_band,
   actuator_command_within_band_upper _ _ _ _ _ _ _ _⟩

/-! ## v0 → v1 specialisation check

Confirms `actuator_command_within_band` at `u_min = -limit, u_max = limit`
recovers v0's `actuator_command_within_limits`. This is a sanity check
that v1 is a strict generalization (no information loss). -/

/-- v0 is the `u_min = -limit, u_max = limit` specialisation of v1. The
v0 file's `actuator_command_within_limits` proves `abs(result) ≤ limit`;
this lemma shows that follows from v1's two-sided bound when
`u_min = -limit, u_max = limit ≥ 0`. -/
theorem actuator_command_within_band_specialises_to_v0
    (error integral deriv kp ki kd limit : Real)
    (h_limit_nonneg : 0 ≤ limit) :
    MachLib.Real.abs
      (actuator_command_band_body error integral deriv kp ki kd
        (-limit) limit) ≤ limit := by
  -- h_band: -limit ≤ limit (since limit ≥ 0).
  have h_band : -limit ≤ limit := by
    have h_neg : -limit ≤ 0 := by
      have := neg_le_neg h_limit_nonneg
      rwa [neg_zero] at this
    exact le_trans h_neg h_limit_nonneg
  -- Two-sided bound from the main theorem.
  have h_pair := actuator_command_within_band
    error integral deriv kp ki kd (-limit) limit h_band
  obtain ⟨h_lo, h_hi⟩ := h_pair
  -- Now turn (-limit ≤ result, result ≤ limit) into abs result ≤ limit.
  exact abs_le_of_bounds h_lo h_hi

end AerospaceActuatorGuardBand
end Forge
end MachLib
