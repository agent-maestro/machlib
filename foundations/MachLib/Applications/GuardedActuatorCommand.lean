import MachLib.Basic
import MachLib.Forge

/-!
# Forge kernel application — flight-control actuator-saturation guard

**Domain:** aerospace flight control — actuator command conditioning.
**Safety class:** DO-178C (software) / DO-254 (airborne electronic
hardware), with the same shape applying to IEC 61508 / ISO 26262
saturation guards.

## The kernel (from Forge, `guarded_actuator_command.eml`)

```eml
@verify(lean, theorem = "actuator_command_within_limits")
@target(fpga, board = "arty_a7", clock_mhz = 100, precision = float32)
fn guarded_actuator_command(error, integral, deriv, kp, ki, kd, limit) -> Real
    requires 0.0 <= limit
    ensures abs(result) <= limit
{
    clamp(kp * error + ki * integral + kd * deriv, -limit, limit)
}
```

The Forge Lean backend lowers `clamp(x, -limit, limit)` to
`min (max x (-limit)) limit`, so the obligation it emits is exactly the
`abs`-bound proved below.

## The verify obligation (was `sorry` in the emitted skeleton)

```
@verify(lean, theorem = "actuator_command_within_limits")
```

The safety-meaningful statement: **the commanded output magnitude never
exceeds the actuator's mechanical travel limit** — `abs(result) ≤ limit`.

## Why this is the strong form

The hypotheses constrain *only* `limit ≥ 0`. There is deliberately **no**
bound assumed on `error`, `integral`, or `deriv`. The guarantee therefore
holds even when the PID inputs are a faulted, saturated, or out-of-range
sensor reading — which is the entire point of a saturation guard. This is
strictly stronger than a bound that assumes well-conditioned inputs (cf.
`safe_pid`, which needs `|error| < 1000` etc.). The clamp is a piecewise
polynomial (`chain_order = 0`), so the same statement is reproduced
bit-exactly by the Q16.16 FPGA emit — no transcendental primitive, hence
none of the Taylor-truncation precision caveats apply.

## Proof strategy

`min`/`max`/`abs` are the `if`-defined operators from `MachLib.Basic`.
The bound is purely order-theoretic:

  * upper rail  `min _ limit ≤ limit`     — `min_le_right`
  * lower rail  `-limit ≤ min (max _ (-limit)) limit`
                — `le_min (le_max_right ..) (-limit ≤ limit)`
  * the two rails give `abs _ ≤ limit`     — `abs_le_of_bounds`

No Mathlib, no analytic axioms, no Khovanskii machinery — only the
`MachLib.Basic` field/order axioms and the four small order lemmas below
(`le_min`, `neg_neg`, `neg_le_neg`, `abs_le_of_bounds`). Each is provable
from existing axioms (no new axioms; contrast C-243), and each is a clean
candidate to promote into `MachLib.Forge` / `MachLib.Lemmas`.
-/

namespace MachLib
namespace Forge
namespace AerospaceActuatorGuard

open MachLib
open MachLib.Real

/-! ## Foundational order lemmas (provable from `MachLib.Basic`; no new axioms) -/

/-- `-(-a) = a`. Inverse is involutive. -/
theorem neg_neg (a : Real) : -(-a) = a := by
  have h : -(-a) + (-a) = 0 := by
    rw [add_comm]; exact add_neg (-a)
  calc -(-a) = -(-a) + 0 := (add_zero _).symm
    _ = -(-a) + (-a + a) := by rw [neg_add_self]
    _ = (-(-a) + -a) + a := (add_assoc _ _ _).symm
    _ = 0 + a := by rw [h]
    _ = a := zero_add a

/-- `a ≤ b → -b ≤ -a`. Negation reverses `≤`. -/
theorem neg_le_neg {a b : Real} (h : a ≤ b) : -b ≤ -a := by
  -- 0 ≤ -a + b, then add -b on the left and simplify the right rail to -a.
  have step1 : (0 : Real) ≤ -a + b := by
    have hx := add_le_add_left h (-a)        -- -a + a ≤ -a + b
    rwa [neg_add_self] at hx
  have step2 := add_le_add_left step1 (-b)    -- -b + 0 ≤ -b + (-a + b)
  rw [add_zero] at step2
  have hrhs : -b + (-a + b) = -a := by
    rw [add_comm (-a) b, ← add_assoc, neg_add_self, zero_add]
  rwa [hrhs] at step2

/-- `c ≤ a → c ≤ b → c ≤ min a b`. Greatest-lower-bound intro
(the `c = 0` specialisation already ships as `min_nonneg`). -/
theorem le_min {a b c : Real} (hca : c ≤ a) (hcb : c ≤ b) :
    c ≤ MachLib.Real.min a b := by
  unfold MachLib.Real.min
  by_cases h : a ≤ b
  · rw [if_pos h]; exact hca
  · rw [if_neg h]; exact hcb

/-- `-c ≤ x → x ≤ c → abs x ≤ c`. The `abs` upper-bound introduction. -/
theorem abs_le_of_bounds {x c : Real} (hlo : -c ≤ x) (hhi : x ≤ c) : abs x ≤ c := by
  unfold abs
  by_cases h : 0 ≤ x
  · rw [if_pos h]; exact hhi
  · rw [if_neg h]
    -- goal: -x ≤ c.  neg_le_neg hlo : -x ≤ -(-c); rewrite -(-c) = c.
    have hx := neg_le_neg hlo
    rwa [neg_neg] at hx

/-! ## The kernel (matches `guarded_actuator_command.eml` exactly)

`clamp(raw, -limit, limit)` lowers to `min (max raw (-limit)) limit`,
identical to the Forge-emitted `guarded_actuator_command` definition. -/

noncomputable def guarded_actuator_command
    (error integral deriv kp ki kd limit : Real) : Real :=
  min (max (kp * error + ki * integral + kd * deriv) (-limit)) limit

/-! ## The safety obligation (DO-178C / DO-254 contract) -/

/-- **Actuator command stays within the mechanical travel limit.**

For any control-law inputs `error, integral, deriv` and any gains
`kp, ki, kd`, and for any non-negative mechanical limit `limit`, the
guarded command magnitude is bounded by `limit`:

  `abs (guarded_actuator_command …) ≤ limit`.

This is the verify obligation `@verify(lean, theorem =
"actuator_command_within_limits")` emitted from the `.eml`. The absence of
any hypothesis on `error/integral/deriv` is the safety content: a faulted
or out-of-range sensor cannot drive the actuator past its stops. -/
theorem actuator_command_within_limits
    (error integral deriv kp ki kd limit : Real)
    (h1 : (0.0 : Real) ≤ limit) :
    abs (guarded_actuator_command error integral deriv kp ki kd limit) ≤ limit := by
  rw [lit_zero_eq] at h1                       -- h1 : (0 : Real) ≤ limit
  have h_neg0 : -limit ≤ (0 : Real) := by
    have hx := add_le_add_left h1 (-limit)     -- -limit + 0 ≤ -limit + limit
    rwa [add_zero, neg_add_self] at hx
  have h_nl : -limit ≤ limit := le_trans h_neg0 h1
  unfold guarded_actuator_command
  apply abs_le_of_bounds
  · exact le_min (le_max_right _ _) h_nl        -- lower rail
  · exact min_le_right _ _                       -- upper rail

/-- **Explicit two-rail form** (the DO-254 reviewer's preferred shape:
both saturation rails named). Trivial corollary of the same bounds. -/
theorem actuator_command_within_band
    (error integral deriv kp ki kd limit : Real)
    (h1 : (0.0 : Real) ≤ limit) :
    -limit ≤ guarded_actuator_command error integral deriv kp ki kd limit
    ∧ guarded_actuator_command error integral deriv kp ki kd limit ≤ limit := by
  rw [lit_zero_eq] at h1
  have h_neg0 : -limit ≤ (0 : Real) := by
    have hx := add_le_add_left h1 (-limit)
    rwa [add_zero, neg_add_self] at hx
  have h_nl : -limit ≤ limit := le_trans h_neg0 h1
  unfold guarded_actuator_command
  exact ⟨le_min (le_max_right _ _) h_nl, min_le_right _ _⟩

end AerospaceActuatorGuard
end Forge
end MachLib
