import MachLib.Basic
import MachLib.Forge
import MachLib.Lemmas
import MachLib.Applications.GuardedActuatorCommand
import MachLib.Applications.ActuatorCommandWithinBand
import MachLib.Applications.ActuatorCommandBandWithRateLimit

/-!
# Forge kernel application — actuator-saturation guard (v3)

**v3 = v2 band + slew-rate + JERK limit**, the discrete-time
second-difference bound on actuator motion. v0 → v1 → v2 → v3.

## The kernel (from Forge, `actuator_command_with_jerk_limit.eml`)

```eml
fn actuator_command_with_jerk_limit(
    error, integral, deriv, kp, ki, kd,
    u_min, u_max, rate_limit, jerk_limit,
    prev_result, prev_prev_result) -> Real
    requires u_min <= u_max
    requires 0.0 <= rate_limit
    requires 0.0 <= jerk_limit
    requires jerk_limit <= rate_limit
    requires u_min <= prev_result
    requires prev_result <= u_max
    requires u_min <= prev_prev_result
    requires prev_prev_result <= u_max
    requires abs(prev_result - prev_prev_result) + jerk_limit <= rate_limit
    requires prev_result - u_min >= rate_limit
    requires u_max - prev_result >= rate_limit
    ensures u_min <= result
    ensures result <= u_max
    ensures abs(result - prev_result) <= rate_limit
    ensures abs(result - (prev_result + (prev_result - prev_prev_result)))
            <= jerk_limit
{
    clamp(kp * error + ki * integral + kd * deriv,
          prev_result + (prev_result - prev_prev_result) - jerk_limit,
          prev_result + (prev_result - prev_prev_result) + jerk_limit)
}
```

## Why a single clamp suffices for FOUR ensures

Let `r_prev := prev_result - prev_prev_result`,
    `center := prev_result + r_prev`,
    `lo := center - jerk_limit`,
    `hi := center + jerk_limit`.

The kernel is `result = clamp(raw, lo, hi)`, so `lo ≤ result ≤ hi` by
construction. The four ensures reduce to:

  1. `u_min ≤ result`     :  chain through `u_min ≤ lo`
  2. `result ≤ u_max`     :  chain through `hi ≤ u_max`
  3. `|result - prev| ≤ rate_limit` :  chain through
        `prev - rate_limit ≤ lo` and `hi ≤ prev + rate_limit`
  4. `|result - center| ≤ jerk_limit` :  directly from `lo ≤ result ≤ hi`

Each chain is one algebraic step.

## Precondition decomposition

The EML contract says `abs(r_prev) + jerk_limit ≤ rate_limit`.
The Lean theorem takes the two unpacked halves:

  `r_prev_upper:    r_prev + jerk_limit ≤ rate_limit`
  `r_prev_lower:   -r_prev + jerk_limit ≤ rate_limit`

By the standard range characterisation `abs a ≤ b ↔ -b ≤ a ∧ a ≤ b`
(MachLib axiom `abs_le_iff` in `Lemmas.lean`), these two unpacked
halves are equivalent to `abs r_prev ≤ rate_limit - jerk_limit`,
i.e. `abs r_prev + jerk_limit ≤ rate_limit`. We do this unpacking
once at the contract/proof boundary and work with the unpacked form
inside the proof.

## Jerk ensures form

The EML contract writes
`abs((result - prev) - r_prev) ≤ jerk_limit`. We prove the
ASSOCIATIVITY-NORMALISED form `abs(result - center) ≤ jerk_limit`,
where `center := prev + r_prev`. These two are equivalent via
`(a - b) - c = a - (b + c)`. The normalised form matches the clamp
geometry directly and avoids associativity rewrites in the proof.
-/

namespace MachLib
namespace Forge
namespace AerospaceActuatorGuardJerk

open MachLib
open MachLib.Real
open MachLib.Forge.AerospaceActuatorGuard
  (neg_neg neg_le_neg abs_le_of_bounds)
open MachLib.Forge.AerospaceActuatorGuardBandRate
  (le_min add_nonneg sub_nonneg_le le_add_nonneg max_le)

/-! ## Algebraic helpers — convert between `c - d ≤ x` / `x ≤ c + d`
   and the abs-friendly forms `-d ≤ x - c` / `x - c ≤ d`.

These two helpers do the SAME transformation v2 spelled out inline,
factored out so the main proof is one-liner-per-ensures.

Both target `sub_def` at SPECIFIC arguments (`c, d`) so internal
subtractions inside `c` (e.g. `prev - prev_prev`) are NOT expanded. -/

/-- From `c - d ≤ x` derive `-d ≤ x - c`. -/
private theorem sub_le_imp {c d x : Real} (h : c - d ≤ x) : -d ≤ x - c := by
  have step := add_le_add_left h (-c)
  -- step : -c + (c - d) ≤ -c + x
  rw [sub_def c d] at step
  -- step : -c + (c + -d) ≤ -c + x
  rw [← add_assoc, neg_add_self, zero_add] at step
  -- step : -d ≤ -c + x
  rw [add_comm (-c) x, ← sub_def] at step
  -- step : -d ≤ x - c
  exact step

/-- From `x ≤ c + d` derive `x - c ≤ d`. -/
private theorem le_add_imp {c d x : Real} (h : x ≤ c + d) : x - c ≤ d := by
  have step := add_le_add_left h (-c)
  -- step : -c + x ≤ -c + (c + d)
  rw [← add_assoc, neg_add_self, zero_add] at step
  -- step : -c + x ≤ d
  rw [add_comm (-c) x, ← sub_def] at step
  -- step : x - c ≤ d
  exact step

/-! ## The kernel body -/

/-- Single jerk-window clamp; matches the Forge emit. -/
noncomputable def actuator_command_jerk_body
    (error integral deriv kp ki kd
     u_min u_max rate_limit jerk_limit
     prev_result prev_prev_result : Real) : Real :=
  MachLib.Real.min
    (MachLib.Real.max
      (kp * error + ki * integral + kd * deriv)
      (prev_result + (prev_result - prev_prev_result) - jerk_limit))
    (prev_result + (prev_result - prev_prev_result) + jerk_limit)

/-! ## Window-bound lemmas — the clamp's intrinsic geometry -/

/-- The lo bound is ≤ the hi bound: window is non-empty when `0 ≤ jerk_limit`. -/
private theorem lo_le_hi
    (prev_result prev_prev_result jerk_limit : Real)
    (h_jerk_nonneg : 0 ≤ jerk_limit) :
    (prev_result + (prev_result - prev_prev_result)) - jerk_limit ≤
    (prev_result + (prev_result - prev_prev_result)) + jerk_limit :=
  le_trans (sub_nonneg_le h_jerk_nonneg) (le_add_nonneg h_jerk_nonneg)

/-- The kernel result is always ≥ lo. -/
private theorem lo_le_result
    (error integral deriv kp ki kd
     u_min u_max rate_limit jerk_limit
     prev_result prev_prev_result : Real)
    (h_jerk_nonneg : 0 ≤ jerk_limit) :
    (prev_result + (prev_result - prev_prev_result)) - jerk_limit ≤
    actuator_command_jerk_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit
      prev_result prev_prev_result := by
  unfold actuator_command_jerk_body
  apply le_min
  · exact le_max_right _ _
  · exact lo_le_hi prev_result prev_prev_result jerk_limit h_jerk_nonneg

/-- The kernel result is always ≤ hi. -/
private theorem result_le_hi
    (error integral deriv kp ki kd
     u_min u_max rate_limit jerk_limit
     prev_result prev_prev_result : Real) :
    actuator_command_jerk_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit
      prev_result prev_prev_result ≤
    (prev_result + (prev_result - prev_prev_result)) + jerk_limit := by
  unfold actuator_command_jerk_body
  exact min_le_right _ _

/-! ## Algebraic helpers — translate preconditions into window bounds -/

/-- From `r_prev + jerk_limit ≤ rate_limit` and `rate_limit ≤ u_max - prev`,
derive `hi ≤ u_max`. -/
private theorem hi_le_umax
    (prev_result u_max rate_limit jerk_limit r_prev : Real)
    (h_r_prev_upper : r_prev + jerk_limit ≤ rate_limit)
    (h_interior_upper : rate_limit ≤ u_max - prev_result) :
    prev_result + r_prev + jerk_limit ≤ u_max := by
  -- prev + (r + j) ≤ prev + rate ≤ prev + (u_max - prev) = u_max
  have step1 : prev_result + (r_prev + jerk_limit) ≤ prev_result + rate_limit :=
    add_le_add_left h_r_prev_upper prev_result
  have step2 : prev_result + rate_limit ≤ u_max := by
    have h := add_le_add_left h_interior_upper prev_result
    -- h : prev + rate ≤ prev + (u_max - prev)
    -- Simplify RHS to u_max:  prev + (u_max + -prev) = u_max + (prev + -prev) = u_max + 0 = u_max
    rw [sub_def, ← add_assoc, add_comm prev_result u_max, add_assoc,
        add_neg, add_zero] at h
    exact h
  rw [← add_assoc] at step1
  exact le_trans step1 step2

/-- From `-r_prev + jerk_limit ≤ rate_limit` and `rate_limit ≤ prev - u_min`,
derive `u_min ≤ lo`.

Algebra:  `-r + j ≤ rate ≤ prev - u_min`
   ⟹  `-r + j ≤ prev - u_min`
   ⟹  `u_min + (j - r) ≤ prev`           (add u_min to both sides, rearrange)
   ⟹  `u_min ≤ prev - j + r = prev + r - j = lo`
-/
private theorem umin_le_lo
    (prev_result u_min rate_limit jerk_limit r_prev : Real)
    (h_r_prev_lower : -r_prev + jerk_limit ≤ rate_limit)
    (h_interior_lower : rate_limit ≤ prev_result - u_min) :
    u_min ≤ prev_result + r_prev - jerk_limit := by
  -- Goal:  u_min ≤ prev + r - jerk.
  -- Chain:  u_min + jerk ≤ prev + r,  then subtract jerk on the right.
  have h_chain : -r_prev + jerk_limit ≤ prev_result - u_min :=
    le_trans h_r_prev_lower h_interior_lower
  -- Step 1: derive  u_min + jerk ≤ prev + r.
  have h_add : u_min + jerk_limit ≤ prev_result + r_prev := by
    -- Add (u_min + r_prev) on the left to h_chain:
    --   (u_min + r) + (-r + j) ≤ (u_min + r) + (prev - u_min)
    have h := add_le_add_left h_chain (u_min + r_prev)
    -- Simplify LHS:  (u_min + r) + (-r + j) = u_min + (r + -r) + j = u_min + 0 + j = u_min + j
    rw [add_assoc, ← add_assoc r_prev, add_neg, zero_add] at h
    -- h : u_min + jerk ≤ (u_min + r) + (prev - u_min)
    -- Simplify RHS:
    --   (u_min + r) + (prev + -u_min)
    -- = u_min + (r + (prev + -u_min))    [add_assoc]
    -- = u_min + ((prev + -u_min) + r)    [add_comm inside]
    -- = u_min + (prev + (-u_min + r))    [add_assoc inside]
    -- = u_min + (prev + (r + -u_min))    [add_comm]
    -- = u_min + ((prev + r) + -u_min)    [add_assoc reverse]
    -- = (u_min + -u_min) + (prev + r)    [add_comm + add_assoc reorder]
    -- = 0 + (prev + r)
    -- = prev + r
    rw [sub_def, add_assoc, add_comm r_prev (prev_result + (-u_min)),
        add_comm prev_result (-u_min), add_assoc (-u_min) prev_result r_prev,
        ← add_assoc u_min (-u_min), add_neg, zero_add] at h
    exact h
  -- Step 2: subtract jerk from both sides (add -jerk on the left):
  have h_final := add_le_add_left h_add (-jerk_limit)
  -- h_final : -jerk + (u_min + jerk) ≤ -jerk + (prev + r)
  -- LHS: -jerk + (u_min + jerk) = u_min + (-jerk + jerk) = u_min + 0 = u_min
  rw [← add_assoc, add_comm (-jerk_limit) u_min, add_assoc,
      add_comm (-jerk_limit) jerk_limit, add_neg, add_zero] at h_final
  -- h_final : u_min ≤ -jerk + (prev + r)
  -- RHS: -jerk + (prev + r) = (prev + r) + -jerk = prev + r - jerk
  rw [add_comm (-jerk_limit) (prev_result + r_prev), ← sub_def] at h_final
  exact h_final

/-- From `-r_prev + jerk_limit ≤ rate_limit`, derive `prev - rate_limit ≤ lo`.
This says: the jerk lo bound stays at most rate_limit below prev.

Algebra:  `-r + j ≤ rate`
   ⟺  `-rate ≤ r - j`
   ⟺  `prev - rate ≤ prev + r - j = lo`
-/
private theorem prev_minus_rl_le_lo
    (prev_result rate_limit jerk_limit r_prev : Real)
    (h_r_prev_lower : -r_prev + jerk_limit ≤ rate_limit) :
    prev_result - rate_limit ≤ prev_result + r_prev - jerk_limit := by
  -- Derive  -rate ≤ r - jerk  from h_r_prev_lower, then add prev to both sides.
  -- Method: from h_r_prev_lower, add (-(rate + (-r + j)) + (r - j)) on the left? Too clever.
  -- Easier: add (r - j - (-r + j)) = (r - j + r - j) — wait that doubles.
  --
  -- Cleanest: add -(jerk + rate) on the left to h_r_prev_lower? No, let's compute directly.
  --
  -- Step A: derive `-rate ≤ r - jerk`.  From h_r_prev_lower : -r + j ≤ rate, apply neg_le_neg:
  --   -rate ≤ -(-r + j).
  -- Simplify RHS via uniqueness of additive inverse: -(-r + j) = r - j.
  -- Without `neg_add`, derive `-rate ≤ r - jerk` by an additive chain.
  -- From h_r_prev_lower, add (r - jerk + rate) on the left:
  --   (r + -jerk + rate) + (-r + jerk) ≤ (r + -jerk + rate) + rate
  -- LHS simplifies to rate; RHS to rate + rate = 2·rate. Not what we want.
  --
  -- DIRECT method via add_le_add_left: the goal is `prev + -rate ≤ prev + (r + -jerk)`.
  -- This follows from add_le_add_left applied to `-rate ≤ r - jerk`.
  -- So we just need `-rate ≤ r - jerk` first.
  --
  -- h_r_prev_lower : -r + jerk ≤ rate
  -- Equivalent rearrangements (each by add_le_add_left of suitable c):
  --   (a) Add r on the left:  r + (-r + jerk) ≤ r + rate
  --        ⟺ jerk ≤ r + rate                      [simplify LHS]
  --   (b) Add -jerk on the left:  -jerk + jerk ≤ -jerk + (r + rate)
  --        ⟺ 0 ≤ -jerk + r + rate                 [simplify LHS]
  --   (c) Add -rate on the left:  -rate + 0 ≤ -rate + (-jerk + r + rate)
  --        ⟺ -rate ≤ r - jerk                      [simplify RHS via add_comm and add_neg]
  --
  -- Or chain (a),(b),(c) explicitly.
  have step_a : jerk_limit ≤ r_prev + rate_limit := by
    have h := add_le_add_left h_r_prev_lower r_prev
    -- h : r + (-r + jerk) ≤ r + rate
    rw [← add_assoc, add_neg, zero_add] at h
    exact h
  have step_b : 0 ≤ r_prev + rate_limit + -jerk_limit := by
    have h := add_le_add_left step_a (-jerk_limit)
    -- h : -jerk + jerk ≤ -jerk + (r + rate)
    rw [add_comm (-jerk_limit) jerk_limit, add_neg] at h
    -- h : 0 ≤ -jerk + (r + rate)
    rw [add_comm (-jerk_limit) (r_prev + rate_limit)] at h
    exact h
  have step_c : -rate_limit ≤ r_prev + -jerk_limit := by
    have h := add_le_add_left step_b (-rate_limit)
    -- h : -rate + 0 ≤ -rate + (r + rate + -jerk)
    rw [add_zero] at h
    -- h : -rate ≤ -rate + (r + rate + -jerk)
    -- Simplify RHS:  -rate + ((r + rate) + -jerk)
    -- = -rate + (r + rate) + -jerk       [add_assoc reverse]
    -- = (r + rate + -rate) + -jerk       [add_comm bringing -rate inside]
    -- We want to end with `r + -jerk`.
    -- Try: -rate + (r + rate + -jerk) = (-rate + r) + (rate + -jerk)   [no, mixing]
    -- = r + (-rate + rate) + -jerk       [add_comm + add_assoc]
    -- = r + 0 + -jerk = r + -jerk
    rw [← add_assoc, add_comm (-rate_limit) (r_prev + rate_limit),
        add_assoc r_prev rate_limit (-rate_limit), add_neg, add_zero] at h
    exact h
  -- Now apply add_le_add_left to step_c with c = prev:
  have h := add_le_add_left step_c prev_result
  -- h : prev + -rate ≤ prev + (r + -jerk)
  -- LHS = prev - rate (via sub_def reversal); RHS = (prev + r) + -jerk = prev + r - jerk
  rw [← sub_def, ← add_assoc, ← sub_def] at h
  exact h

/-- From `r_prev + jerk_limit ≤ rate_limit`, derive `hi ≤ prev + rate_limit`. -/
private theorem hi_le_prev_plus_rl
    (prev_result rate_limit jerk_limit r_prev : Real)
    (h_r_prev_upper : r_prev + jerk_limit ≤ rate_limit) :
    prev_result + r_prev + jerk_limit ≤ prev_result + rate_limit := by
  have h := add_le_add_left h_r_prev_upper prev_result
  -- h : prev + (r + jerk) ≤ prev + rate
  rw [← add_assoc] at h
  exact h

/-! ## Ensures 1 — band lower (`u_min ≤ result`) -/

theorem jerk_band_lower
    (error integral deriv kp ki kd
     u_min u_max rate_limit jerk_limit
     prev_result prev_prev_result : Real)
    (h_jerk_nonneg : 0 ≤ jerk_limit)
    (h_r_prev_lower : -(prev_result - prev_prev_result) + jerk_limit ≤ rate_limit)
    (h_interior_lower : rate_limit ≤ prev_result - u_min) :
    u_min ≤ actuator_command_jerk_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit
      prev_result prev_prev_result := by
  have h_u_min_le_lo : u_min ≤ prev_result + (prev_result - prev_prev_result) - jerk_limit :=
    umin_le_lo prev_result u_min rate_limit jerk_limit
                (prev_result - prev_prev_result) h_r_prev_lower h_interior_lower
  exact le_trans h_u_min_le_lo
    (lo_le_result error integral deriv kp ki kd u_min u_max rate_limit jerk_limit
                  prev_result prev_prev_result h_jerk_nonneg)

/-! ## Ensures 2 — band upper (`result ≤ u_max`) -/

theorem jerk_band_upper
    (error integral deriv kp ki kd
     u_min u_max rate_limit jerk_limit
     prev_result prev_prev_result : Real)
    (h_r_prev_upper : (prev_result - prev_prev_result) + jerk_limit ≤ rate_limit)
    (h_interior_upper : rate_limit ≤ u_max - prev_result) :
    actuator_command_jerk_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit
      prev_result prev_prev_result ≤ u_max :=
  le_trans (result_le_hi _ _ _ _ _ _ _ _ _ _ _ _)
           (hi_le_umax prev_result u_max rate_limit jerk_limit
                       (prev_result - prev_prev_result) h_r_prev_upper h_interior_upper)

/-! ## The main verify obligation -/

/-- **The main verify obligation**: band + rate + jerk all hold under the
v3 preconditions (interior + unpacked-abs r_prev bound).

The jerk ensures clause uses the associativity-normalised form
`|result - (prev + r_prev)| ≤ jerk_limit`, equivalent to the EML form
`|(result - prev) - r_prev| ≤ jerk_limit` modulo `(a-b)-c = a-(b+c)`. -/
theorem actuator_command_with_jerk_limit
    (error integral deriv kp ki kd
     u_min u_max rate_limit jerk_limit
     prev_result prev_prev_result : Real)
    (h_jerk_nonneg : 0 ≤ jerk_limit)
    (h_r_prev_upper :
       (prev_result - prev_prev_result) + jerk_limit ≤ rate_limit)
    (h_r_prev_lower :
       -(prev_result - prev_prev_result) + jerk_limit ≤ rate_limit)
    (h_interior_lower : rate_limit ≤ prev_result - u_min)
    (h_interior_upper : rate_limit ≤ u_max - prev_result) :
    u_min ≤ actuator_command_jerk_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit
      prev_result prev_prev_result ∧
    actuator_command_jerk_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit
      prev_result prev_prev_result ≤ u_max ∧
    MachLib.Real.abs (actuator_command_jerk_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit
      prev_result prev_prev_result - prev_result) ≤ rate_limit ∧
    MachLib.Real.abs (actuator_command_jerk_body
      error integral deriv kp ki kd u_min u_max rate_limit jerk_limit
      prev_result prev_prev_result
      - (prev_result + (prev_result - prev_prev_result))) ≤ jerk_limit := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact jerk_band_lower _ _ _ _ _ _ _ _ _ _ _ _
                          h_jerk_nonneg h_r_prev_lower h_interior_lower
  · exact jerk_band_upper _ _ _ _ _ _ _ _ _ _ _ _
                          h_r_prev_upper h_interior_upper
  · -- Rate bound via abs_le_of_bounds.
    -- Show: prev - rate ≤ result ≤ prev + rate, then translate to abs.
    have h_hi : actuator_command_jerk_body
        error integral deriv kp ki kd u_min u_max rate_limit jerk_limit
        prev_result prev_prev_result ≤ prev_result + rate_limit :=
      le_trans (result_le_hi _ _ _ _ _ _ _ _ _ _ _ _)
               (hi_le_prev_plus_rl prev_result rate_limit jerk_limit
                                    (prev_result - prev_prev_result) h_r_prev_upper)
    have h_lo : prev_result - rate_limit ≤
        actuator_command_jerk_body
          error integral deriv kp ki kd u_min u_max rate_limit jerk_limit
          prev_result prev_prev_result :=
      le_trans (prev_minus_rl_le_lo prev_result rate_limit jerk_limit
                                     (prev_result - prev_prev_result) h_r_prev_lower)
               (lo_le_result _ _ _ _ _ _ _ _ _ _ _ _ h_jerk_nonneg)
    -- Convert to bounds on (result - prev):
    exact abs_le_of_bounds (sub_le_imp h_lo) (le_add_imp h_hi)
  · -- Jerk bound via abs_le_of_bounds on (result - center) where center := prev + r_prev.
    -- Direct from the clamp's geometry:  lo ≤ result ≤ hi.
    have h_hi := result_le_hi
                   error integral deriv kp ki kd u_min u_max rate_limit jerk_limit
                   prev_result prev_prev_result
    have h_lo := lo_le_result
                   error integral deriv kp ki kd u_min u_max rate_limit jerk_limit
                   prev_result prev_prev_result h_jerk_nonneg
    -- Direct from the clamp's geometry via the abs-conversion helpers.
    exact abs_le_of_bounds (sub_le_imp h_lo) (le_add_imp h_hi)

/-! ## v2 → v3 specialisation note

v3 strictly STRENGTHENS the contract over v2 (adds the jerk ensures)
while STRENGTHENING the preconditions (adds interior + unpacked-abs
r_prev bound). v2 holds wherever v3 holds, but v3 doesn't hold
wherever v2 holds (at the rails, v3's interior precondition fails).

The intended deployment: a supervisor selects v3 in the interior and
v2 at the rails — both share the same band/rate ensures, so the
switching is invariant-safe. -/

end AerospaceActuatorGuardJerk
end Forge
end MachLib
