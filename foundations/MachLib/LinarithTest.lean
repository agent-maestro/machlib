/-
MachLib.LinarithTest — coverage tests for `mach_positivity` v1.

Each `example` here mirrors a (mostly) linarith-tagged obligation
in `monogate-engine/proofs/Proofs/`. A green build means the
engine's corresponding `sorry`s will close once their `by sorry`
is replaced with `by mach_positivity` (or for genuine linear
cases, `by mach_linarith`).

Engine theorems covered (per
`monogate-engine/proofs/Proofs/README.md`):

  Aces.nonneg_when_input_nonneg              — positivity
  AtmosphereRayleigh.scatter_positive         — positivity
  ParticlesLifetime.lifetime_scale_positive   — positivity
  ParticlesForces.buoyancy_acceleration_nonneg — positivity (already closed)

Out of scope for v1 (deferred):
  Pulse.in_unit_band                          — needs sin bound + literal 1/2
  AtmosphereRayleigh.phase_nonneg             — needs sq_nonneg
  IkJointLimit.soften_in_band                 — needs nlinarith
-/

import MachLib.Linarith

namespace MachLibTest.Linarith

open MachLib MachLib.Real

/-! ### `mach_positivity` cases -/

/-- Sum of nonnegs is nonneg. -/
example (a b : Real) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by mach_positivity

/-- Product of nonnegs is nonneg. -/
example (a b : Real) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by mach_positivity

/-- Strict-positive sum. -/
example (a b : Real) (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by mach_positivity

/-- Strict-positive product. -/
example (a b : Real) (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by mach_positivity

/-- Mixed strict + nonneg sum. -/
example (a b : Real) (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b := by mach_positivity

/-- Division of nonneg by positive is nonneg. -/
example (a b : Real) (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by mach_positivity

/-- Mirrors `Aces.nonneg_when_input_nonneg`: `0 ≤ x →
    0 ≤ (x * (k1 * x + k2)) / (x * (k3 * x + k4) + k5)`
    where the literal coefficients are all nonneg. -/
example (x : Real) (hx : 0 ≤ x) :
    0 ≤ (x * ((2.51 : Real) * x + (0.03 : Real))) /
        (x * ((2.43 : Real) * x + (0.59 : Real)) + (0.14 : Real)) := by
  mach_positivity

/-- Mirrors `AtmosphereRayleigh.scatter_positive`: `0 < w →
    0 < k / (w*w*w*w)` where `k > 0`. The chain unfolds to a
    quotient of literal-positive over four-fold-positive. -/
example (w : Real) (hw : 0 < w) :
    0 < (1.241e-2 : Real) / (w * w * w * w) := by
  mach_positivity

/-- Long-chain non-neg: a sum-of-nonneg cascade. Mirrors the
    `ParticlesLifetime.lifetime_scale_positive` shape. -/
example (a b c d : Real)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d) :
    0 < a + b + c + d := by
  mach_positivity

/-- Literal positivity (Forge ofScientific_pos bridge). -/
example : (0 : Real) < (0.5 : Real) := by mach_positivity

/-- Literal nonneg. -/
example : (0 : Real) ≤ (1.5 : Real) := by mach_positivity

/-- Squares are non-negative. -/
example (x : Real) : 0 ≤ x * x := by mach_positivity

/-- Smaller piece of the Rayleigh phase: `0 ≤ 1 + x*x`. -/
example (cos_theta : Real) :
    0 ≤ 1 + cos_theta * cos_theta := by
  mach_positivity

/-- Mirrors `AtmosphereRayleigh.phase_nonneg`:
    `0 ≤ k * (1 + cos² θ)` where k is a positive literal. -/
example (cos_theta : Real) :
    0 ≤ (0.046875 : Real) * (1 + cos_theta * cos_theta) := by
  mach_positivity

end MachLibTest.Linarith
