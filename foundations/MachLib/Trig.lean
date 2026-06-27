import MachLib.Basic

/-
MachLib.Trig — sine and cosine, axiomatised.

The same delegation argument as `Exp`: agents reasoning about
trigonometric expressions need the *facts* (Pythagorean identity,
addition formulas, periodicity), not the analytic construction.
We expose the facts as axioms; a future contributor wanting to
build sin/cos from a power series or as the imaginary/real parts
of the complex exponential can do so without breaking any
downstream theorem.
-/

namespace MachLib
namespace Real

axiom sin : Real → Real
axiom cos : Real → Real
axiom tan : Real → Real
axiom pi  : Real

/-! ### Defining axioms -/

axiom sin_zero       : sin 0 = 0
axiom cos_zero       : cos 0 = 1
axiom tan_zero       : tan 0 = 0
axiom tan_def        (x : Real) : cos x ≠ 0 → tan x = sin x / cos x
axiom sin_pi         : sin pi = 0
axiom cos_pi         : cos pi = -1
axiom pi_pos         : 0 < pi
axiom pythagorean (x : Real) : sin x * sin x + cos x * cos x = 1
axiom sin_neg        (x : Real) : sin (-x) = -(sin x)
axiom cos_neg        (x : Real) : cos (-x) = cos x
axiom sin_add        (x y : Real) :
  sin (x + y) = sin x * cos y + cos x * sin y
axiom cos_add        (x y : Real) :
  cos (x + y) = cos x * cos y - sin x * sin y

/-! ### Boundedness

`sin_le_one`/`neg_one_le_sin`/`cos_le_one`/`neg_one_le_cos` PROMOTED to theorems in
`Lemmas.lean` (2026-06-27 audit) — they follow from the squared bounds
(`sin_sq_le_one`/`cos_sq_le_one`, themselves derived from `pythagorean`) via the
`u²≤1 ⇒ u≤1` peeling lemma, which lives downstream of `Trig`. -/

/-! ### Lipschitz (`|sin'| = |cos| ≤ 1`, `|cos'| = |sin| ≤ 1`)

`sin`/`cos` are globally 1-Lipschitz. These were briefly axioms here; now PROVED
(`sin_lipschitz`/`cos_lipschitz`) in `MachLib.TrigLipschitz` via
`mean_value_theorem` + `HasDerivAt_sin`/`HasDerivAt_cos` + boundedness — so the
trusted base no longer carries them as axioms. -/

/-! ### Periodicity (period 2π) -/

axiom sin_periodic (x : Real) : sin (x + (1 + 1) * pi) = sin x
axiom cos_periodic (x : Real) : cos (x + (1 + 1) * pi) = cos x

/-! ### Additional analytic primitives

The forge's industry verticals reach for these names through the
emitted `Real.tanh`, `Real.sqrt`, etc. references. We axiomatise
each with the minimal property set the downstream theorems use;
contributors can add more when a specific theorem needs them. -/

axiom tanh   : Real → Real
axiom sqrt   : Real → Real
axiom atan2  : Real → Real → Real
axiom arcsin : Real → Real
axiom arccos : Real → Real
-- Single-argument arctangent. The Forge backend maps EML `atan` to
-- `Real.arctan`; without this symbol every atan/atan2/accelerometer kernel
-- failed to compile ("unknown constant Real.arctan"). Function-symbol
-- declaration only, same kind as arcsin/arccos above — no new property axiom.
axiom arctan : Real → Real
-- arctan maps ℝ strictly into the OPEN principal range (-π/2, π/2): it
-- approaches ±π/2 only as x → ±∞, never reaching it. Held as axioms (arctan is
-- an opaque symbol with no concrete Real model to derive from) — clearly true
-- and standard, the inverse-tangent principal range, exactly mirroring
-- Mathlib's `Real.arctan_lt_pi_div_two` / `Real.neg_pi_div_two_lt_arctan`.
-- Stated with the decimal `2.0` so they unify with the Forge-emitted bound
-- `pi() / 2.0`. Closes the atan / atan2_pos_x open-interval band obligations.
axiom arctan_lt_pi_div_two     (x : Real) : arctan x < pi / 2.0
axiom neg_pi_div_two_lt_arctan (x : Real) : -(pi / 2.0) < arctan x

-- Half-angle tangent positivity: for x in (0, π) the half-angle x/2 lies in the
-- first quadrant (0, π/2), where tan is positive. Stated with the half baked in
-- (`tan (0.5 * x)` from `x < pi`) ON PURPOSE: the general `tan_pos` on (0, π/2)
-- would force the half-angle range `0.5·x < pi/2`, which needs `0.5·2.0 = 1`
-- over opaque realOfScientific — the decimal reconciliation that is Phase-3's
-- job, not a cheap closer. This form is general (any tan(x/2) on (0,π)) and
-- sound. Closes the perspective-projection coefficients (fov_m00 / fov_m11).
axiom tan_half_pos (x : Real) : 0 < x → x < pi → 0 < tan (0.5 * x)
-- Gauss error function. EML `erf` passes through to a bare `erf` call; without
-- this symbol math/erf.eml failed to compile ("unknown identifier erf").
-- Symbol only — `erf`'s bound/zero properties are NOT asserted here, so the
-- erf kernel obligations honestly remain `sorry` until those axioms land.
axiom erf : Real → Real
-- erf maps ℝ → (-1, 1). The two range bounds are held as axioms (erf is an
-- opaque symbol, so they are not derivable) — clearly true and standard.
-- Close the `erf_kernel` in-unit-interval obligation. C-246.
axiom neg_one_le_erf (x : Real) : -1 ≤ erf x
axiom erf_le_one     (x : Real) : erf x ≤ 1

/-! ### Defining properties (minimal set) -/

-- tanh: bounded in (-1, 1), zero at zero, odd.
axiom tanh_zero     : tanh 0 = 0
axiom tanh_lt_one   (x : Real) : tanh x < 1
axiom neg_one_lt_tanh (x : Real) : -1 < tanh x
axiom tanh_neg      (x : Real) : tanh (-x) = -(tanh x)

-- sqrt: non-negative, fixed at 0 and 1, multiplicative on
-- non-negatives. We follow the GNU/IEEE convention of returning 0
-- on negative input rather than NaN.
axiom sqrt_zero       : sqrt 0 = 0
axiom sqrt_one        : sqrt 1 = 1
axiom sqrt_nonneg     (x : Real) : 0 ≤ sqrt x
axiom sqrt_sq_nonneg  (x : Real) : 0 ≤ x → sqrt x * sqrt x = x
axiom sqrt_neg_zero   (x : Real) : x < 0 → sqrt x = 0
-- Order characterisation (one direction): a nonneg lower bound whose square
-- is ≤ y is itself ≤ sqrt y. Sound for the real square root (z ≥ 0, z² ≤ y ⇒
-- z = sqrt(z²) ≤ sqrt y by monotonicity). Held as an axiom alongside the
-- other sqrt facts — there is no concrete Real model to derive it from.
-- Closes quadratic-formula root-sign obligations (lqr Riccati discriminant).
axiom le_sqrt_of_sq_le {z y : Real} (hz : 0 ≤ z) (h : z * z ≤ y) : z ≤ sqrt y
-- Upper companion: a nonneg bound whose square dominates y bounds sqrt y from
-- above (z ≥ 0, y ≤ z² ⇒ sqrt y ≤ sqrt(z²) = z). Closes the `v − sqrt(clamped)`
-- numerators where the radicand is min-clamped below v² (tof constant-decel).
axiom sqrt_le_of_le_sq {z y : Real} (hz : 0 ≤ z) (h : y ≤ z * z) : sqrt y ≤ z

-- arcsin / arccos: principal-value inverses, bounded.
axiom arcsin_zero  : arcsin 0 = 0
axiom arccos_zero  : arccos 0 = pi / (1 + 1)
axiom arcsin_one   : arcsin 1 = pi / (1 + 1)
axiom arccos_one   : arccos 1 = 0
axiom sin_arcsin   (x : Real) : -1 ≤ x → x ≤ 1 → sin (arcsin x) = x
axiom cos_arccos   (x : Real) : -1 ≤ x → x ≤ 1 → cos (arccos x) = x

-- atan2: the principal-value angle of the point (x, y), in (-π, π].
axiom atan2_zero_one : atan2 0 1 = 0
axiom atan2_one_zero : atan2 1 0 = pi / (1 + 1)
axiom atan2_le_pi    (y x : Real) : atan2 y x ≤ pi
axiom neg_pi_lt_atan2 (y x : Real) : -pi < atan2 y x

/-! ### Derived lemmas -/

theorem sin_sq_add_cos_sq (x : Real) :
    sin x * sin x + cos x * cos x = 1 :=
  pythagorean x

theorem sin_pi_zero : sin pi = 0 := sin_pi
theorem cos_pi_neg_one : cos pi = -1 := cos_pi

theorem sin_two_pi : sin ((1 + 1) * pi) = 0 := by
  have h : sin (0 + (1 + 1) * pi) = sin 0 := sin_periodic 0
  rw [zero_add] at h
  rw [h, sin_zero]

theorem cos_two_pi : cos ((1 + 1) * pi) = 1 := by
  have h : cos (0 + (1 + 1) * pi) = cos 0 := cos_periodic 0
  rw [zero_add] at h
  rw [h, cos_zero]

end Real
end MachLib
