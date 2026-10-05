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

/-! ### Defining axioms

`sin_zero` and `cos_zero` were axioms here until 2026-10-05, and `tan_zero` a theorem of them: all three are
below the addition laws now, which prove them. -/

axiom tan_def        (x : Real) : cos x ≠ 0 → tan x = sin x / cos x

axiom sin_pi         : sin pi = 0
axiom cos_pi         : cos pi = -1
-- `pi_pos` was an axiom here until 2026-10-04: a theorem below `pi_lower_bound` now.

/-- Tight numeric bound on `pi`, to 6 decimal places (`3.141592 < π < 3.141593`) — standard,
well-established mathematics, added specifically to bound `eml_acos.v`'s `HALF_PI` fixed-point
constant (`314159/200000`, computed at RTL elaboration time, NOT exactly `π/2`) against the true
value. The coarser `pi_gt_three`/`pi_gt_one` elsewhere are nowhere near tight enough for this. -/
axiom pi_lower_bound : natCast 3141592 * (1 / natCast 1000000) < pi
axiom pi_upper_bound : pi < natCast 3141593 * (1 / natCast 1000000)

/-- `π > 3`, from the tight bound: `3 = natCast 3000000 / 10⁶ < natCast 3141592 / 10⁶ < π`. A THEOREM since
2026-10-04 -- it was an axiom in `IteratedExpBounds.lean`, and `pi_gt_one` (`SinNotInEMLDepth2Partial.lean`,
"derivable from π > 3 once that's available") and `pi_pos` (here) were two more: three axioms for consequences
of the one `pi_lower_bound` states (the muses' E round: provable means proved). -/
theorem pi_gt_three : (1 + 1 + 1 : Real) < pi := by
  have hM : (0 : Real) < natCast 1000000 := natCast_pos (by decide)
  have h3 : natCast 3 = (1 + 1 + 1 : Real) := by
    rw [show (3 : Nat) = 0 + 1 + 1 + 1 from rfl, natCast_succ, natCast_succ, natCast_succ, natCast_zero, zero_add]
  have hlt : natCast 3 * natCast 1000000 < natCast 3141592 := by
    rw [← natCast_mul]; exact natCast_lt_natCast (by decide)
  have h2 := mul_lt_mul_of_pos_right hlt (one_div_pos_of_pos hM)
  rw [mul_assoc, mul_inv _ (ne_of_gt hM), mul_one_ax, h3] at h2
  exact lt_trans_ax h2 pi_lower_bound

/-- `π > 1`, below `π > 3`. A theorem since 2026-10-04. -/
theorem pi_gt_one : (1 : Real) < pi := by
  have h1 : (1 : Real) < 1 + 1 := by
    have h := add_lt_add_left zero_lt_one_ax (1 : Real)
    rwa [add_zero] at h
  have h2 : (1 : Real) + 1 < 1 + 1 + 1 := by
    have h := add_lt_add_left zero_lt_one_ax ((1 : Real) + 1)
    rwa [add_zero] at h
  exact lt_trans_ax h1 (lt_trans_ax h2 pi_gt_three)

/-- `0 < π`. A theorem since 2026-10-04. -/
theorem pi_pos : 0 < pi := lt_trans_ax zero_lt_one_ax pi_gt_one
axiom pythagorean (x : Real) : sin x * sin x + cos x * cos x = 1
axiom sin_add        (x y : Real) :
  sin (x + y) = sin x * cos y + cos x * sin y
axiom cos_add        (x y : Real) :
  cos (x + y) = cos x * cos y - sin x * sin y

/-! ### What the addition laws prove

`sin_zero`, `cos_zero`, `sin_neg`, `cos_neg`, `sin_periodic` and `cos_periodic` were axioms until 2026-10-05. Each
follows from `pythagorean`, `sin_add` and `cos_add` (the periodicity laws from `sin_pi` and `cos_pi` too), so each is
a theorem (the muses' review of E: provable means proved). The helpers are field algebra at `Basic`'s level: `Trig`
sits below `Ring`, so there is no ring tactic here, and `ac_rfl` does the rearranging. -/

private theorem neg_unique_trig {x y : Real} (h : x + y = 0) : y = -x := by
  have hc : -x + (x + y) = -x + 0 := by rw [h]
  rw [← add_assoc, neg_add_self, zero_add, add_zero] at hc
  exact hc

private theorem mul_neg_trig (a b : Real) : a * -b = -(a * b) := by
  have h : a * b + a * -b = 0 := by rw [← mul_distrib, add_neg, mul_zero]
  exact neg_unique_trig h

private theorem neg_neg_trig (a : Real) : -(-a) = a := (neg_unique_trig (neg_add_self a)).symm

private theorem neg_zero_trig : -(0 : Real) = 0 := (neg_unique_trig (add_zero 0)).symm

private theorem neg_one_mul_neg_one_trig : (-1 : Real) * -1 = 1 := by
  rw [mul_neg_trig, mul_one_ax, neg_neg_trig]

/-- `cos 0 = 1`. With `s = sin 0` and `c = cos 0`, the addition laws at `0 + 0` say `s = s c + c s` and
`c = c c - s s`. So `s s = s (s c + c s)`, which is `2 c (s s)`, and `c (c c) = c (c + s s)`; then
`c = c (s s + c c) = 2 c (s s) + c c = s s + c c = 1`. -/
theorem cos_zero : cos 0 = 1 := by
  have hs : sin 0 = sin 0 * cos 0 + cos 0 * sin 0 := by
    have h := sin_add 0 0
    rwa [add_zero] at h
  have hc : cos 0 = cos 0 * cos 0 - sin 0 * sin 0 := by
    have h := cos_add 0 0
    rwa [add_zero] at h
  have hp : sin 0 * sin 0 + cos 0 * cos 0 = 1 := pythagorean 0
  have hc' : cos 0 + sin 0 * sin 0 = cos 0 * cos 0 := by
    calc cos 0 + sin 0 * sin 0 = (cos 0 * cos 0 - sin 0 * sin 0) + sin 0 * sin 0 := by rw [← hc]
      _ = cos 0 * cos 0 := by rw [sub_def, add_assoc, neg_add_self, add_zero]
  have key : sin 0 * sin 0 = cos 0 * (sin 0 * sin 0) + cos 0 * (sin 0 * sin 0) := by
    calc sin 0 * sin 0 = sin 0 * (sin 0 * cos 0 + cos 0 * sin 0) := by rw [← hs]
      _ = sin 0 * (sin 0 * cos 0) + sin 0 * (cos 0 * sin 0) := mul_distrib _ _ _
      _ = cos 0 * (sin 0 * sin 0) + cos 0 * (sin 0 * sin 0) := by ac_rfl
  calc cos 0 = cos 0 * 1 := (mul_one_ax _).symm
    _ = cos 0 * (sin 0 * sin 0 + cos 0 * cos 0) := by rw [hp]
    _ = cos 0 * (sin 0 * sin 0) + cos 0 * (cos 0 * cos 0) := mul_distrib _ _ _
    _ = cos 0 * (sin 0 * sin 0) + cos 0 * (cos 0 + sin 0 * sin 0) := by rw [hc']
    _ = cos 0 * (sin 0 * sin 0) + (cos 0 * cos 0 + cos 0 * (sin 0 * sin 0)) := by rw [mul_distrib]
    _ = (cos 0 * (sin 0 * sin 0) + cos 0 * (sin 0 * sin 0)) + cos 0 * cos 0 := by ac_rfl
    _ = sin 0 * sin 0 + cos 0 * cos 0 := by rw [← key]
    _ = 1 := hp

/-- `sin 0 = 0`: `sin 0 = sin 0 * cos 0 + cos 0 * sin 0 = sin 0 + sin 0`, since `cos 0 = 1`. -/
theorem sin_zero : sin 0 = 0 := by
  have hs : sin 0 = sin 0 * cos 0 + cos 0 * sin 0 := by
    have h := sin_add 0 0
    rwa [add_zero] at h
  rw [cos_zero, mul_one_ax, one_mul_thm] at hs
  have hc : -(sin 0) + sin 0 = -(sin 0) + (sin 0 + sin 0) := by rw [← hs]
  rw [neg_add_self, ← add_assoc, neg_add_self, zero_add] at hc
  exact hc.symm

/-- `tan 0 = 0`. PROMOTED from axiom to theorem (2026-06-27 audit): `tan 0 =
sin 0 / cos 0 = 0 / 1 = 0` (`tan_def` needs `cos 0 = 1 ≠ 0`; `0/1 = 0·(1/1) = 0`
via `div_def` + `zero_mul`, all `Basic`-level — no downstream tactic needed). -/
theorem tan_zero : tan 0 = 0 := by
  have hc : cos 0 ≠ 0 := by rw [cos_zero]; exact one_ne_zero
  rw [tan_def 0 hc, sin_zero, cos_zero, div_def 0 1 one_ne_zero, zero_mul]

/-- `cos (-x) = cos x`. The addition laws at `x + -x = 0` are two linear equations in `u = cos (-x)` and
`v = sin (-x)`: `S u + C v = 0` and `C u - S v = 1`, with `S = sin x`, `C = cos x`. Their determinant is
`-(S S + C C) = -1`, so they have one solution: `u = S (S u + C v) + C (C u - S v) = C`. -/
theorem cos_neg (x : Real) : cos (-x) = cos x := by
  have hA := sin_add x (-x)
  rw [add_neg, sin_zero] at hA
  have hB := cos_add x (-x)
  rw [add_neg, cos_zero] at hB
  have e1 : sin x * (sin x * cos (-x)) + sin x * (cos x * sin (-x)) = 0 := by
    rw [← mul_distrib, ← hA, mul_zero]
  have e2 : cos x * (cos x * cos (-x)) + -(sin x * (cos x * sin (-x))) = cos x := by
    have hT : sin x * (cos x * sin (-x)) = cos x * (sin x * sin (-x)) := by ac_rfl
    rw [hT, ← mul_neg_trig, ← mul_distrib, ← sub_def, ← hB, mul_one_ax]
  calc cos (-x) = 1 * cos (-x) := (one_mul_thm _).symm
    _ = (sin x * sin x + cos x * cos x) * cos (-x) := by rw [pythagorean x]
    _ = sin x * (sin x * cos (-x)) + cos x * (cos x * cos (-x)) := by
        rw [mul_comm _ (cos (-x)), mul_distrib]; ac_rfl
    _ = (sin x * (sin x * cos (-x)) + sin x * (cos x * sin (-x)))
          + (cos x * (cos x * cos (-x)) + -(sin x * (cos x * sin (-x)))) := by
        rw [← add_zero (sin x * (sin x * cos (-x)) + cos x * (cos x * cos (-x))),
          ← add_neg (sin x * (cos x * sin (-x)))]
        ac_rfl
    _ = cos x := by rw [e1, e2, zero_add]

/-- `sin (-x) = -(sin x)`: the same two equations, solved for `v`: `S + v = (C (S u) - S (S v)) + (S (S v) + C (C v))
= C (S u + C v) = 0`. -/
theorem sin_neg (x : Real) : sin (-x) = -(sin x) := by
  have hA := sin_add x (-x)
  rw [add_neg, sin_zero] at hA
  have hB := cos_add x (-x)
  rw [add_neg, cos_zero] at hB
  have e1 : cos x * (sin x * cos (-x)) + cos x * (cos x * sin (-x)) = 0 := by
    rw [← mul_distrib, ← hA, mul_zero]
  have e2 : cos x * (sin x * cos (-x)) + -(sin x * (sin x * sin (-x))) = sin x := by
    have hM : cos x * (sin x * cos (-x)) = sin x * (cos x * cos (-x)) := by ac_rfl
    rw [hM, ← mul_neg_trig, ← mul_distrib, ← sub_def, ← hB, mul_one_ax]
  have hv : sin (-x) = sin x * (sin x * sin (-x)) + cos x * (cos x * sin (-x)) := by
    calc sin (-x) = 1 * sin (-x) := (one_mul_thm _).symm
      _ = (sin x * sin x + cos x * cos x) * sin (-x) := by rw [pythagorean x]
      _ = sin x * (sin x * sin (-x)) + cos x * (cos x * sin (-x)) := by
          rw [mul_comm _ (sin (-x)), mul_distrib]; ac_rfl
  apply neg_unique_trig
  calc sin x + sin (-x)
      = (cos x * (sin x * cos (-x)) + -(sin x * (sin x * sin (-x))))
          + (sin x * (sin x * sin (-x)) + cos x * (cos x * sin (-x))) := by rw [e2, ← hv]
    _ = (cos x * (sin x * cos (-x)) + cos x * (cos x * sin (-x)))
          + (sin x * (sin x * sin (-x)) + -(sin x * (sin x * sin (-x)))) := by ac_rfl
    _ = 0 := by rw [e1, add_neg, add_zero]

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

/-- `(1 + 1) * pi = pi + pi`. -/
private theorem two_pi_trig : (1 + 1) * pi = pi + pi := by
  rw [mul_comm, mul_distrib, mul_one_ax]

/-- `sin (x + 2 pi) = sin x`, from the addition law twice: `sin pi = 0` and `cos pi = -1` make each half-turn a
sign change, `sin (x + pi + pi) = -(-(sin x))`. A theorem since 2026-10-05. -/
theorem sin_periodic (x : Real) : sin (x + (1 + 1) * pi) = sin x := by
  rw [two_pi_trig, ← add_assoc, sin_add (x + pi) pi, sin_add x pi, cos_pi, sin_pi, mul_zero, mul_zero,
    add_zero, add_zero, mul_assoc, neg_one_mul_neg_one_trig, mul_one_ax]

/-- `cos (x + 2 pi) = cos x`, the same way. A theorem since 2026-10-05. -/
theorem cos_periodic (x : Real) : cos (x + (1 + 1) * pi) = cos x := by
  rw [two_pi_trig, ← add_assoc, cos_add (x + pi) pi, cos_add x pi, cos_pi, sin_pi, mul_zero, mul_zero,
    sub_def, sub_def, neg_zero_trig, add_zero, add_zero, mul_assoc, neg_one_mul_neg_one_trig, mul_one_ax]

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

-- tanh: zero at zero, odd. Its range bounds `tanh_lt_one` and `neg_one_lt_tanh` were
-- axioms here until 2026-10-04; they are THEOREMS in `MachLib/Linarith.lean` now, derived
-- from `Hyperbolic.lean`'s linking axiom `tanh_eq_sinh_div_cosh` and the defining
-- equations of `sinh`/`cosh` (the owner's axiom audit: a law the others prove is not
-- assumed).
axiom tanh_zero     : tanh 0 = 0
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
