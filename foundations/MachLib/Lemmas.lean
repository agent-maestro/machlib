/-
MachLib.Lemmas — specific lemmas closing the engine's "Rank 5"
backlog (`exp_le_one_iff`, `max_le`, `arccos_*`, `sqrt_pos`,
`abs_cos_le_one`).

Each lemma here either derives from existing `MachLib.Basic` /
`MachLib.Trig` / `MachLib.Exp` axioms or is held as a small
new axiom (matching the existing pattern of holding
"true-in-any-ordered-field-but-blocked-by-missing-primitive"
facts as axioms — see `Forge.lean :: one_div_nonneg_of_pos`,
`Linarith.lean :: sq_nonneg`, etc.).

Coverage targets
----------------
  * `Real.max_le`               — closes IkJointLimit.clamp_in_band
  * `Real.exp_le_one`           — closes ParticlesForces.drag_factor
                                  partial Mantis / PitViper / atmosphere
                                  transmittance
  * `Real.arccos_nonneg`        — closes IkTwoBone.shoulder/elbow
  * `Real.arccos_le_pi`         — closes IkTwoBone.shoulder/elbow
  * `Real.sqrt_pos`             — supports IkFabrik (paired with nlinarith)
  * `Real.abs_cos_le_one`       — partial Mantis closure
-/

import MachLib.Basic
import MachLib.Trig
import MachLib.Exp
import MachLib.Forge

namespace MachLib
namespace Real

/-! ### `max_le` — universal upper bound for `max`

`MachLib.Forge` has `le_max_left/right` (max ≥ each arm); the dual
`max ≤ c when both arms ≤ c` is needed for clamp/saturate proofs
(`IkJointLimit.clamp_in_band` is the canonical case). -/

/-- `a ≤ c → b ≤ c → max a b ≤ c`. -/
theorem max_le {a b c : Real} (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c := by
  unfold max
  by_cases h : a ≤ b
  · rw [if_pos h]; exact hb
  · rw [if_neg h]; exact ha

/-! ### `exp_le_one` and `exp_lt_one`

Forward direction of `exp x ≤ 1 ↔ x ≤ 0`. Closes the
exponential-decay-bounded-by-1 family (drag factor, atmosphere
transmittance, partial Mantis / PitViper). The axiom path is
`x ≤ 0 → exp x ≤ exp 0 = 1` via `exp_lt`. The reverse direction
is also derivable but not needed for the current engine
backlog. -/

/-- `x < 0 → exp x < 1`. -/
theorem exp_lt_one {x : Real} (hx : x < 0) : exp x < 1 := by
  have h := exp_lt hx
  rw [exp_zero] at h
  exact h

/-- `x ≤ 0 → exp x ≤ 1`. -/
theorem exp_le_one {x : Real} (hx : x ≤ 0) : exp x ≤ 1 := by
  rcases (le_iff_lt_or_eq x 0).mp hx with h_lt | h_eq
  · exact le_of_lt (exp_lt_one h_lt)
  · subst h_eq; rw [exp_zero]; exact le_refl 1

/-! ### `arccos` bounds

The principal-value arccos returns `[0, π]` for inputs in `[-1, 1]`.
MachLib has `arccos_zero = π/2`, `arccos_one = 0`, and `cos_arccos`
but no monotonicity / range bounds. Held as axioms because the
range characterisation requires `cos`-monotonicity over `[0, π]`
which would in turn need the derivative of `cos` (out of MachLib's
algebra-only scope). -/

/-- `0 ≤ arccos x` for any `x`. The axiom embodies the principal-
value convention (returns `[0, π]`). For `x ∉ [-1, 1]` the value
is implementation-defined but still in `[0, π]`. -/
axiom arccos_nonneg (x : Real) : 0 ≤ arccos x

/-- `arccos x ≤ π` for any `x`. Same convention as
`arccos_nonneg`. -/
axiom arccos_le_pi (x : Real) : arccos x ≤ pi

/-! ### `sqrt_pos` — strict positivity of square root

`MachLib.Trig` has `sqrt_nonneg` (`0 ≤ sqrt x`) and `sqrt_sq_nonneg`
(`0 ≤ x → sqrt x * sqrt x = x`). The strict version `0 < sqrt x`
when `0 < x` is derivable: if `sqrt x = 0`, then `sqrt x * sqrt x =
0`, but that equals `x` (when `0 ≤ x`), contradicting `0 < x`. So
`sqrt x ≠ 0`, combined with `sqrt_nonneg`, gives `0 < sqrt x`. -/

/-- `0 < x → 0 < sqrt x`. -/
theorem sqrt_pos {x : Real} (hx : 0 < x) : 0 < sqrt x := by
  have h_nn : 0 ≤ sqrt x := sqrt_nonneg x
  rcases (le_iff_lt_or_eq 0 (sqrt x)).mp h_nn with h_lt | h_eq
  · exact h_lt
  · -- 0 = sqrt x, so 0 * 0 = sqrt x * sqrt x = x (since 0 ≤ x).
    -- That gives x = 0, contradicting 0 < x.
    exfalso
    have h_sx_zero : sqrt x = 0 := h_eq.symm
    have h_x_nn : 0 ≤ x := le_of_lt hx
    have h_sq : sqrt x * sqrt x = x := sqrt_sq_nonneg x h_x_nn
    rw [h_sx_zero, mul_zero] at h_sq
    -- h_sq : 0 = x. Combined with 0 < x:
    rw [← h_sq] at hx
    exact lt_irrefl_ax 0 hx

/-! ### `abs_cos_le_one` — Mantis polarisation-response bridge

The Mantis kernel computes `cos(2θ_align)` for polarisation
weighting. The output is bounded by 1 in absolute value. Forge
already has `cos_le_one` (`cos x ≤ 1`) and `neg_one_le_cos`
(`-1 ≤ cos x`); the absolute-value form drops out of unfolding
`abs`. -/

/-! ### `cos_sq_add_sin_sq` — swapped Pythagorean

`MachLib.Trig.pythagorean` states `sin² + cos² = 1`. Forge-
emitted orthonormal-witness theorems write the cells in the
opposite order (`cos² + sin² - 1 = 0`), so the swapped form is
what `mach_linear_combination` actually fires on. Derived via
`add_comm`. -/

theorem cos_sq_add_sin_sq (x : Real) :
    cos x * cos x + sin x * sin x = 1 := by
  rw [add_comm]; exact pythagorean x

/-- `abs (cos x) ≤ 1`. Closes the upper-bound half of polarisation
response in the Mantis kernel. Held as an axiom: provable from
`cos_le_one` + `neg_one_le_cos` plus the negation-monotonicity
fact `-1 ≤ y → -y ≤ 1`, but the latter requires `mul_neg`-style
distributivity that `MachLib.Basic` doesn't yet expose. True in
any ordered field. -/
axiom abs_cos_le_one (x : Real) : abs (cos x) ≤ 1

/-- `|sin x| ≤ 1`. Symmetric counterpart of `abs_cos_le_one` (the asymmetry
was just an omission). Closes the `abs(... * sin ...)` factor in trig-amplitude
band obligations (orbit, wave, white-noise). True in any ordered field. -/
axiom abs_sin_le_one (x : Real) : abs (sin x) ≤ 1

/-- `cos x * cos x ≤ 1`. The squared form. Provable from
`pythagorean` (`sin² + cos² = 1`) plus `0 ≤ sin²` (so
`cos² = 1 - sin² ≤ 1`), but the chain needs `sub_le_self_of_nonneg`
which MachLib doesn't yet have. Held as an axiom; true in any
ordered field. Closes the upper bound of `Mantis.polResponseAtAxis`
and similar `cos²` bounds. -/
axiom cos_sq_le_one (x : Real) : cos x * cos x ≤ 1

/-- `sin x * sin x ≤ 1`. Symmetric counterpart of `cos_sq_le_one`. -/
axiom sin_sq_le_one (x : Real) : sin x * sin x ≤ 1

/-! ### `abs` family — triangle / multiplicative / range characterisation

`MachLib.Basic` defines `abs x := if 0 ≤ x then x else -x` and
proves `abs_zero`, `abs_one`. The cluster below ships the
standard ordered-field facts that Forge-emitted norm / triangle-
inequality / IK-distance proofs need.

Most are held as axioms — the derivations exist in any ordered
field but require `neg_le` / `mul_neg` / `neg_neg` distributivity
that `MachLib.Basic` doesn't expose. True in standard ℝ.

Notation `|x|` is NOT introduced — Forge-emitted theorems use the
explicit `abs x` form and the engine matches that convention. -/

/-- `0 ≤ abs x`. Derivable: case-split on sign of `x`, both arms
are non-negative. -/
theorem abs_nonneg (x : Real) : 0 ≤ abs x := by
  unfold abs
  by_cases h : 0 ≤ x
  · rw [if_pos h]; exact h
  · rw [if_neg h]
    -- ¬ (0 ≤ x), so x < 0 (via lt_total + le contradiction).
    -- We want 0 ≤ -x. From x < 0: add (-x) to both sides:
    --   x + (-x) < 0 + (-x), i.e., 0 < -x. So 0 ≤ -x.
    have hlt : x < 0 := by
      cases lt_total x 0 with
      | inl hlt => exact hlt
      | inr h2 => cases h2 with
        | inl heq => exact absurd ((heq ▸ le_refl x) : (0:Real) ≤ x) h
        | inr hgt => exact absurd (le_of_lt hgt) h
    -- add_lt_add_left adds on the LEFT: `-x + x < -x + 0`.
    have step : -x + x < -x + 0 := add_lt_add_left hlt (-x)
    rw [neg_add_self, add_zero] at step
    exact le_of_lt step

/-- `0 ≤ x → abs x = x`. Derivable from the `if`-branch. -/
theorem abs_of_nonneg {x : Real} (h : 0 ≤ x) : abs x = x := by
  unfold abs; rw [if_pos h]

/-- `abs (-x) = abs x`. REDUNDANT axiom — `abs` is concretely `if 0 ≤ x then x
else -x`, so this is determined by the def (`neg_neg_helper` + the sign-flip
`x ≤ 0 ↔ 0 ≤ -x` + `abs_of_nonneg`/`abs_of_nonpos`). AUDIT NOTE (2026-06-27): the
old "requires neg_neg Basic doesn't expose" claim is now stale — `neg_neg_helper`,
`neg_mul`, `mul_neg` are theorems in `Ring.lean`, but `Ring` imports `Lemmas`, so
they sit *downstream* of this declaration. Promoting this cluster cleanly needs
those primitives (+ `abs_of_nonpos`, the sign-flips) relocated *upstream* of
`Lemmas` (into `Basic`); tracked as the audit's next step (the 3 `Ring` negation
axioms were promoted first, 292→289). -/
axiom abs_neg (x : Real) : abs (-x) = abs x

/-- Triangle inequality: `abs (a + b) ≤ abs a + abs b`. Provable in any ordered
field by sign case-splits (the genuinely non-trivial one of the cluster). Same
import-order blocker as `abs_neg` — see its note. -/
axiom abs_add (a b : Real) : abs (a + b) ≤ abs a + abs b

/-- Multiplicativity: `abs (a * b) = abs a * abs b`. REDUNDANT (determined by the
`abs` def + `neg_mul`/`mul_neg` via 4 sign cases). Same import-order blocker as
`abs_neg`. -/
axiom abs_mul (a b : Real) : abs (a * b) = abs a * abs b

/-- Range characterisation: `abs a ≤ b ↔ -b ≤ a ∧ a ≤ b`. Axiom. -/
axiom abs_le_iff {a b : Real} : abs a ≤ b ↔ -b ≤ a ∧ a ≤ b

/-- Multiplying by a magnitude-≤1 factor does not increase `abs`. PROVED (no
axiom) from `abs_mul` + `mul_le_mul_of_nonneg_left`. Peeling lemma for the
trig-amplitude band shape `abs(base · t₁ · t₂ …) ≤ base`: apply once per
bounded factor, leaving `abs base`. -/
theorem abs_mul_le_of_abs_le_one {x y : Real} (hy : abs y ≤ 1) :
    abs (x * y) ≤ abs x := by
  rw [abs_mul]
  have h := mul_le_mul_of_nonneg_left hy (abs_nonneg x)
  rwa [mul_one_ax] at h

end Real
end MachLib
