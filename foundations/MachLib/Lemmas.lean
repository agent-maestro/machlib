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
import MachLib.Sign

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

/-- `cos x * cos x ≤ 1`. PROMOTED from axiom to theorem (2026-06-27 audit): from
`pythagorean` (`sin²+cos²=1`) and `0 ≤ sin²` (`mul_self_nonneg`, now upstream in
`Sign`), `cos² ≤ sin²+cos² = 1`. -/
theorem cos_sq_le_one (x : Real) : cos x * cos x ≤ 1 := by
  have h : cos x * cos x ≤ sin x * sin x + cos x * cos x :=
    le_add_of_nonneg_left (mul_self_nonneg (sin x))
  rwa [pythagorean x] at h

/-- `sin x * sin x ≤ 1`. PROMOTED (symmetric to `cos_sq_le_one`). -/
theorem sin_sq_le_one (x : Real) : sin x * sin x ≤ 1 := by
  have h : sin x * sin x ≤ sin x * sin x + cos x * cos x :=
    le_add_of_nonneg_right (mul_self_nonneg (cos x))
  rwa [pythagorean x] at h

-- `abs_cos_le_one` / `abs_sin_le_one` are now THEOREMS too, but proved BELOW (they
-- need `abs_mul` + the `u²≤1 ⇒ u≤1` helper, which come after this point).

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

/-! `abs_neg` / `abs_add` / `abs_le_iff` were axioms here, but `abs` is concretely
`if 0 ≤ x then x else -x`, so they are determined by the def. They are now THEOREMS
in `FPModel.lean` (2026-06-27 audit), where their proof infrastructure
(`le_abs_self`, `neg_le_abs`, `abs_le_of`, `neg_le_neg`) lives — nothing between
here and `FPModel` used them, so they moved DOWN rather than the infra moving UP. -/

/-- Multiplicativity: `abs (a * b) = abs a * abs b`. PROMOTED from axiom to theorem
(2026-06-27 audit). The 4-way sign split: `abs_of_nonneg`/`abs_of_nonpos` reduce
each `abs` to `±`, then `neg_mul`/`mul_neg`/`neg_mul_neg` close each case. Needed
at `Linarith`'s level (via `abs_mul_le_of_abs_le_one` below), so its sign-split
infra (`neg_nonneg_of_nonpos`, `neg_le_neg`, `nonpos_of_not_nonneg`,
`abs_of_nonpos`) was relocated up into `Sign.lean` to make this provable here. -/
theorem abs_mul (a b : Real) : abs (a * b) = abs a * abs b := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (mul_nonneg ha hb)]
  · have hb' : b ≤ 0 := nonpos_of_not_nonneg hb
    have hp : 0 ≤ a * (-b) := mul_nonneg ha (neg_nonneg_of_nonpos hb')
    rw [mul_neg] at hp
    have hab : a * b ≤ 0 := by
      have h2 := neg_le_neg hp; rwa [neg_neg_helper, neg_zero] at h2
    rw [abs_of_nonneg ha, abs_of_nonpos hb', abs_of_nonpos hab, mul_neg]
  · have ha' : a ≤ 0 := nonpos_of_not_nonneg ha
    have hp : 0 ≤ (-a) * b := mul_nonneg (neg_nonneg_of_nonpos ha') hb
    rw [neg_mul] at hp
    have hab : a * b ≤ 0 := by
      have h2 := neg_le_neg hp; rwa [neg_neg_helper, neg_zero] at h2
    rw [abs_of_nonpos ha', abs_of_nonneg hb, abs_of_nonpos hab, neg_mul]
  · have ha' : a ≤ 0 := nonpos_of_not_nonneg ha
    have hb' : b ≤ 0 := nonpos_of_not_nonneg hb
    have hab : 0 ≤ a * b := by
      have hp : 0 ≤ (-a) * (-b) :=
        mul_nonneg (neg_nonneg_of_nonpos ha') (neg_nonneg_of_nonpos hb')
      rwa [neg_mul_neg] at hp
    rw [abs_of_nonpos ha', abs_of_nonpos hb', abs_of_nonneg hab, neg_mul_neg]

/-- Multiplying by a magnitude-≤1 factor does not increase `abs`. PROVED (no
axiom) from `abs_mul` + `mul_le_mul_of_nonneg_left`. Peeling lemma for the
trig-amplitude band shape `abs(base · t₁ · t₂ …) ≤ base`: apply once per
bounded factor, leaving `abs base`. -/
theorem abs_mul_le_of_abs_le_one {x y : Real} (hy : abs y ≤ 1) :
    abs (x * y) ≤ abs x := by
  rw [abs_mul]
  have h := mul_le_mul_of_nonneg_left hy (abs_nonneg x)
  rwa [mul_one_ax] at h

/-- `0 ≤ u → u·u ≤ 1 → u ≤ 1`. The "square root" of a unit-square bound. -/
theorem le_one_of_sq_le_one {u : Real} (h0 : 0 ≤ u) (hsq : u * u ≤ 1) : u ≤ 1 := by
  rcases lt_total u 1 with h | h | h
  · exact le_of_lt h
  · exact le_of_eq h
  · exfalso
    have hu0 : 0 < u := lt_trans_ax zero_lt_one_ax h
    have e : (1 : Real) * u = u := by rw [mul_comm, mul_one_ax]
    have h1u : u < u * u := by
      have hm := mul_lt_mul_of_pos_right h hu0; rwa [e] at hm
    exact lt_irrefl_ax 1 (lt_of_lt_of_le (lt_trans_ax h h1u) hsq)

/-- `abs (cos x) ≤ 1`. PROMOTED from axiom to theorem (2026-06-27 audit):
`|cos|·|cos| = |cos·cos| = cos·cos ≤ 1` (`cos_sq_le_one`), then `le_one_of_sq_le_one`. -/
theorem abs_cos_le_one (x : Real) : abs (cos x) ≤ 1 := by
  apply le_one_of_sq_le_one (abs_nonneg (cos x))
  rw [← abs_mul, abs_of_nonneg (mul_self_nonneg (cos x))]
  exact cos_sq_le_one x

/-- `abs (sin x) ≤ 1`. PROMOTED (symmetric to `abs_cos_le_one`). -/
theorem abs_sin_le_one (x : Real) : abs (sin x) ≤ 1 := by
  apply le_one_of_sq_le_one (abs_nonneg (sin x))
  rw [← abs_mul, abs_of_nonneg (mul_self_nonneg (sin x))]
  exact sin_sq_le_one x

/-! ### one-sided trig bounds — PROMOTED from `Trig` axioms (2026-06-27 audit).
`sin_le_one`/`neg_one_le_sin`/`cos_le_one`/`neg_one_le_cos` follow from the squared
bounds (`sin_sq_le_one`/`cos_sq_le_one`) via the `u²≤1 ⇒ u≤1` peeling lemma — they
were axioms in `Trig` only because that infra was downstream. -/

/-- `u·u ≤ 1 → u ≤ 1` (no `0 ≤ u` premise). -/
theorem le_one_of_sq_le_one' {u : Real} (hsq : u * u ≤ 1) : u ≤ 1 := by
  by_cases h : 0 ≤ u
  · exact le_one_of_sq_le_one h hsq
  · exact le_trans (nonpos_of_not_nonneg h) (le_of_lt zero_lt_one_ax)

/-- `u·u ≤ 1 → -1 ≤ u`. -/
theorem neg_one_le_of_sq_le_one {u : Real} (hsq : u * u ≤ 1) : -1 ≤ u := by
  by_cases h : 0 ≤ u
  · have hn10 : -(1 : Real) ≤ 0 := by
      have := neg_le_neg (le_of_lt zero_lt_one_ax); rwa [neg_zero] at this
    exact le_trans hn10 h
  · have hn : 0 ≤ -u := neg_nonneg_of_nonpos (nonpos_of_not_nonneg h)
    have hsq' : (-u) * (-u) ≤ 1 := by rw [neg_mul_neg]; exact hsq
    have h2 := neg_le_neg (le_one_of_sq_le_one hn hsq')
    rwa [neg_neg_helper] at h2

theorem sin_le_one (x : Real) : sin x ≤ 1 := le_one_of_sq_le_one' (sin_sq_le_one x)
theorem cos_le_one (x : Real) : cos x ≤ 1 := le_one_of_sq_le_one' (cos_sq_le_one x)
theorem neg_one_le_sin (x : Real) : -1 ≤ sin x := neg_one_le_of_sq_le_one (sin_sq_le_one x)
theorem neg_one_le_cos (x : Real) : -1 ≤ cos x := neg_one_le_of_sq_le_one (cos_sq_le_one x)

end Real
end MachLib
