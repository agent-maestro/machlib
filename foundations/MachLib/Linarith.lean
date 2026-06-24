/-
MachLib.Linarith — `mach_positivity` + `mach_linarith` tactics.

This is MachLib's pragmatic substitute for Mathlib's `positivity`
and `linarith`. Two tactics, each scoped to the canonical Forge-
emitted obligation shapes:

`mach_positivity` v1
--------------------
Closes goals of the form `0 ≤ expr` or `0 < expr` by recursively
decomposing the expression with the existing `MachLib.Forge`
combinators:

  * `add_nonneg`, `add_pos`, `add_pos_of_nonneg_pos` — sums
  * `mul_nonneg`, `mul_pos` — products
  * `div_nonneg_of_nonneg_pos` — division by a positive
  * `exp_nonneg` — exp values (via Forge bridge)
  * `ofScientific_pos` / `ofScientific_nonneg` — decimal literals
  * `zero_lt_one_ax`, `le_refl`, `nonneg_of_pos` — atomic closers
  * `assumption` — closes from a matching hypothesis

The implementation uses `repeat (first | ...)` rather than a
true positivity-extension framework. This keeps v1 tractable and
covers the actual shapes in the engine's obligation backlog
(ACES Narkowicz, Rayleigh phase / scatter coefficient, particles
lifetime scaling — see `monogate-engine/proofs/Proofs/README.md`
for the per-theorem map).

`mach_linarith` v1
------------------
Closes goals that are linear combinations of inequality
hypotheses + the standard order axioms. Specifically the
"convex-band" shape Forge emits for `*_in_unit_band` theorems:
given `-1 ≤ x ≤ 1`, derive `0 ≤ a + b*x ≤ 1` when `a + b = 1`
and `a, b ≥ 0`. (Pulse, atmosphere sun-disk, animation pulse.)

Implementation: a curated `simp only` against the Forge
interval-arithmetic library + `apply` chains. Genuine
Fourier-Motzkin elimination is v2 once a concrete blocker
forces it (probably the IK joint-limit smoothstep sweep).

Out of scope (v2 / future)
--------------------------
  * Hypothesis-driven Fourier-Motzkin (genuinely needs metaprogramming)
  * `nlinarith` (nonlinear arithmetic — far harder)
  * `positivity` extensions (registering new structural lemmas
    via attribute — needs a custom elaborator)
-/

import MachLib.Basic
import MachLib.Forge
import MachLib.Trig

namespace MachLib
namespace Real

/-! ### Strict-positive division helpers (for `mach_positivity`)

`MachLib.Forge` ships `div_nonneg_of_nonneg_pos` and
`one_div_nonneg_of_pos` (the `≤` versions). The `<` versions
below close the strict-positive division shape Forge emits for
the Rayleigh / Mie scattering coefficients (`k / w⁴`,
`k₀ / (1 + g² - 2g·cosθ)^(3/2)`, etc.).

`one_div_pos_of_pos` is held as an axiom in the same spirit as
the `≤` version it parallels — derivable from `mul_inv` plus a
case-split on the sign of `1/b`, but the case-split requires
`mul_neg` distributivity which `MachLib.Basic` doesn't yet
expose. The axiom is true in any standard ordered field. -/

/-- `0 < b → 0 < 1 / b`. Strict-positive form of the inverse. -/
axiom one_div_pos_of_pos {b : Real} (hb : 0 < b) : 0 < 1 / b

/-- `0 < a → 0 < b → 0 < a / b`. -/
theorem div_pos_of_pos_pos
    {a b : Real} (ha : 0 < a) (hb : 0 < b) : 0 < a / b := by
  rw [div_def a b (ne_of_gt hb)]
  exact mul_pos ha (one_div_pos_of_pos hb)

/-! ### Square non-negativity

`MachLib.Basic` exposes `mul_pos` (strict-positive product) but
the standard ordered-field fact `0 ≤ x * x` for arbitrary `x`
needs a sign case-split combined with `(-x) * (-x) = x * x`.
The latter requires `mul_neg` distributivity which `Basic`
doesn't yet expose (cf. the C-242 note in `Forge.lean`). Held
as an axiom in the same spirit as `one_div_nonneg_of_pos` and
`mul_lt_mul_of_pos_right` — true in any ordered field. -/

/-- `0 ≤ x * x`. The "squares are non-negative" fact. Closes the
Rayleigh phase / Mie scattering / particle drag bounds family
where the Forge kernel writes `1 + cos² θ` or `(1 - g)²` shapes. -/
axiom sq_nonneg (x : Real) : 0 ≤ x * x

/-! ### `mach_positivity` tactic

Closes `0 ≤ expr` and `0 < expr` goals by recursive structural
decomposition. Recursion is via `macro_rules` (the macro calls
itself on all subgoals via `<;>`). This is necessary because
`repeat (first | ...)` doesn't traverse multi-goal results from
`apply`-style tactics reliably — when a structural lemma fires
and produces N subgoals, we want all N to be closed by the same
recursive cascade. -/

syntax (name := machPositivity) "mach_positivity" : tactic

macro_rules
  | `(tactic| mach_positivity) => `(tactic|
      first
      -- Atomic closers (cheapest-first)
      | exact zero_lt_one_ax
      | exact le_refl 0
      | exact le_of_lt zero_lt_one_ax
      | assumption
      | (apply le_of_lt; assumption)
      -- Literal positivity (Forge bridge)
      | exact ofScientific_pos _ (by decide)
      | exact ofScientific_nonneg _ (by decide)
      -- Named-constant positivity (Trig bridge — `pi` shows up in
      -- atmosphere phase / scattering kernels via `1 / (16 * pi)`).
      | exact pi_pos
      | exact le_of_lt pi_pos
      -- `sq_nonneg` BEFORE `mul_nonneg` so `0 ≤ x * x` (with no
      -- sign info on `x`) closes via the axiom rather than
      -- splitting into two unprovable `0 ≤ x` subgoals.
      | exact sq_nonneg _
      -- Structural decompositions for `0 ≤ ...`
      | (apply add_nonneg <;> mach_positivity)
      | (apply mul_nonneg <;> mach_positivity)
      | (apply div_nonneg_of_nonneg_pos <;> mach_positivity)
      | (apply div_pos_of_pos_pos <;> mach_positivity)
      | (apply exp_nonneg)
      -- ── Forge-emitter arms (2026-06-24): close per-kernel range/nonneg
      --    obligations (sqrt/max/min/general-div/rpow) that shipped `sorry`.
      | exact sqrt_nonneg _
      | exact le_max_right _ _
      | exact le_max_left _ _
      | (apply min_nonneg <;> mach_positivity)
      | (apply div_nonneg <;> mach_positivity)
      | (apply realPow_nonneg <;> mach_positivity)
      -- Hypothesis weakening: prove `0 ≤ x` from a bound `c ≤ x` in context
      -- (e.g. a kernel `requires age ≥ 1`), reducing to `0 ≤ c`.
      | (refine le_trans ?_ (by assumption) <;> mach_positivity)
      -- Subtraction nonneg: `0 ≤ a - b` from a bound `b ≤ a` (e.g. Adam's
      -- `0 ≤ 1 - beta2` from `beta2 ≤ 1`). Reduces to proving `b ≤ a`.
      | (apply sub_nonneg_of_le <;> mach_positivity)
      -- Floor via transitive max: `FLOOR ≤ max (max .. FLOOR) ..` (e.g. a
      -- clamped composite ≥ one of its inputs).
      | (apply le_max_of_le_left <;> mach_positivity)
      | (apply le_max_of_le_right <;> mach_positivity)
      -- Affine floor: `FLOOR ≤ FLOOR + (nonneg)` (linear-interp band floors).
      | (apply le_add_of_nonneg_right <;> mach_positivity)
      -- Structural decompositions for `0 < ...`. Order matters:
      -- `add_pos_of_nonneg_pos` before `add_pos` so a sum like
      -- `a + b + c + d` with only `d` strictly-positive closes.
      | (apply add_pos_of_nonneg_pos <;> mach_positivity)
      | (apply add_pos <;> mach_positivity)
      | (apply mul_pos <;> mach_positivity)
      -- Weaken-to-nonneg bridge.
      | (apply nonneg_of_pos; mach_positivity))

/-! ### `mach_linarith` tactic — v1 stub

The convex-band closer for `0 ≤ a + b*x ∧ a + b*x ≤ 1` shapes
where `a + b = 1` and `-1 ≤ x ≤ 1`. Wraps the Forge
interval-arithmetic `interval_add_scale` lemma plus a few
literal-positivity helpers.

This is a deliberately narrow v1 — most of the obligations
tagged "linarith-blocked" in the engine table are actually
positivity problems closed by `mach_positivity`. The few
genuinely-linear cases (Pulse.in_unit_band) reduce to
`interval_add_scale` once `1/2` literal arithmetic is in scope. -/

macro "mach_linarith" : tactic => `(tactic|
  ((repeat (first
    | exact zero_lt_one_ax
    | exact (le_refl 0)
    | exact (le_refl 1)
    | exact (le_of_lt zero_lt_one_ax)
    | (apply add_nonneg)
    | (apply add_pos_of_nonneg_pos)
    | (apply le_trans)
    | exact ofScientific_pos _ (by decide)
    | exact ofScientific_nonneg _ (by decide)
    | assumption
    ))
   try done))

end Real
end MachLib
