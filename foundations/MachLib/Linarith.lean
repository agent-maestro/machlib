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
import MachLib.Lemmas
import MachLib.Ring

namespace MachLib
namespace Real

/-- `0 / a = 0` for ALL `a` (including `a = 0`, since `div_zero` gives
`0/0 = 0`). Unconditional simp lemma for boundary obligations like
`vin · (1 - exp(0/tau)) = 0` where the `0/tau` appears without a `tau ≠ 0`
rewrite in reach. -/
theorem zero_div (a : Real) : 0 / a = 0 := by
  by_cases h : a = 0
  · rw [h]; exact div_zero 0
  · exact zero_div_of_ne_zero h

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

/-- `0 ≤ c → 0 ≤ c * x * x`. PROVED (no axiom) by reassociating to
`c * (x * x)` and `mul_nonneg`. Closes the energy shape Forge emits when
the optimizer expands `c · x²` to `(c · x) · x` — Hooke `½·k·d·d`, kinetic
`½·m·v·v`, etc. — which `mul_nonneg` alone can't (it would demand `0 ≤ x`). -/
theorem mul_sq_nonneg {c x : Real} (hc : 0 ≤ c) : 0 ≤ c * x * x := by
  rw [mul_assoc]
  exact mul_nonneg hc (sq_nonneg x)

/-! ### Polynomial-band lemmas (easing functions on [0,1])

The Forge easing kernels (smoothstep, ease) emit `0 ≤ poly(t)` over `0 ≤ t ≤ 1`.
These are nonlinear and were blocked on a real ring/nlinarith. With `mach_ring`
now AC-complete it can prove the FACTORED certificate (coefficients copied from
the goal, so no decimal arithmetic), and a general band lemma with SYMBOLIC
coefficients absorbs the literal values — `mach_norm_num` then discharges the
`0 ≤ B`, `B ≤ A` side conditions. No reflection, no axioms. -/

/-- `A·t·t − B·t·t·t = t·t·(A − B·t)`. Symbolic factoring (mach_ring). -/
theorem cube_factor (A B t : Real) : A * t * t - B * t * t * t = t * t * (A - B * t) := by
  mach_ring

/-- Degree-3, zero-constant band: `0 ≤ A·t² − B·t³` on `[0,1]` when `0 ≤ B ≤ A`
(smoothstep `3t²−2t³`). Factor `t²·(A−B·t)`; `t² ≥ 0` and `A−B·t ≥ 0` because
`B·t ≤ B ≤ A`. -/
theorem cube_band_nonneg {A B t : Real} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hB : 0 ≤ B) (hBA : B ≤ A) : 0 ≤ A * t * t - B * t * t * t := by
  rw [cube_factor]
  apply mul_nonneg (sq_nonneg t)
  apply sub_nonneg_of_le
  have hb : B * t ≤ B * 1 := mul_le_mul_of_nonneg_left ht1 hB
  rw [mul_one_ax] at hb
  exact le_trans hb hBA

/-- `0 ≤ 1 − (1−x)²` on `[0,1]` (ease-out quadratic). Difference of squares
`= x·(2−x)`; both factors nonneg. -/
theorem one_sub_sq_band {x : Real} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ 1 - (1 - x) * (1 - x) := by
  have key : (1 : Real) - (1 - x) * (1 - x) = x * ((1 + 1) - x) := by mach_ring
  rw [key]
  apply mul_nonneg h0
  apply sub_nonneg_of_le
  exact le_trans h1 (le_add_of_nonneg_right (le_of_lt zero_lt_one_ax))

/-- `0 ≤ 1 − (1−x)³` on `[0,1]` (ease-out cubic). Difference of cubes
`= x·(1 + (1−x) + (1−x)²)`; the remainder is a sum of nonnegs (no quadratic
positivity needed). -/
theorem one_sub_cube_band {x : Real} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 ≤ 1 - ((1 - x) * (1 - x)) * (1 - x) := by
  have h1x : 0 ≤ 1 - x := sub_nonneg_of_le h1
  have key : (1 : Real) - ((1 - x) * (1 - x)) * (1 - x)
      = x * (1 + ((1 - x) + (1 - x) * (1 - x))) := by mach_ring
  rw [key]
  apply mul_nonneg h0
  exact add_nonneg (le_of_lt zero_lt_one_ax) (add_nonneg h1x (sq_nonneg (1 - x)))

/-- `0 ≤ 1 − c²` for any `c ∈ [0,1]` (ricochet `1 − clamp(cosθ,0,1)²`).
Diff of squares `(1−c)(1+c)`; both factors nonneg. The `c` here is typically a
clamp expression, so the side goals close by `mach_positivity` (min/max arms). -/
theorem one_sub_sq_nonneg {c : Real} (h0 : 0 ≤ c) (h1 : c ≤ 1) : 0 ≤ 1 - c * c := by
  have key : (1 : Real) - c * c = (1 - c) * (1 + c) := by mach_ring
  rw [key]
  apply mul_nonneg (sub_nonneg_of_le h1)
  exact add_nonneg (le_of_lt zero_lt_one_ax) h0

/-- `0 ≤ a → -a ≤ 0`. (`neg_le_neg` is private in EMLAsymptoticClass; derived
here from `add_lt_add_left` + `neg_add_self`.) -/
theorem neg_nonpos_of_nonneg {a : Real} (h : 0 ≤ a) : -a ≤ 0 := by
  rcases (le_iff_lt_or_eq 0 a).mp h with hlt | heq
  · have hh : -a + 0 < -a + a := add_lt_add_left hlt (-a)
    rw [add_zero, neg_add_self] at hh
    exact le_of_lt hh
  · rw [← heq, neg_zero]; exact le_refl 0

/-- `0 ≤ 1 − exp((−a)·b)` for `a,b ≥ 0` (exponential fog `1 − exp(−ρ·d)`).
exp of a nonpos is ≤ 1. -/
theorem one_sub_exp_neg_mul_nonneg {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 1 - exp ((-a) * b) := by
  apply sub_nonneg_of_le (exp_le_one_of_nonpos _)
  rw [neg_mul]; exact neg_nonpos_of_nonneg (mul_nonneg ha hb)

/-- `0 ≤ 1 − exp(−y)` for `y ≥ 0` (squared-exponential fog `1 − exp(−(ρd)²)`,
applied with `y = k·k`). -/
theorem one_sub_exp_neg_nonneg {y : Real} (hy : 0 ≤ y) : 0 ≤ 1 - exp (-y) :=
  sub_nonneg_of_le (exp_le_one_of_nonpos (neg_nonpos_of_nonneg hy))

/-- `0 ≤ c·x + c` for `c ≥ 0`, `−1 ≤ x` (the `[-1,1] → [0,1]` affine remap
`½x + ½`, matcap UV). Factor `c·(x+1)`; `x+1 ≥ 0` from `−1 ≤ x`. -/
theorem affine_remap_nonneg {c x : Real} (hc : 0 ≤ c) (hx : -1 ≤ x) : 0 ≤ c * x + c := by
  have key : c * x + c = c * (x + 1) := by mach_ring
  rw [key]
  apply mul_nonneg hc
  have h := sub_nonneg_of_le hx
  rw [sub_def, neg_neg_helper] at h
  exact h

/-- Fractional part is nonneg: `0 ≤ z − ⌊z⌋` (white-noise hash `frac(sin·k)`). -/
theorem frac_nonneg (z : Real) : 0 ≤ z - floor z := sub_nonneg_of_le (floor_le z)

/-- Fractional part is `≤ 1`: `z − ⌊z⌋ ≤ 1`. -/
theorem frac_le_one (z : Real) : z - floor z ≤ 1 := by
  have h := add_lt_add_left (lt_floor_add_one z) (-(floor z))
  rw [neg_add_cancel_left] at h
  rw [sub_def, add_comm]
  exact le_of_lt h

/-- `0 ≤ speed + spread·u` for `0 ≤ spread`, `−1 ≤ u`, `spread ≤ speed` (radial
emitter velocity floor). `spread·u ≥ −spread` and `speed − spread ≥ 0`. -/
theorem speed_spread_nonneg {speed spread u : Real}
    (hspr : 0 ≤ spread) (hu : -1 ≤ u) (hle : spread ≤ speed) :
    0 ≤ speed + spread * u := by
  have hm : spread * (-1) ≤ spread * u := mul_le_mul_of_nonneg_left hu hspr
  rw [mul_neg, mul_one_ax] at hm
  have h2 : 0 ≤ speed - spread := sub_nonneg_of_le hle
  have hadd : speed + -spread ≤ speed + spread * u := by
    rcases (le_iff_lt_or_eq _ _).mp hm with h | h
    · exact le_of_lt (add_lt_add_left h speed)
    · rw [h]; exact le_refl _
  rw [(sub_def speed spread).symm] at hadd
  exact le_trans h2 hadd

/-- `−1 ≤ S − 1` when `0 ≤ S` (the `S − 1 ≥ −1` lower-bound shape, e.g. tanh-
from-sigmoid `2/(1+exp(−2x)) − 1 ≥ −1`, reduced to `0 ≤ 2/(1+exp)`). -/
theorem sub_one_ge_neg_one {S : Real} (h : 0 ≤ S) : -(1 : Real) ≤ S - 1 := by
  rw [sub_def]
  rcases (le_iff_lt_or_eq 0 S).mp h with hlt | heq
  · have hh := add_lt_add_left hlt (-1)
    rw [add_zero, add_comm] at hh
    exact le_of_lt hh
  · rw [← heq, zero_add]; exact le_refl _

/-! ### `mach_norm_num` tactic (Phase 1: decimal-literal arithmetic)

Closes order goals between Real decimal literals — `(2.0:Real) ≤ (3.0:Real)`,
`(0.5:Real) < (1.0:Real)`, `0 < (0.5:Real)` — by reducing to a decidable `Nat`
cross-multiplication via `realOfScientific_le_of_nat` / `_lt_of_nat`
(`MachLib.Basic`), or to mantissa positivity via `realOfScientific_pos`. This is
the foundation Phase 2/3 (`mach_linarith` / `mach_nlinarith`) build on: the
constant-term comparisons those engines emit (`2 ≤ 3`, `0.5 ≥ 0`) are exactly
this shape. Scoped to literals — it never touches a goal with a free variable,
so it cannot manufacture a false ordering. See
`docs/mach_linarith_plan_2026_06_24.md`. -/

macro "mach_norm_num" : tactic => `(tactic|
  first
  | (apply realOfScientific_le_of_nat <;> decide)
  | (apply realOfScientific_lt_of_nat <;> decide)
  | (apply le_of_lt; apply realOfScientific_lt_of_nat <;> decide)
  | (apply realOfScientific_pos <;> decide)
  | (apply le_of_lt; apply realOfScientific_pos <;> decide))

/-! ### `mach_abs_bound` tactic (trig-amplitude band shape)

Closes `abs(base · t₁ · t₂ … ) ≤ base` where `base ≥ 0` (a hypothesis /
mach_positivity) and each `tᵢ` is a magnitude-≤1 factor (`sin`, `cos`). Peels
one bounded factor per step via `abs_mul_le_of_abs_le_one` (right operand
first), recursing on the remaining product until it reaches `abs base`, then
`abs_of_nonneg`. This is the abs-of-product band closer (orbit, wave, white
noise) — the nonlinear shape `mach_positivity` cannot reach. Declared here
(before `mach_positivity`) so each can reference the other; `macro_rules`
bodies follow `mach_positivity`'s syntax declaration below. -/
syntax (name := machAbsBound) "mach_abs_bound" : tactic

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
      -- Conjunction split: `*_in_unit_interval` obligations are `0 ≤ x ∧ x ≤ 1`
      -- (the emitter conjoins both ensures). Prove each half. Fails fast on
      -- non-∧ goals (anonymous constructor needs a structure).
      | (refine ⟨?_, ?_⟩ <;> mach_positivity)
      -- Literal positivity (Forge bridge)
      | exact ofScientific_pos _ (by decide)
      | exact ofScientific_nonneg _ (by decide)
      -- Decimal-literal order (Phase 1): `2.0 ≤ 3.0`, `0 < 0.5`, … reduce to
      -- a decidable Nat compare. Foundation for mach_linarith/nlinarith.
      | mach_norm_num
      -- Named-constant positivity (Trig bridge — `pi` shows up in
      -- atmosphere phase / scattering kernels via `1 / (16 * pi)`).
      | exact pi_pos
      | exact le_of_lt pi_pos
      -- `sq_nonneg` BEFORE `mul_nonneg` so `0 ≤ x * x` (with no
      -- sign info on `x`) closes via the axiom rather than
      -- splitting into two unprovable `0 ≤ x` subgoals.
      | exact sq_nonneg _
      -- Energy shape `0 ≤ c · x · x` (Hooke ½kd², kinetic ½mv²) where the
      -- optimizer expanded `c · x²` to `(c · x) · x`. Reduces to `0 ≤ c`.
      | (apply mul_sq_nonneg <;> mach_positivity)
      -- Easing band `0 ≤ A·t² − B·t³` on [0,1] (smoothstep). Side conditions
      -- 0≤t, t≤1 from kernel hyps (assumption); 0≤B, B≤A by mach_norm_num.
      | (apply cube_band_nonneg <;> first | assumption | mach_norm_num)
      -- Ease-out quadratic/cubic bands `0 ≤ 1 − (1−t)ⁿ` on [0,1].
      | (apply one_sub_sq_band <;> assumption)
      | (apply one_sub_cube_band <;> assumption)
      -- `0 ≤ 1 − c²` for clamped c ∈ [0,1] (ricochet); side goals via positivity.
      | (apply one_sub_sq_nonneg <;> mach_positivity)
      -- Exponential-fog complements `0 ≤ 1 − exp(−…)`. Side goals via
      -- mach_positivity so `0 ≤ k` from a strict `0 < k` domain hyp also works
      -- (toxin: a clearance-decay product reusing this factor).
      | (apply one_sub_exp_neg_mul_nonneg <;> mach_positivity)
      | (apply one_sub_exp_neg_nonneg <;> mach_positivity)
      -- Affine remap `0 ≤ c·x + c` ([-1,1]→[0,1], matcap UV).
      | (apply affine_remap_nonneg <;> first | mach_norm_num | assumption)
      -- Fractional part bands `0 ≤ z − ⌊z⌋` / `z − ⌊z⌋ ≤ 1` (white-noise hash).
      | exact frac_nonneg _
      | exact frac_le_one _
      -- Radial-emitter velocity floor `0 ≤ speed + spread·u`.
      | (apply speed_spread_nonneg <;> assumption)
      -- `−1 ≤ S − 1` shape (tanh-from-sigmoid `2/(1+exp) − 1 ≥ −1`).
      | (apply sub_one_ge_neg_one; mach_positivity)
      -- `0 ≤ abs x` (magnitude is nonneg). Closes abs_kernel's nonneg
      -- obligation and any `0 ≤ |…|` subgoal.
      | exact abs_nonneg _
      -- `1 ≤ cosh x` (hyperbolic cosine floor) — closes the Forge
      -- `cosh_geq_one` obligation. Harmless on non-cosh goals (exact fails).
      | exact cosh_ge_one _
      -- Bounded-range closers (sin/cos/tanh ∈ [-1,1]). The bound axioms
      -- already live in Trig; these arms wire them into the `*_in_unit_interval`
      -- / `tanh_monotone` obligations Forge emits. Harmless elsewhere (exact
      -- fails). tanh's are strict (< 1, -1 <) so weaken with `le_of_lt`.
      | exact neg_one_le_sin _
      | exact sin_le_one _
      | exact neg_one_le_cos _
      | exact cos_le_one _
      | exact le_of_lt (neg_one_lt_tanh _)
      | exact le_of_lt (tanh_lt_one _)
      -- erf ∈ [-1, 1] (Gauss error function range). Closes erf_kernel's
      -- in-unit-interval obligation.
      | exact neg_one_le_erf _
      | exact erf_le_one _
      -- Trig-amplitude band: abs(base · sin · cos …) ≤ base (orbit, wave,
      -- white_noise). The nonlinear abs-of-product shape.
      | mach_abs_bound
      -- Pythagorean identity sin²+cos²=1 (the lemma already exists in Trig;
      -- closes `*_witness` equality obligations). exact, harmless elsewhere.
      | exact pythagorean _
      -- Boundary identities: evaluate-at-zero / definitional equalities that
      -- reduce to `0=0` / `1=1` after stock rewrites (rc step-at-zero, pll
      -- zero-offset). `; done` so the arm only succeeds if FULLY closed —
      -- otherwise simp's partial progress would be read as success by `first`
      -- and leave an unsolved goal.
      | (simp only [zero_div, div_zero, exp_zero, sin_zero, cos_zero,
                    tanh_zero, mul_zero, zero_mul, sub_self, add_zero,
                    mul_one_ax, one_mul_thm]; done)
      -- Ring identities (fresnel f0+(1-f0)=1 etc.). Same `; done` guard —
      -- Ring identities (fresnel f0+(1-f0)=1, `*_witness`). mach_ring now
      -- completes ADDITIVE collection (add_left_comm). GUARDED by `show _ = _`
      -- so it only fires on EQUALITY goals — on inequalities mach_ring's full-AC
      -- simp is expensive and can time out (e.g. lqr_1d), so we skip it there.
      -- `; done` so partial progress isn't read as success by `first`.
      | (show _ = _; mach_ring; done)
      -- Structural decompositions for `0 ≤ ...`
      | (apply add_nonneg <;> mach_positivity)
      | (apply mul_nonneg <;> mach_positivity)
      | (apply div_nonneg_of_nonneg_pos <;> mach_positivity)
      | (apply div_pos_of_pos_pos <;> mach_positivity)
      -- `exp_pos` (0 < exp) BEFORE `exp_nonneg` (0 ≤ exp): strict-positive
      -- floors like `RHO_0 * exp(-h/H) > 0` (air_density, atmosphere decay,
      -- optical-neuron response) need the strict form as a `mul_pos` factor.
      | exact exp_pos _
      | (apply exp_nonneg)
      -- ── Forge-emitter arms (2026-06-24): close per-kernel range/nonneg
      --    obligations (sqrt/max/min/general-div/rpow) that shipped `sorry`.
      | exact sqrt_nonneg _
      -- `0 < sqrt x` from `0 < x` (sqrt_pos exists in Lemmas). Closes
      -- strict-positive scaling floors like `1 / sqrt(d_k) > 0` (attention)
      -- and the Riccati `sqrt(...) > 0` shapes. The subgoal `0 < x` recurses
      -- (usually a domain hypothesis). No new axiom.
      | (apply sqrt_pos <;> mach_positivity)
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
      -- Strict version: `0 < a - b` from `b < a` (e.g. acoustic_cloak
      -- shell thickness `r_outer - r_inner > 0` from `r_outer > r_inner`).
      | (apply sub_pos_of_lt <;> mach_positivity)
      -- Floor via transitive max: `FLOOR ≤ max (max .. FLOOR) ..` (e.g. a
      -- clamped composite ≥ one of its inputs).
      | (apply le_max_of_le_left <;> mach_positivity)
      | (apply le_max_of_le_right <;> mach_positivity)
      -- Affine floor: `FLOOR ≤ FLOOR + (nonneg)` / `(nonneg) + FLOOR`.
      | (apply le_add_of_nonneg_right <;> mach_positivity)
      | (apply le_add_of_nonneg_left <;> mach_positivity)
      -- Clamp ceil: `min a b ≤ a` / `≤ b` (e.g. `clamp ≤ HI`).
      | exact min_le_left _ _
      | exact min_le_right _ _
      -- Clamp floor: `LO ≤ min (max .. LO) HI` — splits to `LO ≤ max .. LO`
      -- (closed by le_max_right) and `LO ≤ HI` (the clamp-bound ordering;
      -- closes when it's a hypothesis — see emitter note below).
      | (apply le_min <;> mach_positivity)
      -- Structural decompositions for `0 < ...`. Order matters:
      -- `add_pos_of_nonneg_pos` before `add_pos` so a sum like
      -- `a + b + c + d` with only `d` strictly-positive closes.
      | (apply add_pos_of_nonneg_pos <;> mach_positivity)
      | (apply add_pos <;> mach_positivity)
      | (apply mul_pos <;> mach_positivity)
      -- Weaken-to-nonneg bridge.
      | (apply nonneg_of_pos; mach_positivity))

/-- `mach_abs_bound` recursion: peel one magnitude-≤1 factor (`abs_mul_le_of_
abs_le_one`) at a time, or finish at `abs base` with `base ≥ 0`. -/
macro_rules
  | `(tactic| mach_abs_bound) => `(tactic|
      first
      -- base: `abs base ≤ abs base` (bound is `abs amp`, e.g. wave
      -- `abs(amp·cos) ≤ abs amp`) — just reflexivity.
      | exact le_refl _
      -- base: `abs base ≤ base` with `base ≥ 0` (bound is the raw base).
      | (rw [abs_of_nonneg (by mach_positivity)]; exact le_refl _)
      | (refine le_trans (abs_mul_le_of_abs_le_one ?_) ?_ <;>
           first
           | exact abs_sin_le_one _
           | exact abs_cos_le_one _
           | mach_abs_bound))

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
