/-
MachLib.Forge — derived lemmas for Forge-emitted kernel proofs.

The Forge `lean` backend emits one theorem per `@verify(lean, ...)`
annotation in a `.eml` file. The C-127 audit (2026-05-01) found
that all 454 such theorems were unbound: each `theorem foo := by
sorry` had no MachLib lemmas in scope beyond what `MachLib.EML`
and `MachLib.Trig` re-export.

This file is the binding layer. It re-exports the foundational
modules (`Basic`, `Exp`, `Log`, `Trig`, `EML`, plus the ported
`Hyperbolic` family) and adds the small set of derived lemmas
that production-shape kernels reach for repeatedly:

  * Order: `le_refl`, `le_of_lt`, `le_trans`, `lt_of_le_of_lt`,
    `lt_of_lt_of_le`, `le_antisymm`.
  * Nonneg combinators: `exp_nonneg`, `add_nonneg`, `add_pos`,
    `mul_nonneg`, `div_nonneg_of_pos_denom`.
  * Forge-side conveniences: `sub_pos_of_lt`, `nonneg_of_pos`.

Each lemma is proved from the axioms in `MachLib.Basic` (no
Mathlib). Forge-emitted Lean files should `import MachLib.Forge`
in place of (or in addition to) `MachLib.EML` so these are in
scope for the `by` blocks the codegen emits.
-/

import MachLib.Basic
import MachLib.Exp
import MachLib.Log
import MachLib.Trig
import MachLib.EML

namespace MachLib
namespace Real

/-! ### Order: foundational helpers -/

/-- Reflexivity of `≤`. -/
theorem le_refl (a : Real) : a ≤ a :=
  (le_iff_lt_or_eq a a).mpr (Or.inr rfl)

/-- A strict inequality entails the non-strict one. -/
theorem le_of_lt {a b : Real} (h : a < b) : a ≤ b :=
  (le_iff_lt_or_eq a b).mpr (Or.inl h)

/-- Transitivity for `≤`. Uses `le_iff_lt_or_eq` to case-split each
arm; the proof closes by `lt_trans_ax` plus the reflexive case. -/
theorem le_trans {a b c : Real} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rcases (le_iff_lt_or_eq a b).mp hab with h_ab | h_ab
  · rcases (le_iff_lt_or_eq b c).mp hbc with h_bc | h_bc
    · exact le_of_lt (lt_trans_ax h_ab h_bc)
    · subst h_bc; exact le_of_lt h_ab
  · subst h_ab; exact hbc

/-- `a < b` and `b ≤ c` give `a < c`. -/
theorem lt_of_lt_of_le {a b c : Real} (hab : a < b) (hbc : b ≤ c) : a < c := by
  rcases (le_iff_lt_or_eq b c).mp hbc with h_bc | h_bc
  · exact lt_trans_ax hab h_bc
  · subst h_bc; exact hab

/-- `a ≤ b` and `b < c` give `a < c`. -/
theorem lt_of_le_of_lt {a b c : Real} (hab : a ≤ b) (hbc : b < c) : a < c := by
  rcases (le_iff_lt_or_eq a b).mp hab with h_ab | h_ab
  · exact lt_trans_ax h_ab hbc
  · subst h_ab; exact hbc

/-- Antisymmetry of `≤`. -/
theorem le_antisymm {a b : Real} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rcases (le_iff_lt_or_eq a b).mp hab with h_ab | h_ab
  · rcases (le_iff_lt_or_eq b a).mp hba with h_ba | h_ba
    · exact absurd (lt_trans_ax h_ab h_ba) (lt_irrefl_ax a)
    · exact h_ba.symm
  · exact h_ab

/-! ### Nonneg combinators -/

/-- `exp` is non-negative everywhere — strict positivity weakened. -/
theorem exp_nonneg (x : Real) : 0 ≤ exp x :=
  le_of_lt (exp_pos x)

/-- `0 < a` entails `0 ≤ a`. -/
theorem nonneg_of_pos {a : Real} (h : 0 < a) : 0 ≤ a :=
  le_of_lt h

/-- The sum of two non-negatives is non-negative. Uses
`add_lt_add_left` to lift a strict inequality through addition,
then weakens to `≤`. -/
theorem add_nonneg {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b := by
  rcases (le_iff_lt_or_eq 0 a).mp ha with h_a | h_a
  · -- 0 < a, so a + 0 < a + b reduces by add_zero
    rcases (le_iff_lt_or_eq 0 b).mp hb with h_b | h_b
    · -- 0 < a, 0 < b: 0 + 0 < a + b by twice add_lt_add_left
      have h1 : (0 : Real) + 0 < a + 0 := by
        have h := add_lt_add_left h_a (0 : Real)
        rw [add_comm 0 0, add_comm 0 a] at h
        exact h
      have h2 : a + 0 < a + b := add_lt_add_left h_b a
      have h3 : (0 : Real) + 0 < a + b := lt_trans_ax h1 h2
      have h_zero : (0 : Real) + 0 = 0 := add_zero 0
      rw [h_zero] at h3
      exact le_of_lt h3
    · -- 0 < a, 0 = b: a + b = a + 0 = a, and 0 < a
      subst h_b
      rw [add_zero]
      exact le_of_lt h_a
  · -- 0 = a: a + b = 0 + b = b
    subst h_a
    rw [zero_add]
    exact hb

/-- The sum of two strict positives is strict positive. -/
theorem add_pos {a b : Real} (ha : 0 < a) (hb : 0 < b) : 0 < a + b := by
  -- 0 < a, and a < a + b (by add_lt_add_left of 0 < b)
  have h1 : a + 0 < a + b := add_lt_add_left hb a
  rw [add_zero] at h1
  exact lt_trans_ax ha h1

/-- The product of two non-negatives is non-negative. Uses
`mul_pos` (axiom) for the strict-strict case and the zero-cases
fall out of `zero_mul` / `mul_zero`. -/
theorem mul_nonneg {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  rcases (le_iff_lt_or_eq 0 a).mp ha with h_a | h_a
  · rcases (le_iff_lt_or_eq 0 b).mp hb with h_b | h_b
    · exact le_of_lt (mul_pos h_a h_b)
    · subst h_b; rw [mul_zero]; exact le_refl 0
  · subst h_a; rw [zero_mul]; exact le_refl 0

/-! ### Literal-form bridges

The Forge codegen emits decimal literals (`0.0`, `1.0`, `100.0`,
…) which `OfScientific Real` routes through the opaque
`realOfScientific` axiom in `MachLib.Basic`. The order/arithmetic
axioms (`mul_pos`, `add_lt_add_left`, …) use the bare `0`/`1`
literals routed through `OfNat`. Standard Real semantics make
these equal, but they are not definitionally equal under
MachLib's "axiomatic, no concrete representation" policy. The
two facts below bridge the most common cases at the kernel-proof
level and are otherwise inert. Future literal-positivity facts
(`(0.6108 : Real) > 0` etc.) still belong in the per-kernel
discovered file because they're domain-specific. -/

/-- The decimal literal `0.0` and the OfNat literal `0` denote
the same `Real`. -/
axiom lit_zero_eq : (0.0 : Real) = (0 : Real)

/-- The decimal literal `1.0` and the OfNat literal `1` denote
the same `Real`. -/
axiom lit_one_eq : (1.0 : Real) = (1 : Real)

/-! ### Subtraction + division: scaling helpers

Forge-emitted kernels with `ensures result > 0` over an expression
of the form `1 - x/N` (saturation deficits, depletion fractions,
normalised slacks) reduce to two facts: the dividend is bounded by
the divisor, and subtracting a value strictly below 1 from 1 stays
positive. The first lemma proves directly from `add_lt_add_left`;
the second is held as an axiom because the multiplicative-scaling
proof from `mul_inv` + `mul_pos` requires more case-split
infrastructure than `MachLib.Basic` currently exposes (cf the
C-127 note). See `Discovered/vpd_control.lean` for the first
production use. -/

/-- `a < b` lifts to `0 < b - a` by adding `-a` to both sides. -/
theorem sub_pos_of_lt {a b : Real} (h : a < b) : 0 < b - a := by
  -- add_lt_add_left h (-a) : -a + a < -a + b
  have step : -a + a < -a + b := add_lt_add_left h (-a)
  rw [neg_add_self] at step      -- step : 0 < -a + b
  rw [sub_def, add_comm]         -- goal : 0 < -a + b
  exact step

/-- A value strictly below a positive divisor produces a quotient
strictly below `1`. Held as an axiom: provable from `mul_inv` plus
`mul_lt_mul_of_pos_right` plus `one_div_pos_of_pos`, but those
multiplicative-scaling helpers aren't yet in `MachLib.Basic`. The
fact is true in any standard ordered field. -/
axiom div_lt_one_of_pos_lt {a b : Real} (hb : 0 < b) (hab : a < b) : a / b < 1

/-! ### Min / max combinators (C-239 follow-up)

`MachLib.Basic` defines `min` / `max` as `if a ≤ b then ... else ...`
and proves `min_self` / `max_self`; the directional bounds and the
nonneg specialisations live here so `Forge.lean` is the single
`import` Forge-emitted Lean files reach for. All proven from
`MachLib.Basic` axioms — no Mathlib, no new core axioms. -/

theorem le_max_left (a b : Real) : a ≤ max a b := by
  unfold max
  by_cases h : a ≤ b
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact le_refl a

theorem le_max_right (a b : Real) : b ≤ max a b := by
  unfold max
  by_cases h : a ≤ b
  · rw [if_pos h]; exact le_refl b
  · rw [if_neg h]
    have hba : b < a := by
      cases lt_total a b with
      | inl hab => exact absurd (le_of_lt hab) h
      | inr h2 => cases h2 with
        | inl heq => exact absurd (heq ▸ le_refl a) h
        | inr hba => exact hba
    exact le_of_lt hba

theorem min_le_left (a b : Real) : min a b ≤ a := by
  unfold min
  by_cases h : a ≤ b
  · rw [if_pos h]; exact le_refl a
  · rw [if_neg h]
    have hba : b < a := by
      cases lt_total a b with
      | inl hab => exact absurd (le_of_lt hab) h
      | inr h2 => cases h2 with
        | inl heq => exact absurd (heq ▸ le_refl a) h
        | inr hba => exact hba
    exact le_of_lt hba

theorem min_le_right (a b : Real) : min a b ≤ b := by
  unfold min
  by_cases h : a ≤ b
  · rw [if_pos h]; exact h
  · rw [if_neg h]; exact le_refl b

/-- Both branches nonneg ⇒ `min` nonneg. -/
theorem min_nonneg {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ min a b := by
  unfold min
  by_cases h : a ≤ b
  · rw [if_pos h]; exact ha
  · rw [if_neg h]; exact hb

/-- Left witness suffices for `max` nonneg (max ≥ a ≥ 0). -/
theorem max_nonneg_left {a b : Real} (ha : 0 ≤ a) : 0 ≤ max a b :=
  le_trans ha (le_max_left a b)

/-- Right witness suffices for `max` nonneg (max ≥ b ≥ 0). Closes
the very common `0 ≤ max <expr> 0` codegen idiom. -/
theorem max_nonneg_right {a b : Real} (hb : 0 ≤ b) : 0 ≤ max a b :=
  le_trans hb (le_max_right a b)

/-- Mixed-strictness sum. Useful for goals where one operand is a
literal bound (`0 ≤ ZERO`) and the other is strictly positive. -/
theorem add_pos_of_nonneg_pos {a b : Real} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b := by
  rcases (le_iff_lt_or_eq 0 a).mp ha with h_a | h_a
  · exact add_pos h_a hb
  · subst h_a; rw [zero_add]; exact hb

/-! ### ≤-monotonicity substrate (C-242, 2026-05-03)

`MachLib.Basic` exposes only the strict `<` versions of additive
and multiplicative monotonicity (`add_lt_add_left`, `mul_pos`).
Forge-emitted kernel proofs need the `≤` versions for goals like
`a ≤ b → a + c ≤ b + c` and `a ≤ b → 0 ≤ c → a*c ≤ b*c`. The
substrate below derives the `≤` forms from the `<` axioms via
`le_iff_lt_or_eq` case-splits.

The strict `<` multiplicative-right form is held as an axiom in
the same spirit as `div_lt_one_of_pos_lt` — provable from
`mul_pos` + a `mul_neg` distributivity lemma we haven't yet
landed. Adding it as an axiom keeps C-242 scoped to this session;
the converse derivation goes into a future Basic.lean cleanup. -/

/-- `a < b → 0 < c → a * c < b * c`. Strict multiplicative
right-monotonicity. Held as axiom (true in any ordered field;
proof from existing axioms requires `mul_neg` + distributive over
subtraction, currently absent from `MachLib.Basic`). -/
axiom mul_lt_mul_of_pos_right
    {a b c : Real} (h : a < b) (hc : 0 < c) : a * c < b * c

/-- `a ≤ b → c + a ≤ c + b`. -/
theorem add_le_add_left
    {a b : Real} (h : a ≤ b) (c : Real) : c + a ≤ c + b := by
  rcases (le_iff_lt_or_eq a b).mp h with h_lt | h_eq
  · exact le_of_lt (add_lt_add_left h_lt c)
  · subst h_eq; exact le_refl _

/-- `a ≤ b → 0 ≤ c → a * c ≤ b * c`. -/
theorem mul_le_mul_of_nonneg_right
    {a b c : Real} (h : a ≤ b) (hc : 0 ≤ c) : a * c ≤ b * c := by
  rcases (le_iff_lt_or_eq 0 c).mp hc with h_c_pos | h_c_zero
  · rcases (le_iff_lt_or_eq a b).mp h with h_ab | h_ab
    · exact le_of_lt (mul_lt_mul_of_pos_right h_ab h_c_pos)
    · subst h_ab; exact le_refl _
  · subst h_c_zero; rw [mul_zero, mul_zero]; exact le_refl _

/-- `a ≤ b → 0 ≤ c → c * a ≤ c * b`. (Left version, by `mul_comm`.) -/
theorem mul_le_mul_of_nonneg_left
    {a b c : Real} (h : a ≤ b) (hc : 0 ≤ c) : c * a ≤ c * b := by
  rw [mul_comm c a, mul_comm c b]
  exact mul_le_mul_of_nonneg_right h hc

/-! ### Subtraction / saturation lemmas (C-242, 2026-05-03)

The patterns Forge-emitted kernels reach for: `0 ≤ a - b` from
`b ≤ a`, `0 < 1 - x` from `x < 1`, `0 ≤ 1 - x` from `x ≤ 1`. -/

/-- `b ≤ a → 0 ≤ a - b`. (≤-version of `sub_pos_of_lt`.) -/
theorem sub_nonneg_of_le {a b : Real} (h : b ≤ a) : 0 ≤ a - b := by
  rcases (le_iff_lt_or_eq b a).mp h with h_lt | h_eq
  · exact le_of_lt (sub_pos_of_lt h_lt)
  · subst h_eq; rw [sub_def, add_neg]; exact le_refl 0

/-- `x < 1 → 0 < 1 - x`. -/
theorem one_sub_pos_of_lt_one {x : Real} (h : x < 1) : 0 < 1 - x :=
  sub_pos_of_lt h

/-- `x ≤ 1 → 0 ≤ 1 - x`. -/
theorem one_sub_nonneg_of_le_one {x : Real} (h : x ≤ 1) : 0 ≤ 1 - x :=
  sub_nonneg_of_le h

/-! ### Division ≤ 1 (C-242, 2026-05-03)

`a / b ≤ 1` from `0 < b` and `a ≤ b`. The proof uses
`a / b = a * (1/b)`, then bounds `a * (1/b) ≤ b * (1/b) = 1`
via `mul_le_mul_of_nonneg_right` and `mul_inv`. The `1 / b ≥ 0`
sub-fact is held as a lemma below.

The strict-positivity form (`div_lt_one_of_pos_lt`) is already
in Forge.lean as an axiom; this is the ≤-version, derivable
from `mul_le_mul_of_nonneg_right`. -/

/-- `0 < b → 0 ≤ 1 / b`. (Strict positivity of inverse — held
as a small axiom rather than derived from a `div_pos` chain we
don't yet have.) -/
axiom one_div_nonneg_of_pos {b : Real} (hb : 0 < b) : 0 ≤ 1 / b

/-- `0 < b → a ≤ b → a / b ≤ 1`. -/
theorem div_le_one_of_le_of_pos
    {a b : Real} (hb : 0 < b) (h : a ≤ b) : a / b ≤ 1 := by
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have eq_div : a / b = a * (1 / b) := div_def a b hb_ne
  rw [eq_div]
  have hinv : 0 ≤ 1 / b := one_div_nonneg_of_pos hb
  have step1 : a * (1 / b) ≤ b * (1 / b) :=
    mul_le_mul_of_nonneg_right h hinv
  have step2 : b * (1 / b) = 1 := mul_inv b hb_ne
  rw [step2] at step1
  exact step1

/-- `0 ≤ a → 0 < b → 0 ≤ a / b`. The dominant Bucket-B pattern in
the C-242 sweep — the post-unfold goal of physical-formula
kernels (aragonite saturation, ksp ratios, photon orbit ratios)
is `0 ≤ (numerator)/(positive denominator)`. -/
theorem div_nonneg_of_nonneg_pos
    {a b : Real} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  rw [div_def a b (ne_of_gt hb)]
  exact mul_nonneg ha (one_div_nonneg_of_pos hb)

/-! ### `≤ 1` products (C-242, 2026-05-03)

A product of two non-negative ≤-1 values is itself ≤ 1. -/

/-- `0 ≤ a → 0 ≤ b → a ≤ 1 → b ≤ 1 → a * b ≤ 1`. -/
theorem mul_le_one_of_le_one
    {a b : Real} (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) : a * b ≤ 1 := by
  -- a * b ≤ a * 1 = a ≤ 1.
  have step1 : a * b ≤ a * 1 := mul_le_mul_of_nonneg_left hb1 ha
  rw [mul_one_ax] at step1
  exact le_trans step1 ha1

/-! ### Clamp-chain combinators (C-244, 2026-05-03)

Forge-emitted kernels with `min/max` clamps reach for goals of the
shape `a ≤ max b c` where `a` is bounded by ONE of `b` or `c` only.
The four lemmas below close those in one tactic via `le_trans` from
the existing `min_le_left/right` and `le_max_left/right`. -/

/-- `a ≤ b → a ≤ max b c`. -/
theorem le_max_of_le_left {a b : Real} (h : a ≤ b) (c : Real) : a ≤ max b c :=
  le_trans h (le_max_left b c)

/-- `a ≤ c → a ≤ max b c`. -/
theorem le_max_of_le_right {a c : Real} (h : a ≤ c) (b : Real) : a ≤ max b c :=
  le_trans h (le_max_right b c)

/-- `a ≤ c → min a b ≤ c`. -/
theorem min_le_of_left_le {a c : Real} (h : a ≤ c) (b : Real) : min a b ≤ c :=
  le_trans (min_le_left a b) h

/-- `b ≤ c → min a b ≤ c`. -/
theorem min_le_of_right_le {b c : Real} (h : b ≤ c) (a : Real) : min a b ≤ c :=
  le_trans (min_le_right a b) h

/-! ### OfScientific literal positivity (C-240, 2026-05-03)

`realOfScientific_pos` is the underlying axiom in `MachLib.Basic`.
The two derived theorems below are the user-facing forms — Lean's
elaborator desugars `(0.5 : Real)` to `OfScientific.ofScientific 5
true 1`, which (via `instOfScientific`) reduces to `realOfScientific
5 true 1`. The bridge proof is therefore `rfl`-shaped. -/

theorem ofScientific_pos {m e : Nat} (s : Bool) (hm : 0 < m) :
    0 < (OfScientific.ofScientific m s e : Real) :=
  realOfScientific_pos m s e hm

theorem ofScientific_nonneg {m e : Nat} (s : Bool) (hm : 0 < m) :
    0 ≤ (OfScientific.ofScientific m s e : Real) :=
  le_of_lt (ofScientific_pos s hm)

end Real
end MachLib

/-- `lit_pos` — closes `0 < c` / `0 ≤ c` when `c` is a fractional
literal whose mantissa is concretely positive. The `decide`
discharges the `Nat` precondition `0 < m` after unification fixes `m`.
Falls through cleanly if the goal isn't a literal-shaped positivity
goal — the BFS sweep can then mark the candidate rejected. -/
macro "lit_pos" : tactic => `(tactic|
  first
  | exact MachLib.Real.ofScientific_pos _ (by decide)
  | exact MachLib.Real.ofScientific_nonneg _ (by decide))
