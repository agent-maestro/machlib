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

/-! ### Future work — division-side lemmas

The C-127 audit identified `div_nonneg_of_pos_denom`,
`one_div_pos_of_pos`, and `sub_pos_of_lt` as natural members of
this binding. They reduce to combinations of `mul_inv`, `mul_pos`,
and `add_lt_add_left`, but the rewrite-pattern dance against the
exact axiom convention proved finicky — we hold them for the next
iteration of MachLib.Forge rather than ship a half-broken file.

Once `one_div_pos_of_pos` lands, division non-negativity is one
line via `mul_nonneg`. Tracking issue: pre-registered as C-128's
sibling once Java/Kotlin tuple codegen is in. -/

end Real
end MachLib
