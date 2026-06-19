import MachLib.LambertW
import MachLib.LambertWAsymptotics
import MachLib.Ring

/-!
# MachLib.LambertWFunctionalEquation — uniqueness foundation for Path B/C closure

## Why this file exists (2026-06-19, Path B)

The 2026-06-13 scoping doc identified three paths for closing the
Lambert-W any-depth EML barrier:

  - Path A: asymptotic growth comparison (partial in LambertWAsymptotics.lean)
  - Path B: functional-equation algebraic-structure argument
  - Path C: composition with a known-out function

This file is Path B foundation. The key idea: if `W ∈ EML_k` via tree
`t`, then `t.eval` satisfies the functional equation
`t.eval(x) · exp(t.eval(x)) = x`. Combined with W's UNIQUENESS as
the solution, this forces `t.eval = W` on the principal branch,
which lets us reason about specific values, derivatives, etc.

This file ships:

  - `y_mul_exp_y_strict_mono_on_nonneg`: `y ↦ y · exp(y)` is strictly
    monotone on `[0, ∞)`.
  - `y_mul_exp_y_injective_on_nonneg`: hence injective on `[0, ∞)`.
  - `lambertW_unique_at_pos`: `W(y)` is the UNIQUE nonneg `w` with
    `w · exp(w) = y`, for `y ≥ 0`.
  - `lambertW_at_nat_e_pow`: `W(n · exp(n)) = n` for any `n : Nat`.

## What this enables

The unique-solution + specific-values theorems are the foundation for
case-analysis arguments on hypothetical EML representations:

  If `t ∈ EML_k` with `t.eval = W`, then `t.eval(n · exp(n)) = n` for
  every natural `n`. This is an INFINITE SEQUENCE of value constraints
  on `t`. For each EMLTree shape, evaluate `t.eval(n · exp(n))`
  symbolically and check against `= n`.

For depth 0/1, this approach already worked (the previously-shipped
`lambertW_not_in_eml_0` and `lambertW_not_in_eml_1` use specific
values W(0)=0 and W(1)∈(0,1) for the constraints). The any-depth
closure would extend this to arbitrary depth via INDUCTION, using
the value sequence `{W(n·exp(n)) = n : n ∈ ℕ}`.

## What's still open

Even with the unique-solution + infinite-value-sequence machinery,
the actual case analysis for arbitrary depth EMLTrees is
combinatorially complex (per the scoping doc's "Difficulty"
section). The case-explosion-at-depth-k approach needs either:

  - An INDUCTIVE argument on depth that handles the cases generically.
  - A TRANSCENDENCE argument over `ℝ_exp` (model-theoretic).
  - A more clever SHAPE constraint that crystallises across depths.

This file is the substrate that any of these approaches would build on.

## New axioms

ZERO. All theorems derived from the existing infrastructure
(`exp_lt`, `exp_pos`, `exp_zero`, `lambertW_func_eq`,
`lambertW_monotone`, field axioms, etc.).
-/

namespace MachLib
namespace Real

/-! ## Strict monotonicity of `y · exp(y)` on the nonnegative reals -/

/-- Helper: `c * (b - a) = c * b - c * a` via existing distributivity
+ subtraction axioms. -/
private theorem mul_sub_helper (c a b : Real) :
    c * (b - a) = c * b - c * a := by
  have e1 : (b - a) = b + -a := sub_def _ _
  have e2 : c * b - c * a = c * b + -(c * a) := sub_def _ _
  rw [e1, e2, mul_distrib, mul_neg]

/-- `y ↦ y · exp(y)` is strictly monotone on `[0, ∞)`.

Specifically: for `0 ≤ y₁ < y₂`, `y₁ · exp(y₁) < y₂ · exp(y₂)`.

Proof: split into two strict-monotonicity steps:
  (i)  `y₁ · exp(y₁) < y₂ · exp(y₁)` (from `y₁ < y₂` and `exp(y₁) > 0`).
  (ii) `y₂ · exp(y₁) ≤ y₂ · exp(y₂)` (from `exp(y₁) ≤ exp(y₂)` and `y₂ ≥ 0`).

Combine via transitivity. -/
theorem y_mul_exp_y_strict_mono_on_nonneg
    (y1 y2 : Real) (hy1 : 0 ≤ y1) (hlt : y1 < y2) :
    y1 * exp y1 < y2 * exp y2 := by
  have hy2_nonneg : 0 ≤ y2 := le_trans hy1 ((le_iff_lt_or_eq _ _).mpr (Or.inl hlt))
  -- Step (i): y1 · exp(y1) < y2 · exp(y1).
  have h_exp1_pos : 0 < exp y1 := exp_pos y1
  have step1 : y1 * exp y1 < y2 * exp y1 := by
    -- Use the strict monotonicity helper from LambertWAsymptotics:
    -- mul_lt_mul_pos_left says 0 < c → a < b → c · a < c · b. We want
    -- exp(y1) · y1 < exp(y1) · y2. Then commute.
    have h := MachLib.Real.mul_pos h_exp1_pos (by
      have := add_lt_add_left hlt (-y1)
      rw [neg_add_self, add_comm (-y1) y2, ← sub_def] at this
      exact this)
    -- h : 0 < exp(y1) · (y2 - y1)
    rw [mul_sub_helper] at h
    -- h : 0 < exp(y1) · y2 - exp(y1) · y1
    have step_h := add_lt_add_left h (exp y1 * y1)
    rw [add_zero, sub_def, add_comm (exp y1 * y2) (-(exp y1 * y1)),
        ← add_assoc, add_neg, zero_add] at step_h
    -- step_h : exp(y1) · y1 < exp(y1) · y2
    rw [mul_comm (exp y1) y1, mul_comm (exp y1) y2] at step_h
    exact step_h
  -- Step (ii): y2 · exp(y1) ≤ y2 · exp(y2).
  have h_exp_le : exp y1 ≤ exp y2 := exp_monotone ((le_iff_lt_or_eq _ _).mpr (Or.inl hlt))
  have step2 : y2 * exp y1 ≤ y2 * exp y2 :=
    mul_le_mul_of_nonneg_left h_exp_le hy2_nonneg
  -- Transitivity: step1 (<) + step2 (≤) → strict <.
  rcases (le_iff_lt_or_eq _ _).mp step2 with h_lt | h_eq
  · exact lt_trans_ax step1 h_lt
  · rw [h_eq] at step1
    exact step1

/-! ## Injectivity of `y · exp(y)` on the nonnegative reals -/

/-- `y · exp(y)` is INJECTIVE on `[0, ∞)`. -/
theorem y_mul_exp_y_injective_on_nonneg
    (y1 y2 : Real) (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2)
    (heq : y1 * exp y1 = y2 * exp y2) :
    y1 = y2 := by
  rcases lt_total y1 y2 with hlt | heq' | hgt
  · -- y1 < y2: strict mono gives y1·exp(y1) < y2·exp(y2), contradiction with heq.
    have h := y_mul_exp_y_strict_mono_on_nonneg y1 y2 hy1 hlt
    exact absurd heq (ne_of_lt h)
  · exact heq'
  · -- y2 < y1: symmetric contradiction.
    have h := y_mul_exp_y_strict_mono_on_nonneg y2 y1 hy2 hgt
    exact absurd heq.symm (ne_of_lt h)

/-! ## Uniqueness of the Lambert-W solution

If `w ≥ 0` and `w · exp(w) = y`, then `w = W(y)` (provided `y ≥ 0`).
This is the inverse-function statement: W is the unique nonneg
solution to the defining equation. -/

/-- **Uniqueness of W on the principal branch**: any nonneg `w`
satisfying `w · exp(w) = y` equals `W(y)`.

Proof: `W(y) · exp(W(y)) = y` (by `lambertW_func_eq`). So
`w · exp(w) = W(y) · exp(W(y))`. By injectivity of `y · exp(y)` on
`[0, ∞)`, `w = W(y)`. -/
theorem lambertW_unique_at_pos (y : Real) (hy : 0 ≤ y)
    (w : Real) (hw : 0 ≤ w)
    (heq : w * exp w = y) :
    w = lambertW y := by
  have h_W_nonneg : 0 ≤ lambertW y := lambertW_nonneg_at_nonneg y hy
  have h_W_eq : lambertW y * exp (lambertW y) = y := lambertW_func_eq y hy
  have h_combined : w * exp w = lambertW y * exp (lambertW y) := by
    rw [heq, h_W_eq]
  exact y_mul_exp_y_injective_on_nonneg w (lambertW y) hw h_W_nonneg h_combined

/-! ## Specific values: `W(n · exp(n)) = n` -/

/-- For any natural `n` (cast to Real), `W(n · exp(n)) = n`.

Proof: directly from uniqueness — `n · exp(n) = y` solved by `w = n`. -/
theorem lambertW_at_nat_e_pow (n : Real) (hn : 0 ≤ n) :
    lambertW (n * exp n) = n := by
  have h_y_nonneg : 0 ≤ n * exp n := by
    -- nonneg * positive = nonneg
    rcases (le_iff_lt_or_eq _ _).mp hn with hn_pos | hn_zero
    · -- n > 0: n · exp(n) > 0
      have h_exp_pos : 0 < exp n := exp_pos n
      exact (le_iff_lt_or_eq _ _).mpr (Or.inl (mul_pos hn_pos h_exp_pos))
    · -- n = 0: n · exp(n) = 0
      rw [← hn_zero, zero_mul]
      exact le_refl _
  have h_func : n * exp n = n * exp n := rfl
  -- By uniqueness: lambertW (n · exp n) = n.
  exact (lambertW_unique_at_pos (n * exp n) h_y_nonneg n hn h_func).symm

/-! ## Closing notes — what this enables

This file establishes that **W is the unique nonneg solution to
`w · exp(w) = y`** for `y ≥ 0`. With this + the infinite sequence
of specific values `{W(n · exp(n)) = n : n ∈ ℕ_{≥0}}`, any
hypothetical EML representation `t.eval = W` is constrained by:

```
∀ n ∈ ℝ, n ≥ 0 → t.eval (n · exp(n)) = n
```

For each specific n (treating n as a constant), this is a single
algebraic constraint on `t`'s parameters. Combined across n, it's
an INFINITE FAMILY of constraints.

## How a depth-k closure would use this (sketch)

For each EMLTree shape of depth ≤ k:

1. Symbolically evaluate `t.eval (n · exp(n))` as a function of `n`.
2. Set it equal to `n`.
3. Derive constraints on `t`'s parameters (constants in `const c` nodes).
4. Show NO assignment of parameters satisfies all constraints.

For depth 0: trivial (const c → c = n for all n, contradiction).
For depth 1: case analysis on 4 shapes (already done in
`LambertW.lambertW_not_in_eml_1`).
For depth 2+: case analysis on more shapes (combinatorial explosion).

## What's still open

The depth-k case analysis is the genuine remaining work. Two paths:

(a) **Inductive depth argument**: show that for any t with `t.eval = W`,
    `t.depth` must increase with the number of W-values to match. Since
    matching infinitely many values requires infinite depth, no finite
    depth works.

(b) **Transcendence**: W is transcendental over ℝ_exp. EML is a
    sub-algebra of ℝ_exp,Pfaff. Transcendence over ℝ_exp implies W ∉ EML
    (since EML's algebraic closure is bounded by ℝ_exp).

Either path needs ~500+ lines of new infrastructure. This file's
contribution is the FOUNDATION — uniqueness + specific values — that
either path will build on.

## Axiom audit

ZERO new axioms beyond what's already in `LambertW.lean` +
`LambertWAsymptotics.lean`. All theorems derived from existing
primitives.
-/

end Real
end MachLib
