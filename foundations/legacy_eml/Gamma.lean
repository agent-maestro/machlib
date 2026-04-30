-- MonogateEML/Gamma.lean
-- Wraps Mathlib's Real.Gamma identities into the MonogateEML namespace.
--
-- Scope (honest):
--   - The Gamma functional equation Γ(s+1) = s·Γ(s)
--   - Base case Γ(1) = 1
--   - Factorial connection Γ(n+1) = n!
--   - Positivity on (0, ∞)
--   - Derivative existence away from non-positive integers
--   - The harmonic / Euler-Mascheroni derivative formula at integer points
--
-- Out of scope (NOT proved here):
--   - Chain identity Γ' = Γ·ψ (digamma) — Mathlib does not currently expose
--     a named `digamma` function; the identity at integer points uses
--     `harmonic n - eulerMascheroniConstant` instead.
--   - Pfaffian-chain-order Lean witness (`gamma=2` in eml-cost registry) —
--     would require defining digamma plus a Pfaffian-class membership
--     lemma. Multi-day project.
--
-- The witnesses below establish gamma's *defining structural property*
-- (the functional equation no elementary function satisfies), which is
-- the standard non-elementary witness used in textbook treatments.
--
-- Author: Claude per feedback_lean_writing_protocol_2026_04_25;
-- pending user verification in VS Code lean4 extension before any
-- public-surface claims of "Lean-verified" status.

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.Harmonic.GammaDeriv

namespace MonogateGamma

open Real

-- ============================================================
-- 1. Functional equation (the structural non-elementary witness)
-- ============================================================

/-- **Functional equation** Γ(s+1) = s · Γ(s) for s ≠ 0.

    No elementary function satisfies this functional equation;
    this is the standard "gamma is not elementary" witness used in
    textbook treatments (cf. Hardy, Boros-Moll). -/
theorem gamma_functional_equation {s : ℝ} (hs : s ≠ 0) :
    Gamma (s + 1) = s * Gamma s :=
  Real.Gamma_add_one hs

/-- **Base case** Γ(1) = 1. Combined with the functional equation,
    this fixes Γ on positive integers as the factorial. -/
theorem gamma_one : Gamma 1 = 1 :=
  Real.Gamma_one

/-- **Factorial connection** Γ(n+1) = n! for natural n. The two
    properties (functional equation + base case) determine Γ on ℕ. -/
theorem gamma_nat_eq_factorial (n : ℕ) : Gamma (n + 1) = n.factorial :=
  Real.Gamma_nat_eq_factorial n

-- ============================================================
-- 2. Positivity (relevant for the elementary-class witness:
-- gamma is positive on (0, ∞) but takes integer values nowhere
-- except at positive integers, etc.)
-- ============================================================

/-- Γ is strictly positive on (0, ∞). -/
theorem gamma_pos_of_pos {s : ℝ} (hs : 0 < s) : 0 < Gamma s :=
  Real.Gamma_pos_of_pos hs

-- ============================================================
-- 3. Differentiability (existence; concrete formula only at
-- integer points via harmonic / Euler-Mascheroni)
-- ============================================================

/-- Γ is differentiable at every point not equal to a non-positive integer. -/
theorem gamma_differentiable_at {s : ℝ} (hs : ∀ m : ℕ, s ≠ -m) :
    DifferentiableAt ℝ Gamma s :=
  Real.differentiableAt_Gamma hs

/-- **Derivative at positive integers** (Mathlib's `deriv_Gamma_nat`):
    Γ'(n+1) = n! · (-γ + harmonic n), where γ is the Euler-Mascheroni
    constant and harmonic n = 1 + 1/2 + ... + 1/n.

    This is the closest Mathlib analogue of the textbook chain identity
    Γ'(s) = Γ(s) · ψ(s); at integer points ψ(n+1) = -γ + harmonic n,
    so the formula matches once digamma is named. -/
theorem deriv_gamma_at_nat (n : ℕ) :
    deriv Gamma (n + 1) = n.factorial * (-eulerMascheroniConstant + harmonic n) :=
  Real.deriv_Gamma_nat n

end MonogateGamma
