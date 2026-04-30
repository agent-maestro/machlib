-- MonogateEML/SelfMapConjugacy.lean
-- Formalizes Prop A-1 (Blind omnibus session A, 2026-04-22/23):
--
-- The F16 self-maps EAL(x,x) = exp(x) + ln(x) and EXL(y,y) = exp(y) · ln(y)
-- are topologically conjugate via the real exponential.
-- Symbolically: g ∘ exp = exp ∘ f on (0, ∞), where f = EAL self-map,
-- g = EXL self-map.
--
-- The same algebra pairs EML(x,x) = exp(x) − ln(x) with
-- EDL(y,y) = exp(y) / ln(y).
--
-- These conjugacies explain the Blind Session 01 observation that EAL and
-- EXL self-maps have identical multipliers (4.3164206…) at their distinct
-- fixed points: by conjugacy, they share every dynamical invariant.
--
-- Session: blind-exploration follow-up; not yet user-verified in VS Code.
-- T_EAL_EXL_CONJ / T_EML_EDL_CONJ
--
-- NAMING-CLARIFICATION (filed 2026-04-27 EVE):
-- The names "EXL" and "EDL" used in this file refer to the binary
-- operators
--    EXL(x, y) = exp(x) * ln(y)        diagonal: g(y) = exp(y) * ln(y)
--    EDL(x, y) = exp(x) / ln(y)        diagonal: g(y) = exp(y) / ln(y)
--
-- These are DIFFERENT from the F16 glossary in
-- monogate-research/data/superbest.md, where:
--    F13 EXL(x, y) = exp(x * ln(y)) = y^x        diagonal: x^x
--
-- Both naming conventions are mathematically valid; the overlap is in
-- the name only. The conjugacy theorems below are correct under THIS
-- file's conventions. Empirical numerical confirmation at 30+ digit
-- precision is in
-- monogate-research/exploration/f16-self-map-dynamics-2026-04-27/.
-- Reconciliation between the two conventions is pending.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace MonogateSelfMapConjugacy

/-- **EAL↔EXL conjugacy via exp.** Let `f(x) = exp(x) + ln(x)` be the EAL
self-map (the value of the F16 operator `EAL` evaluated on the diagonal)
and `g(y) = exp(y) · ln(y)` the EXL self-map. Then on the positive reals,
`g(exp(x)) = exp(f(x))`.

This is the identity `exp(exp(x) + ln(x)) = exp(exp(x)) · x = exp(exp(x)) · ln(exp(x))`.
-/
theorem eal_exl_conjugacy (x : ℝ) (hx : 0 < x) :
    Real.exp (Real.exp x) * Real.log (Real.exp x)
      = Real.exp (Real.exp x + Real.log x) := by
  rw [Real.exp_add, Real.log_exp, Real.exp_log hx]

/-- **EML↔EDL conjugacy via exp.** Let `f(x) = exp(x) − ln(x)` be the EML
self-map and `g(y) = exp(y) / ln(y)` the EDL self-map. Then on the
positive reals with `x ≠ 1` (so `ln(x) ≠ 0`), `g(exp(x)) = exp(f(x))`.

This is the identity `exp(exp(x) − ln(x)) = exp(exp(x)) / x = exp(exp(x)) / ln(exp(x))`.
-/
theorem eml_edl_conjugacy (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) :
    Real.exp (Real.exp x) / Real.log (Real.exp x)
      = Real.exp (Real.exp x - Real.log x) := by
  have h_log_ne : Real.log x ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hx hx1
  rw [Real.exp_sub, Real.log_exp, Real.exp_log hx]

/-- Corollary: the pairing of fixed points. If `x*` is a fixed point of the
EAL self-map (so `exp(x*) + ln(x*) = x*` on `(0, ∞)`), then `exp(x*)` is a
fixed point of the EXL self-map. -/
theorem eal_exl_fixed_point_pairing (x : ℝ) (hx : 0 < x)
    (h_fp : Real.exp x + Real.log x = x) :
    Real.exp (Real.exp x) * Real.log (Real.exp x) = Real.exp x := by
  rw [eal_exl_conjugacy x hx, h_fp]

/-- The orbit of `g = EXL self-map` starting at `exp(x)` is the `exp`-image
of the orbit of `f = EAL self-map` starting at `x`, step by step.
Stated as the single-step conjugacy: one application of `g` on `exp(x)`
is the `exp` of one application of `f` on `x`. (Iteration is handled by
repeated application.) -/
theorem eal_exl_single_step_conjugacy (x : ℝ) (hx : 0 < x) :
    (fun y => Real.exp y * Real.log y) (Real.exp x)
      = Real.exp ((fun x => Real.exp x + Real.log x) x) := by
  exact eal_exl_conjugacy x hx

-- ===================================================================
-- EML↔EDL partners: single-step conjugacy and fixed-point pairing
-- ===================================================================

/-- EML↔EDL single-step conjugacy: `g(exp x) = exp(f x)` where
    `f(x) = exp(x) − ln x` and `g(y) = exp(y) / ln y`. -/
theorem eml_edl_single_step_conjugacy (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) :
    (fun y => Real.exp y / Real.log y) (Real.exp x)
      = Real.exp ((fun x => Real.exp x - Real.log x) x) :=
  eml_edl_conjugacy x hx hx1

/-- Corollary: pairing of fixed points for the EML↔EDL conjugacy.
    If `x*` is a fixed point of the EML self-map on (0, ∞) \ {1} (so
    `exp(x*) − ln(x*) = x*`), then `exp(x*)` is a fixed point of the
    EDL self-map. -/
theorem eml_edl_fixed_point_pairing (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1)
    (h_fp : Real.exp x - Real.log x = x) :
    Real.exp (Real.exp x) / Real.log (Real.exp x) = Real.exp x := by
  rw [eml_edl_conjugacy x hx hx1, h_fp]

-- ===================================================================
-- Algebraic pre-conditions of the conjugacies (reusable step lemmas)
-- ===================================================================

/-- The key rewrite used in both conjugacies: for x > 0,
    `ln(exp x) = x` AND `exp(ln x) = x`. Packaged as a named step. -/
theorem exp_log_round_trip (x : ℝ) (hx : 0 < x) :
    Real.log (Real.exp x) = x ∧ Real.exp (Real.log x) = x :=
  ⟨Real.log_exp x, Real.exp_log hx⟩

/-- On (0, ∞) \ {1}, ln x ≠ 0 (so EDL self-map is well-defined). -/
theorem log_ne_zero_on_punctured_pos (x : ℝ) (hx : 0 < x) (hx1 : x ≠ 1) :
    Real.log x ≠ 0 :=
  Real.log_ne_zero_of_pos_of_ne_one hx hx1

/-- The value `exp x` at a non-unity positive `x` also avoids 1. Useful for
    iterating the conjugacy (a fixed point of EML distinct from 1 maps to
    a fixed point of EDL distinct from 1). -/
theorem exp_ne_one_of_ne_zero (x : ℝ) (hx : x ≠ 0) : Real.exp x ≠ 1 := by
  intro h
  have : x = 0 := by
    have := congrArg Real.log h
    rwa [Real.log_exp, Real.log_one] at this
  exact hx this

/-- Dually, `0 < exp x` for any real `x` is the positivity needed to plug
    the output of the conjugacy back into its hypothesis. -/
theorem exp_pos_for_iteration (x : ℝ) : 0 < Real.exp x := Real.exp_pos x

-- ===================================================================
-- Rephrasings that emphasize the functional-equation form
-- ===================================================================

/-- EAL↔EXL conjugacy in the form `g ∘ exp = exp ∘ f` on (0, ∞). -/
theorem eal_exl_functional_equation :
    ∀ x : ℝ, 0 < x →
      (fun y => Real.exp y * Real.log y) (Real.exp x)
        = Real.exp ((fun x => Real.exp x + Real.log x) x) :=
  fun x hx => eal_exl_conjugacy x hx

/-- EML↔EDL conjugacy in the form `g ∘ exp = exp ∘ f` on (0, ∞) \ {1}. -/
theorem eml_edl_functional_equation :
    ∀ x : ℝ, 0 < x → x ≠ 1 →
      (fun y => Real.exp y / Real.log y) (Real.exp x)
        = Real.exp ((fun x => Real.exp x - Real.log x) x) :=
  fun x hx hx1 => eml_edl_conjugacy x hx hx1

end MonogateSelfMapConjugacy
