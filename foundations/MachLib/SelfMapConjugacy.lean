import MachLib.Log

/-!
MachLib.SelfMapConjugacy — port of legacy_eml/SelfMapConjugacy.lean
to MachLib's axiomatic ℝ regime (no Mathlib dependency).

Formalises the F16 self-map conjugacies (Blind omnibus session A,
2026-04-22/23) — the EAL/EXL pair and the EML/EDL pair are
topologically conjugate via the real exponential.

Original Mathlib-dependent file at
`legacy_eml/SelfMapConjugacy.lean`. The 12 theorems below are the
same statements re-proved against MachLib axioms; the only
substantive change is dropping the complex flavouring (the
original used `Complex` interchangeably with `Real`; MachLib is
real-only, so we keep just the real branch).

NAMING-CLARIFICATION (preserved from the legacy file):
The names "EXL" and "EDL" used here refer to the binary
operators
   EXL(x, y) = exp(x) * log(y)        diagonal: g(y) = exp(y) * log(y)
   EDL(x, y) = exp(x) / log(y)        diagonal: g(y) = exp(y) / log(y)

These are DIFFERENT from the F16 glossary in
monogate-research/data/superbest.md, where:
   F13 EXL(x, y) = exp(x * log(y)) = y^x        diagonal: x^x
Both naming conventions are mathematically valid; the overlap is
in the name only. The conjugacy theorems below are correct under
THIS file's conventions.

Status: AUTHORED BY CLAUDE per
feedback_lean_writing_protocol_2026_04_25 — pending user
verification in VS Code lean4 extension before any public-surface
claims of "Lean-verified" status.
-/

namespace MachLib
namespace SelfMapConjugacy

open MachLib.Real

/-! ## EAL ↔ EXL conjugacy via exp -/

/-- **EAL ↔ EXL conjugacy via exp.** Let `f(x) = exp(x) + log(x)` be
the EAL self-map and `g(y) = exp(y) · log(y)` the EXL self-map.
Then on the positive reals,
`g(exp x) = exp(f x)`, i.e.
`exp(exp x) · log(exp x) = exp(exp x + log x)`. -/
theorem eal_exl_conjugacy (x : Real) (hx : 0 < x) :
    exp (exp x) * log (exp x) = exp (exp x + log x) := by
  rw [exp_add, log_exp, exp_log hx]

/-- Corollary: pairing of fixed points. If `x*` is a fixed point of
the EAL self-map (`exp(x*) + log(x*) = x*` on `(0, ∞)`), then
`exp(x*)` is a fixed point of the EXL self-map. -/
theorem eal_exl_fixed_point_pairing (x : Real) (hx : 0 < x)
    (h_fp : exp x + log x = x) :
    exp (exp x) * log (exp x) = exp x := by
  rw [eal_exl_conjugacy x hx, h_fp]

/-- EAL ↔ EXL conjugacy in single-step functional form. -/
theorem eal_exl_single_step_conjugacy (x : Real) (hx : 0 < x) :
    (fun y => exp y * log y) (exp x)
      = exp ((fun x => exp x + log x) x) :=
  eal_exl_conjugacy x hx

/-- EAL ↔ EXL conjugacy in the form `g ∘ exp = exp ∘ f` on (0, ∞). -/
theorem eal_exl_functional_equation :
    ∀ x : Real, 0 < x →
      (fun y => exp y * log y) (exp x)
        = exp ((fun x => exp x + log x) x) :=
  fun x hx => eal_exl_conjugacy x hx

/-! ## EML ↔ EDL conjugacy via exp -/

/-- **EML ↔ EDL conjugacy via exp.** Let `f(x) = exp(x) − log(x)` be
the EML self-map and `g(y) = exp(y) / log(y)` the EDL self-map.
Then on the positive reals with `x ≠ 1` (so `log x ≠ 0`),
`g(exp x) = exp(f x)`, i.e.
`exp(exp x) / log(exp x) = exp(exp x − log x)`. -/
theorem eml_edl_conjugacy (x : Real) (hx : 0 < x) (hx1 : x ≠ 1) :
    exp (exp x) / log (exp x) = exp (exp x - log x) := by
  -- log x ≠ 0 (kept for documentation; the rewrite chain doesn't
  -- branch on it because MachLib's div is total)
  have _h_log_ne : log x ≠ 0 := log_ne_zero_of_pos_of_ne_one hx hx1
  rw [exp_sub, log_exp, exp_log hx]

/-- Corollary: pairing of fixed points for the EML ↔ EDL conjugacy.
If `x*` is a fixed point of the EML self-map on `(0, ∞) \ {1}`
(i.e. `exp(x*) − log(x*) = x*`), then `exp(x*)` is a fixed point
of the EDL self-map. -/
theorem eml_edl_fixed_point_pairing (x : Real) (hx : 0 < x) (hx1 : x ≠ 1)
    (h_fp : exp x - log x = x) :
    exp (exp x) / log (exp x) = exp x := by
  rw [eml_edl_conjugacy x hx hx1, h_fp]

/-- EML ↔ EDL conjugacy in single-step functional form. -/
theorem eml_edl_single_step_conjugacy (x : Real) (hx : 0 < x) (hx1 : x ≠ 1) :
    (fun y => exp y / log y) (exp x)
      = exp ((fun x => exp x - log x) x) :=
  eml_edl_conjugacy x hx hx1

/-- EML ↔ EDL conjugacy in the form `g ∘ exp = exp ∘ f` on
`(0, ∞) \ {1}`. -/
theorem eml_edl_functional_equation :
    ∀ x : Real, 0 < x → x ≠ 1 →
      (fun y => exp y / log y) (exp x)
        = exp ((fun x => exp x - log x) x) :=
  fun x hx hx1 => eml_edl_conjugacy x hx hx1

/-! ## Algebraic preconditions (reusable step lemmas) -/

/-- The key rewrite shared by both conjugacies: for `x > 0`,
`log(exp x) = x` AND `exp(log x) = x`. -/
theorem exp_log_round_trip (x : Real) (hx : 0 < x) :
    log (exp x) = x ∧ exp (log x) = x :=
  ⟨log_exp x, exp_log hx⟩

/-- On `(0, ∞) \ {1}`, `log x ≠ 0`. (Direct rename of the helper in
`MachLib.Log` for readability inside this conjugacy file.) -/
theorem log_ne_zero_on_punctured_pos (x : Real) (hx : 0 < x) (hx1 : x ≠ 1) :
    log x ≠ 0 :=
  log_ne_zero_of_pos_of_ne_one hx hx1

/-- For `x ≠ 0`, `exp x ≠ 1`. Useful for iterating the conjugacy:
a fixed point of EML distinct from 1 maps to a fixed point of EDL
distinct from 1. -/
theorem exp_ne_one_of_ne_zero (x : Real) (hx : x ≠ 0) : exp x ≠ 1 := by
  intro h
  -- exp x = 1 ⇒ exp x = exp 0 ⇒ x = 0 by exp_injective, contra hx.
  have hzero : exp x = exp 0 := by rw [h, exp_zero]
  exact hx (exp_injective hzero)

/-- `0 < exp x` for any real `x` — positivity needed to plug the
output of the conjugacy back into its hypothesis. -/
theorem exp_pos_for_iteration (x : Real) : 0 < exp x := exp_pos x

end SelfMapConjugacy
end MachLib
