import MachLib.LibmBudget
import MachLib.GroundedPIDInstances

/-!
# The `LibmBudget` restatements, instantiated on `real_abs_eps = 0`

`LibmBudget.lean`'s `pid_sin_at_budget`, `pid_cos_at_budget`, `pid_atan_at_budget` and `pid_abs_at_budget` take
`hb : RuntimeLibmBudget B`, which asks `real_abs_eps = 0`, `real_sin_eps ≤ B`, `real_cos_eps ≤ B`, `real_atan_eps ≤ B`
and `0 ≤ B`. Until 2026-09-14 nothing said `real_abs_eps = 0`; `real_abs_eps_eq_zero` (`FPGrounding.lean`,
owner-approved, measured) now does.

## What the instances say, and what they do not

  * `pid_abs_at_budget_instantiated` is the one with new content: on the PID domain, the runtime `abs` of the PID law
    reads back within `absErr` of the exact `abs`, with NO libm term. Every unit of its error is the arithmetic's.
  * `pid_sin_at_budget_instantiated` and its two siblings instantiate `B` at `real_sin_eps + real_cos_eps +
    real_atan_eps`. No axiom bounds those three constants by a number (the harness measures their suprema at about
    `0.50u`, `0.50u` and `1.0025u`), so this `B` is symbolic and the three instances are weaker than
    `pid_sin_grounded_instantiated` and its siblings, whose bound carries only their own constant. A numeric `B` such as
    `4u` would need three further axioms, which were not approved.

The domain is `PIDInputDomain env B δ` (`GroundedPIDInstances.lean`), and each instance has a specimen at
`pidSpecimenEnv`, where every input is `floatOfR 0.004`.
-/

namespace Certcom

open MachLib MachLib.Real

/-- `real_sin_eps`, `real_cos_eps` and `real_atan_eps` are non-negative: at any finite float each bounds an absolute
value. -/
theorem libm_eps_nonneg {a : Float} (ha : a.isFinite = true) :
    0 ≤ real_sin_eps ∧ 0 ≤ real_cos_eps ∧ 0 ≤ real_atan_eps :=
  ⟨le_trans (abs_nonneg _) (real_sin_rounds a ha), le_trans (abs_nonneg _) (real_cos_rounds a ha),
    le_trans (abs_nonneg _) (real_atan_rounds a ha)⟩

/-- **`RuntimeLibmBudget` holds at `B = real_sin_eps + real_cos_eps + real_atan_eps`**, given any finite float (which
only shows the three constants non-negative). `abs_exact` is `real_abs_eps_eq_zero`. -/
theorem runtimeLibmBudget_sum {a : Float} (ha : a.isFinite = true) :
    RuntimeLibmBudget (real_sin_eps + real_cos_eps + real_atan_eps) := by
  obtain ⟨hs, hc, ht⟩ := libm_eps_nonneg ha
  exact
    { abs_exact := real_abs_eps_eq_zero
      sin := le_trans (le_add_of_nonneg_right hc) (le_add_of_nonneg_right ht)
      cos := le_trans (le_add_of_nonneg_left hs) (le_add_of_nonneg_right ht)
      atan := le_add_of_nonneg_left (add_nonneg hs hc)
      nonneg := add_nonneg (add_nonneg hs hc) ht }

/-- **`pid_sin_at_budget`, instantiated** on `PIDInputDomain`, at the symbolic budget. -/
theorem pid_sin_at_budget_instantiated (env : Env) {B δ : MachLib.Real} (h : PIDInputDomain env B δ) :
    AbsEnc ((real_sin_eps + real_cos_eps + real_atan_eps) + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .sin pidRawEML))).toF)
      (sin (exactR realToR env pidRawEML)) :=
  pid_sin_at_budget env (pidRawEML_domain_facts h _ _).1 (runtimeLibmBudget_sum h.fin_e)

/-- **`pid_cos_at_budget`, instantiated** on `PIDInputDomain`, at the symbolic budget. -/
theorem pid_cos_at_budget_instantiated (env : Env) {B δ : MachLib.Real} (h : PIDInputDomain env B δ) :
    AbsEnc ((real_sin_eps + real_cos_eps + real_atan_eps) + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .cos pidRawEML))).toF)
      (cos (exactR realToR env pidRawEML)) :=
  pid_cos_at_budget env (pidRawEML_domain_facts h _ _).1 (runtimeLibmBudget_sum h.fin_e)

/-- **`pid_atan_at_budget`, instantiated** on `PIDInputDomain`, at the symbolic budget. -/
theorem pid_atan_at_budget_instantiated (env : Env) {B δ : MachLib.Real} (h : PIDInputDomain env B δ) :
    AbsEnc ((real_sin_eps + real_cos_eps + real_atan_eps) + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .atan pidRawEML))).toF)
      (atan (exactR realToR env pidRawEML)) :=
  pid_atan_at_budget env (pidRawEML_domain_facts h _ _).1 (runtimeLibmBudget_sum h.fin_e)

/-- **`pid_abs_at_budget`, instantiated** on `PIDInputDomain`: the runtime `abs` of the PID law is within `absErr` of
the exact `abs`, with no libm term. -/
theorem pid_abs_at_budget_instantiated (env : Env) {B δ : MachLib.Real} (h : PIDInputDomain env B δ) :
    AbsEnc (absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC (tr1OfEML .abs pidRawEML))).toF)
      (abs (exactR realToR env pidRawEML)) :=
  pid_abs_at_budget env (pidRawEML_domain_facts h _ _).1 (runtimeLibmBudget_sum h.fin_e)

/-- Specimen for `pid_sin_at_budget_instantiated`, at `pidSpecimenEnv`. -/
theorem pid_sin_at_budget_specimen :
    AbsEnc ((real_sin_eps + real_cos_eps + real_atan_eps) + 1 * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .sin pidRawEML))).toF)
      (sin (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_sin_at_budget_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain

/-- Specimen for `pid_cos_at_budget_instantiated`, at `pidSpecimenEnv`. -/
theorem pid_cos_at_budget_specimen :
    AbsEnc ((real_sin_eps + real_cos_eps + real_atan_eps) + 1 * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .cos pidRawEML))).toF)
      (cos (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_cos_at_budget_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain

/-- Specimen for `pid_atan_at_budget_instantiated`, at `pidSpecimenEnv`. -/
theorem pid_atan_at_budget_specimen :
    AbsEnc ((real_sin_eps + real_cos_eps + real_atan_eps) + 1 * absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .atan pidRawEML))).toF)
      (atan (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_atan_at_budget_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain

/-- Specimen for `pid_abs_at_budget_instantiated`, at `pidSpecimenEnv`. -/
theorem pid_abs_at_budget_specimen :
    AbsEnc (absErr realToR pidSpecimenEnv pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv (emitC (tr1OfEML .abs pidRawEML))).toF)
      (abs (exactR realToR pidSpecimenEnv pidRawEML)) :=
  pid_abs_at_budget_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain

end Certcom
