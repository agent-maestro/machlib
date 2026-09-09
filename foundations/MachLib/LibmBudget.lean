import MachLib.FPGrounding

/-!
# The libm budget — the NUMERIC half of the float bridge

## The finding this module exists for (2026-09-08)

The libm grounding programme reached 13 of 14 `Trans1` primitives, and every grounded theorem
concludes a bound of the shape `real_<f>_eps + absErr`. **`real_<f>_eps` is an `axiom` constant with
no constraint anywhere in the corpus** — not `0 ≤ eps`, not a relation to the unit roundoff `u`,
nothing. Counted across `MachLib/`: `real_sin_eps` has 10 mentions and **0** constraining it;
`real_cos_eps` 7 and 0; `real_atan_eps` 7 and 0; `real_abs_eps` 6 and 0.

So a grounded theorem says *"the error is bounded by a fixed constant, uniform in the input"*.
**The uniformity is real content** and was hard-won: the 2026-07-22 audit found it FALSE for
`exp`/`log`/`sqrt`/`asin`/`acos`/`tan` — unbounded range, domain `NaN`, poles — and repaired those
six with domain hypotheses, which is why they carry `R`/`lo`/`hi` parameters and the globally
Lipschitz five do not. **The ACCURACY content, however, is nil**: the statement holds for any
sufficiently large constant, so a reader of `pid_sin_grounded` cannot extract a number from it.

Meanwhile the forward-error certifier **measured** the budget — `u = 2⁻⁵³` for the correctly-rounded
operations (`+ × ÷ √`, and note IEEE-754 *requires* `√` to be correctly rounded, unlike every
transcendental) and `4u`, two ulp, for the libm transcendentals, over ~1.4M samples — and the
measurement's own headline finding was that the libm transcendentals are **not** correctly rounded.

**Those two halves never met.** `AXIOM_MANIFEST.md` classifies the 22 float-bridge rows as
"validated by measurement", and says a reader of an atan/tan bench certificate should read that block
first. The measurement exists and is good; nothing in Lean consumes its numbers. This module is the
join.

## Why an interface and not more axioms

`FPBridge` faced the same choice for the rounding facts and made it the same way: an explicit,
enumerable structure, satisfiable by a degenerate instance so that theorems taking it are provably
not vacuous. Adding `axiom real_sin_eps_le : real_sin_eps ≤ 4 * u` would work and would widen the
disclosed footprint by one row per primitive for a fact that is *already* empirical. Taking it as a
hypothesis keeps the trust in one named place, keeps the axiom count where it is, and — unlike an
axiom — carries a consistency witness.

`RuntimeLibmBudget` is the empirical instance, and it is **deliberately unprovable here**: it is a
claim about an opaque `Float` runtime, exactly like the `_rounds` axioms it quantifies. What changes
is that the claim is now *quantitative* and *in one place*, instead of implicit in four unconstrained
constants scattered through the grounded theorems.

## What the consistency witness does NOT establish — read this before citing a green audit

`libmBudget_satisfiable` proves `LibmBudget 0 0 0 0 0`. That is enough to show the interface is not
an empty Prop, and it is enough for `tools/hypothesis_audit.py` to see a PRODUCER and therefore not
flag `LibmBudget` as consumed-but-unproduced. **Do not read that green line as evidence that the
runtime satisfies the budget.** It is satisfied at the degenerate instance; `RuntimeLibmBudget` is a
different instantiation and nothing here proves it. This is the corpus's own hazard — *"a green gate
line is a claim about the gate's SCOPE, not about your theorem"* — and the vacuity lesson from
`positive_branch_impossible`, where hypotheses were satisfiable-looking and unsatisfiable in fact.
Here the direction is reversed but the discipline is the same: the witness is a consistency check,
not evidence, and the empirical claim stays empirical.

## `abs` is EXACT, and the corpus already knew the argument

`FPBridge.neg` is stated as an **equality**, not a `RoundsW`, with the reason given in its docstring:
IEEE-754 negation flips the sign bit and cannot round. `abs` clears the sign bit and is exact for the
same reason — it is a §5.5.1 quiet-computational operation, alongside `negate` and `copySign`. So the
budget's `abs` field is `= 0`, not `≤ B`. The asymmetry between `neg` and `abs` was an oversight, not
a judgement.
-/

namespace Certcom
open MachLib.Real

/-- **The libm accuracy budget, as an explicit interface.** `B` is the per-call absolute bound
claimed for the globally-Lipschitz primitives; `abs` is exact and gets `0`.

Parameterised by the epsilon values rather than stated directly over the `axiom` constants, so that
it has a consistency witness (`libmBudget_satisfiable`) and cannot be vacuously assumed.
`RuntimeLibmBudget` below is the instance that carries the empirical content. -/
structure LibmBudget (absE sinE cosE atanE B : MachLib.Real) : Prop where
  /-- IEEE-754 `abs` clears the sign bit — exact, no rounding. Same status, and the same reason, as
  `FPBridge.neg` being an equality rather than a `RoundsW`. -/
  abs_exact : absE = 0
  sin : sinE ≤ B
  cos : cosE ≤ B
  atan : atanE ≤ B
  /-- A budget is a bound, so it is non-negative. Stated rather than derived because the epsilons
  themselves carry no sign constraint — which is half of what this module is about. -/
  nonneg : 0 ≤ B

/-- **Consistency witness.** The interface is satisfiable — an exact runtime with a zero budget obeys
every field — so a theorem taking a `LibmBudget` is not vacuous. This is NOT a claim about any real
libm; it is the same move as `FPBridge`'s degenerate zero-map witness, and for the same reason. -/
theorem libmBudget_satisfiable : LibmBudget 0 0 0 0 0 where
  abs_exact := rfl
  sin := le_refl _
  cos := le_refl _
  atan := le_refl _
  nonneg := le_refl _

/-- **The empirical instance.** The disclosed libm rounding constants of `FPGrounding`, all within a
single budget `B`. Unprovable here by construction — `Float` is opaque — and that is the honest
status: it is the same trust as the `_rounds` axioms, made quantitative and collected in one place.
The certifier's measured value for the libm transcendentals is `B = 4 * u` (two ulp). -/
abbrev RuntimeLibmBudget (B : MachLib.Real) : Prop :=
  LibmBudget real_abs_eps real_sin_eps real_cos_eps real_atan_eps B

/-- Weakening an absolute-error envelope. `AbsEnc E` is `abs (fl - e) ≤ E`, so a larger `E` is a
weaker claim. This is what turns a symbolic grounded bound into the budgeted one. -/
theorem absenc_mono {E E' fl e : MachLib.Real} (h : AbsEnc E fl e) (hle : E ≤ E') : AbsEnc E' fl e :=
  le_trans h hle

/-! ### The join, on the grounded kernels

Each theorem below is the corresponding `FPGrounding` headline with its opaque epsilon replaced by
the budget. The bound is now a NUMBER as soon as `B` and `u` are instantiated (`B = 4u`,
`u = 2⁻⁵³`), which is what a certificate reader needs and what the symbolic form could not give. -/

/-- `sin(PID law)`, at the budget: within `B + absErr` of the exact ℝ value. -/
theorem pid_sin_at_budget (env : Env) {B : MachLib.Real} (hb : RuntimeLibmBudget B) :
    AbsEnc (B + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env
        (emitC (tr1OfEML .sin pidRawEML))).toF)
      (sin (exactR realToR env pidRawEML)) :=
  absenc_mono (pid_sin_grounded env)
    (add_le_add_both hb.sin (le_refl _))

/-- `cos(PID law)`, at the budget. -/
theorem pid_cos_at_budget (env : Env) {B : MachLib.Real} (hb : RuntimeLibmBudget B) :
    AbsEnc (B + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env
        (emitC (tr1OfEML .cos pidRawEML))).toF)
      (cos (exactR realToR env pidRawEML)) :=
  absenc_mono (pid_cos_grounded env)
    (add_le_add_both hb.cos (le_refl _))

/-- `atan(PID law)`, at the budget. -/
theorem pid_atan_at_budget (env : Env) {B : MachLib.Real} (hb : RuntimeLibmBudget B) :
    AbsEnc (B + 1 * absErr realToR env pidRawEML)
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env
        (emitC (tr1OfEML .atan pidRawEML))).toF)
      (atan (exactR realToR env pidRawEML)) :=
  absenc_mono (pid_atan_grounded env)
    (add_le_add_both hb.atan (le_refl _))

end Certcom
