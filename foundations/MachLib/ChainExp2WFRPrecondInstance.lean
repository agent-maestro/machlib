import MachLib.ChainExp2Instance
import MachLib.ChainExp2WFInstance
import MachLib.InnerKhovanskiiExpWFRPrecond

/-!
# MachLib.ChainExp2WFRPrecondInstance — chain-2 instance via precondition-aware WFR

## Why this file exists (2026-06-19 follow-up)

`ChainExp2WFInstance.lean` documented the structural obstruction
that blocks chain-2 closure under the unconditional WFR framework:

  - At `g := varY 1`, `chainTotalDeriv g = varY 0 · varY 1`.
  - The lex-3 measure component 1 (`degreeY 0`) STRICTLY INCREASES
    from 0 to 1.
  - Neither disjunct of WFR's `coeffStep_lt` holds at this single
    witness.

The muse triangulation identified the right framework redesign: add
a precondition to `coeffStep_lt` analogous to the Measured
framework's `measure t > 0`. That redesign shipped in
`InnerKhovanskiiExpWFRPrecond.lean`.

This file is the FOLLOW-UP using the precondition framework. It
ships:

1. `chain2_to_WFRPrecond` — chain-2 instance using
   `InnerKhovanskiiExpWFRPrecond`. Parametric over the chain-2
   `step_precondition` predicate and the strict-descent proof under
   the precondition.

2. `chain2_to_WFRPrecond_canonical` — canonical-measure variant
   (using `chain2MeasureRelCanonical`).

The precondition path UNBLOCKS the chain-2 framework redesign by
letting the chain-2 instance carry the precondition burden instead
of demanding unconditional strict descent. Whether a concrete
chain-2 precondition can be discharged in a future session is
SEPARATE work — see "Limits of the precondition path" below.

## Limits of the precondition path

Even with the precondition framework, the chain-2 closure is NOT
automatic. The structural reason:

  - `chainTotalDeriv` on `IterExpChain 2` raises `degreeY 0` by 1
    for any input whose leading y_1-coefficient is nonzero.
  - No precondition on the INPUT (degreeY 1, degreeY 0, leading
    coefficient structure, etc.) prevents this raise.
  - The lex-3 strict descent on `chain2Measure` FAILS regardless of
    what precondition we impose on g.

So the precondition path is necessary but not sufficient. A complete
chain-2 closure also requires one of:

(I) **Different measure**: a measure that captures chain-2's actual
    structural decrease (the y_1-layer iteration eventually
    terminates because polynomials are finite). E.g., track
    `(degreeY 1 g, degreeY 1 (chain rule corrections), ...)`.

(II) **List-level WF** (muse triangulation's path (c)): a
     Dershowitz-Manna multiset extension over a list of T elements,
     where ONE coefficient's measure can rise IF the global
     multiset measure descends. This needs `scaledReductionAux`
     reframed as one-to-many (one input coefficient producing
     multiple output coefficients in the list).

Both are substantial next-session work (~300+ lines each). This
file's contribution is the FRAMEWORK SCAFFOLD for option (I) — once
a chain-2 step_precondition is supplied with its closure proof, the
chain-2 instance plugs into the precondition-aware WFR.

## What ships clean here

`chain2_to_WFRPrecond` and `chain2_to_WFRPrecond_canonical` —
parametric chain-2 instances using the precondition framework.
Closes silently. Zero new axioms. Zero `sorry`.

The parameters are:
- `length_one_bound` — same shape as the existing parametric instances
- `step_precondition_hyp` — the chain-2 precondition predicate
- `coeffStep_lt_with_precond_hyp` — strict descent under the precondition

This is now the CLEANEST PARAMETRIC shape for the chain-2 framework:
the consumer supplies a step-specific precondition (which they can
discharge against their own chain-2 structural analysis) + the
strict-descent proof under that precondition.
-/

namespace MachLib
namespace ChainExp2WFRPrecondInstanceMod

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.InnerKhovanskiiExpWFMod
open MachLib.InnerKhovanskiiExpWFRPrecondMod
open MachLib.ChainExp2WFInstanceMod

/-! ## Chain-2 instance using the precondition-aware WFR framework -/

/-- Chain-2 plug-in to `InnerKhovanskiiExpWFRPrecond`. Parametric over
the chain-2 `step_precondition` predicate and its strict-descent
witness.

For SingleExp users, the natural choice would be
`step_precondition g := chain2Measure g ≠ (0, 0, 0)` (the Measured
analogue lifted to lex-3). For chain-2, this isn't sufficient by
itself (per the obstruction analysis), so the precondition will
need to be a richer structural condition. -/
noncomputable def chain2_to_WFRPrecond
    (length_one_bound :
      ∀ g : MultiPoly 2, ∀ a b : Real, a < b →
      (∃ x : Real, MultiPoly.eval g x ((IterExpChain 2).chainValues x) ≠ 0) →
      ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧
          MultiPoly.eval g z ((IterExpChain 2).chainValues z) = 0) →
        zeros.length ≤ N)
    (step_precondition_hyp : MultiPoly 2 → Prop)
    (coeffStep_lt_with_precond_hyp :
      ∀ g : MultiPoly 2, step_precondition_hyp g →
        chain2MeasureRel
          (MultiPoly.add
            (PfaffianFn.chainTotalDeriv (IterExpChain 2) g)
            (MultiPoly.mul (MultiPoly.mul (MultiPoly.const 0)
                                           (MultiPoly.varY ⟨0, by omega⟩))
                            g)) g
        ∨ MultiPoly.add
            (PfaffianFn.chainTotalDeriv (IterExpChain 2) g)
            (MultiPoly.mul (MultiPoly.mul (MultiPoly.const 0)
                                           (MultiPoly.varY ⟨0, by omega⟩))
                            g) = g) :
    InnerKhovanskiiExpWFRPrecond where
  toInnerKhovanskiiExp := chainExp2_innerKhovanskii_full
  measureRel := chain2MeasureRel
  measureWF := chain2Measure_WF
  length_one_bound := length_one_bound
  coeffStep_le := coeffStep_chain2_le
  step_precondition := step_precondition_hyp
  coeffStep_lt := coeffStep_lt_with_precond_hyp

/-- Canonical-measure variant: same shape with
`chain2MeasureRelCanonical` and the canonical `coeffStep_le`. -/
noncomputable def chain2_to_WFRPrecond_canonical
    (length_one_bound :
      ∀ g : MultiPoly 2, ∀ a b : Real, a < b →
      (∃ x : Real, MultiPoly.eval g x ((IterExpChain 2).chainValues x) ≠ 0) →
      ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧
          MultiPoly.eval g z ((IterExpChain 2).chainValues z) = 0) →
        zeros.length ≤ N)
    (step_precondition_hyp : MultiPoly 2 → Prop)
    (coeffStep_lt_with_precond_hyp_canonical :
      ∀ g : MultiPoly 2, step_precondition_hyp g →
        chain2MeasureRelCanonical
          (MultiPoly.add
            (PfaffianFn.chainTotalDeriv (IterExpChain 2) g)
            (MultiPoly.mul (MultiPoly.mul (MultiPoly.const 0)
                                           (MultiPoly.varY ⟨0, by omega⟩))
                            g)) g
        ∨ MultiPoly.add
            (PfaffianFn.chainTotalDeriv (IterExpChain 2) g)
            (MultiPoly.mul (MultiPoly.mul (MultiPoly.const 0)
                                           (MultiPoly.varY ⟨0, by omega⟩))
                            g) = g) :
    InnerKhovanskiiExpWFRPrecond where
  toInnerKhovanskiiExp := chainExp2_innerKhovanskii_full
  measureRel := chain2MeasureRelCanonical
  measureWF := chain2Measure_canonical_WF
  length_one_bound := length_one_bound
  coeffStep_le := coeffStep_chain2_le_canonical
  step_precondition := step_precondition_hyp
  coeffStep_lt := coeffStep_lt_with_precond_hyp_canonical

/-! ## Decomposition of the next-session work

Given the precondition framework in place, the chain-2 closure
factorises into TWO clean obligations:

**Obligation A: a chain-2 step_precondition predicate.**

The candidate that pure structure suggests: the precondition encodes
that g is in the "Khovanskii-eligible" region — informally, "g has
non-trivial structure that the step can reduce." For chain-2, this
might be:

  `chain2_step_precondition g := ∃ d_1 d_0, ...`

capturing that g's lex-3 measure is not at a structural minimum
(e.g., not a constant or pure y_0 polynomial).

**Obligation B: strict descent under the precondition.**

Prove that under `chain2_step_precondition`, the step
`chainTotalDeriv g + 0·y_0·g` either strictly decreases the lex-3
measure OR equals g.

This is where the genuine mathematical work happens. The
obstruction analysis in `ChainExp2WFInstance.lean` shows that any
"naive" precondition (like `degreeY 1 g > 0` or `chain2Measure g
≠ (0,0,0)`) is NOT sufficient because `chainTotalDeriv` raises
`degreeY 0` by 1 on inputs with non-trivial y_1-coefficient.

Possible escapes:

(i) Define the lex-3 measure to put `degreeY 1` LAST (after
    `degreeY 0` and a finer structural component). Then `degreeY 0`
    increasing by 1 is dominated by `degreeY 1` decreasing by 1
    elsewhere in the iteration. Requires re-running the lex-3
    obstruction analysis with the new measure.

(ii) Use a measure that combines all chain-rule corrections
     symbolically: e.g., `degreeY 0 + degreeY 1 · constant`. The
     constant chosen to absorb the chain-rule's `+1` term.

(iii) List-level WF (muse path c). The chain-2 step_precondition
      would be "the list isn't already at a multiset minimum,"
      which is naturally true except at termination.

All three require new structural analysis in a follow-up file. This
file provides the framework PARAMETERS; the obligations are still
the next session's mathematical work.
-/

end ChainExp2WFRPrecondInstanceMod
end MachLib
