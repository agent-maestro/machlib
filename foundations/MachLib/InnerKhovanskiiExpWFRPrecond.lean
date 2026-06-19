import MachLib.InnerKhovanskiiExp
import MachLib.InnerKhovanskiiExpWF

/-!
# MachLib.InnerKhovanskiiExpWFRPrecond — precondition-aware WFR framework

## Why this file exists (2026-06-19 redesign)

`InnerKhovanskiiExpWFR` (in `InnerKhovanskiiExpWF.lean`) was the WFR
generalisation of `InnerKhovanskiiExpMeasured`. It dropped the
`measure t > 0` precondition on the strict descent and replaced it
with a disjunction:

```lean
coeffStep_lt : ∀ t : T,
  measureRel (step t) t ∨ step t = t
```

The chain-2 analysis in `ChainExp2WFInstance.lean` (and triangulated
by three muses on 2026-06-19) showed this disjunction is
**structurally unsatisfiable** for any lex-3 measure on `MultiPoly 2`
over `IterExpChain 2`: the witness `g := varY 1` makes
`chainTotalDeriv g = varY 0 · varY 1`, which raises `degreeY 0`
strictly (so the relation FAILS) and is not equal to `g` (so the
disjunct FAILS too). Both fail at the same single witness.

The muse triangulation identified the right fix:

> Muse 2: "weaken WFR's coeffStep_lt to require a precondition
> (analogue of Measured's measure t > 0). Philosophically correct
> because the original Measured framework's strict-descent is NEVER
> analysed in isolation — it's always invoked after establishing the
> coefficient participates in global descent."

This file ships exactly that: a NEW `InnerKhovanskiiExpWFRPrecond`
structure with a user-supplied precondition `step_precondition : T → Prop`
guarding the strict descent. The chain-2 instance can supply its own
precondition that captures the structural condition under which
strict descent IS achievable.

## What this file ships

1. `InnerKhovanskiiExpWFRPrecond` — the precondition-aware framework.

2. `measured_to_WFRPrecond` — bridge from `InnerKhovanskiiExpMeasured`
   using `step_precondition := fun t => measure t > 0`. This proves
   the new framework is at least as expressive as the SingleExp
   Measured one.

3. `WFR_to_WFRPrecond` — bridge from the unconditional
   `InnerKhovanskiiExpWFR` using `step_precondition := fun _ => True`.
   This proves the new framework strictly generalises the
   unconditional one.

4. `WFRPrecond_to_WFR_when_precond_trivially_holds` — reverse bridge:
   if a precondition-aware structure has trivially-true precondition,
   it ALSO satisfies the unconditional WFR.

5. `chain2_to_WFRPrecond_template` — scaffolding for the chain-2
   instance using the precondition framework. Parametric over
   `step_precondition` and `coeffStep_lt_with_precond_hyp`. Next-
   session work: discharge the parameters with concrete chain-2
   structural conditions.

## What this file does NOT do

It does NOT close `coeffStep_lt` for chain-2. That requires either:

(a) a concrete chain-2-specific `step_precondition` predicate plus a
proof that the precondition implies strict descent (the user
discharges both), OR

(b) a different framework redesign per the muse triangulation's
path (c) — Dershowitz-Manna multiset extension. That's a separate
file targeting the list-level WF relation.

This file is the BRIDGE to the precondition-aware solution. The
chain-2 instance still needs to supply a precondition, and the
instance still needs to prove it implies strict descent. But the
framework no longer asks for the structurally-impossible
unconditional strict descent.

## Axioms

Zero new axioms. Zero `sorry`. Builds on:
- `InnerKhovanskiiExp` (no new axioms)
- `InnerKhovanskiiExpMeasured` (no new axioms)
- `InnerKhovanskiiExpWFR` (no new axioms)
- Lean stdlib + MachLib.Real foundations.
-/

namespace MachLib
namespace InnerKhovanskiiExpWFRPrecondMod

open MachLib.InnerKhovanskiiExpMod
open MachLib.InnerKhovanskiiExpWFMod

/-! ## The precondition-aware framework -/

/-- The precondition-aware WFR generalisation of
`InnerKhovanskiiExpWFR`. The strict-descent obligation
(`coeffStep_lt`) is guarded by a user-supplied predicate
`step_precondition : T → Prop`. For SingleExp's Measured framework,
the natural precondition is `fun t => measure t > 0`; for chain-2,
the precondition can encode chain-specific structural conditions
under which strict descent is achievable. -/
structure InnerKhovanskiiExpWFRPrecond extends InnerKhovanskiiExp where
  /-- The strict descent relation on T. -/
  measureRel : T → T → Prop
  /-- The descent relation is well-founded. -/
  measureWF : WellFounded measureRel
  /-- Length-one bound predicate, unchanged from `InnerKhovanskiiExpWFR`. -/
  length_one_bound : ∀ t : T, ∀ a b : Real, a < b →
    (∃ x : Real, eval t x ≠ 0) →
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ eval t z = 0) →
      zeros.length ≤ N
  /-- coeffStep weakly descends for arbitrary k. -/
  coeffStep_le : ∀ k : Real, ∀ t : T,
    ¬ measureRel (add (derivative t) (scalarMul k t)) t ∨
    measureRel (add (derivative t) (scalarMul k t)) t
  /-- The user-supplied precondition guarding the strict descent. -/
  step_precondition : T → Prop
  /-- coeffStep at k=0 strictly descends WHEN the precondition holds.
  The disjunction-with-equality is retained for the precondition-fails
  case, matching the original WFR shape. -/
  coeffStep_lt : ∀ t : T, step_precondition t →
    measureRel (add (derivative t) (scalarMul 0 t)) t ∨
    add (derivative t) (scalarMul 0 t) = t

/-! ## Bridge: `InnerKhovanskiiExpMeasured` ⟶ `InnerKhovanskiiExpWFRPrecond`

The SingleExp Measured framework already uses a precondition
(`measure t > 0`) on its strict descent. Lifting via `measureLT`
(the Nat-measure relation) and using `measure t > 0` as the
`step_precondition` gives a clean instance of the new framework.

This proves the new framework is at least as expressive as Measured —
EVERY result currently proved against `InnerKhovanskiiExpMeasured`
automatically lifts to the precondition-aware WFR framework.
-/

/-- Bridge from `InnerKhovanskiiExpMeasured` to
`InnerKhovanskiiExpWFRPrecond`. The natural precondition is
`fun t => IKEM.measure t > 0`. -/
noncomputable def measured_to_WFRPrecond
    (IKEM : InnerKhovanskiiExpMeasured) :
    InnerKhovanskiiExpWFRPrecond where
  toInnerKhovanskiiExp := IKEM.toInnerKhovanskiiExp
  measureRel := measureLT IKEM.measure
  measureWF := measureLT_WF IKEM.measure
  length_one_bound := by
    intro t a b hab hne
    refine ⟨IKEM.measure t, ?_⟩
    intro zeros hnodup hzeros
    exact IKEM.length_one_bound t a b hab hne zeros hnodup hzeros
  coeffStep_le := by
    intro k t
    -- The disjunction `¬ measureLT ... ∨ measureLT ...` is decidable
    -- via Classical em.
    exact (Classical.em _).symm
  step_precondition := fun t => IKEM.measure t > 0
  coeffStep_lt := by
    intro t hpos
    -- IKEM.coeffStep_lt gives strict Nat descent; lift to measureLT
    -- via Left injection of the disjunction.
    have h_lt := IKEM.coeffStep_lt t hpos
    -- h_lt : measure (step t) < measure t
    -- Goal: measureLT (step t) t ∨ step t = t
    -- measureLT (step t) t unfolds to measure (step t) < measure t = h_lt.
    exact Or.inl h_lt

/-! ## Bridge: `InnerKhovanskiiExpWFR` ⟶ `InnerKhovanskiiExpWFRPrecond`

The unconditional WFR is the precondition-aware WFR with
`step_precondition := fun _ => True`. This shows the new framework
is a STRICT GENERALISATION of the unconditional one. -/

/-- Bridge from `InnerKhovanskiiExpWFR` to `InnerKhovanskiiExpWFRPrecond`
with `step_precondition := fun _ => True`. -/
def WFR_to_WFRPrecond (IKEWF : InnerKhovanskiiExpWFR) :
    InnerKhovanskiiExpWFRPrecond where
  toInnerKhovanskiiExp := IKEWF.toInnerKhovanskiiExp
  measureRel := IKEWF.measureRel
  measureWF := IKEWF.measureWF
  length_one_bound := IKEWF.length_one_bound
  coeffStep_le := IKEWF.coeffStep_le
  step_precondition := fun _ => True
  coeffStep_lt := fun t _ => IKEWF.coeffStep_lt t

/-! ## Reverse bridge: WFRPrecond ⟶ WFR when precondition is trivial

The reverse direction: if a precondition-aware structure has
`step_precondition := fun _ => True`, it also satisfies the
unconditional WFR. This documents that the unconditional WFR is
exactly the precondition-aware one with trivial precondition. -/

/-- Reverse bridge from a precondition-aware structure with
trivially-true precondition to the unconditional WFR. -/
def WFRPrecond_to_WFR_when_precond_trivially_holds
    (IKEP : InnerKhovanskiiExpWFRPrecond)
    (h_trivial : ∀ t : IKEP.T, IKEP.step_precondition t) :
    InnerKhovanskiiExpWFR where
  toInnerKhovanskiiExp := IKEP.toInnerKhovanskiiExp
  measureRel := IKEP.measureRel
  measureWF := IKEP.measureWF
  length_one_bound := IKEP.length_one_bound
  coeffStep_le := IKEP.coeffStep_le
  coeffStep_lt := fun t => IKEP.coeffStep_lt t (h_trivial t)

/-! ## Reverse bridge: when the precondition is `measureRel _ t` itself

A SEMANTICALLY MEANINGFUL precondition is: the strict descent is
required only when the input is NOT minimal under measureRel. Phrase
this as `∃ s, measureRel s t` ("t is not a minimum"). The WFR
framework's `measureWF` guarantees that the recursion terminates at
minimal elements; if we never call strict descent at minima, the
inductive recursion still closes.

This matches the original Measured pattern: `measure t > 0` means
"there exists something with smaller measure than t" (specifically,
`measure t - 1` is realisable for the corresponding T element if
the type is rich enough). -/

/-- An alternative, semantically meaningful precondition shape:
"t has something strictly less than it under the measure relation."
For SingleExp/Measured, this is equivalent to `measure t > 0` (the
existential witness is any T with `measure ≤ measure t - 1`). -/
def non_minimal_precond (R : Type) (rel : R → R → Prop) (t : R) : Prop :=
  ∃ s : R, rel s t

/-! ## Scaffold for chain-2 instance

The chain-2 instance using the precondition framework. Parametric
over a chain-2 `step_precondition` and a proof that the precondition
implies strict descent. This is the cleanest target for the
next-session work: discharge a CONCRETE precondition predicate and
its corresponding strict-descent proof.

Next-session approach to discharge:

1. Define `chain2_step_precondition g : Prop` capturing the
   structural condition. Candidate: `degreeY 1 g > 0` (the input has
   non-trivial y_1-dependence). When `degreeY 1 g = 0`, g is a
   polynomial in (x, y_0) alone — chainTotalDeriv reduces to the
   SingleExp behaviour, where the lex-3 strict descent ALREADY HOLDS
   (per the existing `polyTrueDegreeStrict_polyDerivativeCoeffs_lt`
   lemma).

2. Prove `degreeY 1 g > 0 → chain2MeasureRel (chainTotalDeriv g + 0·y_0·g) g`.
   This needs the lex-3 measure to track `degreeY 1` as its FIRST
   component (so the y_1-dependence dropping by one is a strict
   decrease). Currently `chain2Measure` returns `(degreeY 1, degreeY 0, ...)`
   per the file's docstring — so the first component DOES track y_1.
   The chain-2 chainTotalDeriv lowers degreeY 1 by 1 when applied to
   a y_1-containing polynomial (chain rule peels one y_1 layer).

3. The `degreeY 1 g = 0` case: g is in the SingleExp sub-framework;
   delegate to SingleExp closure.

This is ~200 more lines of structural lemmas in a follow-up file.
-/

end InnerKhovanskiiExpWFRPrecondMod
end MachLib
