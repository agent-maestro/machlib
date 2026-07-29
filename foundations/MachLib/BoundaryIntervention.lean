import MachLib.BoundaryRun

/-!
# `BoundaryInterventionPair` — the manifest's obligation is *determined by* its intervention

Third pass of the `HighDimensional` audit. The previous pass stalled on obligations of this shape:

```
    log_domain_lift_intervention_obligation :
      ValidInterventionPair p →
      PairUsesIntervention p logDomainLift →
      PairHasRescueTransition p domainWall logDomainRescue →
      PositiveCoordinateInterventionObligation p
```

and I recorded that they were **not retirable**, because the conclusion was an opaque predicate.
That was right about the previous pass and wrong as a general verdict — **the conclusion has a
referent too**, and finding it is what unblocks the cluster.

## The referent: the obligation is a FIELD, not a judgement

`forge/tools/boundary_optimizer_benchmark.py` builds each pair as

```
    {"intervention": …, "from_event": …, "to_event": …,
     "obligation": operator["obligation"],           ← copied from RESCUE_OPERATORS
     "raw": …, "intervened": …, "finite_survival_delta": …}
```

and `proof_carrying_rescue_replay.py` pins the table it is copied from:

| intervention | transition | obligation |
|---|---|---|
| `log_domain_lift` | `domain_wall → log_domain_rescue` | `PositiveCoordinate` |
| `guard_clamp` | `overflow_wall → guard_rescue` | `OutputSafety` |
| `precision_escape` | `phantom_attractor → interior_sample` | `PrecisionSensitivity` |
| `saturation_deshelf` | `saturation_shelf → corner_concentration` | `ClampInvariant` |

So `PositiveCoordinateInterventionObligation p` is not a claim about geometry — it is
`p.obligation = positiveCoordinate`. And the four axioms say: **a valid pair's declared obligation
is the one its intervention's operator declares.** That is an *internal-consistency* property of the
manifest, and it is exactly what `operatorSpec` below makes checkable.

## What is structural and what is empirical, again

**Structural — retired.** Obligation/transition consistency. `ValidPair` says the pair's `from`,
`to` and `obligation` agree with `operatorSpec p.intervention`. The four obligations then fall out by
case analysis, and they are *worth* having: they turn "the generator copies the right field" from a
property of a Python script into a theorem about the artifact.

**Empirical — NOT retired.** `PairNonregressingSurvival` — that the intervention does not make
survival *worse* (`finite_survival_delta ≥ 0`) — is a claim about whether the rescue operators
actually work. A badly chosen intervention can regress survival, so it is defined here as a
*property a pair may or may not have*, never assumed. `regressingPair` witnesses a valid pair that
lacks it, which is what keeps the distinction honest.

`sorryAx`-free, zero new axioms.
-/

namespace MachLib.HighDimensional

open MachLib.Real

/-- The four rescue interventions. -/
inductive BoundaryIntervention where
  | logDomainLift
  | guardClamp
  | precisionEscape
  | saturationDeshelf
deriving DecidableEq, Repr

/-- The four obligations a rescue can carry. -/
inductive InterventionObligation where
  | positiveCoordinate
  | outputSafety
  | precisionSensitivity
  | clampInvariant
deriving DecidableEq, Repr

/-- **`RESCUE_OPERATORS`, transcribed.** The single place the mapping lives, so a pair can be checked
against it instead of against a reader's memory. -/
def operatorSpec : BoundaryIntervention → BoundaryEventClass × BoundaryEventClass × InterventionObligation
  | .logDomainLift =>
      (BoundaryEventClass.domainWall, BoundaryEventClass.logDomainRescue,
       InterventionObligation.positiveCoordinate)
  | .guardClamp =>
      (BoundaryEventClass.overflowWall, BoundaryEventClass.guardRescue,
       InterventionObligation.outputSafety)
  | .precisionEscape =>
      (BoundaryEventClass.phantomAttractor, BoundaryEventClass.interiorSample,
       InterventionObligation.precisionSensitivity)
  | .saturationDeshelf =>
      (BoundaryEventClass.saturationShelf, BoundaryEventClass.cornerConcentration,
       InterventionObligation.clampInvariant)

/-- **An intervention pair**, as the benchmark emits it: one intervention, the transition it claims,
the obligation it declares, and the two runs it compares. -/
structure InterventionPair where
  intervention : BoundaryIntervention
  fromEvent : BoundaryEventClass
  toEvent : BoundaryEventClass
  obligation : InterventionObligation
  raw : RunPacket
  intervened : RunPacket

/-- **Pair validity** — the manifest's own internal consistency, and *nothing about efficacy*.
Both runs valid, and the declared transition and obligation match the operator table. Deliberately
says nothing about `finite_survival_delta`: whether the rescue helps is the empirical question. -/
structure ValidPair (p : InterventionPair) : Prop where
  rawValid : ValidRun p.raw
  intervenedValid : ValidRun p.intervened
  matchesSpec : (p.fromEvent, p.toEvent, p.obligation) = operatorSpec p.intervention

/-- The pair used this intervention. -/
def UsesIntervention (p : InterventionPair) (i : BoundaryIntervention) : Prop := p.intervention = i

/-- The pair claims this rescue transition. -/
def HasRescueTransition (p : InterventionPair) (a b : BoundaryEventClass) : Prop :=
  p.fromEvent = a ∧ p.toEvent = b

/-- The pair declares this obligation. -/
def DeclaresObligation (p : InterventionPair) (o : InterventionObligation) : Prop :=
  p.obligation = o

/-- **Survival does not regress** — `finite_survival_delta ≥ 0`. A PROPERTY, never an assumption:
whether a rescue operator actually helps is the thing the benchmark is measuring. -/
def NonregressingSurvival (p : InterventionPair) : Prop :=
  finiteSurvivalRate p.raw ≤ finiteSurvivalRate p.intervened

/-! ## Structural: the declared obligation is determined by the intervention -/

/-- The general form. The four named obligations below are instances. -/
theorem obligation_of_valid {p : InterventionPair} (h : ValidPair p) :
    p.obligation = (operatorSpec p.intervention).2.2 := by
  have := h.matchesSpec
  exact congrArg (fun t => t.2.2) this

theorem log_domain_lift_declares_positive_coordinate {p : InterventionPair}
    (h : ValidPair p) (hi : UsesIntervention p BoundaryIntervention.logDomainLift) :
    DeclaresObligation p InterventionObligation.positiveCoordinate := by
  have ho := obligation_of_valid h
  rw [hi] at ho
  exact ho

theorem guard_clamp_declares_output_safety {p : InterventionPair}
    (h : ValidPair p) (hi : UsesIntervention p BoundaryIntervention.guardClamp) :
    DeclaresObligation p InterventionObligation.outputSafety := by
  have ho := obligation_of_valid h
  rw [hi] at ho
  exact ho

theorem precision_escape_declares_precision_sensitivity {p : InterventionPair}
    (h : ValidPair p) (hi : UsesIntervention p BoundaryIntervention.precisionEscape) :
    DeclaresObligation p InterventionObligation.precisionSensitivity := by
  have ho := obligation_of_valid h
  rw [hi] at ho
  exact ho

theorem saturation_deshelf_declares_clamp_invariant {p : InterventionPair}
    (h : ValidPair p) (hi : UsesIntervention p BoundaryIntervention.saturationDeshelf) :
    DeclaresObligation p InterventionObligation.clampInvariant := by
  have ho := obligation_of_valid h
  rw [hi] at ho
  exact ho

/-- And the transition is determined too — a valid `logDomainLift` pair claims exactly
`domainWall → logDomainRescue`, so the third hypothesis of the original axiom was redundant. -/
theorem log_domain_lift_transition {p : InterventionPair}
    (h : ValidPair p) (hi : UsesIntervention p BoundaryIntervention.logDomainLift) :
    HasRescueTransition p BoundaryEventClass.domainWall BoundaryEventClass.logDomainRescue := by
  have hs := h.matchesSpec
  rw [hi] at hs
  exact ⟨congrArg (fun t => t.1) hs, congrArg (fun t => t.2.1) hs⟩

/-! ## Empirical: efficacy is NOT implied by validity

`ValidPair` constrains bookkeeping, not outcomes. The witness below is a fully valid pair whose
intervention makes survival *worse* — so `NonregressingSurvival` is genuine content that the
benchmark must measure, not something the schema hands over. -/

private def okRun (fails : Nat) : RunPacket :=
  { mode := BoundaryMode.baseline,
    sampleCount := 10, domainFailures := fails, centerHits := 1, boundaryHits := 9,
    events := requiredEvents, transitions := requiredTransitions }

private theorem okRun_valid {f : Nat} (h : f ≤ 10) : ValidRun (okRun f) :=
  { samplesPositive := (by decide : (0:Nat) < 10)
    failuresBounded := h
    hasRequired := fun _ hm => hm
    hasTransitions := fun _ hm => hm
    graphWellFormed :=
      (by decide : ∀ t ∈ requiredTransitions, t.1 ∈ requiredEvents ∧ t.2 ∈ requiredEvents)
    countsConsistent := (by decide : (1:Nat) + 9 ≤ 10) }

/-- A valid pair whose "rescue" REGRESSES survival to ZERO: 0 failures before, all 10 after. -/
def regressingPair : InterventionPair :=
  { intervention := BoundaryIntervention.logDomainLift
    fromEvent := BoundaryEventClass.domainWall
    toEvent := BoundaryEventClass.logDomainRescue
    obligation := InterventionObligation.positiveCoordinate
    raw := okRun 0
    intervened := okRun 10 }

theorem regressingPair_valid : ValidPair regressingPair :=
  { rawValid := okRun_valid (by decide)
    intervenedValid := okRun_valid (by decide)
    matchesSpec := rfl }

/-- **The independence witness.** Validity does not imply the rescue helps. -/
theorem nonregression_not_implied :
    ∃ p : InterventionPair, ValidPair p ∧ ¬ NonregressingSurvival p := by
  refine ⟨regressingPair, regressingPair_valid, ?_⟩
  intro hle
  have h10 : (0 : Real) < natCast 10 := natCast_pos (by decide)
  -- hle unfolds to  10/10 <= 0/10 ; clear the divisor
  have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt h10)
  rw [show finiteSurvivalRate regressingPair.raw = natCast 10 / natCast 10 from rfl,
      show finiteSurvivalRate regressingPair.intervened = natCast 0 / natCast 10 from rfl,
      div_mul_cancel (ne_of_gt h10), div_mul_cancel (ne_of_gt h10), natCast_zero] at hmul
  -- hmul : natCast 10 <= 0, against 0 < natCast 10
  exact lt_irrefl_ax _ (lt_of_lt_of_le h10 hmul)

end MachLib.HighDimensional
