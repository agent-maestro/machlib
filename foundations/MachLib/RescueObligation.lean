import MachLib.BoundaryRun

/-!
# Owing an obligation is not discharging it

Fifth pass. The remaining run-level obligation predicates (`PositiveCoordinateObligation`,
`OutputSafetyObligation`, …) looked like the intervention cluster, and the tempting move was to
define each as its triggering transition — `PositiveCoordinateObligation p := HasTransition p
domainWall logDomainRescue`. That closes six axioms and **proves nothing**: the two named
`*_rescue_obligation` facts become `fun _ h => h`.

Reading `forge/tools/proof_carrying_rescue_suite.py` shows why that would be wrong, and what the
real content is. The registry does not record obligations as present/absent — it records a
**status**:

```python
  "status": {
      "routed":     True,                                  # always
      "witnessed":  lane["has_transition_witness"] is True,
      "proven":     concrete is not None,                  # a CONCRETE witness exists
      "ci_guarded": True,
      ...
  }
```

**`routed` is unconditional. `proven` is not.** That gap is the project's graded-evidence discipline
written into the artifact, and it is the thing worth formalising: an obligation can be routed,
witnessed, and still unproven.

## The split, again, and sharper

* **`Owes`** — structural. A packet exhibiting `domain_wall → log_domain_rescue` **owes** the
  positive-coordinate obligation. That is a fact about the trace, and it is definitional.
* **`Discharged`** — *not* implied by owing. It requires a concrete witness, which the registry
  tracks separately and which `routed: True` never supplies.

`owing_does_not_discharge` is the theorem that keeps the two apart. Without it, defining `Owes` as
the obligation predicate would have quietly collapsed "we routed this" into "we proved this" — the
exact conflation the registry's own `status` block exists to prevent.

`sorryAx`-free, zero new axioms.
-/

namespace MachLib.HighDimensional

/-- The obligations a boundary run can incur. -/
inductive RescueObligation where
  | positiveCoordinate
  | outputSafety
  | precisionSensitivity
  | clampInvariant
deriving DecidableEq, Repr

/-- **The trigger table**: which transition makes which obligation fall due. Transcribed from
`RESCUE_OPERATORS`, same source as `operatorSpec`. -/
def triggeringTransition : RescueObligation → BoundaryEventClass × BoundaryEventClass
  | .positiveCoordinate => (BoundaryEventClass.domainWall, BoundaryEventClass.logDomainRescue)
  | .outputSafety => (BoundaryEventClass.overflowWall, BoundaryEventClass.guardRescue)
  | .precisionSensitivity =>
      (BoundaryEventClass.phantomAttractor, BoundaryEventClass.interiorSample)
  | .clampInvariant =>
      (BoundaryEventClass.saturationShelf, BoundaryEventClass.cornerConcentration)

/-- **A packet OWES an obligation** when its trace exhibits the triggering transition. Structural,
and decidable from the artifact alone. -/
def Owes (p : RunPacket) (o : RescueObligation) : Prop :=
  (triggeringTransition o) ∈ p.transitions

/-- **The registry's status block**, transcribed. `routed` is unconditional in the generator;
`proven` requires a concrete witness. -/
structure ObligationStatus where
  routed : Bool
  witnessed : Bool
  proven : Bool
deriving DecidableEq, Repr

/-- **Discharged** means *proven*, not routed and not merely witnessed. -/
def Discharged (s : ObligationStatus) : Prop := s.proven = true

/-! ## The theorem that keeps routing and proving apart -/

/-- The status the generator emits for a lane that is routed and witnessed but has **no concrete
witness** — `CONCRETE_WITNESSES.get(operator)` returning `None`. -/
def routedNotProven : ObligationStatus :=
  { routed := true, witnessed := true, proven := false }

/-- **Owing does not discharge.** A packet can owe an obligation, have it routed and witnessed, and
still not have it proven. This is why `Owes` must not be used as the obligation predicate: doing so
would make `routed: True` — which the generator sets unconditionally — look like a proof. -/
theorem owing_does_not_discharge :
    ∃ s : ObligationStatus, s.routed = true ∧ s.witnessed = true ∧ ¬ Discharged s := by
  refine ⟨routedNotProven, rfl, rfl, ?_⟩
  intro h
  exact Bool.noConfusion h

/-- And the converse direction is not free either: a proven obligation is not *automatically*
witnessed in the registry's sense, so the three flags are genuinely three flags. -/
def provenNotWitnessed : ObligationStatus :=
  { routed := true, witnessed := false, proven := true }

theorem witnessed_and_proven_independent :
    ∃ s : ObligationStatus, Discharged s ∧ s.witnessed = false :=
  ⟨provenNotWitnessed, rfl, rfl⟩

/-! ## What IS structural: the trigger

These retire the two named transition obligations — but note what they say. They establish that the
obligation is **owed**, which is exactly as much as the transition can establish. -/

theorem owes_positiveCoordinate_of_transition {p : RunPacket}
    (h : HasTransition p BoundaryEventClass.domainWall BoundaryEventClass.logDomainRescue) :
    Owes p RescueObligation.positiveCoordinate := h

theorem owes_outputSafety_of_transition {p : RunPacket}
    (h : HasTransition p BoundaryEventClass.overflowWall BoundaryEventClass.guardRescue) :
    Owes p RescueObligation.outputSafety := h

/-- A valid run owes the positive-coordinate obligation — its trace contains the transition by
`ValidRun.hasTransitions`. **Owed, not discharged.** -/
theorem valid_owes_positiveCoordinate {p : RunPacket} (h : ValidRun p) :
    Owes p RescueObligation.positiveCoordinate :=
  owes_positiveCoordinate_of_transition (domain_wall_reaches_log_domain_rescue h)

theorem valid_owes_outputSafety {p : RunPacket} (h : ValidRun p) :
    Owes p RescueObligation.outputSafety :=
  owes_outputSafety_of_transition (overflow_wall_reaches_guard_rescue h)

theorem valid_owes_precisionSensitivity {p : RunPacket} (h : ValidRun p) :
    Owes p RescueObligation.precisionSensitivity :=
  phantom_attractor_reaches_interior_sample h

theorem valid_owes_clampInvariant {p : RunPacket} (h : ValidRun p) :
    Owes p RescueObligation.clampInvariant :=
  saturation_shelf_reaches_corner_concentration h

end MachLib.HighDimensional
