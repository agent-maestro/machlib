import MachLib.Basic
import MachLib.EML
import MachLib.BallCubeRatio
import MachLib.GuardedLowering
import MachLib.RescueObligation
import MachLib.GeometricDecay
import MachLib.BoundaryRun
import MachLib.BoundaryIntervention

/-!
# High-Dimensional EML Obligations

Draft theorem queue generated from the Monogate high-D frontier packets.
These declarations intentionally carry `sorry`; they are compile-checked
formalization targets, not completed proof claims.
-/

namespace MachLib
namespace HighDimensional

open MachLib.Real

/-- Convergence predicate. **Was an opaque axiom until 2026-07-28**, which is exactly why
`high_dim_ball_cube_ratio_tends_zero` below carried a `sorry` for a month: there is nothing to
prove about an uninterpreted symbol. It is now `MachLib.Real.TendstoTo`, the ordinary ε–N
definition (`Limits.lean`). The `sorry` was a gap in the VOCABULARY, not in the argument. -/
abbrev TendstoTo : (Nat -> Real) -> Real -> Prop := MachLib.Real.TendstoTo

/-- Volume ratio: unit d-ball divided by the cube `[-1,1]^d`. **Also formerly an opaque axiom**;
now `MachLib.Real.bcRatio`, defined by the standard recurrence `r(d) = r(d-2)·π/(2d)`. That
recurrence is where the geometry enters and is stated as such in `BallCubeRatio.lean`; it was
checked numerically against `π^(d/2)/Γ(d/2+1)` at d = 1..12 (agreement < 1e-12). -/
noncomputable abbrev ballCubeRatio : Nat -> Real := MachLib.Real.bcRatio

/-- Cube boundary-shell probability: `1 − (1−ε)^d`, the complement being the concentric cube of
side `1−ε`. **Was an opaque axiom** — and unlike the packet placeholders this one needed a PROOF,
not a definition. -/
noncomputable abbrev cubeBoundaryShellProbability : Real -> Nat -> Real :=
  MachLib.Real.cubeShell

/-- **Concentration of measure**, proven in `GeometricDecay.lean` from a division-free Bernoulli
step. Essentially all of a high-dimensional cube lies near its surface. -/
theorem cubeBoundaryShellProbability_tends_one
    (eps : Real) (heps : 0 < eps ∧ eps < 1) :
    TendstoTo (cubeBoundaryShellProbability eps) 1 :=
  MachLib.Real.cubeShell_tendsto_one heps.1 heps.2

/-- Raw first-layer EML log-domain survival: `(1/2)^(2^(d−1))`, independent symmetric leaves.
**Was an axiom together with its own "decay" fact** — and the fact was the DEFINITION, so pinning
both meant the ledger carried an entry for `x = x`. -/
noncomputable def firstLayerSurvival (d : Nat) : Real :=
  realPow (1 / natCast 2 : Real) (natCast (2 ^ (d - 1)))

/-- Definitional, now that `firstLayerSurvival` has a definition. -/
theorem firstLayerSurvival_decay
    (d : Nat) :
    firstLayerSurvival d = realPow (1 / natCast 2 : Real) (natCast (2 ^ (d - 1))) := rfl

/-- Replay packet. **Was an opaque axiom until 2026-07-29** — the same defect that kept
`high_dim_ball_cube_ratio_tends_zero` open for a month: three uninterpreted symbols and a theorem
relating them, so there was nothing to prove. Now `GuardedLowering.Packet`, modelled on the manifest
Forge already emits and replays (`forge.optimizer.proof_carrying_rescue_suite.v0`, four lanes, one
named obligation each). -/
abbrev ReplayPacket : Type := GuardedLowering.Packet

/-- Guard validity: every lane carries its guard. -/
abbrev ValidGuards : ReplayPacket -> Prop := GuardedLowering.ValidGuards

/-- Domain preservation: every obligation declared in the source survives the lowering. NOT
definitionally implied by `ValidGuards` — an unguarded lane is dropped by `lower`, and
`GuardedLowering.badPacket_not_preserved` exhibits a packet where this FAILS. -/
abbrev DomainPreserved : ReplayPacket -> Prop := GuardedLowering.DomainPreserved

/-- Now `BoundaryRun.RunPacket` — `forge.optimizer.boundary_run_benchmark.v1` made concrete. -/
abbrev BoundaryRunPacket : Type := RunPacket

/-- Packet validity: schema, simulated boundary flags, and replay fields agree. -/
abbrev ValidBoundaryRunPacket : BoundaryRunPacket -> Prop := ValidRun

/-- Packet mode says the run used guarded EML evaluation. -/
axiom GuardedBoundaryMode : BoundaryRunPacket -> Prop

/-- Packet mode says the run used log-domain candidate coordinates. -/
axiom LogDomainBoundaryMode : BoundaryRunPacket -> Prop

/-- Packet finite-survival metric, as exported by Forge/electronics evidence. -/
noncomputable abbrev packetFiniteSurvivalRate : BoundaryRunPacket -> Real := finiteSurvivalRate

/-- Packet boundary-hit count, abstracted as a real for ratio obligations. -/
noncomputable def packetBoundaryHits (p : BoundaryRunPacket) : Real := natCast p.boundaryHits

/-- Packet center-hit count, abstracted as a real for ratio obligations. -/
noncomputable def packetCenterHits (p : BoundaryRunPacket) : Real := natCast p.centerHits

/-- Guarded packets have a nonnegative finite-survival metric. -/
theorem guarded_boundary_packet_finite_survival_nonneg
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    GuardedBoundaryMode p ->
    0 <= packetFiniteSurvivalRate p :=
  fun hv _ => finiteSurvivalRate_nonneg hv

/-- Log-domain candidate packets preserve the finite-survival metric lower bound. -/
theorem log_domain_boundary_packet_finite_survival_nonneg
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    LogDomainBoundaryMode p ->
    0 <= packetFiniteSurvivalRate p :=
  fun hv _ => finiteSurvivalRate_nonneg hv

/-- Benchmark-observed boundary dominance relation for one replay packet. -/
axiom BoundaryDominatesCenter : BoundaryRunPacket -> Prop

/-- Packet contains at least one event of the given class. -/
abbrev PacketHasEvent : BoundaryRunPacket -> BoundaryEventClass -> Prop := HasEvent

/-- Packet contains at least one transition from one event class to another. -/
abbrev PacketHasTransition :
    BoundaryRunPacket -> BoundaryEventClass -> BoundaryEventClass -> Prop := HasTransition

/-- Packet transition entropy metric exported by Forge/electronics evidence. -/
axiom packetTransitionEntropy : BoundaryRunPacket -> Real

/-- Transition graph is well-formed for the packet trace. -/
axiom ValidTransitionGraph : BoundaryRunPacket -> Prop

/-- Reviewer-facing semantic tier for rescue operators.
`semanticRewrite` is intentionally not assigned to any v0 rescue operator. -/
inductive RescueSemanticTier where
  | packetBridgeOnly
  | concreteSampleInvariant
  | restrictedSemanticRewrite
  | semanticRewrite

/-- Current v0 semantic tier for each rescue operator. -/
def rescueSemanticTier : BoundaryIntervention -> RescueSemanticTier
  | BoundaryIntervention.logDomainLift => RescueSemanticTier.restrictedSemanticRewrite
  | BoundaryIntervention.guardClamp => RescueSemanticTier.concreteSampleInvariant
  | BoundaryIntervention.precisionEscape => RescueSemanticTier.concreteSampleInvariant
  | BoundaryIntervention.saturationDeshelf => RescueSemanticTier.concreteSampleInvariant

/-- Packet pair witnessing one raw/intervened benchmark comparison. -/
abbrev BoundaryInterventionPair : Type := InterventionPair

/-- Pair validity: same dimension/depth/sample/seed comparison, simulated only. -/
abbrev ValidInterventionPair : BoundaryInterventionPair -> Prop := ValidPair

/-- The named intervention used by a pair. -/
abbrev PairUsesIntervention : BoundaryInterventionPair -> BoundaryIntervention -> Prop := UsesIntervention

/-- The pair exhibits a from-event to to-event rescue transition. -/
abbrev PairHasRescueTransition :
    BoundaryInterventionPair -> BoundaryEventClass -> BoundaryEventClass -> Prop :=
    HasRescueTransition

/-- Finite survival did not regress in the pairwise benchmark. -/
abbrev PairNonregressingSurvival : BoundaryInterventionPair -> Prop := NonregressingSurvival

/-- Obligation predicates attached to taxonomy classes. -/
axiom BaselineReplayValid : BoundaryRunPacket -> Prop
axiom DomainPreservationObligation : BoundaryRunPacket -> Prop
axiom BoundedEvaluationObligation : BoundaryRunPacket -> Prop
/-- **OWED, not discharged.** The original axiom established only that the obligation falls
due; `RescueObligation.owing_does_not_discharge` proves that is strictly weaker than proven. -/
abbrev ClampInvariantObligation (p : BoundaryRunPacket) : Prop := Owes p RescueObligation.clampInvariant
/-- **OWED, not discharged.** The original axiom established only that the obligation falls
due; `RescueObligation.owing_does_not_discharge` proves that is strictly weaker than proven. -/
abbrev PrecisionSensitivityObligation (p : BoundaryRunPacket) : Prop := Owes p RescueObligation.precisionSensitivity
/-- **OWED, not discharged.** The original axiom established only that the obligation falls
due; `RescueObligation.owing_does_not_discharge` proves that is strictly weaker than proven. -/
abbrev OutputSafetyObligation (p : BoundaryRunPacket) : Prop := Owes p RescueObligation.outputSafety
/-- **OWED, not discharged.** The original axiom established only that the obligation falls
due; `RescueObligation.owing_does_not_discharge` proves that is strictly weaker than proven. -/
abbrev PositiveCoordinateObligation (p : BoundaryRunPacket) : Prop := Owes p RescueObligation.positiveCoordinate
axiom BoundaryDynamicsObligation : BoundaryRunPacket -> Prop
axiom InterventionSoundnessObligation : BoundaryInterventionPair -> Prop
abbrev PositiveCoordinateInterventionObligation (p : BoundaryInterventionPair) : Prop :=
  DeclaresObligation p InterventionObligation.positiveCoordinate
abbrev OutputSafetyInterventionObligation (p : BoundaryInterventionPair) : Prop :=
  DeclaresObligation p InterventionObligation.outputSafety
abbrev PrecisionEscapeInterventionObligation (p : BoundaryInterventionPair) : Prop :=
  DeclaresObligation p InterventionObligation.precisionSensitivity
abbrev ClampDeshelfInterventionObligation (p : BoundaryInterventionPair) : Prop :=
  DeclaresObligation p InterventionObligation.clampInvariant

/-- Concrete v0 log-domain witness extracted from a Forge rescue trace.
This is intentionally smaller than `BoundaryRunPacket`: it records only the
fields needed to discharge the positive-coordinate part of the log-domain lane
without appealing to the abstract packet-obligation bridge. -/
structure LogDomainPositiveCoordinateWitness where
  rawCoordinate : Real
  liftedCoordinate : Real
  rawEvent : BoundaryEventClass
  rescuedEvent : BoundaryEventClass
  liftedPositive : 0 < liftedCoordinate
  rawIsDomainWall : rawEvent = BoundaryEventClass.domainWall
  rescueIsLogDomain : rescuedEvent = BoundaryEventClass.logDomainRescue

/-- Concrete positive-coordinate obligation for one log-domain rescue sample. -/
def ConcretePositiveCoordinateObligation
    (w : LogDomainPositiveCoordinateWitness) : Prop :=
  0 < w.liftedCoordinate ∧
    w.rawEvent = BoundaryEventClass.domainWall ∧
    w.rescuedEvent = BoundaryEventClass.logDomainRescue

/-- Restricted semantic contract for the log-domain lift lane. It says the
rescue is a representation change from a raw domain wall into a positive
internal coordinate for this small log-domain program class. -/
def RestrictedLogDomainLiftSemantics
    (w : LogDomainPositiveCoordinateWitness) : Prop :=
  w.rawEvent = BoundaryEventClass.domainWall ∧
    0 < w.liftedCoordinate ∧
    w.rescuedEvent = BoundaryEventClass.logDomainRescue

/-- Concrete v0 guard-clamp witness extracted from a Forge rescue trace.
This is the second independent discharged foothold: instead of proving
positivity by a log-domain lift, it proves a guarded coordinate remains inside
an explicit output bound for one overflow rescue sample. -/
structure GuardClampOutputSafetyWitness where
  rawCoordinate : Real
  guardedCoordinate : Real
  outputLimit : Real
  rawEvent : BoundaryEventClass
  rescuedEvent : BoundaryEventClass
  guardWithinLimit : guardedCoordinate ≤ outputLimit
  rawIsOverflowWall : rawEvent = BoundaryEventClass.overflowWall
  rescueIsGuardRescue : rescuedEvent = BoundaryEventClass.guardRescue

/-- Concrete output-safety obligation for one guard-clamp rescue sample. -/
def ConcreteOutputSafetyObligation
    (w : GuardClampOutputSafetyWitness) : Prop :=
  w.guardedCoordinate ≤ w.outputLimit ∧
    w.rawEvent = BoundaryEventClass.overflowWall ∧
    w.rescuedEvent = BoundaryEventClass.guardRescue

/-- Concrete v0 precision-escape witness extracted from a Forge rescue trace.
This witness is deliberately local: it records that low precision reported a
stalled gradient, while the higher-precision replay exposed a nonzero escape
signal and moved the sample back to the interior. -/
structure PrecisionEscapeWitness where
  probeCoordinate : Real
  escapedCoordinate : Real
  lowPrecisionGradient : Real
  highPrecisionGradient : Real
  rawEvent : BoundaryEventClass
  rescuedEvent : BoundaryEventClass
  lowPrecisionStalled : lowPrecisionGradient = 0
  highPrecisionEscapes : ¬ highPrecisionGradient = 0
  rawIsPhantomAttractor : rawEvent = BoundaryEventClass.phantomAttractor
  rescueIsInteriorSample : rescuedEvent = BoundaryEventClass.interiorSample

/-- Concrete precision-escape obligation for one phantom-attractor sample. -/
def ConcretePrecisionEscapeObligation
    (w : PrecisionEscapeWitness) : Prop :=
  w.lowPrecisionGradient = 0 ∧
    ¬ w.highPrecisionGradient = 0 ∧
    w.rawEvent = BoundaryEventClass.phantomAttractor ∧
    w.rescuedEvent = BoundaryEventClass.interiorSample

/-- Concrete v0 saturation-deshelf witness extracted from a Forge rescue trace.
This witness is deliberately local: it records that the recovered pre-clamp
pressure is still compatible with the declared clamp interval, and that the
trace moved from a saturation shelf to corner concentration. -/
structure SaturationDeshelfClampWitness where
  probeCoordinate : Real
  preClampPressure : Real
  lowerBound : Real
  upperBound : Real
  rawEvent : BoundaryEventClass
  rescuedEvent : BoundaryEventClass
  lowerLePressure : lowerBound ≤ preClampPressure
  pressureLeUpper : preClampPressure ≤ upperBound
  rawIsSaturationShelf : rawEvent = BoundaryEventClass.saturationShelf
  rescueIsCornerConcentration : rescuedEvent = BoundaryEventClass.cornerConcentration

/-- Concrete clamp-invariant obligation for one saturation-deshelf sample. -/
def ConcreteClampInvariantObligation
    (w : SaturationDeshelfClampWitness) : Prop :=
  w.lowerBound ≤ w.preClampPressure ∧
    w.preClampPressure ≤ w.upperBound ∧
    w.rawEvent = BoundaryEventClass.saturationShelf ∧
    w.rescuedEvent = BoundaryEventClass.cornerConcentration

/-- Concrete local invariant semantics currently discharged by v0 witnesses.
Precision escape is intentionally `False` here: it has packet/replay evidence,
but no concrete sample-invariant theorem yet. -/
def RescueHasConcreteSampleInvariant : BoundaryIntervention -> Prop
  | BoundaryIntervention.logDomainLift =>
      ∀ w : LogDomainPositiveCoordinateWitness, ConcretePositiveCoordinateObligation w
  | BoundaryIntervention.guardClamp =>
      ∀ w : GuardClampOutputSafetyWitness, ConcreteOutputSafetyObligation w
  | BoundaryIntervention.precisionEscape =>
      ∀ w : PrecisionEscapeWitness, ConcretePrecisionEscapeObligation w
  | BoundaryIntervention.saturationDeshelf =>
      ∀ w : SaturationDeshelfClampWitness, ConcreteClampInvariantObligation w

/-- Restricted semantic rewrite status currently exists only for the
log-domain lift lane. -/
def RescueHasRestrictedSemanticRewrite : BoundaryIntervention -> Prop
  | BoundaryIntervention.logDomainLift =>
      ∀ w : LogDomainPositiveCoordinateWitness, RestrictedLogDomainLiftSemantics w
  | _ => False

/-- Valid high-dimensional packets may witness boundary dominance. -/
axiom boundary_dominates_center_from_packet
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    packetCenterHits p <= packetBoundaryHits p ->
    BoundaryDominatesCenter p

axiom interior_sample_obligation
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.interiorSample ->
    BaselineReplayValid p

axiom domain_wall_obligation
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.domainWall ->
    DomainPreservationObligation p

axiom overflow_wall_obligation
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.overflowWall ->
    BoundedEvaluationObligation p

axiom saturation_shelf_obligation
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.saturationShelf ->
    ClampInvariantObligation p

axiom phantom_attractor_obligation
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.phantomAttractor ->
    PrecisionSensitivityObligation p

axiom guard_rescue_obligation
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.guardRescue ->
    OutputSafetyObligation p

axiom log_domain_rescue_obligation
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.logDomainRescue ->
    PositiveCoordinateObligation p

axiom transition_graph_obligation
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    ValidTransitionGraph p ->
    BoundaryDynamicsObligation p

theorem domain_to_log_domain_rescue_obligation
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasTransition p BoundaryEventClass.domainWall BoundaryEventClass.logDomainRescue ->
    PositiveCoordinateObligation p :=
  fun hv _ => valid_owes_positiveCoordinate hv

theorem overflow_to_guard_rescue_obligation
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasTransition p BoundaryEventClass.overflowWall BoundaryEventClass.guardRescue ->
    OutputSafetyObligation p :=
  fun hv _ => valid_owes_outputSafety hv

theorem log_domain_lift_intervention_obligation
    (p : BoundaryInterventionPair) :
    ValidInterventionPair p ->
    PairUsesIntervention p BoundaryIntervention.logDomainLift ->
    PairHasRescueTransition p BoundaryEventClass.domainWall BoundaryEventClass.logDomainRescue ->
    PositiveCoordinateInterventionObligation p :=
  fun hv hi _ => log_domain_lift_declares_positive_coordinate hv hi

theorem guard_clamp_intervention_obligation
    (p : BoundaryInterventionPair) :
    ValidInterventionPair p ->
    PairUsesIntervention p BoundaryIntervention.guardClamp ->
    PairHasRescueTransition p BoundaryEventClass.overflowWall BoundaryEventClass.guardRescue ->
    OutputSafetyInterventionObligation p :=
  fun hv hi _ => guard_clamp_declares_output_safety hv hi

theorem precision_escape_intervention_obligation
    (p : BoundaryInterventionPair) :
    ValidInterventionPair p ->
    PairUsesIntervention p BoundaryIntervention.precisionEscape ->
    PairHasRescueTransition p BoundaryEventClass.phantomAttractor BoundaryEventClass.interiorSample ->
    PrecisionEscapeInterventionObligation p :=
  fun hv hi _ => precision_escape_declares_precision_sensitivity hv hi

theorem saturation_deshelf_intervention_obligation
    (p : BoundaryInterventionPair) :
    ValidInterventionPair p ->
    PairUsesIntervention p BoundaryIntervention.saturationDeshelf ->
    PairHasRescueTransition p BoundaryEventClass.saturationShelf BoundaryEventClass.cornerConcentration ->
    ClampDeshelfInterventionObligation p :=
  fun hv hi _ => saturation_deshelf_declares_clamp_invariant hv hi

/-- The volume ratio `V(unit_ball_d) / V([-1,1]^d)` tends to zero. -/
theorem high_dim_ball_cube_ratio_tends_zero :
    TendstoTo ballCubeRatio 0 :=
  MachLib.Real.bcRatio_tendsto_zero

/-- For fixed `eps` in `(0,1)`, the cube boundary-shell probability tends to one. -/
theorem cube_boundary_shell_probability_tends_one
    (eps : Real) (heps : 0 < eps ∧ eps < 1) :
    TendstoTo (cubeBoundaryShellProbability eps) 1 := by
  exact cubeBoundaryShellProbability_tends_one eps heps

/-- Independent symmetric leaves make first-layer raw log-domain survival decay exponentially. -/
theorem eml_first_layer_log_domain_survival_decay
    (d : Nat) :
    firstLayerSurvival d = realPow (1 / natCast 2 : Real) (natCast (2 ^ (d - 1))) := by
  exact firstLayerSurvival_decay d

/-- Guarded lowering preserves declared positive-domain obligations through replay packets. -/
theorem guarded_lowering_preserves_domain_annotations
    (p : ReplayPacket) :
    ValidGuards p -> DomainPreserved p :=
  GuardedLowering.guarded_lowering_preserves_domain p

/-- Course 006 guarded simulator packets expose a nonnegative survival metric. -/
theorem guarded_boundary_packet_survival_nonnegative
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    GuardedBoundaryMode p ->
    0 <= packetFiniteSurvivalRate p := by
  intro hvalid hmode
  exact guarded_boundary_packet_finite_survival_nonneg p hvalid hmode

/-- Course 006 log-domain candidate packets expose a nonnegative survival metric. -/
theorem log_domain_boundary_packet_survival_nonnegative
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    LogDomainBoundaryMode p ->
    0 <= packetFiniteSurvivalRate p := by
  intro hvalid hmode
  exact log_domain_boundary_packet_finite_survival_nonneg p hvalid hmode

/-- Packet-level bridge from benchmark counts to the boundary-dominance predicate. -/
theorem boundary_dominance_packet_bridge
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    packetCenterHits p <= packetBoundaryHits p ->
    BoundaryDominatesCenter p := by
  intro hvalid hcounts
  exact boundary_dominates_center_from_packet p hvalid hcounts

theorem domain_wall_maps_to_domain_preservation
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.domainWall ->
    DomainPreservationObligation p := by
  intro hvalid hevent
  exact domain_wall_obligation p hvalid hevent

theorem overflow_wall_maps_to_bounded_evaluation
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.overflowWall ->
    BoundedEvaluationObligation p := by
  intro hvalid hevent
  exact overflow_wall_obligation p hvalid hevent

theorem saturation_shelf_maps_to_clamp_invariant
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.saturationShelf ->
    ClampInvariantObligation p := by
  intro hvalid hevent
  exact saturation_shelf_obligation p hvalid hevent

theorem phantom_attractor_maps_to_precision_sensitivity
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.phantomAttractor ->
    PrecisionSensitivityObligation p := by
  intro hvalid hevent
  exact phantom_attractor_obligation p hvalid hevent

theorem guard_rescue_maps_to_output_safety
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.guardRescue ->
    OutputSafetyObligation p := by
  intro hvalid hevent
  exact guard_rescue_obligation p hvalid hevent

theorem log_domain_rescue_maps_to_positive_coordinates
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.logDomainRescue ->
    PositiveCoordinateObligation p := by
  intro hvalid hevent
  exact log_domain_rescue_obligation p hvalid hevent

theorem valid_transition_graph_maps_to_boundary_dynamics
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    ValidTransitionGraph p ->
    BoundaryDynamicsObligation p := by
  intro hvalid hgraph
  exact transition_graph_obligation p hvalid hgraph

/-- Closed foothold: one observed transition gives a nonempty transition graph witness. -/
theorem transition_graph_nonempty_from_transition
    (p : BoundaryRunPacket)
    (fromEvent toEvent : BoundaryEventClass) :
    PacketHasTransition p fromEvent toEvent ->
    ∃ x : BoundaryEventClass, ∃ y : BoundaryEventClass, PacketHasTransition p x y := by
  intro htransition
  exact Exists.intro fromEvent (Exists.intro toEvent htransition)

theorem domain_to_log_domain_rescue_maps_to_positive_coordinates
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasTransition p BoundaryEventClass.domainWall BoundaryEventClass.logDomainRescue ->
    PositiveCoordinateObligation p := by
  intro hvalid htransition
  exact domain_to_log_domain_rescue_obligation p hvalid htransition

/-- A valid log-domain rescue packet carries both the positive-coordinate
obligation and a concrete nonempty transition-graph witness. -/
theorem log_domain_rescue_packet_carries_positive_coordinate_witness
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    LogDomainBoundaryMode p ->
    PacketHasTransition p BoundaryEventClass.domainWall BoundaryEventClass.logDomainRescue ->
    PositiveCoordinateObligation p ∧
      (∃ x : BoundaryEventClass, ∃ y : BoundaryEventClass, PacketHasTransition p x y) := by
  intro hvalid _hmode htransition
  exact And.intro
    (domain_to_log_domain_rescue_obligation p hvalid htransition)
    (transition_graph_nonempty_from_transition
      p
      BoundaryEventClass.domainWall
      BoundaryEventClass.logDomainRescue
      htransition)

/-- First discharged log-domain lane foothold: the concrete positive-coordinate
part of a Forge log-domain rescue sample follows directly from the witness
record, without invoking `PositiveCoordinateObligation` or a packet bridge
axiom. This is not yet the full semantic rewrite theorem; it is the local
sample-level obligation that the generated Forge fixture can expose. -/
theorem log_domain_positive_coordinate_witness_discharges_concrete_obligation
    (w : LogDomainPositiveCoordinateWitness) :
    ConcretePositiveCoordinateObligation w := by
  exact And.intro w.liftedPositive
    (And.intro w.rawIsDomainWall w.rescueIsLogDomain)

/-- First restricted semantic rewrite foothold: for the small log-domain
program class represented by `LogDomainPositiveCoordinateWitness`, the rescue
operator rewrites a raw domain-wall sample into a positive internal-coordinate
sample with a log-domain rescue event. This is deliberately narrower than a
full optimizer semantic rewrite theorem. -/
theorem log_domain_lift_restricted_semantic_rewrite
    (w : LogDomainPositiveCoordinateWitness) :
    RestrictedLogDomainLiftSemantics w := by
  exact And.intro w.rawIsDomainWall
    (And.intro w.liftedPositive w.rescueIsLogDomain)

/-- Second discharged rescue foothold: the concrete output-safety part of a
Forge guard-clamp rescue sample follows directly from the witness record,
without invoking `OutputSafetyObligation` or a packet bridge axiom. This is a
sample-level bound witness, not the final semantic rewrite theorem for all
guarded programs. -/
theorem guard_clamp_output_safety_witness_discharges_concrete_obligation
    (w : GuardClampOutputSafetyWitness) :
    ConcreteOutputSafetyObligation w := by
  exact And.intro w.guardWithinLimit
    (And.intro w.rawIsOverflowWall w.rescueIsGuardRescue)

/-- Third discharged rescue foothold: the concrete precision-escape part of a
Forge phantom-attractor sample follows directly from the witness record. This
is a local precision-sensitivity witness, not a convergence or optimizer
correctness theorem. -/
theorem precision_escape_witness_discharges_concrete_obligation
    (w : PrecisionEscapeWitness) :
    ConcretePrecisionEscapeObligation w := by
  exact And.intro w.lowPrecisionStalled
    (And.intro w.highPrecisionEscapes
      (And.intro w.rawIsPhantomAttractor w.rescueIsInteriorSample))

/-- Third discharged rescue foothold: the concrete clamp-invariant part of a
Forge saturation-deshelf sample follows directly from the witness record. This
does not claim that deshelf is rescue-normal or that every saturation rewrite is
semantically proved. -/
theorem saturation_deshelf_clamp_witness_discharges_concrete_obligation
    (w : SaturationDeshelfClampWitness) :
    ConcreteClampInvariantObligation w := by
  exact And.intro w.lowerLePressure
    (And.intro w.pressureLeUpper
      (And.intro w.rawIsSaturationShelf w.rescueIsCornerConcentration))

/-- The log-domain lane is at the restricted semantic rewrite tier and still
carries the concrete positive-coordinate sample invariant. -/
theorem log_domain_lift_has_restricted_semantic_rewrite :
    rescueSemanticTier BoundaryIntervention.logDomainLift =
      RescueSemanticTier.restrictedSemanticRewrite ∧
    RescueHasRestrictedSemanticRewrite BoundaryIntervention.logDomainLift ∧
    RescueHasConcreteSampleInvariant BoundaryIntervention.logDomainLift := by
  exact And.intro rfl
    (And.intro
      (fun w => log_domain_lift_restricted_semantic_rewrite w)
      (fun w => log_domain_positive_coordinate_witness_discharges_concrete_obligation w))

/-- The guard-clamp lane is at the v0 concrete-sample-invariant tier. -/
theorem guard_clamp_has_concrete_sample_invariant_semantics :
    rescueSemanticTier BoundaryIntervention.guardClamp =
      RescueSemanticTier.concreteSampleInvariant ∧
    RescueHasConcreteSampleInvariant BoundaryIntervention.guardClamp := by
  exact And.intro rfl
    (fun w => guard_clamp_output_safety_witness_discharges_concrete_obligation w)

/-- The precision-escape lane is now at the v0 concrete-sample-invariant tier. -/
theorem precision_escape_has_concrete_sample_invariant_semantics :
    rescueSemanticTier BoundaryIntervention.precisionEscape =
      RescueSemanticTier.concreteSampleInvariant ∧
    RescueHasConcreteSampleInvariant BoundaryIntervention.precisionEscape := by
  exact And.intro rfl
    (fun w => precision_escape_witness_discharges_concrete_obligation w)

/-- The saturation-deshelf lane is at the v0 concrete-sample-invariant tier. -/
theorem saturation_deshelf_has_concrete_sample_invariant_semantics :
    rescueSemanticTier BoundaryIntervention.saturationDeshelf =
      RescueSemanticTier.concreteSampleInvariant ∧
    RescueHasConcreteSampleInvariant BoundaryIntervention.saturationDeshelf := by
  exact And.intro rfl
    (fun w => saturation_deshelf_clamp_witness_discharges_concrete_obligation w)

theorem overflow_to_guard_rescue_maps_to_output_safety
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasTransition p BoundaryEventClass.overflowWall BoundaryEventClass.guardRescue ->
    OutputSafetyObligation p := by
  intro hvalid htransition
  exact overflow_to_guard_rescue_obligation p hvalid htransition

/-- A valid guarded rescue packet carries both the output-safety obligation and
a concrete nonempty transition-graph witness. -/
theorem guard_rescue_packet_carries_output_safety_witness
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    GuardedBoundaryMode p ->
    PacketHasTransition p BoundaryEventClass.overflowWall BoundaryEventClass.guardRescue ->
    OutputSafetyObligation p ∧
      (∃ x : BoundaryEventClass, ∃ y : BoundaryEventClass, PacketHasTransition p x y) := by
  intro hvalid _hmode htransition
  exact And.intro
    (overflow_to_guard_rescue_obligation p hvalid htransition)
    (transition_graph_nonempty_from_transition
      p
      BoundaryEventClass.overflowWall
      BoundaryEventClass.guardRescue
      htransition)

/-- A phantom-attractor escape packet carries the precision-sensitivity
obligation and a concrete nonempty transition-graph witness. The event witness
is explicit because transitions are currently packet evidence, not a semantic
constructor for events. -/
theorem precision_escape_packet_carries_precision_witness
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.phantomAttractor ->
    PacketHasTransition p BoundaryEventClass.phantomAttractor BoundaryEventClass.interiorSample ->
    PrecisionSensitivityObligation p ∧
      (∃ x : BoundaryEventClass, ∃ y : BoundaryEventClass, PacketHasTransition p x y) := by
  intro hvalid hevent htransition
  exact And.intro
    (phantom_attractor_obligation p hvalid hevent)
    (transition_graph_nonempty_from_transition
      p
      BoundaryEventClass.phantomAttractor
      BoundaryEventClass.interiorSample
      htransition)

/-- A saturation-deshelf packet carries the clamp-invariant obligation and a
concrete nonempty transition-graph witness. As with phantom attractors, the
event witness is explicit because transition evidence does not yet construct
event membership. -/
theorem saturation_deshelf_packet_carries_clamp_witness
    (p : BoundaryRunPacket) :
    ValidBoundaryRunPacket p ->
    PacketHasEvent p BoundaryEventClass.saturationShelf ->
    PacketHasTransition p BoundaryEventClass.saturationShelf BoundaryEventClass.cornerConcentration ->
    ClampInvariantObligation p ∧
      (∃ x : BoundaryEventClass, ∃ y : BoundaryEventClass, PacketHasTransition p x y) := by
  intro hvalid hevent htransition
  exact And.intro
    (saturation_shelf_obligation p hvalid hevent)
    (transition_graph_nonempty_from_transition
      p
      BoundaryEventClass.saturationShelf
      BoundaryEventClass.cornerConcentration
      htransition)

/-- Suite-level structural hook for the v0 proof-carrying rescue manifest:
if all four lane packets carry their witnesses, then the suite exposes all four
obligation witnesses. -/
theorem proof_carrying_rescue_suite_v0_carries_all_obligations
    (logPacket guardPacket precisionPacket saturationPacket : BoundaryRunPacket) :
    ValidBoundaryRunPacket logPacket ->
    LogDomainBoundaryMode logPacket ->
    PacketHasTransition logPacket BoundaryEventClass.domainWall BoundaryEventClass.logDomainRescue ->
    ValidBoundaryRunPacket guardPacket ->
    GuardedBoundaryMode guardPacket ->
    PacketHasTransition guardPacket BoundaryEventClass.overflowWall BoundaryEventClass.guardRescue ->
    ValidBoundaryRunPacket precisionPacket ->
    PacketHasEvent precisionPacket BoundaryEventClass.phantomAttractor ->
    PacketHasTransition precisionPacket BoundaryEventClass.phantomAttractor BoundaryEventClass.interiorSample ->
    ValidBoundaryRunPacket saturationPacket ->
    PacketHasEvent saturationPacket BoundaryEventClass.saturationShelf ->
    PacketHasTransition saturationPacket BoundaryEventClass.saturationShelf BoundaryEventClass.cornerConcentration ->
    PositiveCoordinateObligation logPacket ∧
      OutputSafetyObligation guardPacket ∧
      PrecisionSensitivityObligation precisionPacket ∧
      ClampInvariantObligation saturationPacket := by
  intro hlogValid hlogMode hlogTransition
  intro hguardValid hguardMode hguardTransition
  intro hprecisionValid hprecisionEvent hprecisionTransition
  intro hsatValid hsatEvent hsatTransition
  exact And.intro
    (And.left
      (log_domain_rescue_packet_carries_positive_coordinate_witness
        logPacket hlogValid hlogMode hlogTransition))
    (And.intro
      (And.left
        (guard_rescue_packet_carries_output_safety_witness
          guardPacket hguardValid hguardMode hguardTransition))
      (And.intro
        (And.left
          (precision_escape_packet_carries_precision_witness
            precisionPacket hprecisionValid hprecisionEvent hprecisionTransition))
        (And.left
          (saturation_deshelf_packet_carries_clamp_witness
            saturationPacket hsatValid hsatEvent hsatTransition))))

theorem log_domain_lift_pair_maps_to_positive_coordinates
    (p : BoundaryInterventionPair) :
    ValidInterventionPair p ->
    PairUsesIntervention p BoundaryIntervention.logDomainLift ->
    PairHasRescueTransition p BoundaryEventClass.domainWall BoundaryEventClass.logDomainRescue ->
    PositiveCoordinateInterventionObligation p := by
  intro hvalid huses htransition
  exact log_domain_lift_intervention_obligation p hvalid huses htransition

theorem guard_clamp_pair_maps_to_output_safety
    (p : BoundaryInterventionPair) :
    ValidInterventionPair p ->
    PairUsesIntervention p BoundaryIntervention.guardClamp ->
    PairHasRescueTransition p BoundaryEventClass.overflowWall BoundaryEventClass.guardRescue ->
    OutputSafetyInterventionObligation p := by
  intro hvalid huses htransition
  exact guard_clamp_intervention_obligation p hvalid huses htransition

theorem precision_escape_pair_maps_to_precision_obligation
    (p : BoundaryInterventionPair) :
    ValidInterventionPair p ->
    PairUsesIntervention p BoundaryIntervention.precisionEscape ->
    PairHasRescueTransition p BoundaryEventClass.phantomAttractor BoundaryEventClass.interiorSample ->
    PrecisionEscapeInterventionObligation p := by
  intro hvalid huses htransition
  exact precision_escape_intervention_obligation p hvalid huses htransition

theorem saturation_deshelf_pair_maps_to_clamp_obligation
    (p : BoundaryInterventionPair) :
    ValidInterventionPair p ->
    PairUsesIntervention p BoundaryIntervention.saturationDeshelf ->
    PairHasRescueTransition p BoundaryEventClass.saturationShelf BoundaryEventClass.cornerConcentration ->
    ClampDeshelfInterventionObligation p := by
  intro hvalid huses htransition
  exact saturation_deshelf_intervention_obligation p hvalid huses htransition

end HighDimensional
end MachLib
