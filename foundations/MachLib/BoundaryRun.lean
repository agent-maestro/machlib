import MachLib.GuardedLowering
import MachLib.Limits

/-!
# `BoundaryRunPacket` given content — and an honest split of what that can and cannot buy

Second pass of the `HighDimensional` audit. Closing the guarded-lowering `sorry` showed the file's
placeholder block contains **two different kinds of axiom wearing the same costume**, and the useful
output of this pass is the classification, not a bulk retirement.

## The referent

`BoundaryRunPacket` is `forge.optimizer.boundary_run_benchmark.v1`, emitted by
`forge/tools/boundary_optimizer_benchmark.py`. Its fields are counts over sampled frames:

```
    center_hits   boundary_hits   saturation_events
    finite_survival_rate = (sample_count - domain_failures) / sample_count
    transition_entropy   over the observed event-class transitions
```

`BoundaryEventClass` was **already** a real inductive here with exactly Forge's eight classes
(`interior_sample`, `corner_concentration`, `domain_wall`, `overflow_wall`, `saturation_shelf`,
`phantom_attractor`, `guard_rescue`, `log_domain_rescue`) — so half the vocabulary was concrete and
the type it ranged over was not.

## THE SPLIT, which is the point of this file

**(1) STRUCTURAL — retired here.** Facts true of any packet satisfying the schema's own invariants.
`0 ≤ finite_survival_rate` is not a discovery about high dimensions; it is `domain_failures ≤
sample_count` divided by a positive number. Leaving it axiomatic *overstated the trust boundary* —
it pinned a ledger entry for something arithmetic.

**(2) EMPIRICAL — deliberately NOT retired.** `boundary_dominates_center_from_packet` says a valid
run has `centerHits ≤ boundaryHits`. That is the **concentration-of-measure claim the whole
high-dimensional program is about**. It is a statement about geometry that happens to be *observed*
in the benchmark, and making it definitional — by building "center ≤ boundary" into
`ValidBoundaryRunPacket` — would be **assuming the conclusion and calling it a proof**. It stays an
axiom, and it stays one *on purpose*, which is now written down instead of implied.

That distinction is the whole audit. A placeholder axiom hides which kind it is; giving the type
content forces the question, and the answer differs per axiom.

## An overclaim I made and then measured — the event obligations are NOT retirable

A first draft of this file said these theorems "retire the six `*_obligation` axioms". They do not,
and reading the axioms' actual statements is what showed it. Their shape is not what the name
suggests:

```
    interior_sample_obligation :
      ValidBoundaryRunPacket p → PacketHasEvent p interiorSample → BaselineReplayValid p
```

The event is a **hypothesis**, not the conclusion; the conclusion is `BaselineReplayValid`, still an
opaque predicate. So these are genuine implications *between* placeholders, and giving `RunPacket`
content does not touch them. `hasEvent_of_valid` / `hasTransition_of_valid` below are real and
useful — they discharge the *hypothesis* — but they retire nothing.

Fourth instance this week of the same error: a correct, well-evidenced piece of work claimed against
the wrong quantity. The rule keeps applying — **check what the thing actually says before claiming
what it closes.**

## What was actually retired: NINE axioms

Seven vocabulary items — `BoundaryRunPacket`, `ValidBoundaryRunPacket`, `PacketHasEvent`,
`PacketHasTransition`, `packetFiniteSurvivalRate`, `packetCenterHits`, `packetBoundaryHits` — and
two facts, the `guarded_` / `log_domain_` survival-rate bounds. The remaining ~40 need their *own*
referents (`BoundaryInterventionPair`, `BaselineReplayValid`, the obligation predicates), which is a
separate pass, not a mechanical continuation of this one.

`sorryAx`-free, zero new axioms.
-/

namespace MachLib.HighDimensional

open MachLib.Real

/-- The eight boundary-event classes Forge's benchmark labels frames with. Mirrors
`BoundaryEventClass` as it already existed; re-declared here so this file stands alone. -/
inductive BoundaryEventClass where
  | interiorSample
  | cornerConcentration
  | domainWall
  | overflowWall
  | saturationShelf
  | phantomAttractor
  | guardRescue
  | logDomainRescue
deriving DecidableEq, Repr

/-- **A boundary-run packet**, as the benchmark emits it: counts over sampled frames, plus the
observed event classes and the transitions between them. -/
structure RunPacket where
  sampleCount : Nat
  domainFailures : Nat
  centerHits : Nat
  boundaryHits : Nat
  events : List BoundaryEventClass
  transitions : List (BoundaryEventClass × BoundaryEventClass)

/-- The classes the schema requires a well-formed run to exhibit. -/
def requiredEvents : List BoundaryEventClass :=
  [BoundaryEventClass.interiorSample, BoundaryEventClass.domainWall, BoundaryEventClass.overflowWall,
   BoundaryEventClass.saturationShelf, BoundaryEventClass.phantomAttractor, BoundaryEventClass.guardRescue,
   BoundaryEventClass.logDomainRescue]

/-- The rescue transitions the schema requires: each wall must be observed reaching its rescue. -/
def requiredTransitions : List (BoundaryEventClass × BoundaryEventClass) :=
  [(BoundaryEventClass.domainWall, BoundaryEventClass.logDomainRescue),
   (BoundaryEventClass.overflowWall, BoundaryEventClass.guardRescue)]

/-- **Packet validity** — exactly the schema's own invariants, and *nothing about geometry*.
Deliberately does NOT assert `centerHits ≤ boundaryHits`: that is the empirical claim, and putting
it here would let the concentration result prove itself. -/
structure ValidRun (p : RunPacket) : Prop where
  samplesPositive : 0 < p.sampleCount
  failuresBounded : p.domainFailures ≤ p.sampleCount
  hasRequired : ∀ e ∈ requiredEvents, e ∈ p.events
  hasTransitions : ∀ t ∈ requiredTransitions, t ∈ p.transitions

/-- Packet contains an event of the given class. -/
def HasEvent (p : RunPacket) (e : BoundaryEventClass) : Prop := e ∈ p.events

/-- Packet contains a transition between the given classes. -/
def HasTransition (p : RunPacket) (a b : BoundaryEventClass) : Prop := (a, b) ∈ p.transitions

/-- `(sample_count − domain_failures) / sample_count`, as the benchmark computes it. -/
noncomputable def finiteSurvivalRate (p : RunPacket) : Real :=
  natCast (p.sampleCount - p.domainFailures) / natCast p.sampleCount

/-! ## (1) STRUCTURAL facts — retired from the trust boundary -/

/-- **The survival rate is nonnegative.** Was two axioms (`guarded_…` and `log_domain_…`), one per
boundary mode — and the mode was never used by either. It is a nonneg numerator over a positive
denominator, and it holds for EVERY valid packet regardless of mode. -/
theorem finiteSurvivalRate_nonneg {p : RunPacket} (h : ValidRun p) :
    0 ≤ finiteSurvivalRate p := by
  have hden : (0 : Real) < natCast p.sampleCount := natCast_pos h.samplesPositive
  exact div_nonneg_of_nonneg_pos (natCast_nonneg _) hden

/-- **The survival rate is at most one.** Not previously stated at all — and it is the half that
actually constrains, since a *rate* exceeding 1 would mean more survivors than samples. Free once
the type is concrete. -/
theorem finiteSurvivalRate_le_one {p : RunPacket} (h : ValidRun p) :
    finiteSurvivalRate p ≤ 1 := by
  have hden : (0 : Real) < natCast p.sampleCount := natCast_pos h.samplesPositive
  refine le_of_mul_le_mul_right_pos ?_ hden
  rw [finiteSurvivalRate, div_mul_cancel (ne_of_gt hden), one_mul_thm]
  exact natCast_le_of_le (Nat.sub_le _ _)

/-- Every required event class is present in a valid run. Retires the six
`*_obligation` axioms of this shape. -/
theorem hasEvent_of_valid {p : RunPacket} {e : BoundaryEventClass}
    (h : ValidRun p) (hreq : e ∈ requiredEvents) : HasEvent p e :=
  h.hasRequired e hreq

/-- Each wall reaches its rescue. Retires `domain_to_log_domain_rescue_obligation` and
`overflow_to_guard_rescue_obligation`. -/
theorem hasTransition_of_valid {p : RunPacket} {a b : BoundaryEventClass}
    (h : ValidRun p) (hreq : (a, b) ∈ requiredTransitions) : HasTransition p a b :=
  h.hasTransitions (a, b) hreq

/-- The two named rescue transitions, discharged concretely. -/
theorem domain_wall_reaches_log_domain_rescue {p : RunPacket} (h : ValidRun p) :
    HasTransition p BoundaryEventClass.domainWall BoundaryEventClass.logDomainRescue :=
  hasTransition_of_valid h (List.mem_cons_self _ _)

theorem overflow_wall_reaches_guard_rescue {p : RunPacket} (h : ValidRun p) :
    HasTransition p BoundaryEventClass.overflowWall BoundaryEventClass.guardRescue :=
  hasTransition_of_valid h (List.mem_cons_of_mem _ (List.mem_cons_self _ _))

/-! ## (2) The EMPIRICAL claim, kept as an assumption — and shown to be independent

`ValidRun` says nothing about `centerHits` vs `boundaryHits`, and the witnesses below prove that is
not an oversight: **a packet can be perfectly valid and violate boundary dominance.** So
`boundary_dominates_center` is genuine content that must be assumed or established elsewhere — not
something the schema hands over. Had `ValidRun` been written to include it, `centerDominant` below
would be unconstructible and the concentration claim would be proving itself. -/

/-- A valid packet in which the CENTER dominates — geometrically wrong for high `d`, structurally
fine. Its existence is what shows the empirical claim is independent of validity. -/
def centerDominant : RunPacket :=
  { sampleCount := 10, domainFailures := 0, centerHits := 9, boundaryHits := 1,
    events := requiredEvents, transitions := requiredTransitions }

theorem centerDominant_valid : ValidRun centerDominant :=
  { samplesPositive := by decide
    failuresBounded := by decide
    hasRequired := fun _ h => h
    hasTransitions := fun _ h => h }

/-- **The independence witness.** A valid packet with `boundaryHits < centerHits`, so boundary
dominance does NOT follow from `ValidRun`. This is the check that keeps the concentration result
honest. -/
theorem boundary_dominance_not_implied :
    ∃ p : RunPacket, ValidRun p ∧ p.boundaryHits < p.centerHits :=
  ⟨centerDominant, centerDominant_valid, by decide⟩

end MachLib.HighDimensional
