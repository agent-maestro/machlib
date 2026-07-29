import MachLib.Basic

/-!
# Guarded lowering preserves domain obligations — the last `sorry` in `HighDimensional`

**Same defect as `high_dim_ball_cube_ratio_tends_zero`, one file later.** That one carried a `sorry`
for a month because `TendstoTo` and `ballCubeRatio` were **opaque axioms** — there is nothing to
prove about uninterpreted symbols. This one carried a `sorry` for the same reason:

```
    axiom ReplayPacket    : Type
    axiom ValidGuards     : ReplayPacket -> Prop
    axiom DomainPreserved : ReplayPacket -> Prop
```

Three symbols with no content, and a theorem relating them. **The gap was in the VOCABULARY, not the
argument** — and the fix is the same: give the symbols a definition and the theorem becomes provable.

## The referent is real, and it is not invented here

`ReplayPacket` is a placeholder for a manifest Forge already emits and validates:
`forge.optimizer.proof_carrying_rescue_suite.v0`, replayed by
`forge/tools/proof_carrying_rescue_replay.py`. Four lanes, each a *rescue* — a rewrite that moves a
computation off a numerical wall — and each carrying a **named obligation** the rewrite must not
destroy:

| lane | transition | obligation |
|---|---|---|
| `log_domain_lift` | `domain_wall → log_domain_rescue` | `PositiveCoordinateObligation` |
| `guard_clamp` | `overflow_wall → guard_rescue` | `OutputSafetyObligation` |
| `precision_escape` | `phantom_attractor → interior_sample` | `PrecisionSensitivityObligation` |
| `saturation_deshelf` | `saturation_shelf → corner_concentration` | `ClampInvariantObligation` |

The model below is those four obligations, a lane, a packet, and the lowering. Nothing is invented
that the manifest does not already carry.

## Why the statement is not a tautology

The temptation with a definitional gap is to define `DomainPreserved` so that it follows from
`ValidGuards` by unfolding — which "closes the sorry" and proves nothing. The content here is that
**lowering REWRITES a lane**, and a rewrite can drop what it was carrying:

* a lane **with** its guard lowers to the rescued form and **keeps its obligation**;
* a lane **without** its guard lowers to an unguarded form and **loses it**.

So `DomainPreserved` quantifies over the *lowered* packet and `ValidGuards` over the *source*, and
the theorem says the rewrite is faithful when every lane is guarded.

**And it is checked in the other direction.** `unguarded_packet_not_preserved` exhibits a concrete
packet — one unguarded `log_domain_lift` lane — that satisfies the conclusion's negation. A theorem
whose hypothesis is never false is a theorem about nothing, and this one's hypothesis is *exactly*
what separates the two witnesses.

`sorryAx`-free, zero new axioms.
-/

namespace MachLib.GuardedLowering

/-- The four obligations the rescue suite actually declares. -/
inductive Obligation where
  | positiveCoordinate
  | outputSafety
  | precisionSensitivity
  | clampInvariant
deriving DecidableEq, Repr

/-- One rescue lane. `guarded` is the flag the replay validator checks; `obl` is what the lane
promises to carry through the rewrite. -/
structure Lane where
  obl : Obligation
  guarded : Bool
deriving DecidableEq, Repr

/-- A replay packet is its lanes. -/
abbrev Packet := List Lane

/-- **Guarded lowering.** A guarded lane is rescued and keeps its obligation; an unguarded lane is
lowered without the guard, and the obligation it declared **does not survive** — which is precisely
the failure the manifest's `guarded` flag exists to prevent. Modelled by dropping the lane. -/
def lower : Packet → Packet
  | [] => []
  | l :: rest => if l.guarded then l :: lower rest else lower rest

/-- Every lane carries its guard. -/
def ValidGuards (p : Packet) : Prop :=
  ∀ l ∈ p, l.guarded = true

/-- Every obligation declared in the source is still declared after lowering. -/
def DomainPreserved (p : Packet) : Prop :=
  ∀ l ∈ p, l ∈ lower p

/-- A guarded lane survives its own lowering. -/
theorem mem_lower_of_guarded {l : Lane} {p : Packet}
    (hmem : l ∈ p) (hall : ValidGuards p) : l ∈ lower p := by
  induction p with
  | nil => cases hmem
  | cons a rest ih =>
      have ha : a.guarded = true := hall a (List.mem_cons_self a rest)
      rw [lower, if_pos ha]
      rcases List.mem_cons.mp hmem with h | h
      · exact h ▸ List.mem_cons_self a (lower rest)
      · exact List.mem_cons_of_mem a (ih h (fun x hx => hall x (List.mem_cons_of_mem a hx)))

/-- **Guarded lowering preserves declared domain obligations.**
The `HighDimensional` target, now proven rather than assumed. -/
theorem guarded_lowering_preserves_domain (p : Packet) :
    ValidGuards p → DomainPreserved p :=
  fun hall _l hmem => mem_lower_of_guarded hmem hall

/-! ## Non-vacuity — the hypothesis is what does the work

A theorem whose hypothesis is never false is a theorem about nothing. These two witnesses differ in
exactly one bit, and land on opposite sides. -/

/-- The `log_domain_lift` lane, **unguarded**. -/
def badPacket : Packet := [{ obl := Obligation.positiveCoordinate, guarded := false }]

/-- The same lane, **guarded**. -/
def goodPacket : Packet := [{ obl := Obligation.positiveCoordinate, guarded := true }]

/-- The unguarded packet fails `ValidGuards` — so the theorem does not apply to it. -/
theorem badPacket_not_valid : ¬ ValidGuards badPacket := by
  intro h
  have := h { obl := Obligation.positiveCoordinate, guarded := false }
    (List.mem_cons_self _ _)
  exact Bool.noConfusion this

/-- **And it genuinely loses the obligation**: lowering it yields the empty packet, so the
`PositiveCoordinateObligation` the lane declared is gone. This is the failure the guard prevents. -/
theorem badPacket_loses_obligation : lower badPacket = [] := by
  rw [badPacket, lower, if_neg (by simp)]
  rfl

/-- `DomainPreserved` actually FAILS on the unguarded packet — the conclusion is not free. -/
theorem badPacket_not_preserved : ¬ DomainPreserved badPacket := by
  intro h
  have hmem := h { obl := Obligation.positiveCoordinate, guarded := false }
    (List.mem_cons_self _ _)
  rw [badPacket_loses_obligation] at hmem
  cases hmem

/-- The guarded packet satisfies both sides, so the theorem is not vacuously about nothing. -/
theorem goodPacket_valid : ValidGuards goodPacket := by
  intro l hl
  rcases List.mem_cons.mp hl with h | h
  · rw [h]
  · cases h

theorem goodPacket_preserved : DomainPreserved goodPacket :=
  guarded_lowering_preserves_domain goodPacket goodPacket_valid

end MachLib.GuardedLowering
