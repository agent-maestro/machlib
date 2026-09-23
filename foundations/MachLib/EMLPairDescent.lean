import MachLib.EMLProductMerge

/-!
# A relation on PAIRS — the eighth failed mechanism, and it dies on the same wall from a new side

`EmlGermApproachResearch.md` §4 lists seven dead mechanisms and, after (7), leaves **a relation on
pairs `(A, C)`** at the head of what is untouched. The reason it looked alive is real: every
mechanism so far measures **one tree**, while the conjecture is about a **pair** — `C < exp ∘ A` on a
ray, and the gap `exp (A x) − C x`. Mechanism (4) quantifies over `μ : EMLTree → W` descending to
**both** children of a single tree; mechanism (7) over carriers the right-hand germ class embeds
into. A well-founded relation on pairs that the peel step decreases is neither.

The peel sends `(A, C)` to `(A₁, A₂·C)` — `peel_merge_tree` / `peel_step_tree`, with the merge of
(7) proved and usable. So the relation is not hypothetical, and this file builds it.

## What was built, in the order the discipline requires

1. **`≺` defined precisely** (§1). `PeelRel` is the one-step peel on pairs — the relation the route
   names, with no measure interposed — and `PairDescent` is the class: **any** measure on pairs
   into **any** well-founded order that the peel step decreases.
2. **Well-foundedness settled before anything else** (§2). **VERDICT: WELL-FOUNDED**, proved
   (`peelRel_wf`), and the class is inhabited (`pairDescent_inhabited`). Both verdicts are
   available on the instrument: §5 refutes a floor read off the same measure.
3. **Mechanism (4) does NOT transport** (§2b), and this was checked first because it is one lemma
   either way. The exact configuration (4) refutes — a measure pricing `recipTree` at or below its
   own argument — is **realised** here by a live `PairDescent`
   (`cheap_recip_survives_in_pairs`), because the peel step never asks for descent to a right
   child and `lspTree` provably does not have it (`lspTree_not_right_descending`). So the pair
   class is genuinely outside (4) rather than (4) in new clothes.
4. **The minimal elements, computed before any floor was attempted** (§3).
5. **The six §3 fixtures, measured** (§4).
6. **Only then, the floor** (§5). It is the conjecture.

## The minimal elements, which is the question the route turns on

```
pairMinimal_iff :  PairMinimal (A, C)  ↔  A.lspTree = 0
```

Both directions. An `eml` left germ always has a peel below it, so it is never minimal; a leaf left
germ has nothing below it, because the peel step's only constructor needs an `eml`. And at class
width the first half survives for **every** `PairDescent` (`pairDescent_eml_not_minimal`): the
minimal set of any pair relation the peel decreases is contained in `{A.lspTree = 0}`.

**That set is `EMLPeelRecursion`'s T2 cell, verbatim.** So the pair route's minimal elements are
the cell §4(6) already proved is the whole obligation — the second of the three deaths the route
was expected to die, *"the minimal elements are the same two cells wearing different clothes"*.

The other cell is here too, as the peel step's own side condition: `peel_step` needs `0 < c`, so a
run also stops where the accumulated right-hand germ goes non-positive, and that is T1 —
`peelTerminalNoCancel_iff_growthEnvelope`. Two exits, both already priced.

## And the cell cannot be shrunk by choosing a different `≺`

The obvious repair is to add edges below `(const 0, C)` so that it stops being minimal. That is
closed, at the width of every base-case set:

```
base_must_contain_constZero :  a sound peel-driven pair recursion whose base cases are
                               ≺-minimal contains `(const 0, C)` for every `C`
```

The proof is the run itself: instantiate the induction at `P A C := S (leftLeaf A) (peelAccum A C)`,
whose step case is `rfl` because that is exactly what a peel does, and read the conclusion at
`A := const 0`. **Both verdicts on the instrument**: the same theorem refutes the `var`-only base
case (`var_only_base_is_unsound`), so it is not vacuous, and the full leaf base case is sound
(`pair_peel_induction`) — the pair recursion is a valid induction principle, machine-checked.

## The fixture table — and the row that decides it

| §3 fixture | steps as left germ | terminal left germ | as the conjecture's target | verdict |
|---|---|---|---|---|
| `recipTree t` | 2 | `const 0` | — | terminal cell is T2 verbatim |
| `posEmbed t` | 1 | `const 0` | — | same |
| `capNode n` | 1 | `const 0` | — | same |
| `deepDecay m` | 2 for every `m` | `const 0` | pair measure **0**, floor height `m+1` | **BLIND** |
| `gapTarget n c` | `n + 1` | `var` | — | over-works; the one fixture not landing on `const 0` |
| `eTree (eTree A)` | — | — | — | **never enters** — the strict hypothesis fails |

The decisive row is `deepDecay`, and at pair width it is sharper than it was for `lspTree`.
`EMLPeelRecursion` records the peel count as *anti-correlated* with the floor height —
**constant** on the extremal family. On pairs it is **zero** on that family, and not by accident:
`decayFloor_of_emlGermApproach` routes every instance of `DecayFloor` through the pair
`(const 0, approachTarget t)`, whose left germ is a leaf. So

> **the entire obligation the conjecture reduces to consists of `≺`-minimal pairs**
> (`decayFloor_reduction_is_minimal`). The recursion never runs on them at all.

`pairCount_cannot_carry_floor` turns that into `False`: no function of the pair measure assigns a
floor height, because `deepDecay m` forces `m + 1 ≤ f 0` for every `m`.

## Where it dies

```
PairTerminalCell ↔ EmlGermApproach        (pairTerminalCell_iff_emlGermApproach)
```

Forward costs nothing — `(const 0).lspTree = 0`, so the cell contains `PeelTerminalConstZero`
verbatim; the converse is the trivial instantiation. Per `EmlGermApproachResearch.md` §9 an
equivalence with a converse is not progress.

## What this rules out, as a bound on a class

**Out.** Every well-founded relation on pairs `(A, C)` that the peel step decreases, whatever its
carrier and order type. Its minimal elements are contained in `{A.lspTree = 0}`; that cell is the
obligation; and no sound choice of base case can omit the `(const 0, C)` instances, because the peel
itself carries every pair to one. The pair reading does **not** escape (6) — it *is* (6), with the
accumulator named and the measure read off the first coordinate.

**And the second coordinate cannot rescue it.** `no_accumulator_descent`: no measure of the
accumulator alone descends along the merge in any well-founded order, because the merge iterates —
`C, A₂·C, A₂·(A₂·C), …` would be an infinite descending chain. So a pair measure's descent must come
from the left germ's syntax, which is `lspTree`'s territory.

**In, still.** What §4's width paragraph listed and this does not touch: a recursion whose terminal
cell is neither of (6)'s two — the open question is whether one exists, and the answer is now
constrained from a third side; and non-structural arguments. Dropping the syntax is closed at pair
width too (`no_germInvariant_pair_bound`): no function of the **germ pair** bounds the peel count,
by `selfLeftNode` exactly as in (7).

## Scope

**Bounds nothing, discharges nothing, assumes nothing.** No axiom; the `DecayFloor` ⇄
`EmlGermApproach` ⇄ `GrowthEnvelope` row stays open, one obligation. This is a route-closure and a
fixture set in the sense `EmlGermApproachResearch.md` §3 uses the word.
-/

namespace MachLib

open Real

/-! ## §1 — the relation, stated before anything is proved

The route's step is fixed by `EMLProductMerge`: `peel_merge_tree` rewrites the gap at `eml A₁ A₂`
against right-hand germ `R` as the gap at `A₁` against `mergeTree A₂ R`. So the relation on pairs
is that step and nothing else — no measure is interposed, because interposing one is what every
earlier mechanism did. -/

/-- **The one-step peel, as a relation on pairs.** `PeelRel p q` reads *"`p` is one peel below
`q`"*. The only constructor needs an `eml` left germ, which is what makes §3's minimality
computation two lines. -/
inductive PeelRel : EMLTree × EMLTree → EMLTree × EMLTree → Prop where
  | step (A₁ A₂ C : EMLTree) :
      PeelRel (A₁, mergeTree A₂ C) (EMLTree.eml A₁ A₂, C)

/-- The obvious measure on pairs: the peel count of the left germ. It reads **nothing** about the
second coordinate, which §5 shows is not a defect of this choice but the shape of the route. -/
def PairMeasure (p : EMLTree × EMLTree) : Nat := p.1.lspTree

/-- **The class**, at the width mechanism (4) is stated at: any measure on **pairs**, into any
type, under any well-founded order, that the peel step decreases. `WfDescent` demands descent to
both children of one tree; this demands descent along one step of the pair recursion. -/
structure PairDescent where
  /-- The order the measure lands in. -/
  W : Type
  /-- The measure, on pairs. -/
  μ : EMLTree × EMLTree → W
  /-- The strict order. -/
  R : W → W → Prop
  /-- …which is well-founded, so it supports an induction. -/
  wf : WellFounded R
  /-- The peel step strictly decreases it. -/
  peel_lt : ∀ A₁ A₂ C : EMLTree, R (μ (A₁, mergeTree A₂ C)) (μ (EMLTree.eml A₁ A₂, C))

/-! ## §2 — well-foundedness, settled before anything else

`EmlGermApproachResearch.md` §5 requires this first, and for candidate 3 it was the step that
failed (`compLt_not_wf`). Here it holds, and cheaply. -/

/-- The peel strictly lowers the peel count of the left germ — the whole content of the
well-foundedness proof. -/
theorem peelRel_measure_lt {p q : EMLTree × EMLTree} (h : PeelRel p q) :
    PairMeasure p < PairMeasure q := by
  cases h with
  | step A₁ A₂ C => exact EMLTree.lspTree_left_lt A₁ A₂

/-- **VERDICT: the pair relation is WELL-FOUNDED.** It is a subrelation of the inverse image of
`<` under `PairMeasure`, and nothing about the accumulator is used — the merge may inflate the
right-hand germ by `115` levels a step (`mergeTree_depth_le`) without touching this. -/
theorem peelRel_wf : WellFounded PeelRel :=
  Subrelation.wf peelRel_measure_lt (InvImage.wf PairMeasure Nat.lt_wfRel.wf)

/-- The measure as a member of the class. -/
def lspPairDescent : PairDescent where
  W := Nat
  μ := PairMeasure
  R := (· < ·)
  wf := Nat.lt_wfRel.wf
  peel_lt := fun A₁ _ _ => EMLTree.lspTree_left_lt A₁ _

/-- **The class is inhabited**, so what follows is not about an empty extension — the same
discipline `wfDescent_inhabited` follows for mechanism (4). -/
theorem pairDescent_inhabited : Nonempty PairDescent := ⟨lspPairDescent⟩

/-! ### §2b — mechanism (4) does not transport, and this was checked first

The cheapest way for this route to die would have been for the pair relation to project to a tree
measure, with `no_wf_descent_of_cheap_recip` transporting verbatim. It does not, and the reason is
structural: `WfDescent` demands descent to the **right** child, and the peel step never asks for
it. -/

/-- **The pair measure's tree half is not a `WfDescent` measure.** `capNode 1`'s right child is the
`2`-tower, priced at `2`, while the node itself is priced at `1` — `lspTree_right_unbounded`, read
as a refutation. -/
theorem lspTree_not_right_descending :
    ¬ ∀ A B : EMLTree, B.lspTree < (EMLTree.eml A B).lspTree := by
  intro h
  have hb := h (EMLTree.const (0 : Real)) (EMLTree.towerTree 2)
  have h1 : (EMLTree.towerTree 2).lspTree = 2 := lsp_towerTree 2
  have h2 : (EMLTree.eml (EMLTree.const (0 : Real)) (EMLTree.towerTree 2)).lspTree = 1 := rfl
  omega

/-- **The configuration mechanism (4) refutes is REALISED here.** `no_wf_descent_of_cheap_recip`
concludes `False` from a both-children descent that prices `recipTree t` at or below `t`; the pair
measure prices it at `2` for every `t`, so on any left germ with two or more peels the reciprocal
is cheap — and no contradiction follows, because there is no right-child obligation to violate. -/
theorem cheap_recip_survives_in_pairs (t C : EMLTree) (h : 2 ≤ t.lspTree) :
    PairMeasure (recipTree t, C) ≤ PairMeasure (t, C) := by
  show (recipTree t).lspTree ≤ t.lspTree
  rw [lsp_recipTree t]
  exact h

/-- **So the pair class is not mechanism (4).** Three facts: the cheap reciprocal is realised, the
class is inhabited, and the right-child descent that would make (4) apply is refuted. Had any one
of them failed the other way, mechanism (8) would have been (4) transported and this file would be
one lemma long. -/
theorem mechanism_four_does_not_transport :
    (∀ t C : EMLTree, 2 ≤ t.lspTree → PairMeasure (recipTree t, C) ≤ PairMeasure (t, C)) ∧
    Nonempty PairDescent ∧
    ¬ (∀ A B : EMLTree, B.lspTree < (EMLTree.eml A B).lspTree) :=
  ⟨cheap_recip_survives_in_pairs, pairDescent_inhabited, lspTree_not_right_descending⟩

/-! ## §3 — the minimal elements, computed before any floor is attempted

`EmlGermApproachResearch.md`'s brief for this route is explicit: *a route survives only if its
minimal elements avoid both identified cells, so work out what the minimal elements ARE before
trying to prove anything about them.* -/

/-- `p` has nothing strictly below it. -/
def PairMinimal (p : EMLTree × EMLTree) : Prop := ∀ q, ¬ PeelRel q p

/-- A leaf left germ is minimal — the peel has no constructor that reaches it. -/
theorem pairMinimal_of_lsp_zero (A C : EMLTree) (h : A.lspTree = 0) : PairMinimal (A, C) := by
  intro q hq
  have hlt := peelRel_measure_lt hq
  have h0 : PairMeasure (A, C) = 0 := h
  omega

theorem eml_of_lsp_ne_zero : ∀ A : EMLTree, A.lspTree ≠ 0 →
    ∃ A₁ A₂ : EMLTree, A = EMLTree.eml A₁ A₂ := by
  intro A
  cases A with
  | const c => intro h; exact absurd rfl h
  | var => intro h; exact absurd rfl h
  | eml A₁ A₂ => intro _; exact ⟨A₁, A₂, rfl⟩

/-- …and an `eml` left germ is not, because the peel applies to it. -/
theorem not_pairMinimal_of_lsp_ne_zero (A C : EMLTree) (h : A.lspTree ≠ 0) :
    ¬ PairMinimal (A, C) := by
  intro hmin
  obtain ⟨A₁, A₂, he⟩ := eml_of_lsp_ne_zero A h
  rw [he] at hmin
  exact hmin (A₁, mergeTree A₂ C) (PeelRel.step A₁ A₂ C)

/-- **THE MINIMAL ELEMENTS, both directions.** They are exactly the pairs whose left germ is a
leaf — `EMLPeelRecursion`'s T2 cell, which §4(6) proved is the conjecture. -/
theorem pairMinimal_iff (A C : EMLTree) : PairMinimal (A, C) ↔ A.lspTree = 0 := by
  constructor
  · intro hmin
    rcases Nat.eq_zero_or_pos A.lspTree with h | h
    · exact h
    · exact absurd hmin (not_pairMinimal_of_lsp_ne_zero A C (by omega))
  · exact pairMinimal_of_lsp_zero A C

/-- **At class width, half of that survives for every `PairDescent`.** Whatever carrier and order a
pair relation uses, a pair with an `eml` left germ has something strictly below it, so the minimal
set of any peel-decreased relation is contained in `{A.lspTree = 0}`. Shrinking it further needs an
edge the peel does not supply — which is a second mechanism, not this one. -/
theorem pairDescent_eml_not_minimal (m : PairDescent) (A₁ A₂ C : EMLTree) :
    ∃ p : EMLTree × EMLTree, m.R (m.μ p) (m.μ (EMLTree.eml A₁ A₂, C)) :=
  ⟨(A₁, mergeTree A₂ C), m.peel_lt A₁ A₂ C⟩

/-! ### The run, counted

Where the recursion stops, and after how many steps. `peelAccum` (mechanism (7)) is the
accumulator; `leftLeaf` is the left germ it stops at. -/

/-- The leaf at the end of the leftmost spine — the left germ the run terminates at. -/
def leftLeaf : EMLTree → EMLTree
  | EMLTree.const c => EMLTree.const c
  | EMLTree.var => EMLTree.var
  | EMLTree.eml A _ => leftLeaf A

theorem leftLeaf_lsp : ∀ t : EMLTree, (leftLeaf t).lspTree = 0 := by
  intro t
  induction t with
  | const c => rfl
  | var => rfl
  | eml A B ih _ => exact ih

/-- A leaf left germ is its own terminus, and its accumulator is untouched. -/
theorem leftLeaf_self (A : EMLTree) (h : A.lspTree = 0) : leftLeaf A = A := by
  cases A with
  | const c => rfl
  | var => rfl
  | eml A₁ A₂ => exact absurd h (by show A₁.lspTree + 1 ≠ 0; omega)

theorem peelAccum_self (A C : EMLTree) (h : A.lspTree = 0) : peelAccum A C = C := by
  cases A with
  | const c => rfl
  | var => rfl
  | eml A₁ A₂ => exact absurd h (by show A₁.lspTree + 1 ≠ 0; omega)

/-- Chains of peels, with their length. -/
inductive PeelChain : Nat → EMLTree × EMLTree → EMLTree × EMLTree → Prop where
  | refl (p : EMLTree × EMLTree) : PeelChain 0 p p
  | step {n : Nat} {p q r : EMLTree × EMLTree} :
      PeelRel q r → PeelChain n p q → PeelChain (n + 1) p r

/-- **The run, end to end.** From `(A, C)` the peel reaches `(leftLeaf A, peelAccum A C)` in
**exactly** `A.lspTree` steps — a minimal pair by `leftLeaf_lsp`, and `peel_terminates` bounds the
count by the depth. This is the route working exactly as intended, which is why the file continues
to §5 rather than stopping here. -/
theorem peel_run : ∀ A C : EMLTree, PeelChain A.lspTree (leftLeaf A, peelAccum A C) (A, C) := by
  intro A
  induction A with
  | const c => intro C; exact PeelChain.refl _
  | var => intro C; exact PeelChain.refl _
  | eml A₁ A₂ ih1 _ =>
      intro C
      exact PeelChain.step (PeelRel.step A₁ A₂ C) (ih1 (mergeTree A₂ C))

/-- **Every minimal pair is reached**, by the run from itself, so restricting the terminal cell to
*reachable* accumulators shrinks nothing: `peelAccum (const 0) C = C` for every `C`. -/
theorem every_minimal_pair_is_a_terminus (A C : EMLTree) (h : A.lspTree = 0) :
    PeelChain A.lspTree (A, C) (A, C) := by
  rw [h]
  exact PeelChain.refl _

/-! ## §4 — the six fixtures, measured before any theorem was attempted

`EmlGermApproachResearch.md` §3's families, priced in the pair order. Two columns are new: the left
germ the run terminates at, and the pair measure the family carries when it appears where the
conjecture actually puts it. -/

theorem leftLeaf_recipTree (t : EMLTree) : leftLeaf (recipTree t) = EMLTree.const 0 := rfl

theorem leftLeaf_posEmbed (t : EMLTree) : leftLeaf (posEmbed t) = EMLTree.const 0 := rfl

theorem leftLeaf_capNode (n : Nat) : leftLeaf (capNode n) = EMLTree.const 0 := rfl

theorem leftLeaf_deepDecay (m : Nat) : leftLeaf (deepDecay m) = EMLTree.const 0 := rfl

theorem leftLeaf_towerTree : ∀ n : Nat, leftLeaf (EMLTree.towerTree n) = EMLTree.var := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => exact ih

/-- **The one fixture that does not land on `const 0`.** `gapTarget n c` runs down the tower's
leftmost spine to `var` — `n + 1` peels for a gap that is the constant `c` and a floor of height
`0`. Recorded because it is the only evidence in this table that the terminal cell has two shapes
at all. -/
theorem leftLeaf_gapTarget (n : Nat) (c : Real) :
    leftLeaf (gapTarget n c) = EMLTree.var := leftLeaf_towerTree n

/-- **Four of the six fixtures terminate at `const 0` — the T2 cell verbatim**, with their peel
counts from `EMLPeelRecursion` §2 unchanged. -/
theorem fixtures_terminate_at_constZero (t : EMLTree) (n m : Nat) :
    (leftLeaf (recipTree t) = EMLTree.const 0 ∧ (recipTree t).lspTree = 2) ∧
    (leftLeaf (posEmbed t) = EMLTree.const 0 ∧ (posEmbed t).lspTree = 1) ∧
    (leftLeaf (capNode n) = EMLTree.const 0 ∧ (capNode n).lspTree = 1) ∧
    (leftLeaf (deepDecay m) = EMLTree.const 0 ∧ (deepDecay m).lspTree = 2) :=
  ⟨⟨rfl, lsp_recipTree t⟩, ⟨rfl, lsp_posEmbed t⟩, ⟨rfl, lsp_capNode n⟩,
   ⟨rfl, lsp_deepDecay m⟩⟩

/-- **The hypothesis boundary: the meeting pair never enters the recursion.** `(A, eTree A)` has
gap identically `0`, so the strict hypothesis fails at every `x` and there is nothing to peel.
`EMLPeelRecursion`'s `peel_gap_pos` says the same thing from inside: positivity is inherited once
the recursion starts, and the boundary is at the entry. -/
theorem pair_entry_fails_at_meeting (A : EMLTree) (x : Real) :
    ¬ ((eTree A).eval x < exp (A.eval x)) := by
  intro h
  rw [eTree_eval] at h
  exact (ne_of_lt h) rfl

/-! ### The row that decides it

`EMLPeelRecursion` records the peel count as **constant** on `deepDecay`. At pair width it is
**zero** there, and on the pairs the conjecture is actually reduced to. -/

theorem approachTarget_pair_measure (t : EMLTree) :
    PairMeasure (EMLTree.const (0 : Real), approachTarget t) = 0 := rfl

/-- **The whole obligation lives among the minimal elements.**
`decayFloor_of_emlGermApproach` instantiates the left germ at `const 0` and nothing else, so every
instance of `DecayFloor` arrives as a pair the recursion cannot take a single step on: minimal,
measure `0`, accumulator untouched. **The route's engine never turns over on its own workload.** -/
theorem decayFloor_reduction_is_minimal (t : EMLTree) :
    PairMinimal (EMLTree.const 0, approachTarget t) ∧
    PairMeasure (EMLTree.const (0 : Real), approachTarget t) = 0 ∧
    peelAccum (EMLTree.const (0 : Real)) (approachTarget t) = approachTarget t :=
  ⟨pairMinimal_of_lsp_zero _ _ rfl, rfl, rfl⟩

/-- **No floor height is a function of the pair measure.** The mirror of
`peelCount_cannot_carry_floor` at pair width, and sharper: there the measure was pinned at `2` on
the extremal family, here at `0`, and `0` is the value it takes on every instance of the
obligation. `deepDecay m` forces `m + 1 ≤ f 0` for every `m`. -/
theorem pairCount_cannot_carry_floor (f : Nat → Nat)
    (hf : ∀ (A C : EMLTree) (X₀ : Real), 1 ≤ X₀ →
      (∀ x : Real, X₀ ≤ x → C.eval x < exp (A.eval x)) →
      ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
        exp (-(EMLTree.towerFn (f (PairMeasure (A, C))) x)) ≤ exp (A.eval x) - C.eval x) :
    False := by
  have key : ∀ m : Nat, m + 1 ≤ f 0 := by
    intro m
    have hgap : ∀ x : Real,
        exp ((EMLTree.const 0).eval x) - (approachTarget (deepDecay m)).eval x
          = (deepDecay m).eval x := by
      intro x
      rw [approachTarget_eval]
      show exp ((0 : Real)) - (1 - (deepDecay m).eval x) = (deepDecay m).eval x
      rw [exp_zero]; mach_ring
    have hlt : ∀ x : Real, (1 : Real) ≤ x →
        (approachTarget (deepDecay m)).eval x < exp ((EMLTree.const 0).eval x) := by
      intro x _
      have u := add_lt_add_left (deepDecay_pos m x) (1 - (deepDecay m).eval x)
      have e1 : (1 : Real) - (deepDecay m).eval x + 0 = 1 - (deepDecay m).eval x := by mach_ring
      have e2 : (1 : Real) - (deepDecay m).eval x + (deepDecay m).eval x = 1 := by mach_ring
      rw [e1, e2] at u
      rw [approachTarget_eval]
      show (1 : Real) - (deepDecay m).eval x < exp ((0 : Real))
      rw [exp_zero]; exact u
    obtain ⟨X₁, hX₁, h⟩ :=
      hf (EMLTree.const 0) (approachTarget (deepDecay m)) 1 (le_refl 1) hlt
    rw [approachTarget_pair_measure] at h
    have h' : ∀ x : Real, X₁ ≤ x →
        exp (-(EMLTree.towerFn (f 0) x)) ≤ (deepDecay m).eval x := by
      intro x hx
      have hh := h x hx
      rwa [hgap x] at hh
    exact floorHeight_of_deepDecay m (f 0) X₁ hX₁ h'
  have h := key (f 0)
  omega

/-! ## §5 — the floor, attempted last: the terminal cell is the conjecture -/

/-- **The pair route's terminal cell**: the obligation restricted to the `≺`-minimal pairs. -/
def PairTerminalCell : Prop :=
  ∀ j : Nat, ∃ k : Nat, ∀ (A C : EMLTree) (X₀ : Real),
    A.depth ≤ j → C.depth ≤ j → A.lspTree = 0 → 1 ≤ X₀ →
    (∀ x : Real, X₀ ≤ x → C.eval x < exp (A.eval x)) →
    ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
      exp (-(EMLTree.towerFn k x)) ≤ exp (A.eval x) - C.eval x

/-- **The cell contains `EMLPeelRecursion`'s T2 verbatim**, because `const 0` is a leaf. -/
theorem peelTerminalConstZero_of_pairTerminalCell (h : PairTerminalCell) :
    PeelTerminalConstZero := by
  intro j
  obtain ⟨k, hk⟩ := h j
  refine ⟨k, ?_⟩
  intro C X₀ hC hX₀ hlt
  have h0 : (EMLTree.const (0 : Real)).depth ≤ j := by simp only [EMLTree.depth]; omega
  exact hk (EMLTree.const 0) C X₀ h0 hC rfl hX₀ hlt

/-- …and the conjecture gives the cell back by dropping one hypothesis — no depth inflation at
all, where mechanism (7)'s converse cost `j ↦ 116 · j`. -/
theorem pairTerminalCell_of_emlGermApproach (hG : EmlGermApproach) : PairTerminalCell := by
  intro j
  obtain ⟨k, hk⟩ := hG j
  refine ⟨k, ?_⟩
  intro A C X₀ hA hC _ hX₀ hlt
  exact hk A C X₀ hA hC hX₀ hlt

/-- **THE RESULT. The pair route's minimal elements are the conjecture, with a converse.** Per
`EmlGermApproachResearch.md` §9 an equivalence with a converse is not progress: the relation is
well-founded, the peel decreases it, the run terminates — and it lands on the statement it started
from, at the same depth. -/
theorem pairTerminalCell_iff_emlGermApproach : PairTerminalCell ↔ EmlGermApproach :=
  ⟨fun h => peelTerminalConstZero_iff_emlGermApproach.mp
      (peelTerminalConstZero_of_pairTerminalCell h),
   pairTerminalCell_of_emlGermApproach⟩

/-- **Both of the route's exits, together.** The minimal elements are T2; the peel step's own side
condition `0 < c` is T1. Neither is free, and `EMLPeelRecursion` §3 priced both. -/
theorem pair_route_exits_are_the_conjecture :
    (PairTerminalCell ↔ EmlGermApproach) ∧ (PeelTerminalNoCancel ↔ EmlGermApproach) :=
  ⟨pairTerminalCell_iff_emlGermApproach, peel_terminal_cells_are_the_conjecture.1⟩

/-! ### The cell cannot be shrunk by choosing a different `≺`

The repair the class invites is to give `(const 0, C)` a predecessor so that it stops being
minimal. Closed here at the width of every base-case set. -/

/-- **The pair recursion is a valid induction principle**, with the full leaf base case. This is
the positive half of the instrument, and it is what makes the theorem below a statement about the
base case rather than about soundness. -/
theorem pair_peel_induction {P : EMLTree → EMLTree → Prop}
    (base : ∀ A C, A.lspTree = 0 → P A C)
    (step : ∀ A₁ A₂ C, P A₁ (mergeTree A₂ C) → P (EMLTree.eml A₁ A₂) C) :
    ∀ A C, P A C := by
  intro A
  induction A with
  | const c => intro C; exact base _ C rfl
  | var => intro C; exact base _ C rfl
  | eml A₁ A₂ ih1 _ => intro C; exact step A₁ A₂ C (ih1 (mergeTree A₂ C))

/-- **Any sound peel-driven pair recursion has `(const 0, C)` among its base cases.** `S` is the
base-case set, assumed to consist of pairs the recursion stops at (`≺`-minimal, `hstop`); `hsound`
is the induction principle it claims. Instantiating that principle at
`P A C := S (leftLeaf A) (peelAccum A C)` — whose step case is `rfl`, because that substitution *is*
a peel — and reading the conclusion at `const 0` gives the base case back.

> **The cell is not a choice.** The peel carries every pair to a leaf left germ, so no relation
> decreased by it can route around `(const 0, C)`, and that instance is the whole obligation
> (`peelTerminalConstZero_iff_emlGermApproach`). -/
theorem base_must_contain_constZero (S : EMLTree → EMLTree → Prop)
    (hstop : ∀ A C, S A C → A.lspTree = 0)
    (hsound : ∀ P : EMLTree → EMLTree → Prop,
       (∀ A C, S A C → P A C) →
       (∀ A₁ A₂ C, P A₁ (mergeTree A₂ C) → P (EMLTree.eml A₁ A₂) C) →
       ∀ A C, P A C)
    (C : EMLTree) : S (EMLTree.const 0) C :=
  hsound (fun A C' => S (leftLeaf A) (peelAccum A C'))
    (by
      intro A C' hS
      have h0 := hstop A C' hS
      rw [leftLeaf_self A h0, peelAccum_self A C' h0]
      exact hS)
    (fun _ _ _ h => h) (EMLTree.const 0) C

/-- **Both verdicts on that instrument.** It is not vacuous: fed the `var`-only base case — the one
`leftLeaf_gapTarget` shows is genuinely reached by a §3 fixture — it returns a refutation, because
the four other fixtures terminate at `const 0`. A base case that covers one leaf and not the other
is unsound, and the theorem says which one is missing. -/
theorem var_only_base_is_unsound :
    ¬ (∀ P : EMLTree → EMLTree → Prop,
        (∀ A C, A = EMLTree.var → P A C) →
        (∀ A₁ A₂ C, P A₁ (mergeTree A₂ C) → P (EMLTree.eml A₁ A₂) C) →
        ∀ A C, P A C) := by
  intro hsound
  have h := base_must_contain_constZero (fun A _ => A = EMLTree.var)
    (by intro A C hA; rw [hA]; rfl) hsound EMLTree.var
  exact EMLTree.noConfusion h

/-! ## §6 — the second coordinate cannot carry the descent, and the germ pair has no count

Two escapes remain to price. The first is to put the descent in the accumulator rather than the
left germ; the second is to drop the syntax so the recursion never has to stop. -/

/-- **No measure of the accumulator alone descends along the merge, in any well-founded order.**
The merge iterates — `C`, `A₂·C`, `A₂·(A₂·C)`, … — so such a measure would carry an infinite
descending chain. Hence a pair measure's descent must come from the left germ's **syntax**, which
is `lspTree`'s territory and therefore §5's. -/
theorem no_accumulator_descent {W : Type} (ν : EMLTree → W) (R : W → W → Prop)
    (hwf : WellFounded R)
    (hdesc : ∀ A₂ C : EMLTree, R (ν (mergeTree A₂ C)) (ν C)) : False := by
  have key : ∀ w : W, ∀ D : EMLTree, ν D = w → False := by
    intro w
    refine hwf.induction (C := fun w => ∀ D : EMLTree, ν D = w → False) w ?_
    intro y ih D hD
    refine ih (ν (mergeTree (EMLTree.const 1) D)) ?_ (mergeTree (EMLTree.const 1) D) rfl
    rw [← hD]
    exact hdesc (EMLTree.const 1) D
  exact key (ν EMLTree.var) EMLTree.var rfl

/-- **No function of the GERM PAIR bounds the peel count.** `no_germInvariant_peel_bound` at pair
width: `selfLeftNode` re-presents any tree two spine levels up with the same germ, and the second
coordinate may be held fixed while it iterates. So dropping the syntax — the escape that keeps the
recursion from ever reaching a leaf — costs the measure here exactly as it does in mechanism (7). -/
theorem no_germInvariant_pair_bound (f : (Real → Real) → (Real → Real) → Nat)
    (hf : ∀ A C : EMLTree, A.lspTree ≤ f A.eval C.eval) : False := by
  have hb := hf (iterSelf (f EMLTree.var.eval (EMLTree.const (0 : Real)).eval + 1) EMLTree.var)
    (EMLTree.const 0)
  rw [iterSelf_germ, iterSelf_lsp] at hb
  have hv : EMLTree.var.lspTree = 0 := rfl
  omega

/-! ## §7 — the mechanism, in one statement -/

/-- **Mechanism (8).** Four facts, and the route is between them:

1. the relation is **well-founded** (`peelRel_wf`) and the class is inhabited
   (`pairDescent_inhabited`) — this is not a route that fails to get started;
2. its **minimal elements are exactly the leaf-left-germ pairs** (`pairMinimal_iff`), and at class
   width every peel-decreased relation's minimal set is **contained in** that one
   (`pairDescent_eml_not_minimal`);
3. that cell **is the conjecture, with a converse** (`pairTerminalCell_iff_emlGermApproach`), and
   no sound base case can omit it (`base_must_contain_constZero`);
4. the escapes are priced: the accumulator cannot carry the descent (`no_accumulator_descent`) and
   the germ pair cannot bound the count (`no_germInvariant_pair_bound`).

So the pair reading does not escape mechanism (6) — it **is** (6), with the accumulator named and
the measure read off the first coordinate. -/
theorem pair_relation_changes_nothing :
    WellFounded PeelRel ∧
    (∀ A C : EMLTree, PairMinimal (A, C) ↔ A.lspTree = 0) ∧
    (PairTerminalCell ↔ EmlGermApproach) :=
  ⟨peelRel_wf, pairMinimal_iff, pairTerminalCell_iff_emlGermApproach⟩

end MachLib
