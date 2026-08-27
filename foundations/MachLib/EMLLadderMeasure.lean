import MachLib.EMLDecayFloorIsGrowth
import MachLib.EMLSizeCost

/-!
# No grammar-respecting measure carries the ladder

`(dj)` proved `DecayFloor ↔ GrowthEnvelope` and closed with a sentence rather than a theorem:
*"any proof must find an induction parameter that is not depth."* The obvious next reach is
**size** — the corpus already prices trees that way (`EMLSizeCost`, `two_mul_depth_succ_le_size`),
and `T38-NNP` prices silicon that way. This says that reach fails, and says it for every measure of
that kind at once rather than one at a time.

## The two facts, from one hypothesis

A measure "respects the grammar" if an `eml` node costs at least `step > 0` more than **either**
child — `LadderMeasure` below. That single hypothesis generates both halves of the picture:

* `step_children` — a node at level `j + step` has both children at level `j`. This is the ladder
  step's own arithmetic: `U (j + step) ⟸ U j ∧ D j`.
* `recip_ge` — `recipTree` is **two** `eml` nodes, so `μ (recipTree t) ≥ μ t + 2 * step`.

and therefore `recip_not_at_one_step`: the reciprocal of a tree at level `n` does not fit at level
`n + step`, the level the step produces. **The route consumes the envelope one full step above what
it delivers, for every measure of this shape.** Not a property of depth; a property of the fact that
the step spends one node and the reciprocal spends two.

## Sharp on both specimens

An abstract bound nobody can meet proves nothing, so both instances are checked against it and both
meet `recip_ge` with **equality**:

```
depthMeasure  step = 1   (recipTree t).depth = t.depth + 2   = t.depth + 2 * step
sizeMeasure   step = 2   (recipTree t).size  = t.size  + 4   = t.size  + 2 * step
```

The size column is the answer to the question that prompted the file. It is not a coincidence that
it doubles: one `eml` node costs `1` depth and `2` size (the node and the leaf it needs), so every
construction in `EMLDecayFloorIsGrowth` costs exactly twice as much in size as in depth — the
converse route included, `+3` and `+6`.

## Scope

**This bounds nothing and discharges nothing.** It is a route-closure: it says where not to look,
and `GrowthEnvelope` stays open, unchanged, as one obligation with `DecayFloor`. In particular it
does *not* say no proof exists — only that no induction whose parameter is a grammar-respecting
measure can run the reciprocal transfer as its step. A parameter that is not of this shape (one that
can *decrease* under `recipTree`, or that is not a function of the tree at all) is untouched.

**Where the escape hatch is, and why it is not one.** The hypothesis doing the work is `step_pos`.
A measure that prices an `eml` node at `0` evades `recip_ge` — but then `step_children` hands back
`μ A ≤ j` from `μ (eml A B) ≤ j` with **no decrease**, so there is no induction left to carry. The
hypothesis that makes the obstruction bite is the same one that makes the ladder a ladder. That
coincidence is the actual content of this file, and it is why swapping depth for another measure
does not help: the two facts have one source. (Prose, not a theorem — "no induction terminates" is
not a proposition this corpus can state, and it is not being claimed as one.)
-/

namespace MachLib

/-! ## §1 — the class of measures -/

/-- **A measure that respects the grammar.** `step` is what one `eml` node costs, and the two
fields say a node costs at least that much more than *either* child.

Stated with `≤` rather than an equation because both consequences below only need the inequality,
and every measure worth the name satisfies it — including ones that weight the two sides
differently, which an equation would exclude. -/
structure LadderMeasure where
  /-- The measure itself. -/
  μ : EMLTree → Nat
  /-- What one `eml` node costs. -/
  step : Nat
  /-- A node must cost something, or the "ladder" has no rungs. -/
  step_pos : 0 < step
  /-- An `eml` node costs at least `step` more than its left child. -/
  left_le : ∀ A B : EMLTree, μ A + step ≤ μ (EMLTree.eml A B)
  /-- An `eml` node costs at least `step` more than its right child. -/
  right_le : ∀ A B : EMLTree, μ B + step ≤ μ (EMLTree.eml A B)

namespace LadderMeasure

/-- **The ladder step's arithmetic.** A node at level `j + step` has both children at level `j` —
which is exactly what `depth_le_three_growth_envelope` uses when it opens with `U₂` for the left
child and the decay bound for the right. One step buys one node. -/
theorem step_children (m : LadderMeasure) (A B : EMLTree) (j : Nat)
    (h : m.μ (EMLTree.eml A B) ≤ j + m.step) : m.μ A ≤ j ∧ m.μ B ≤ j := by
  have hl := m.left_le A B
  have hr := m.right_le A B
  exact ⟨by omega, by omega⟩

/-- One `log` node. -/
theorem negLog_ge (m : LadderMeasure) (t : EMLTree) :
    m.μ t + m.step ≤ m.μ (negLogTree t) :=
  m.right_le (EMLTree.const 0) t

/-- **The reciprocal spends two nodes.** No measure of this class can price it at less. -/
theorem recip_ge (m : LadderMeasure) (t : EMLTree) :
    m.μ t + 2 * m.step ≤ m.μ (recipTree t) := by
  have h1 := m.negLog_ge t
  have h2 := m.left_le (negLogTree t) (EMLTree.const 1)
  show m.μ t + 2 * m.step ≤ m.μ (EMLTree.eml (negLogTree t) (EMLTree.const 1))
  omega

/-- The `exp` wrapper the converse route inserts to avoid the sign split. -/
theorem eTree_ge (m : LadderMeasure) (t : EMLTree) :
    m.μ t + m.step ≤ m.μ (eTree t) :=
  m.left_le t (EMLTree.const 1)

/-- **The converse route spends three.** `recipTree (eTree t)` — the tree `(dj)` routes through so
that positivity is free — costs `3 * step`, matching `+3` in depth and `+6` in size. -/
theorem recip_eTree_ge (m : LadderMeasure) (t : EMLTree) :
    m.μ t + 3 * m.step ≤ m.μ (recipTree (eTree t)) := by
  have h1 := m.eTree_ge t
  have h2 := m.recip_ge (eTree t)
  omega

/-- **The obstruction.** The step produces level `n + step`; the reciprocal of a tree at level `n`
does not fit there, and never will, for any measure in the class.

Stated as a negation on purpose. The positive form would be an inequality between two levels, which
reads as bookkeeping; what is being claimed is that a particular move is *unavailable*. -/
theorem recip_not_at_one_step (m : LadderMeasure) (t : EMLTree) :
    ¬ (m.μ (recipTree t) ≤ m.μ t + m.step) := by
  intro h
  have hr := m.recip_ge t
  have hs := m.step_pos
  omega

end LadderMeasure

/-! ## §2 — the two specimens

`recip_ge` is an inequality about an abstract `μ`; an abstract bound that no real measure meets
proves nothing (this corpus has paid for that lesson once already — see the witness audit's reason
for existing). Both instances below meet it with **equality**, so the class is inhabited and the
bound is sharp, not merely true. -/

/-- Every tree has at least one node. -/
theorem one_le_size (t : EMLTree) : 1 ≤ t.size := by
  induction t with
  | const c => simp [EMLTree.size]
  | var => simp [EMLTree.size]
  | eml a b iha ihb => simp only [EMLTree.size]; omega

/-- **Depth is a ladder measure, with `step = 1`.** -/
def depthMeasure : LadderMeasure where
  μ := EMLTree.depth
  step := 1
  step_pos := Nat.zero_lt_one
  left_le := by
    intro A B
    simp only [EMLTree.depth]
    have h : A.depth ≤ max A.depth B.depth := Nat.le_max_left _ _
    omega
  right_le := by
    intro A B
    simp only [EMLTree.depth]
    have h : B.depth ≤ max A.depth B.depth := Nat.le_max_right _ _
    omega

/-- **Size is a ladder measure, with `step = 2`** — one for the node, one for the leaf it needs.
That factor of two is the whole reason every construction in `EMLDecayFloorIsGrowth` costs twice as
much in size as in depth. -/
def sizeMeasure : LadderMeasure where
  μ := EMLTree.size
  step := 2
  step_pos := by omega
  left_le := by
    intro A B
    have := one_le_size B
    show A.size + 2 ≤ 1 + A.size + B.size
    omega
  right_le := by
    intro A B
    have := one_le_size A
    show B.size + 2 ≤ 1 + A.size + B.size
    omega

/-! ## §3 — the size arithmetic, exactly

The depth figures are already in `EMLDecayFloorIsGrowth` (`recipTree_depth`, `+2`). These are their
size counterparts, and they are what a session reaching for size would have had to compute. -/

/-- `eTree` costs two nodes of size. -/
theorem eTree_size (t : EMLTree) : (eTree t).size = t.size + 2 := by
  simp only [eTree, EMLTree.size]; omega

/-- **Four on the nose** — `2 * sizeMeasure.step`, so `recip_ge` is tight here. -/
theorem recipTree_size (t : EMLTree) : (recipTree t).size = t.size + 4 := by
  simp only [recipTree, negLogTree, EMLTree.size]; omega

/-- **Six** — the converse route, `3 * sizeMeasure.step`, tight against `recip_eTree_ge`. -/
theorem recipTree_eTree_size (t : EMLTree) : (recipTree (eTree t)).size = t.size + 6 := by
  rw [recipTree_size, eTree_size]

/-! ### The bounds are met, not merely stated -/

/-- `recip_ge` is **sharp** for depth: `2 * step = 2`, and `recipTree_depth` is an equation. -/
theorem depthMeasure_recip_sharp (t : EMLTree) :
    depthMeasure.μ (recipTree t) = depthMeasure.μ t + 2 * depthMeasure.step := by
  show (recipTree t).depth = t.depth + 2 * 1
  rw [recipTree_depth]

/-- `recip_ge` is **sharp** for size too: `2 * step = 4`. So neither specimen escapes the
obstruction by being priced loosely — both sit exactly on the bound. -/
theorem sizeMeasure_recip_sharp (t : EMLTree) :
    sizeMeasure.μ (recipTree t) = sizeMeasure.μ t + 2 * sizeMeasure.step := by
  show (recipTree t).size = t.size + 2 * 2
  rw [recipTree_size]

/-- **The answer to the question that prompted the file.** Size fails exactly as depth does: the
reciprocal of a size-`n` tree does not fit at size `n + 2`, which is the level one ladder step
produces. Reaching for size instead of depth changes the numbers and nothing else. -/
theorem size_ladder_fails (t : EMLTree) :
    ¬ ((recipTree t).size ≤ t.size + 2) :=
  sizeMeasure.recip_not_at_one_step t

/-- And depth, restated through the general theorem rather than through `recipTree_depth`, so the
two specimens are known to be the *same* obstruction and not two coincidences. -/
theorem depth_ladder_fails (t : EMLTree) :
    ¬ ((recipTree t).depth ≤ t.depth + 1) :=
  depthMeasure.recip_not_at_one_step t

end MachLib
