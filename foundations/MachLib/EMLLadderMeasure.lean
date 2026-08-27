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
measure can run the reciprocal transfer as its step.

**And "grammar-respecting" is not a restriction** — that is §3. Every `Nat`-valued measure strictly
descending to both children *is* a `LadderMeasure` with `step = 1`, definitionally, and descending to
both children is exactly what the ladder step needs (it recurses left for the envelope and right for
the floor). So the class is not a shape chosen to make the theorem come out; it is the set of
measures that can carry a structural induction at all. The escape route *"then use a measure that
does not grow under `recipTree`"* closes with it (`no_structural_induction_of_cheap_recip`): such
measures exist, and none of them descends.

**The honest residual, at the right width.** `§4` closes the germ arm as well, so what these
sections kill is **local scalar growth descent through the syntax tree** — a `Nat`-valued measure on
trees, syntactic or germ-based, descending to both children.

That is *not* the claim that no well-founded induction can work, and the difference matters. A
lexicographic order with an unbounded second component, an ordinal rank, a well-founded **relation**
on germs rather than a function of them, and any non-structural argument are all untouched. State
the result at that width and no wider.

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

/-! ## §3 — the hypothesis is not a restriction

`§1` reads as a theorem about a *class* of measures, which invites the reply *"then use a measure
outside the class"*. There is nowhere to go. A structural induction on an EML tree recurses into its
children, and the ladder step recurses into **both** — left for the envelope, right for the floor.
A `Nat`-valued measure supporting that must strictly descend to both children, and any measure that
does **is** a `LadderMeasure` with `step = 1`, definitionally: `Nat.lt n m` *is* `n + 1 ≤ m`, so the
two descent hypotheses are the two fields, verbatim and with no proof. -/

/-- **Strict descent to both children is a ladder measure**, with `step = 1`. -/
def LadderMeasure.ofStrictDescent (m : EMLTree → Nat)
    (hl : ∀ A B : EMLTree, m A < m (EMLTree.eml A B))
    (hr : ∀ A B : EMLTree, m B < m (EMLTree.eml A B)) : LadderMeasure where
  μ := m
  step := 1
  step_pos := Nat.zero_lt_one
  left_le := hl
  right_le := hr

/-- **Every measure that can carry the induction pays two steps for the reciprocal.** The
`LadderMeasure` packaging drops out and what is left is a statement about any `Nat`-valued measure
whatsoever that descends to both children. -/
theorem recip_not_at_one_step_of_strict_descent (m : EMLTree → Nat)
    (hl : ∀ A B : EMLTree, m A < m (EMLTree.eml A B))
    (hr : ∀ A B : EMLTree, m B < m (EMLTree.eml A B)) (t : EMLTree) :
    ¬ (m (recipTree t) ≤ m t + 1) :=
  (LadderMeasure.ofStrictDescent m hl hr).recip_not_at_one_step t

/-- **The escape route, closed by contraposition.** *"Then find a measure that does not grow under
`recipTree`."* Such measures exist — the constant `0` is one — but none of them strictly descends to
both children, so there is no induction left for it to be the parameter of. **Cheap reciprocals and
structural descent cannot be had together.**

Stated on a single `t`, because that is all it takes: one tree priced cheaply is enough to refute
descent everywhere. -/
theorem no_structural_induction_of_cheap_recip (m : EMLTree → Nat) (t : EMLTree)
    (hcheap : m (recipTree t) ≤ m t + 1) :
    ¬ ((∀ A B : EMLTree, m A < m (EMLTree.eml A B)) ∧
       (∀ A B : EMLTree, m B < m (EMLTree.eml A B))) := by
  intro h
  exact recip_not_at_one_step_of_strict_descent m h.1 h.2 t hcheap

/-- **Discrimination — the incompatibility is not vacuous on the descent side.** `depth` really does
strictly descend to both children, so the hypothesis of
`recip_not_at_one_step_of_strict_descent` is satisfiable and the theorem is not about an empty class.
`sizeMeasure` gives a second witness, at a different `step`. -/
theorem depth_strict_descent (A B : EMLTree) :
    A.depth < (EMLTree.eml A B).depth ∧ B.depth < (EMLTree.eml A B).depth :=
  ⟨depthMeasure.left_le A B, depthMeasure.right_le A B⟩

/-- **And not vacuous on the cheap side either — the theorem is fired, not merely stated.** The
constant measure prices every reciprocal at `0`, so it satisfies the hypothesis; what
`no_structural_induction_of_cheap_recip` returns is that it descends nowhere, which is exactly
right and is the whole point. A transfer no measure satisfies would prove nothing. -/
theorem const_measure_not_descending :
    ¬ ((∀ A B : EMLTree, (fun _ : EMLTree => (0 : Nat)) A
          < (fun _ : EMLTree => (0 : Nat)) (EMLTree.eml A B)) ∧
       (∀ A B : EMLTree, (fun _ : EMLTree => (0 : Nat)) B
          < (fun _ : EMLTree => (0 : Nat)) (EMLTree.eml A B))) :=
  no_structural_induction_of_cheap_recip (fun _ => 0) EMLTree.var (by show (0 : Nat) ≤ 0 + 1; omega)

/-! ## §4 — the germ route escapes §1, and dies of something else

`§3` left one opening: *an induction on the **germ** rather than on the syntax.* It is the natural
next reach, and it really does escape `§1` — but not for long. Two facts, both cheap, closing from
opposite sides.

**It escapes.** Every syntactic measure pays `2 * step` for `recipTree` (`recip_ge`). A germ measure
pays **nothing** — it goes *down*. Where `t ≥ 1`, `recipTree t` is `e / t x`, hence at most `e`: a
constant, tower height `0`, however fast `t` grew. So a parameter tracking the growth of the germ is
genuinely outside the class `§1` and `§3` cover, and no argument there touches it.

**And it dies anyway.** Such a parameter must still descend to **both** children — `§3` identified
that as the real requirement — and it does not descend to the *right* one. Totalised `log` sees to
it: `eml (const 0) (towerTree (n+1))` is `1 − towerFn n x`, **non-positive on the ray**, so it needs
no height at all, while its right child *is* the `(n+1)`-tower. The gap is not a constant to be
absorbed; it is unbounded in `n`.

> A node can be arbitrarily **flatter** than the child it is built from, because the right child
> enters under a `log`. Growth descends on the left and inverts on the right.

So the two routes fail for opposite reasons — **syntactic measures grow too fast under `recipTree`;
germ measures do not descend to the right child.** Nothing here bounds anything either.

`open Real` is scoped to this section on purpose: it shadows `max`, which `§2`'s `depthMeasure`
needs. -/

section GermRoute

open Real

/-- **The reciprocal collapses the germ.** Where `t ≥ 1` on a ray, `recipTree t` is bounded by `e`
there — tower height `0`, no matter how fast `t` grew. This is why a germ-based parameter escapes
`recip_ge`: the construction that costs every syntactic measure two steps costs a growth measure
less than nothing. -/
theorem recipTree_germ_bounded (t : EMLTree) (X : Real)
    (h : ∀ x : Real, X ≤ x → 1 ≤ t.eval x) :
    ∀ x : Real, X ≤ x → (recipTree t).eval x ≤ exp 1 := by
  intro x hx
  rw [recipTree_eval]
  have hpos : (0 : Real) < t.eval x := lt_of_lt_of_le zero_lt_one_ax (h x hx)
  have hlog : (0 : Real) ≤ log (t.eval x) := by
    have hl1 : log (1 : Real) = 0 := by
      have hz : exp (0 : Real) = 1 := exp_zero
      rw [← hz, log_exp]
    have hm := log_le_log zero_lt_one_ax (h x hx)
    rw [hl1] at hm; exact hm
  have hle : (1 : Real) - log (t.eval x) ≤ 1 := by
    have u := add_le_add_wit (le_refl (1 : Real)) (neg_le_neg_wit hlog)
    have e1 : (1 : Real) + -log (t.eval x) = 1 - log (t.eval x) := by mach_ring
    have e2 : (1 : Real) + -(0 : Real) = 1 := by mach_ring
    rw [e1, e2] at u; exact u
  exact exp_monotone hle

/-- The node that flattens its own right child: `1 − towerFn n x`. -/
noncomputable def capNode (n : Nat) : EMLTree :=
  EMLTree.eml (EMLTree.const 0) (EMLTree.towerTree (n + 1))

theorem capNode_eval (n : Nat) (x : Real) :
    (capNode n).eval x = 1 - EMLTree.towerFn n x := by
  show exp ((0 : Real)) - log ((EMLTree.towerTree (n + 1)).eval x) = _
  rw [exp_zero, EMLTree.towerTree_eval]
  show (1 : Real) - log (exp (EMLTree.towerFn n x)) = _
  rw [log_exp]

/-- **Non-positive on the ray**, at every `n`: the node needs no ceiling at all. -/
theorem capNode_nonpos (n : Nat) {x : Real} (hx : 1 ≤ x) : (capNode n).eval x ≤ 0 := by
  rw [capNode_eval]
  have h1 := towerFn_ge_one n hx
  have u := add_le_add_wit (le_refl (1 : Real)) (neg_le_neg_wit h1)
  have e1 : (1 : Real) + -EMLTree.towerFn n x = 1 - EMLTree.towerFn n x := by mach_ring
  have e2 : (1 : Real) + -(1 : Real) = 0 := by mach_ring
  rw [e1, e2] at u; exact u

/-- **No growth measure descends to the right child, and the gap is unbounded.** For every `n` there
is a node non-positive on `[1, ∞)` — needing no tower height — whose right child *is* the
`(n+1)`-tower. A parameter tracking how fast the germ grows therefore cannot decrease from a node to
its right child, so it cannot carry a structural induction, and `§3`'s residual closes on the germ
side too. -/
theorem tower_height_does_not_descend_right (n : Nat) :
    ∃ A B : EMLTree,
      (∀ x : Real, 1 ≤ x → (EMLTree.eml A B).eval x ≤ 0) ∧
      (∀ x : Real, B.eval x = EMLTree.towerFn (n + 1) x) :=
  ⟨EMLTree.const 0, EMLTree.towerTree (n + 1),
   fun _ hx => capNode_nonpos n hx,
   EMLTree.towerTree_eval (n + 1)⟩

end GermRoute

end MachLib