import MachLib.EMLDecayNotIterating

/-!
# The third quantity, named

`(dg)` established that the `U_j`/`V_j` pair was split along the wrong seam: **growth** and
**lower-bound** iterate into each other cleanly (`node_lower_of_right_upper`), while **decay** —
distance from zero *from above* — is a third quantity neither envelope controls. `(de)`/`(df)` showed
it grows with depth.

This module states that third quantity as a **named obligation**, the corpus's device for committing
a partial result without overstating it, and proves the half that does not need cancellation.

## The statement

```
DecayFloor : ∀ j, ∃ k, ∀ t, t.depth ≤ j → (eventually positive) →
                            eventually  exp (-(towerFn k x)) ≤ t.eval x
```

`k` depends on the **depth only**, not on the tree — that is what makes it a real statement rather
than bookkeeping. Without the uniformity the existential could be chosen per tree and the content
would evaporate; with it, the claim is that a *fixed* tower height serves every tree of a given
depth.

`towerFn` is the corpus's own `k`-fold exponential (`towerFn 0 x = x`, `towerFn (n+1) x = exp ∘`), the
same one `towerTree` realises — so the obligation is stated against an object the depth programme
already uses.

## What is proved here

`decayFloor_clamped` — the **clamped** half. Where the right child is eventually non-positive,
`log = 0` and the node *is* `exp ∘ A`, so the floor is exactly a **lower bound on `A`** and nothing
else. No cancellation, no approximation. Composed with `node_lower_of_right_upper` this is the branch
that inherits from the envelopes.

Both witnesses from `(de)`/`(df)` are checked against it: `decayFast` (depth 3) needs `k = 0` and
`decayFaster` (depth 4) needs `k = 1`, so the obligation is satisfiable where it has been tested and
the height demonstrably grows.

## What is open, precisely

The **positive-`B`** branch: `exp (A x) − log (B x) > 0` with `B` eventually positive, where the node
can be tiny because `exp (A x)` nearly cancels `log (B x)`. That is an approximation question — how
closely can one EML germ approach another without meeting it — and neither envelope, nor
`evSign_all`, nor the zero bound speaks to it. `evSign_all` gives eventual non-vanishing; this asks
to be *bounded away* from zero, which is strictly more.

Stated so that if it is ever proved, the ledger gate notices.
-/

namespace MachLib

open Real

/-- **The third quantity.** For each depth there is a single tower height serving every tree of that
depth: an eventually-positive tree is eventually bounded below by `exp (-(towerFn k x))`.

The uniformity in `k` is the content. Quantified per tree it would be near-vacuous. -/
def DecayFloor : Prop :=
  ∀ j : Nat, ∃ k : Nat, ∀ (t : EMLTree) (X₀ : Real), t.depth ≤ j → 1 ≤ X₀ →
    (∀ x : Real, X₀ ≤ x → 0 < t.eval x) →
    ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
      exp (-(EMLTree.towerFn k x)) ≤ t.eval x

/-- **The clamped half.** A non-positive right child totalises its `log` to `0`, so the node is
`exp ∘ A` and the floor is exactly a lower bound on `A` — the branch that inherits from the
envelopes, with no cancellation anywhere. -/
theorem decayFloor_clamped (A B : EMLTree) (E : Real → Real) (X₀ : Real)
    (hclamp : ∀ x : Real, X₀ ≤ x → B.eval x ≤ 0)
    (hlow : ∀ x : Real, X₀ ≤ x → -(E x) ≤ A.eval x) :
    ∀ x : Real, X₀ ≤ x → exp (-(E x)) ≤ (EMLTree.eml A B).eval x := by
  intro x hx
  show exp (-(E x)) ≤ exp (A.eval x) - log (B.eval x)
  rw [log_nonpos (hclamp x hx)]
  have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
  rw [e]
  exact exp_monotone (hlow x hx)

/-! ## The two witnesses, checked against the obligation -/

/-- `decayFast` (depth 3, value `exp (1 − x)`) sits above the height-`0` floor: `towerFn 0 x = x`. -/
theorem decayFast_floor : ∀ x : Real, 1 ≤ x →
    exp (-(EMLTree.towerFn 0 x)) ≤ decayFast.eval x := by
  intro x _
  rw [decayFast_eval x]
  show exp (-x) ≤ exp (1 - x)
  refine exp_monotone ?_
  have v := add_le_add_wit (le_of_lt zero_lt_one_ax) (le_refl (-x))
  have e1 : (0 : Real) + -x = -x := by mach_ring
  have e2 : (1 : Real) + -x = 1 - x := by mach_ring
  rw [e1, e2] at v; exact v

/-- `decayFaster` (depth 4, value `exp (−exp x)`) needs height `1`: `towerFn 1 x = exp x`. So the
height grows with depth, as `(df)`'s separation forces. -/
theorem decayFaster_floor : ∀ x : Real, 1 ≤ x →
    exp (-(EMLTree.towerFn 1 x)) ≤ decayFaster.eval x := by
  intro x _
  rw [decayFaster_eval x]
  show exp (-(exp x)) ≤ exp (-exp x)
  exact le_refl _

/-! ## §2 — the open branch is not a corner case

It is tempting to read `DecayFloor` as "the clamped branch is done, now handle the positive-`B` case
separately". That reading is wrong, and this section says why.

**Every tree re-embeds into a positive-`B` node at `+4` depth.** With `eTree t = eml t (const 1)`
computing `exp ∘ t` (because `log 1 = 0` — the same identity `expTree_eval` uses in
`EMLSignReduction`):

```
posEmbed t = eml (const 0) (eTree (eml (const 0) (eTree t)))
```

unwinds to `1 − (1 − t x) = t x`, and its right child is `exp (1 − t x)` — **positive everywhere**,
not merely eventually. `posEmbed_depth` is `t.depth + 4` on the nose.

So the positive-`B` branch **contains the whole problem**. `floor_transfer_via_posEmbed` makes the
consequence explicit: a floor for the embedded node is a floor for the original tree, verbatim.

> Solving the positive-`B` branch at depth `j + 4` solves `DecayFloor` at depth `j`.

Which also says the branch is *at least as hard* as the general obligation, up to a depth shift of 4.
There is no route that disposes of it as a special case, and an attempt that only ever reasons about
"nearly-cancelling" nodes is reasoning about every node in disguise.

**What this does not do:** it does not bound anything. It is a statement about where the difficulty
lives, not a step toward removing it.
-/

/-- `exp ∘ t` as a tree. -/
noncomputable def eTree (t : EMLTree) : EMLTree := EMLTree.eml t (EMLTree.const 1)

theorem eTree_eval (t : EMLTree) (x : Real) : (eTree t).eval x = exp (t.eval x) := by
  show exp (t.eval x) - log (1 : Real) = exp (t.eval x)
  rw [log_one]; mach_ring

theorem eTree_depth (t : EMLTree) : (eTree t).depth = 1 + t.depth := by
  show 1 + max t.depth 0 = 1 + t.depth
  omega

/-- **Every tree re-embeds into a node whose right child is positive everywhere**, at `+4` depth. -/
noncomputable def posEmbed (t : EMLTree) : EMLTree :=
  EMLTree.eml (EMLTree.const 0) (eTree (EMLTree.eml (EMLTree.const 0) (eTree t)))

theorem posEmbed_right_pos (t : EMLTree) (x : Real) :
    0 < (eTree (EMLTree.eml (EMLTree.const 0) (eTree t))).eval x := by
  rw [eTree_eval]; exact exp_pos _

theorem posEmbed_eval (t : EMLTree) (x : Real) : (posEmbed t).eval x = t.eval x := by
  show exp ((EMLTree.const 0).eval x)
      - log ((eTree (EMLTree.eml (EMLTree.const 0) (eTree t))).eval x) = t.eval x
  rw [eTree_eval, log_exp]
  show exp (0 : Real) - (exp ((EMLTree.const 0).eval x) - log ((eTree t).eval x)) = t.eval x
  rw [eTree_eval, log_exp]
  show exp (0 : Real) - (exp (0 : Real) - t.eval x) = t.eval x
  rw [exp_zero]; mach_ring

theorem posEmbed_depth (t : EMLTree) : (posEmbed t).depth = t.depth + 4 := by
  simp only [posEmbed, eTree, EMLTree.depth]
  omega

/-- **The floor transfers.** A floor for the embedded node is a floor for the original tree — they
are the same function. So solving the positive-`B` branch at depth `j + 4` solves `DecayFloor` at
depth `j`. -/
theorem floor_transfer_via_posEmbed (t : EMLTree) (k : Nat) (X₁ : Real)
    (h : ∀ x : Real, X₁ ≤ x → exp (-(EMLTree.towerFn k x)) ≤ (posEmbed t).eval x) :
    ∀ x : Real, X₁ ≤ x → exp (-(EMLTree.towerFn k x)) ≤ t.eval x := by
  intro x hx
  rw [← posEmbed_eval t x]
  exact h x hx


end MachLib
