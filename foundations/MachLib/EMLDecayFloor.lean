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

end MachLib
