import MachLib.EMLDecayFloorIsGrowth

/-!
# The missing input, named — and it is a separation, not a bound away from zero

Three commits closed the induction search: `(dk)`/`(dl)` killed every local scalar growth descent
through the syntax tree, and `(dm)` killed the germ-side version. What was left was not a choice of
parameter but a **mathematical input**, and this file states it — exactly, and no wider.

## What the obligation must NOT say

It is tempting to describe the missing input as *"a non-vanishing EML germ is bounded away from
zero"*. **Taken literally that is false**, and for perfectly ordinary members of the class:
`exp (1 − x)` and `e / x` are positive everywhere on the ray and have infimum `0`. Both are EML
germs; `decayFast_floor` is one of them, already exercised against `DecayFloor`.

What `DecayFloor` consumes is not a positive constant. It is an **effective lower envelope** of one
specific shape — `exp (-(towerFn k x))`, with `k` depending on the depth bound and **not** on the
tree. That is what `EmlNodeSeparation` states and all it states.

## Exactly what the downstream proof consumes

`DecayFloor` splits on the sign of the right child. The clamped branch (`B ≤ 0` eventually) is
already a theorem — totalised `log` makes the node `exp ∘ A`, and `decayFloor_clamped` closes it with
no cancellation anywhere. What is left is the branch where `B` is eventually **positive** and
`exp (A x)` can approach `log (B x)` from above. So the obligation carries that restriction rather
than quantifying over every pair:

```
EmlNodeSeparation :
  ∀ j, ∃ k, ∀ A B X₀,  A.depth ≤ j → B.depth ≤ j → 1 ≤ X₀ →
    (∀ x ≥ X₀, 0 < B.eval x) →                            -- the positive-B branch, and only it
    (∀ x ≥ X₀, 0 < exp (A.eval x) - log (B.eval x)) →      -- they do not meet
    ∃ X₁ ≥ X₀, ∀ x ≥ X₁, exp (-(towerFn k x)) ≤ exp (A.eval x) - log (B.eval x)
```

Same quantifier order as `DecayFloor`, same floor shape, `k` from the depth bound alone. Two germs
that **do not meet** on a ray are separated there by an effective envelope.

## It is an EQUIVALENCE, and saying so is the point

`decayFloor_of_emlNodeSeparation` and `emlNodeSeparation_of_decayFloor` are both proved, so this is a
**third name for one obligation**, not a shrink:

```
Sep j      ⟸  DecayFloor (j+1)        one node
DecayFloor j ⟸  Sep (j+3)             via posEmbed
```

The forward direction needs no induction at all — `(di)`'s `posEmbed` already re-embeds every tree
into a node whose right child is positive **everywhere**, so the restricted obligation reaches every
tree. Recording the equivalence rather than only the useful direction is what stops a later session
reading this as progress on difficulty. **It is not.**

What it *is*: the obligation restated in the idiom in which an external theorem could be cited. A
Hardy-field, o-minimal or Pfaffian separation result is a statement about two germs failing to meet;
it is not a statement about tower floors for shallow syntax trees. Until now nothing in the corpus
was shaped like the thing that would buy it.

## Stress cases, in §3

Shipped with the statement rather than after it, because an obligation nobody has attacked is an
obligation nobody has understood:

* **exact cancellation** — `B = eTree (eTree A)` makes the node identically `0`. The node-positivity
  hypothesis fails exactly there, which is the boundary the statement must have and does.
* **near-cancellation of two rapidly growing germs** — `gapNode n c` has `exp (A x)` and `log (B x)`
  both growing like an `(n+1)`-fold tower while their difference is the constant `c`. The floor
  needed is height `0` while the germs live at height `n+1`: **separation is not controlled by
  growth rate**, at any `n`.
* **the totalised-log branch** — excluded by hypothesis and covered by `decayFloor_clamped`; the two
  branches are exhaustive by `evSign_all`.
* **decaying germs** — `decayFast` tends to `0` and still meets the floor, which is the concrete
  reason the statement is an envelope and not a positive constant.

## Scope

**Bounds nothing, discharges nothing, assumes nothing.** No axiom is added, and the row enters the
ledger **open**. An external mathematical input is not automatically an axiom: until it is
deliberately accepted without proof it is simply an obligation nobody has discharged, and the ledger
now distinguishes those two states (`assumed` vs `open`, `(dm)`).
-/

namespace MachLib

open Real

/-! ## §1 — the obligation -/

/-- **The separation `DecayFloor` consumes, and nothing wider.**

`k` depends on the depth bound `j` alone — per pair it could be chosen after seeing the germs and
the statement would evaporate, exactly as for `DecayFloor` itself. -/
def EmlNodeSeparation : Prop :=
  ∀ j : Nat, ∃ k : Nat, ∀ (A B : EMLTree) (X₀ : Real),
    A.depth ≤ j → B.depth ≤ j → 1 ≤ X₀ →
    (∀ x : Real, X₀ ≤ x → 0 < B.eval x) →
    (∀ x : Real, X₀ ≤ x → 0 < exp (A.eval x) - log (B.eval x)) →
    ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
      exp (-(EMLTree.towerFn k x)) ≤ exp (A.eval x) - log (B.eval x)

/-! ## §2 — the reduction, both ways -/

/-- The right child `posEmbed` builds, named so the depth arithmetic can be stated once. -/
noncomputable def posEmbedRight (t : EMLTree) : EMLTree :=
  eTree (EMLTree.eml (EMLTree.const 0) (eTree t))

theorem posEmbedRight_depth (t : EMLTree) : (posEmbedRight t).depth = t.depth + 3 := by
  simp only [posEmbedRight, eTree, EMLTree.depth]
  omega

theorem posEmbed_eq (t : EMLTree) :
    posEmbed t = EMLTree.eml (EMLTree.const 0) (posEmbedRight t) := rfl

/-- **The separation buys `DecayFloor`, with no induction.** `(di)`'s `posEmbed` re-embeds every tree
into a node whose right child is positive *everywhere*, so the restricted obligation reaches every
tree — at `+3` depth, which is where the `j + 3` comes from. -/
theorem decayFloor_of_emlNodeSeparation (hS : EmlNodeSeparation) : DecayFloor := by
  intro j
  obtain ⟨k, hk⟩ := hS (j + 3)
  refine ⟨k, ?_⟩
  intro t X₀ hdepth hX₀ hpos
  have hA : (EMLTree.const 0).depth ≤ j + 3 := by simp only [EMLTree.depth]; omega
  have hB : (posEmbedRight t).depth ≤ j + 3 := by rw [posEmbedRight_depth]; omega
  have hBpos : ∀ x : Real, X₀ ≤ x → 0 < (posEmbedRight t).eval x :=
    fun x _ => posEmbed_right_pos t x
  have hnode : ∀ x : Real, X₀ ≤ x →
      0 < exp ((EMLTree.const 0).eval x) - log ((posEmbedRight t).eval x) := by
    intro x hx
    have e : exp ((EMLTree.const 0).eval x) - log ((posEmbedRight t).eval x)
        = (posEmbed t).eval x := rfl
    rw [e, posEmbed_eval]
    exact hpos x hx
  obtain ⟨X₁, hX₁, hfloor⟩ := hk (EMLTree.const 0) (posEmbedRight t) X₀ hA hB hX₀ hBpos hnode
  refine ⟨X₁, hX₁, ?_⟩
  refine floor_transfer_via_posEmbed t k X₁ ?_
  intro x hx
  have e : (posEmbed t).eval x
      = exp ((EMLTree.const 0).eval x) - log ((posEmbedRight t).eval x) := rfl
  rw [e]
  exact hfloor x hx

/-- **And `DecayFloor` buys the separation back**, one node up. Stated so that nobody reads the
forward direction as a reduction in difficulty: the two are the same obligation. -/
theorem emlNodeSeparation_of_decayFloor (hD : DecayFloor) : EmlNodeSeparation := by
  intro j
  obtain ⟨k, hk⟩ := hD (j + 1)
  refine ⟨k, ?_⟩
  intro A B X₀ hA hB hX₀ _ hnode
  have hd : (EMLTree.eml A B).depth ≤ j + 1 := by
    simp only [EMLTree.depth]
    have h : max A.depth B.depth ≤ j := Nat.max_le.mpr ⟨hA, hB⟩
    omega
  exact hk (EMLTree.eml A B) X₀ hd hX₀ hnode

/-- **One obligation, three names.** -/
theorem emlNodeSeparation_iff_decayFloor : EmlNodeSeparation ↔ DecayFloor :=
  ⟨decayFloor_of_emlNodeSeparation, emlNodeSeparation_of_decayFloor⟩

/-- The composition with `(dj)`, so the cycle is closed in the corpus and not only in the ledger. -/
theorem emlNodeSeparation_of_growthEnvelope (hG : GrowthEnvelope) : EmlNodeSeparation :=
  emlNodeSeparation_of_decayFloor (decayFloor_of_growthEnvelope hG)

/-! ## §3 — stress cases

An obligation nobody has attacked is an obligation nobody has understood, so these ship with the
statement rather than after it. Each one probes a place the statement could have been wrong. -/

/-- **Exact cancellation.** `B = eTree (eTree A)` makes `log (B x)` equal `exp (A x)` on the nose, so
the node is identically `0` — at every `A`, every `x`. The right child is an `exp`, hence positive
everywhere, so this pair *satisfies* the `B`-positivity hypothesis and fails only the node-positivity
one. That is precisely the boundary the statement must have: two EML germs **can** meet, and where
they meet no envelope exists, so the hypothesis is load-bearing and cannot be dropped. -/
theorem exact_cancellation_node_zero (A : EMLTree) (x : Real) :
    exp (A.eval x) - log ((eTree (eTree A)).eval x) = 0 := by
  rw [eTree_eval, log_exp, eTree_eval]
  mach_ring

theorem exact_cancellation_right_pos (A : EMLTree) (x : Real) :
    0 < (eTree (eTree A)).eval x := by
  rw [eTree_eval]; exact exp_pos _

/-- The right child of the near-cancellation pair: `exp (towerFn (n+1) x − c)`. -/
noncomputable def gapRight (n : Nat) (c : Real) : EMLTree :=
  eTree (EMLTree.eml (EMLTree.towerTree n) (EMLTree.const (exp c)))

theorem gapRight_pos (n : Nat) (c x : Real) : 0 < (gapRight n c).eval x := by
  rw [gapRight, eTree_eval]; exact exp_pos _

theorem gapRight_depth (n : Nat) (c : Real) : (gapRight n c).depth = n + 2 := by
  simp only [gapRight, eTree, EMLTree.depth, EMLTree.towerTree_depth]
  omega

/-- **Near-cancellation of two arbitrarily fast-growing germs.** With `A = towerTree n`, both
`exp (A x)` and `log (B x)` grow like an `(n+1)`-fold tower, and their difference is the constant
`c` — exactly, at every `x`, for every `n` and every `c`.

> The germs live at tower height `n + 1`; the floor their difference needs is height **0**.
> **Separation is not controlled by growth rate.**

That is the case a growth-based argument would be expected to handle and cannot even see, and it is
why `(dm)`'s germ-height parameter was never going to be the right instrument. -/
theorem gapNode_eval (n : Nat) (c x : Real) :
    exp ((EMLTree.towerTree n).eval x) - log ((gapRight n c).eval x) = c := by
  rw [gapRight, eTree_eval, log_exp]
  show exp ((EMLTree.towerTree n).eval x)
      - (exp ((EMLTree.towerTree n).eval x) - log (exp c)) = c
  rw [log_exp]; mach_ring

/-- The pair meets the floor at tower height `0`, at every `n` — the concrete form of the sentence
above. Stated at `c = 1` so the arithmetic is exact rather than a chase for `X₁`. -/
theorem gapNode_meets_floor (n : Nat) {x : Real} (hx : 0 ≤ x) :
    exp (-(EMLTree.towerFn 0 x))
      ≤ exp ((EMLTree.towerTree n).eval x) - log ((gapRight n 1).eval x) := by
  rw [gapNode_eval]
  show exp (-x) ≤ (1 : Real)
  have hz : exp (0 : Real) = 1 := exp_zero
  rw [← hz]
  refine exp_monotone ?_
  have u := neg_le_neg_wit hx
  have e : -(0 : Real) = 0 := by mach_ring
  rw [e] at u; exact u

/-- **A node that tends to zero and still meets the floor.** `posEmbed decayFast` is a
positive-`B` pair — its right child is an `exp`, positive *everywhere* — whose node is `exp (1 − x)`,
which has infimum `0` on the ray.

This is the concrete reason the obligation is an **envelope** and not a positive constant: read as
*"bounded away from zero"* the statement would be **false here**, on a member of its own class. -/
theorem decaying_node_eval (x : Real) :
    exp ((EMLTree.const 0).eval x) - log ((posEmbedRight decayFast).eval x) = exp (1 - x) := by
  have e : exp ((EMLTree.const 0).eval x) - log ((posEmbedRight decayFast).eval x)
      = (posEmbed decayFast).eval x := rfl
  rw [e, posEmbed_eval, decayFast_eval]

theorem decaying_node_meets_floor {x : Real} (hx : 1 ≤ x) :
    exp (-(EMLTree.towerFn 0 x))
      ≤ exp ((EMLTree.const 0).eval x) - log ((posEmbedRight decayFast).eval x) := by
  have e : exp ((EMLTree.const 0).eval x) - log ((posEmbedRight decayFast).eval x)
      = (posEmbed decayFast).eval x := rfl
  rw [e, posEmbed_eval]
  exact decayFast_floor x hx

/-- **The totalised-log branch, excluded by hypothesis and covered elsewhere.** A non-positive right
child makes the node `exp ∘ A`, which `decayFloor_clamped` already floors. Together with
`evSign_all` — every tree is eventually of one sign — the two branches are exhaustive, so the
restriction in `EmlNodeSeparation` loses nothing. -/
theorem clamped_node_is_exp (A B : EMLTree) (x : Real) (h : B.eval x ≤ 0) :
    exp (A.eval x) - log (B.eval x) = exp (A.eval x) := by
  rw [log_nonpos h]; mach_ring

end MachLib
