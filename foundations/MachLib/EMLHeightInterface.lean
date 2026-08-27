import MachLib.EMLGermApproach

/-!
# The height interface: which half of the problem is free, and which is all of it

The instruction was to stop attacking `DecayFloor` and instead build the smallest interface under
which it becomes almost automatic — a **height filtration**, closed under the operations the grammar
uses, in which subtraction stays inside its layer instead of escaping upward the way every syntactic
measure does (`EMLLadderMeasure`). Two lemmas were named:

```
(1)  EML depth  ⟹  bounded height
(2)  nonzero bounded-height germ  ⟹  leading-monomial floor
```

This file builds the interface, proves (1) **from the closure axioms alone**, states (2), and derives
`DecayFloor`. It also reports what the construction says about the split, which is not what the
framing predicts.

## The finding: (1) is free, and (2) is the whole problem

`HeightModel` asks for exactly the closure the reframing calls for — leaves cost `0`, `exp` costs at
most one, `log` costs nothing, and **subtraction stays in the layer**. From those four,

```
eh_le_depth :  M.eh t.eval ≤ t.depth
```

falls out by structural induction in four lines. That is lemma (1), unconditionally, for **every**
model. It is not an achievement of transseries; it is what "closed under subtraction, one per `exp`"
means.

**And the interface is inhabited by a model that makes lemma (1) vacuous**: `zeroModel`, height
identically `0`, satisfies every closure axiom. So the closure half **cannot** be where the content
is — it is satisfied by a height that distinguishes nothing.

The content is entirely in lemma (2), and `not_leadingMonomialFloor_zeroModel` proves that is not an
artifact of a badly chosen model: for the zero height the floor property is **outright false**, and
the refutation is a family `deepDecay m` of eventually-positive EML germs whose values fall below
`exp (−towerFn m x)` for every `m`.

> **The interface exposes a trade-off rather than a decomposition.** A *coarse* height makes (1)
> trivial and (2) false. A height as fine as `depth` makes (1) trivial and (2) *is* `DecayFloor`,
> circularly. What is wanted is the **coarsest germ-invariant height for which (2) is still true** —
> and *that*, not the closure, is what transseries theory would have to supply.

This is worth having even so, and it is why the file exists: it routes the question. Anyone who
brings a height function now has a mechanical check — satisfy four closure axioms, then prove the
floor — and the corpus will tell them immediately whether their model is too coarse.

## What is *not* claimed

No transseries were formalised, no embedding constructed, no axiom added. `M.eh` is an abstract
`Nat`-valued function on germs; nothing here says a transseries height exists, is germ-invariant, or
satisfies the floor. The germ-invariance that distinguishes a real height from `depth` is
deliberately **not** an axiom here — adding it would make the structure uninhabited by anything this
corpus can exhibit, and an uninstantiated abstraction is the failure mode this corpus has already
paid for once.
-/

namespace MachLib

open Real

/-! ## §1 — the interface -/

/-- **A height filtration on germs**, asking for exactly the closure the grammar uses.

Stated on germs (`Real → Real`) rather than on trees on purpose: a height that reads the *syntax*
is a tree measure, and `EMLLadderMeasure` already showed those cannot carry the induction. The
point of the reframing is a quantity that sees only the function. -/
structure HeightModel where
  /-- The height of a germ. -/
  eh : (Real → Real) → Nat
  /-- Constants are at the bottom. -/
  eh_const : ∀ c : Real, eh (fun _ => c) = 0
  /-- So is the variable. -/
  eh_id : eh (fun x => x) = 0
  /-- **Subtraction stays inside the layer.** This is the axiom the whole reframing turns on, and
  the one no tree measure satisfies. -/
  eh_sub : ∀ f g : Real → Real, eh (fun x => f x - g x) ≤ Nat.max (eh f) (eh g)
  /-- `exp` costs at most one level. -/
  eh_exp : ∀ f : Real → Real, eh (fun x => exp (f x)) ≤ eh f + 1
  /-- `log` costs nothing. -/
  eh_log : ∀ f : Real → Real, eh (fun x => log (f x)) ≤ eh f

/-! ## §2 — lemma (1), free from the closure axioms -/

/-- **EML depth bounds height, in every model.** Four lines of structural induction: an `eml` node is
one `exp`, one `log` and one subtraction, so it costs at most one level over the worse child.

This is the lemma the reframing hoped transseries would supply. It needs no transseries — it is what
the closure axioms *say*. -/
theorem HeightModel.eh_le_depth (M : HeightModel) : ∀ t : EMLTree, M.eh t.eval ≤ t.depth := by
  intro t
  induction t with
  | const c =>
      show M.eh (fun _ => c) ≤ 0
      rw [M.eh_const c]
      omega
  | var =>
      show M.eh (fun x => x) ≤ 0
      rw [M.eh_id]
      omega
  | eml A B ihA ihB =>
      have hA1 : A.depth ≤ Nat.max A.depth B.depth := Nat.le_max_left _ _
      have hB1 : B.depth ≤ Nat.max A.depth B.depth := Nat.le_max_right _ _
      have hsub := M.eh_sub (fun x => exp (A.eval x)) (fun x => log (B.eval x))
      have hexp := M.eh_exp A.eval
      have hlog := M.eh_log B.eval
      have hmaxle : Nat.max (M.eh (fun x => exp (A.eval x))) (M.eh (fun x => log (B.eval x)))
          ≤ 1 + Nat.max A.depth B.depth :=
        Nat.max_le.mpr ⟨by omega, by omega⟩
      show M.eh (fun x => exp (A.eval x) - log (B.eval x)) ≤ 1 + Nat.max A.depth B.depth
      exact Nat.le_trans hsub hmaxle

/-! ## §3 — lemma (2), which is all of it -/

/-- **The leading-monomial floor**: a bounded-height germ that stays positive on a ray has an
effective tower floor whose height depends on the height bound alone.

This is the transseries statement — "a nonzero transseries has a dominant term, and the germ is
eventually of that order" — transported to the corpus's vocabulary. It is **not proved anywhere**. -/
def LeadingMonomialFloor (M : HeightModel) : Prop :=
  ∀ k : Nat, ∃ m : Nat, ∀ (t : EMLTree) (X₀ : Real),
    M.eh t.eval ≤ k → 1 ≤ X₀ → (∀ x : Real, X₀ ≤ x → 0 < t.eval x) →
    ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
      exp (-(EMLTree.towerFn m x)) ≤ t.eval x

/-- **The payoff: the two lemmas give `DecayFloor`.** Lemma (1) puts a depth-`j` tree at height `≤ j`;
lemma (2) hands back a floor from the height bound alone. No induction on the tree anywhere. -/
theorem decayFloor_of_heightModel (M : HeightModel) (h : LeadingMonomialFloor M) : DecayFloor := by
  intro j
  obtain ⟨m, hm⟩ := h j
  refine ⟨m, ?_⟩
  intro t X₀ hdepth hX₀ hpos
  exact hm t X₀ (Nat.le_trans (M.eh_le_depth t) hdepth) hX₀ hpos

/-- And therefore the approach obligation, through `(do)`'s equivalence. -/
theorem emlGermApproach_of_heightModel (M : HeightModel) (h : LeadingMonomialFloor M) :
    EmlGermApproach :=
  emlGermApproach_of_decayFloor (decayFloor_of_heightModel M h)

/-! ## §4 — the closure half is free, and the floor half is not

Both halves of the finding, as theorems rather than as prose. -/

/-- **The interface is inhabited** — by a height that distinguishes nothing. Every closure axiom
holds for the constant `0`, so satisfying them is no evidence of anything. -/
def zeroModel : HeightModel where
  eh := fun _ => 0
  eh_const := fun _ => rfl
  eh_id := rfl
  eh_sub := fun _ _ => Nat.zero_le _
  eh_exp := fun _ => Nat.zero_le _
  eh_log := fun _ => Nat.zero_le _

/-- A germ that decays faster than `exp (−towerFn m x)`: `exp (1 − towerFn (m+1) x)`. -/
noncomputable def deepDecay (m : Nat) : EMLTree :=
  eTree (EMLTree.eml (EMLTree.const 0) (eTree (EMLTree.towerTree (m + 1))))

theorem deepDecay_eval (m : Nat) (x : Real) :
    (deepDecay m).eval x = exp (1 - EMLTree.towerFn (m + 1) x) := by
  rw [deepDecay, eTree_eval]
  show exp (exp ((0 : Real)) - log ((eTree (EMLTree.towerTree (m + 1))).eval x)) = _
  rw [exp_zero, eTree_eval, EMLTree.towerTree_eval, log_exp]

theorem deepDecay_pos (m : Nat) (x : Real) : 0 < (deepDecay m).eval x := by
  rw [deepDecay_eval]; exact exp_pos _

/-- **The floor property is not free.** For every `m` this germ is eventually positive and falls
*below* `exp (−towerFn m x)`, so no single tower height serves every EML germ. -/
theorem deepDecay_below_floor (m : Nat) {x : Real} (hx : 1 ≤ x) :
    (deepDecay m).eval x < exp (-(EMLTree.towerFn m x)) := by
  rw [deepDecay_eval]
  refine exp_lt ?_
  have h1 : 1 ≤ EMLTree.towerFn m x := towerFn_ge_one m hx
  have h0 : 0 < EMLTree.towerFn m x := lt_of_lt_of_le zero_lt_one_ax h1
  have hstep : 1 + EMLTree.towerFn m x < exp (EMLTree.towerFn m x) :=
    exp_gt_one_plus_self _ h0
  have hT : EMLTree.towerFn (m + 1) x = exp (EMLTree.towerFn m x) := rfl
  rw [hT]
  have u := add_lt_add_left hstep (-(EMLTree.towerFn m x) - 1)
  have e1 : -(EMLTree.towerFn m x) - 1 + (1 + EMLTree.towerFn m x) = 0 := by mach_ring
  have e2 : -(EMLTree.towerFn m x) - 1 + exp (EMLTree.towerFn m x)
      = exp (EMLTree.towerFn m x) - 1 - EMLTree.towerFn m x := by mach_ring
  rw [e1, e2] at u
  -- 0 < exp T - 1 - T,  i.e.  1 - exp T < -T
  have v := add_lt_add_left u (1 - exp (EMLTree.towerFn m x))
  have e3 : 1 - exp (EMLTree.towerFn m x) + 0 = 1 - exp (EMLTree.towerFn m x) := by mach_ring
  have e4 : 1 - exp (EMLTree.towerFn m x)
      + (exp (EMLTree.towerFn m x) - 1 - EMLTree.towerFn m x)
      = -(EMLTree.towerFn m x) := by mach_ring
  rw [e3, e4] at v
  exact v

/-- **So the closure axioms alone prove nothing.** `zeroModel` satisfies every one of them and
refutes the floor outright: `LeadingMonomialFloor` is false for it, because one tower height would
have to serve every EML germ and `deepDecay` outruns each in turn.

The reframing's lemma (1) is therefore *free*, and the entire difficulty sits in lemma (2). -/
theorem not_leadingMonomialFloor_zeroModel : ¬ LeadingMonomialFloor zeroModel := by
  intro h
  obtain ⟨m, hm⟩ := h 0
  obtain ⟨X₁, hX₁, hfloor⟩ :=
    hm (deepDecay m) 1 (Nat.le_refl 0) (le_refl 1) (fun x _ => deepDecay_pos m x)
  have hx : (1 : Real) ≤ X₁ := hX₁
  have hle := hfloor X₁ (le_refl X₁)
  have hlt := deepDecay_below_floor m hx
  exact (ne_of_lt (lt_of_lt_of_le hlt hle)) rfl

/-! ## §5 — how fast must the height grow? Pinned, by proof rather than by search

The counterexample machine was to enumerate small trees and measure *(depth, exp count, log count,
leading-monomial height)* to decide whether the conjecture should be `h ≤ d`, `h ≤ 2d`, or something
subtler. `deepDecay` answers that directly and exactly, so the search is not needed.

`deepDecay m` has depth **`m + 4`** on the nose and falls below the height-`m` floor. So:

```
eh_le_depth               height ≤ depth                     (every model, §2)
height_m_fails_at_depth_m_add_four   height m FAILS at depth m + 4
```

> **The required tower height is at most `d` and at least `d − 3`.** It is `d` up to an additive
> constant — not `2d`, not `log d`, and certainly not bounded.

Two consequences worth carrying. The obligation is *not* asking for a bounded height, so any attempt
that hopes to find one is misreading it. And the slope is `1`: **one `eml` node buys exactly one
tower level of decay, in the worst case** — the same exchange rate `(dj)` found for growth, which is
what one would expect if `DecayFloor` and `GrowthEnvelope` really are one obligation, and is a small
independent check that they are.

The three-node gap between `d − 3` and `d` is the cost of the wrapper `deepDecay` needs to make its
right child positive — the same `+3`/`+4` constants that `posEmbed` and `approachTarget` pay. It is
an artifact of the encoding, not of the mathematics. -/

theorem deepDecay_depth (m : Nat) : (deepDecay m).depth = m + 4 := by
  simp only [deepDecay, eTree, EMLTree.depth, EMLTree.towerTree_depth]
  omega

/-- **Height `m` fails at depth `m + 4`**, for every `m`. So the tower height any proof of
`DecayFloor` produces must grow with the depth bound — at least like `depth − 3`. -/
theorem height_m_fails_at_depth_m_add_four (m : Nat) :
    ¬ (∀ (t : EMLTree) (X₀ : Real), t.depth ≤ m + 4 → 1 ≤ X₀ →
        (∀ x : Real, X₀ ≤ x → 0 < t.eval x) →
        ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
          exp (-(EMLTree.towerFn m x)) ≤ t.eval x) := by
  intro h
  obtain ⟨X₁, hX₁, hfloor⟩ :=
    h (deepDecay m) 1 (Nat.le_of_eq (deepDecay_depth m)) (le_refl 1) (fun x _ => deepDecay_pos m x)
  exact (ne_of_lt (lt_of_lt_of_le (deepDecay_below_floor m hX₁) (hfloor X₁ (le_refl X₁)))) rfl

/-! ## §6 — the bracket as a theorem, at both ends

`§5` gives the growth rate as two one-sided facts. This makes them a single bracket on a bounded
form, in the idiom the corpus already uses for `TowerLowerBoundUpTo`.

```
decayFloorUpTo_two          depth ≤ 2  is DISCHARGED, at height 0 — which is optimal, 0 being least
decayFloorUpTo_height_ge    depth ≤ m+4 forces height ≥ m + 1
```

So the required height is **`0` for `d ≤ 2`, and at least `d − 3` thereafter**, with `d` as the
standing upper bound from `eh_le_depth`. Every witness the corpus has sits on the lower edge:
`decayFast` (depth 3, height 0), `decayFaster` (depth 4, height 1), `deepDecay m` (depth `m+4`,
height `m+1`). **The conjecture the data supports is `max (0, d − 3)`, exactly** — and the three-node
offset is the positive-right-child wrapper, not mathematics.

Nothing here proves the upper half at any `d ≥ 3`; that is `DecayFloor` and remains open. What the
bracket buys is a **falsifiable target**: a proposed floor construction that produces height `2d`, or
`d`, is not merely unsharp — it is above a boundary the corpus can now name. -/

/-- `towerFn` is non-decreasing in height on the ray, one step. -/
theorem towerFn_le_succ (n : Nat) {x : Real} (hx : 1 ≤ x) :
    EMLTree.towerFn n x ≤ EMLTree.towerFn (n + 1) x := by
  have _ := towerFn_ge_one n hx
  exact le_of_lt (exp_grows_strictly_thm _)

/-- …and hence in height generally. -/
theorem towerFn_mono (a : Nat) : ∀ (d : Nat) {x : Real}, 1 ≤ x →
    EMLTree.towerFn a x ≤ EMLTree.towerFn (a + d) x := by
  intro d
  induction d with
  | zero => intro x _; exact le_refl _
  | succ n ih =>
      intro x hx
      have e : a + (n + 1) = a + n + 1 := by omega
      rw [e]
      exact le_trans (ih hx) (towerFn_le_succ (a + n) hx)

/-- **`DecayFloor` bounded by depth**, the corpus's usual device for committing the proved part of an
open obligation. -/
def DecayFloorUpTo (N : Nat) : Prop :=
  ∀ j : Nat, j ≤ N → ∃ k : Nat, ∀ (t : EMLTree) (X₀ : Real), t.depth ≤ j → 1 ≤ X₀ →
    (∀ x : Real, X₀ ≤ x → 0 < t.eval x) →
    ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
      exp (-(EMLTree.towerFn k x)) ≤ t.eval x

/-- **Depth ≤ 2 is discharged, at height `0`** — and `0` is optimal because it is least. This is the
one end of the bracket that is a theorem rather than a bound. -/
theorem decayFloorUpTo_two : DecayFloorUpTo 2 := by
  intro j hj
  refine ⟨0, ?_⟩
  intro t X₀ hd hX₀ hpos
  exact decayFloor_upTo_two t X₀ (Nat.le_trans hd hj) hX₀ hpos

/-- **The other end: depth `m + 4` forces height `≥ m + 1`.** A height `k ≤ m` would give a height-`m`
floor by monotonicity of `towerFn`, and `deepDecay m` refutes that. -/
theorem decayFloorUpTo_height_ge (m : Nat) (k : Nat)
    (hk : ∀ (t : EMLTree) (X₀ : Real), t.depth ≤ m + 4 → 1 ≤ X₀ →
      (∀ x : Real, X₀ ≤ x → 0 < t.eval x) →
      ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
        exp (-(EMLTree.towerFn k x)) ≤ t.eval x) :
    m + 1 ≤ k := by
  -- `by_contra` does not exist here; `rcases Nat.lt_or_ge` is the local idiom.
  rcases Nat.lt_or_ge m k with hlt | hkm
  · omega
  refine absurd ?_ (height_m_fails_at_depth_m_add_four m)
  intro t X₀ hd hX₀ hpos
  obtain ⟨X₁, hX₁, hf⟩ := hk t X₀ hd hX₀ hpos
  refine ⟨X₁, hX₁, fun x hx => ?_⟩
  have hx1 : (1 : Real) ≤ x := le_trans hX₀ (le_trans hX₁ hx)
  have hmono : EMLTree.towerFn k x ≤ EMLTree.towerFn m x := by
    have e : k + (m - k) = m := by omega
    have h := towerFn_mono k (m - k) hx1
    rw [e] at h; exact h
  have hneg : -(EMLTree.towerFn m x) ≤ -(EMLTree.towerFn k x) := neg_le_neg_wit hmono
  exact le_trans (exp_monotone hneg) (hf x hx)

end MachLib
