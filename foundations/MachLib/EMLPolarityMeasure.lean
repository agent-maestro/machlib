import MachLib.EMLHeightVsDepth
import MachLib.LexProd

/-!
# Polarity and vector measures — and the obstruction at WELL-FOUNDED width

`EMLLadderMeasure` closes the ladder's induction search for `Nat`-valued measures, and states its
own residual carefully: *lexicographic orders, ordinal ranks and well-founded relations are
untouched.* `EmlGermApproachResearch.md` §5 lists the two candidates that residual invites —
a **vector** measure `(exp-height, log-depth, alternation, size)`, and a **polarity-aware** measure
treating the `exp` side differently from the `log` side, since `§4`'s germ route fails
*specifically on the right child* (`tower_height_does_not_descend_right`).

Both are built here, evaluated against every adversarial family in §3, and both die. The
interesting part is *where* and *why*.

## The escape is real

The polarity pair `(ehTree, ldTree)` is, as far as this corpus knows, the **first measure that
strictly descends to both children** (`pol_left`, `pol_right`). On the right child the `exp`
component may tie — it does on `capNode`, with a gap of exactly zero, which is what
`ehTree_not_right_le` records — and `ldTree` breaks the tie, unconditionally. It is genuinely
outside `§4`'s class: `no_nat_collapse` proves no `Nat`-valued function is strictly monotone for
this order, so `LadderMeasure.ofStrictDescent` cannot reach it. And on the construction that costs
every syntactic scalar measure two steps, the `exp` component pays **one**:
`eh_recipTree_of_one_le`. That is exactly the escape §5(2) predicted.

## And it is not enough, for a reason that has nothing to do with `Nat`

`recipTree = eTree ∘ negLogTree` (`recip_eq_eTree_negLog`): one `exp` node and one `log` node. The
cost is **relocated, not reduced** — both components rise by one.

Stated at its real width, for **every** measure into **every** well-founded order that descends to
both children (`WfDescent`, which contains `LadderMeasure` via `ofLadderMeasure` and the polarity
pair via `polDescent`):

```
recip_not_below :  ¬ R (μ (recipTree t)) (μ t)          the reciprocal is two strict steps up
recip_ne        :    μ (recipTree t) ≠ μ t
posEmbed_not_below : the positive-branch re-embedding is four strict steps up
```

The proofs use **only well-foundedness** — three rotate-the-cycle lemmas, `no_cycle2/3/5`. There is
no step arithmetic anywhere. So `§4(1)`'s *"`recipTree` costs `2 · step` while a rung buys
`1 · step`"* was the shadow of something simpler: the transfer travels **up**, and a well-founded
order has nothing to say against that whatever its order type. Lexicographic orders, vectors and
ordinal ranks are ruled out by the same three lines as `Nat`.

The polarity idea in its strongest form — a measure carrying a **polarity bit the `log` edge
flips**, which is the bit the ladder's own recursion carries, since a floor for
`exp (A x) − log (B x)` needs a *lower* bound on the left child and an *upper* bound on the right —
fails identically, at the flipped polarity (`PolWfDescent`, `pol_recip_not_below`).

## What this does NOT close

A single well-founded order descending to both children. **Not**: a mutual induction over
`(tree, polarity)` pairs with *different* relations per polarity; a measure descending on one side
only, with the other side carried by a different argument; a well-founded relation on **germs**
rather than a function of them; anything non-structural. The plain ladder
(`decayFloor_of_ladderInputs`) is in the first of those classes already — it is a structural
induction on the depth bound and needs no measure at all, which is why a better measure cannot
help it: its residue is `NodeDecayBound`, not a parameter.

## Two facts a future session should not re-derive

* **The reindexing is bookkeeping, both ways.** `ehTree, ldTree ≤ depth ≤ ehTree + ldTree`
  (`reindexing_is_two_way`), so *"`k` from the depth bound alone"* and *"`k` from the polarity pair
  alone"* are the same statement. Per `EmlGermApproachResearch.md` §9 that is not progress.
* **`k` cannot come from the `log` component.** `deepDecay m` forces the floor height to `m + 1`
  while its `ldTree` stays flat at `2` for every `m` (`pol_deepDecay`,
  `deepDecay_forces_first_component`).

## Scope

**Bounds nothing, discharges nothing, assumes nothing.** No axiom; the `DecayFloor` ⇄
`EmlGermApproach` ⇄ `GrowthEnvelope` row stays open. This is a route-closure and a fixture set, in
the sense §3 uses the word: each family below is measured once, here, so that the next candidate is
tested rather than argued about.
-/

namespace MachLib

namespace EMLTree

/-- **Syntactic log-depth**, the exact dual of `ehTree`: a `log` (right) edge costs one level, an
`exp` (left) edge costs nothing. Where `ehTree` is the greatest number of left edges on a
root-to-leaf path, this is the greatest number of right edges. -/
def ldTree : EMLTree → Nat
  | const _   => 0
  | var       => 0
  | eml A B   => Nat.max A.ldTree (B.ldTree + 1)

/-- **Alternation**: the greatest number of direction changes along a root-to-leaf path, given the
direction of the edge that entered the subtree (`true` = entered on a left/`exp` edge). The third
component of the vector candidate. -/
def altFrom : Bool → EMLTree → Nat
  | _, const _ => 0
  | _, var     => 0
  | d, eml A B =>
      Nat.max ((if d then 0 else 1) + altFrom true A) ((if d then 1 else 0) + altFrom false B)

/-- The alternation of a tree, at either incoming polarity. -/
def altTree (t : EMLTree) : Nat := Nat.max (altFrom true t) (altFrom false t)

theorem ldTree_eml (A B : EMLTree) : (eml A B).ldTree = Nat.max A.ldTree (B.ldTree + 1) := rfl

/-- **Log-depth descends to the RIGHT child**, by one, always — the mirror of `ehTree_left_le`, and
the step every measure in `EmlGermApproachResearch.md` §4 fails. -/
theorem ldTree_right_lt (A B : EMLTree) : B.ldTree < (eml A B).ldTree := by
  rw [ldTree_eml]
  have h : B.ldTree + 1 ≤ Nat.max A.ldTree (B.ldTree + 1) := Nat.le_max_right _ _
  omega

theorem ldTree_left_le (A B : EMLTree) : A.ldTree ≤ (eml A B).ldTree := by
  rw [ldTree_eml]; exact Nat.le_max_left _ _

theorem ehTree_eml (A B : EMLTree) : (eml A B).ehTree = Nat.max (A.ehTree + 1) B.ehTree := rfl

/-- `ehTree` does not *descend* to the right child, but it never rises past the node either. That
non-strict half is what lets the pair below tie in the first component and break in the second. -/
theorem ehTree_right_le (A B : EMLTree) : B.ehTree ≤ (eml A B).ehTree := by
  rw [ehTree_eml]; exact Nat.le_max_right _ _

theorem ldTree_le_depth : ∀ t : EMLTree, t.ldTree ≤ t.depth := by
  intro t
  induction t with
  | const c => exact Nat.le_refl 0
  | var     => exact Nat.le_refl 0
  | eml A B ihA ihB =>
      have hA : A.depth ≤ Nat.max A.depth B.depth := Nat.le_max_left _ _
      have hB : B.depth ≤ Nat.max A.depth B.depth := Nat.le_max_right _ _
      show Nat.max A.ldTree (B.ldTree + 1) ≤ 1 + Nat.max A.depth B.depth
      exact Nat.max_le.mpr ⟨by omega, by omega⟩

/-- **Depth is bounded by the pair.** Every root-to-leaf path carries at most `ehTree` left edges
and at most `ldTree` right edges, so it has at most `ehTree + ldTree` edges in all. -/
theorem depth_le_eh_add_ld : ∀ t : EMLTree, t.depth ≤ t.ehTree + t.ldTree := by
  intro t
  induction t with
  | const c => exact Nat.le_refl 0
  | var     => exact Nat.le_refl 0
  | eml A B ihA ihB =>
      have h1 : A.ehTree + 1 ≤ (eml A B).ehTree := ehTree_left_le A B
      have h2 : B.ehTree ≤ (eml A B).ehTree := ehTree_right_le A B
      have h3 : A.ldTree ≤ (eml A B).ldTree := ldTree_left_le A B
      have h4 : B.ldTree + 1 ≤ (eml A B).ldTree := ldTree_right_lt A B
      show 1 + Nat.max A.depth B.depth ≤ (eml A B).ehTree + (eml A B).ldTree
      rcases Nat.le_total A.depth B.depth with h | h
      · have he : Nat.max A.depth B.depth = B.depth :=
          Nat.le_antisymm (Nat.max_le.mpr ⟨h, Nat.le_refl _⟩) (Nat.le_max_right _ _)
        rw [he]; omega
      · have he : Nat.max A.depth B.depth = A.depth :=
          Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.le_refl _, h⟩) (Nat.le_max_left _ _)
        rw [he]; omega

end EMLTree

open MachLib.LexProd

/-! ## §1 — the two candidates -/

/-- **Candidate 2 — the polarity-aware measure.** `exp`-height for the left/`exp` side,
`log`-depth for the right/`log` side, compared lexicographically. -/
def polMeasure (t : EMLTree) : Nat × Nat := (t.ehTree, t.ldTree)

def polLt : Nat × Nat → Nat × Nat → Prop := lexProd (· < ·) (· < ·)

theorem polLt_wf : WellFounded polLt := natPairLex_wf

/-- **Candidate 1 — the vector measure** `(exp-height, log-depth, alternation, size)`, under the
same lexicographic order one level deeper. -/
def vecMeasure (t : EMLTree) : Nat × (Nat × (Nat × Nat)) :=
  (t.ehTree, (t.ldTree, (t.altTree, t.size)))

def vecLt : Nat × (Nat × (Nat × Nat)) → Nat × (Nat × (Nat × Nat)) → Prop :=
  lexProd (· < ·) (lexProd (· < ·) (lexProd (· < ·) (· < ·)))

theorem vecLt_wf : WellFounded vecLt := natQuadLex_wf

/-! ## §2 — both candidates strictly descend to BOTH children -/

/-- **Descent to the left child**, in the `exp` component, always. -/
theorem pol_left (A B : EMLTree) : polLt (polMeasure A) (polMeasure (EMLTree.eml A B)) := by
  refine Or.inl ?_
  show A.ehTree < (EMLTree.eml A B).ehTree
  have h : A.ehTree + 1 ≤ (EMLTree.eml A B).ehTree := EMLTree.ehTree_left_le A B
  omega

/-- **…and to the right child.** The `exp` component may tie — on `capNode` it does, with a gap of
exactly zero — and the `log` component then breaks the tie, unconditionally. This is the step the
germ-growth measure fails at, and fails at unboundedly
(`tower_height_does_not_descend_right`). -/
theorem pol_right (A B : EMLTree) : polLt (polMeasure B) (polMeasure (EMLTree.eml A B)) := by
  have hle : B.ehTree ≤ (EMLTree.eml A B).ehTree := EMLTree.ehTree_right_le A B
  rcases Nat.lt_or_ge B.ehTree (EMLTree.eml A B).ehTree with h | h
  · exact Or.inl h
  · exact Or.inr ⟨by show B.ehTree = (EMLTree.eml A B).ehTree; omega, EMLTree.ldTree_right_lt A B⟩

/-- **The vector's last two components are never consulted.** Every polarity descent lifts to a
vector descent, because the lexicographic comparison is already decided by the first two — the
`exp` component drops on the left and the `log` component drops on the right, both
unconditionally. Alternation and size change no verdict in this file, and the two candidates
therefore stand or fall together. -/
theorem vec_of_pol {s t : EMLTree} (h : polLt (polMeasure s) (polMeasure t)) :
    vecLt (vecMeasure s) (vecMeasure t) := by
  rcases h with h1 | ⟨heq, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨heq, Or.inl h2⟩

theorem vec_left (A B : EMLTree) : vecLt (vecMeasure A) (vecMeasure (EMLTree.eml A B)) :=
  vec_of_pol (pol_left A B)

theorem vec_right (A B : EMLTree) : vecLt (vecMeasure B) (vecMeasure (EMLTree.eml A B)) :=
  vec_of_pol (pol_right A B)

/-! ## §3 — the candidates are NOT `Nat`-valued, so `ofStrictDescent` does not reach them

`EMLLadderMeasure` §3 is the reason a new candidate has to clear this bar: *any* `Nat`-valued
measure descending to both children **is** a `LadderMeasure` with `step = 1`, definitionally. The
polarity order is not `Nat`, and this says so by proof rather than by inspection. -/

/-- A right spine `1 − log (1 − log (… x))`: `exp`-height `1`, `log`-depth `n`. -/
noncomputable def rightSpine : Nat → EMLTree
  | 0     => EMLTree.var
  | n + 1 => EMLTree.eml (EMLTree.const 0) (rightSpine n)

theorem rightSpine_eh_le (n : Nat) : (rightSpine n).ehTree ≤ 1 := by
  induction n with
  | zero => show (0 : Nat) ≤ 1; omega
  | succ k ih =>
      show Nat.max ((EMLTree.const 0).ehTree + 1) (rightSpine k).ehTree ≤ 1
      exact Nat.max_le.mpr ⟨by show (0 : Nat) + 1 ≤ 1; omega, ih⟩

theorem rightSpine_eh (n : Nat) : (rightSpine (n + 1)).ehTree = 1 := by
  show Nat.max ((EMLTree.const 0).ehTree + 1) (rightSpine n).ehTree = 1
  exact Nat.le_antisymm
    (Nat.max_le.mpr ⟨by show (0 : Nat) + 1 ≤ 1; omega, rightSpine_eh_le n⟩)
    (Nat.le_max_left _ _)

theorem rightSpine_ld (n : Nat) : (rightSpine n).ldTree = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show Nat.max (EMLTree.const 0).ldTree ((rightSpine k).ldTree + 1) = k + 1
      rw [ih]
      exact Nat.le_antisymm
        (Nat.max_le.mpr ⟨by show (0 : Nat) ≤ k + 1; omega, Nat.le_refl _⟩)
        (Nat.le_max_right _ _)

theorem pol_rightSpine (n : Nat) : polMeasure (rightSpine (n + 1)) = (1, n + 1) := by
  show ((rightSpine (n + 1)).ehTree, (rightSpine (n + 1)).ldTree) = (1, n + 1)
  rw [rightSpine_eh n, rightSpine_ld (n + 1)]

/-- **The polarity order does not collapse to `Nat`.** No `Nat`-valued function is strictly
monotone for `polLt`: the `(1, ·)` column is an infinite chain below `(2, 0)`, so a collapse would
need infinitely many naturals strictly below one. The candidate is therefore genuinely outside the
class `LadderMeasure.ofStrictDescent` covers. -/
theorem no_nat_collapse : ¬ ∃ f : Nat × Nat → Nat, ∀ p q, polLt p q → f p < f q := by
  rintro ⟨f, hf⟩
  have step : ∀ l : Nat, l ≤ f (1, l) := by
    intro l
    induction l with
    | zero => omega
    | succ n ih =>
        have h := hf (1, n) (1, n + 1) (Or.inr ⟨rfl, by omega⟩)
        omega
  have hkey := hf (1, f (2, 0)) (2, 0) (Or.inl (by omega))
  have h2 := step (f (2, 0))
  omega

/-- …and the infinite chain is realised by actual EML trees rather than only in the abstract order:
every right spine sits strictly below `exp (exp x)`. -/
theorem rightSpine_below_eTree (n : Nat) :
    polLt (polMeasure (rightSpine (n + 1))) (polMeasure (eTree (eTree EMLTree.var))) := by
  refine Or.inl ?_
  rw [pol_rightSpine n]
  show (1 : Nat) < (eTree (eTree EMLTree.var)).ehTree
  have h : (eTree (eTree EMLTree.var)).ehTree = 2 := rfl
  omega

/-! ## §4 — the obstruction, at the width of ARBITRARY well-founded orders -/

/-- **A measure into an arbitrary well-founded order, descending to both children** — the class
`EMLLadderMeasure` names as untouched. `LadderMeasure` embeds in it (`ofLadderMeasure`) and so does
the polarity candidate (`polDescent`), which `no_nat_collapse` shows `LadderMeasure` does not. -/
structure WfDescent where
  /-- The order the measure lands in. -/
  W : Type
  /-- The measure. -/
  μ : EMLTree → W
  /-- The strict order. -/
  R : W → W → Prop
  /-- …which is well-founded, so it supports an induction. -/
  wf : WellFounded R
  /-- An `eml` node is strictly above its left child. -/
  left_lt : ∀ A B : EMLTree, R (μ A) (μ (EMLTree.eml A B))
  /-- …and strictly above its right child. -/
  right_lt : ∀ A B : EMLTree, R (μ B) (μ (EMLTree.eml A B))

/-- A well-founded relation has no 2-cycle. Proved by rotating the cycle into the inductive
hypothesis — `by_contra` does not exist here and is not needed. -/
theorem no_cycle2 {W : Type} {R : W → W → Prop} (hwf : WellFounded R) :
    ∀ a b : W, R a b → R b a → False := by
  intro a
  refine hwf.induction (C := fun a => ∀ b, R a b → R b a → False) a ?_
  intro x ih b hxb hbx
  exact ih b hbx x hbx hxb

/-- …nor a 3-cycle. -/
theorem no_cycle3 {W : Type} {R : W → W → Prop} (hwf : WellFounded R) :
    ∀ a b c : W, R a b → R b c → R c a → False := by
  intro a
  refine hwf.induction (C := fun a => ∀ b c, R a b → R b c → R c a → False) a ?_
  intro x ih b c hxb hbc hcx
  exact ih c hcx x b hcx hxb hbc

/-- …nor a 5-cycle, which is what the four-node re-embedding needs. -/
theorem no_cycle5 {W : Type} {R : W → W → Prop} (hwf : WellFounded R) :
    ∀ a b c d e : W, R a b → R b c → R c d → R d e → R e a → False := by
  intro a
  refine hwf.induction
    (C := fun a => ∀ b c d e, R a b → R b c → R c d → R d e → R e a → False) a ?_
  intro x ih b c d e hxb hbc hcd hde hex
  exact ih e hex x b c d hex hxb hbc hcd hde

/-- **Every `LadderMeasure` is a `WfDescent`**: the new class contains the old one, so what follows
re-proves `recip_not_at_one_step` as a special case rather than replacing it. -/
def ofLadderMeasure (m : LadderMeasure) : WfDescent where
  W := Nat
  μ := m.μ
  R := (· < ·)
  wf := Nat.lt_wfRel.wf
  left_lt := fun A B => by have := m.left_le A B; have := m.step_pos; omega
  right_lt := fun A B => by have := m.right_le A B; have := m.step_pos; omega

/-- **…and the polarity candidate is one too**, so the class is strictly larger — the theorems
below are not about an empty extension. -/
def polDescent : WfDescent where
  W := Nat × Nat
  μ := polMeasure
  R := polLt
  wf := polLt_wf
  left_lt := pol_left
  right_lt := pol_right

/-- The vector candidate, likewise. -/
def vecDescent : WfDescent where
  W := Nat × (Nat × (Nat × Nat))
  μ := vecMeasure
  R := vecLt
  wf := vecLt_wf
  left_lt := vec_left
  right_lt := vec_right

/-- **The reciprocal is two strict steps up, in every such order**: one `log` edge into
`negLogTree`, one `exp` edge out of it. -/
theorem recip_two_steps (m : WfDescent) (t : EMLTree) :
    m.R (m.μ t) (m.μ (negLogTree t)) ∧ m.R (m.μ (negLogTree t)) (m.μ (recipTree t)) :=
  ⟨m.right_lt (EMLTree.const 0) t, m.left_lt (negLogTree t) (EMLTree.const 1)⟩

/-- **…and therefore never at or below the tree's own level.** This is `recip_not_at_one_step` with
the `Nat` step arithmetic removed. What forbids the reciprocal transfer is the **direction of
travel**, not the number `2`: a well-founded order has nothing to say against a construction that
moves up, whatever its order type. -/
theorem recip_not_below (m : WfDescent) (t : EMLTree) :
    ¬ m.R (m.μ (recipTree t)) (m.μ t) := by
  intro h
  obtain ⟨h1, h2⟩ := recip_two_steps m t
  exact no_cycle3 m.wf _ _ _ h1 h2 h

theorem recip_ne (m : WfDescent) (t : EMLTree) : m.μ (recipTree t) ≠ m.μ t := by
  intro h
  obtain ⟨h1, h2⟩ := recip_two_steps m t
  rw [h] at h2
  exact no_cycle2 m.wf _ _ h1 h2

/-- **The escape route, closed at the new width.** A measure pricing the reciprocal at or below its
own argument descends to both children in **no** well-founded order whatever — not lexicographic,
not a vector, not an ordinal rank. Cheap reciprocals and both-children descent cannot be had
together, and `Nat` had nothing to do with it.

The `Nat` form is `no_structural_induction_of_cheap_recip`; this is the same statement with the
codomain and the order universally quantified. -/
theorem no_wf_descent_of_cheap_recip {W : Type} (μ : EMLTree → W) (R : W → W → Prop)
    (hwf : WellFounded R) (t : EMLTree)
    (hcheap : R (μ (recipTree t)) (μ t) ∨ μ (recipTree t) = μ t) :
    ¬ ((∀ A B : EMLTree, R (μ A) (μ (EMLTree.eml A B))) ∧
       (∀ A B : EMLTree, R (μ B) (μ (EMLTree.eml A B)))) := by
  rintro ⟨hl, hr⟩
  let m : WfDescent := ⟨W, μ, R, hwf, hl, hr⟩
  rcases hcheap with h | h
  · exact recip_not_below m t h
  · exact recip_ne m t h

/-- **`posEmbed` is four strict steps up**, by the same argument, so the positive-branch
re-embedding `(di)` routes through is unavailable at its own level in every well-founded order
too. -/
theorem posEmbed_not_below (m : WfDescent) (t : EMLTree) :
    ¬ m.R (m.μ (posEmbed t)) (m.μ t) := by
  intro h
  have s1 : m.R (m.μ t) (m.μ (eTree t)) := m.left_lt t (EMLTree.const 1)
  have s2 : m.R (m.μ (eTree t)) (m.μ (EMLTree.eml (EMLTree.const 0) (eTree t))) :=
    m.right_lt (EMLTree.const 0) (eTree t)
  have s3 : m.R (m.μ (EMLTree.eml (EMLTree.const 0) (eTree t)))
      (m.μ (eTree (EMLTree.eml (EMLTree.const 0) (eTree t)))) :=
    m.left_lt _ (EMLTree.const 1)
  have s4 : m.R (m.μ (eTree (EMLTree.eml (EMLTree.const 0) (eTree t)))) (m.μ (posEmbed t)) :=
    m.right_lt (EMLTree.const 0) (eTree (EMLTree.eml (EMLTree.const 0) (eTree t)))
  exact no_cycle5 m.wf _ _ _ _ _ s1 s2 s3 s4 h

/-! ## §5 — candidate 2 in its strongest reading: a POLARITY-INDEXED measure

`§4` treats the polarity pair as a vector. The stronger reading of *"treat the two sides
differently"* is not a vector at all: it is a measure carrying a **polarity bit that the grammar
flips on the `log` edge** — the bit the ladder's own recursion carries, since a floor for
`exp (A x) − log (B x)` needs a *lower* bound on the left child and an *upper* bound on the right.
It fails identically, at the flipped polarity. -/

/-- A measure indexed by a polarity bit which the `log` edge flips. -/
structure PolWfDescent where
  /-- The order the measure lands in. -/
  W : Type
  /-- The measure, read at a polarity. -/
  μ : EMLTree → Bool → W
  /-- The strict order. -/
  R : W → W → Prop
  /-- …which is well-founded. -/
  wf : WellFounded R
  /-- The `exp` edge keeps the polarity. -/
  left_lt : ∀ (A B : EMLTree) (p : Bool), R (μ A p) (μ (EMLTree.eml A B) p)
  /-- The `log` edge **flips** it. -/
  right_lt : ∀ (A B : EMLTree) (p : Bool), R (μ B (!p)) (μ (EMLTree.eml A B) p)

/-- **The reciprocal is two steps up here too — at the flipped polarity.** `recipTree` spends one
`exp` edge (polarity kept) and one `log` edge (polarity flipped). -/
theorem pol_recip_two_steps (m : PolWfDescent) (t : EMLTree) (p : Bool) :
    m.R (m.μ t (!p)) (m.μ (negLogTree t) p) ∧ m.R (m.μ (negLogTree t) p) (m.μ (recipTree t) p) :=
  ⟨m.right_lt (EMLTree.const 0) t p, m.left_lt (negLogTree t) (EMLTree.const 1) p⟩

/-- **So the bit changes which side pays, not the direction of travel.** -/
theorem pol_recip_not_below (m : PolWfDescent) (t : EMLTree) (p : Bool) :
    ¬ m.R (m.μ (recipTree t) p) (m.μ t (!p)) := by
  intro h
  obtain ⟨h1, h2⟩ := pol_recip_two_steps m t p
  exact no_cycle3 m.wf _ _ _ h1 h2 h

theorem pol_recip_ne (m : PolWfDescent) (t : EMLTree) (p : Bool) :
    m.μ (recipTree t) p ≠ m.μ t (!p) := by
  intro h
  obtain ⟨h1, h2⟩ := pol_recip_two_steps m t p
  rw [h] at h2
  exact no_cycle2 m.wf _ _ h1 h2

/-! ## §6 — the §3 fixtures, measured

Each family in `EmlGermApproachResearch.md` §3, priced in both components. These are the numbers a
future candidate is tested against; they are computed once, here. -/

theorem eh_eTree (t : EMLTree) : (eTree t).ehTree = t.ehTree + 1 := by
  show Nat.max (t.ehTree + 1) (EMLTree.const 1).ehTree = t.ehTree + 1
  exact Nat.le_antisymm
    (Nat.max_le.mpr ⟨Nat.le_refl _, by show (0 : Nat) ≤ _; omega⟩) (Nat.le_max_left _ _)

theorem ld_eTree (t : EMLTree) : (eTree t).ldTree = Nat.max t.ldTree 1 := rfl

theorem eh_negLog (t : EMLTree) : (negLogTree t).ehTree = Nat.max 1 t.ehTree := rfl

theorem ld_negLog (t : EMLTree) : (negLogTree t).ldTree = t.ldTree + 1 := by
  show Nat.max (EMLTree.const 0).ldTree (t.ldTree + 1) = t.ldTree + 1
  exact Nat.le_antisymm
    (Nat.max_le.mpr ⟨by show (0 : Nat) ≤ _; omega, Nat.le_refl _⟩) (Nat.le_max_right _ _)

/-- **`recipTree = eTree ∘ negLogTree`** — one `exp` node and one `log` node. The polarity split
puts them in different components, which is exactly the hope of §5(2) and exactly why it changes
nothing. -/
theorem recip_eq_eTree_negLog (t : EMLTree) : recipTree t = eTree (negLogTree t) := rfl

/-! ### `recipTree` — the `exp` component pays ONE where depth and size pay TWO -/

theorem eh_recipTree (t : EMLTree) : (recipTree t).ehTree = Nat.max 1 t.ehTree + 1 := by
  show Nat.max ((negLogTree t).ehTree + 1) (EMLTree.const 1).ehTree = _
  show Nat.max (Nat.max ((EMLTree.const 0).ehTree + 1) t.ehTree + 1) 0 = _
  exact Nat.le_antisymm
    (Nat.max_le.mpr ⟨Nat.le_refl _, by omega⟩) (Nat.le_max_left _ _)

theorem ld_recipTree (t : EMLTree) : (recipTree t).ldTree = t.ldTree + 1 := by
  show Nat.max (negLogTree t).ldTree ((EMLTree.const 1).ldTree + 1) = _
  show Nat.max (Nat.max (EMLTree.const 0).ldTree (t.ldTree + 1)) (0 + 1) = _
  have hin : Nat.max (EMLTree.const 0).ldTree (t.ldTree + 1) = t.ldTree + 1 :=
    Nat.le_antisymm (Nat.max_le.mpr ⟨by show (0 : Nat) ≤ _; omega, Nat.le_refl _⟩)
      (Nat.le_max_right _ _)
  rw [hin]
  exact Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.le_refl _, by omega⟩) (Nat.le_max_left _ _)

/-- **The escape §5(2) predicted, realised.** Where `depthMeasure` and `sizeMeasure` pay two nodes
for the reciprocal (`depthMeasure_recip_sharp`, `sizeMeasure_recip_sharp`, both tight), the
`exp`-height pays exactly one. The escape is real — and `recip_not_below` is why it is not
enough: `ld_recipTree` shows the other node is paid in the other component. -/
theorem eh_recipTree_of_one_le (t : EMLTree) (h : 1 ≤ t.ehTree) :
    (recipTree t).ehTree = t.ehTree + 1 := by
  rw [eh_recipTree]
  have hm : Nat.max 1 t.ehTree = t.ehTree :=
    Nat.le_antisymm (Nat.max_le.mpr ⟨h, Nat.le_refl _⟩) (Nat.le_max_right _ _)
  omega

/-! ### `posEmbed` -/

theorem eh_posEmbed (t : EMLTree) : (posEmbed t).ehTree = t.ehTree + 2 := by
  show (negLogTree (eTree (negLogTree (eTree t)))).ehTree = t.ehTree + 2
  rw [eh_negLog, eh_eTree, eh_negLog, eh_eTree]
  have h1 : Nat.max 1 (t.ehTree + 1) = t.ehTree + 1 :=
    Nat.le_antisymm (Nat.max_le.mpr ⟨by omega, Nat.le_refl _⟩) (Nat.le_max_right _ _)
  rw [h1]
  have h2 : Nat.max 1 (t.ehTree + 1 + 1) = t.ehTree + 2 :=
    Nat.le_antisymm (Nat.max_le.mpr ⟨by omega, by omega⟩)
      (by have := Nat.le_max_right 1 (t.ehTree + 1 + 1); omega)
  rw [h2]

/-! ### `capNode n` — the fixture that killed mechanism (2) -/

theorem eh_towerTree : ∀ n : Nat, (EMLTree.towerTree n).ehTree = n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      show Nat.max ((EMLTree.towerTree k).ehTree + 1) (EMLTree.const 0).ehTree = k + 1
      rw [ih]
      exact Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.le_refl _, by show (0 : Nat) ≤ _; omega⟩)
        (Nat.le_max_left _ _)

theorem ld_towerTree_le : ∀ n : Nat, (EMLTree.towerTree n).ldTree ≤ 1 := by
  intro n
  induction n with
  | zero => show (0 : Nat) ≤ 1; omega
  | succ k ih =>
      show Nat.max (EMLTree.towerTree k).ldTree ((EMLTree.const 0).ldTree + 1) ≤ 1
      exact Nat.max_le.mpr ⟨ih, by show (0 : Nat) + 1 ≤ 1; omega⟩

theorem ld_towerTree_succ (n : Nat) : (EMLTree.towerTree (n + 1)).ldTree = 1 := by
  show Nat.max (EMLTree.towerTree n).ldTree ((EMLTree.const 0).ldTree + 1) = 1
  exact Nat.le_antisymm
    (Nat.max_le.mpr ⟨ld_towerTree_le n, by show (0 : Nat) + 1 ≤ 1; omega⟩)
    (Nat.le_trans (by show (1 : Nat) ≤ (0 : Nat) + 1; omega) (Nat.le_max_right _ _))

theorem pol_capNode (n : Nat) : polMeasure (capNode n) = (n + 1, 2) := by
  have he : (capNode n).ehTree = n + 1 := by
    show Nat.max ((EMLTree.const 0).ehTree + 1) (EMLTree.towerTree (n + 1)).ehTree = n + 1
    rw [eh_towerTree (n + 1)]
    exact Nat.le_antisymm (Nat.max_le.mpr ⟨by show (0 : Nat) + 1 ≤ n + 1; omega, Nat.le_refl _⟩)
      (Nat.le_max_right _ _)
  have hl : (capNode n).ldTree = 2 := by
    show Nat.max (EMLTree.const 0).ldTree ((EMLTree.towerTree (n + 1)).ldTree + 1) = 2
    rw [ld_towerTree_succ n]
    exact Nat.le_antisymm (Nat.max_le.mpr ⟨by show (0 : Nat) ≤ 2; omega, by omega⟩)
      (Nat.le_trans (by show (2 : Nat) ≤ 1 + 1; omega) (Nat.le_max_right _ _))
  show ((capNode n).ehTree, (capNode n).ldTree) = (n + 1, 2)
  rw [he, hl]

/-- **The fixture that killed the germ route is SURVIVED.** No growth measure descends from
`capNode n` to its right child — the node is non-positive on the ray while the child is the
`(n+1)`-tower, and the gap is unbounded in `n`. The polarity measure descends there for every `n`:
the `exp` component ties, exactly as `ehTree_not_right_le` says it must, and the `log` component
breaks the tie. -/
theorem pol_descends_capNode (n : Nat) :
    polLt (polMeasure (EMLTree.towerTree (n + 1))) (polMeasure (capNode n)) := by
  have hc := pol_capNode n
  refine Or.inr ⟨?_, ?_⟩
  · show (EMLTree.towerTree (n + 1)).ehTree = (capNode n).ehTree
    rw [eh_towerTree (n + 1)]
    have h : (capNode n).ehTree = n + 1 := congrArg Prod.fst hc
    omega
  · show (EMLTree.towerTree (n + 1)).ldTree < (capNode n).ldTree
    rw [ld_towerTree_succ n]
    have h : (capNode n).ldTree = 2 := congrArg Prod.snd hc
    omega

/-! ### `deepDecay m` — and why `k` cannot come from the `log` component -/

theorem pol_deepDecay (m : Nat) : polMeasure (deepDecay m) = (m + 3, 2) := by
  have hE : (eTree (EMLTree.towerTree (m + 1))).ehTree = m + 2 := by
    rw [eh_eTree, eh_towerTree]
  have hL : (eTree (EMLTree.towerTree (m + 1))).ldTree = 1 := by
    rw [ld_eTree, ld_towerTree_succ]
    exact Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.le_refl 1, Nat.le_refl 1⟩) (Nat.le_max_left _ _)
  have he : (deepDecay m).ehTree = m + 3 := by
    show (eTree (negLogTree (eTree (EMLTree.towerTree (m + 1))))).ehTree = m + 3
    rw [eh_eTree, eh_negLog, hE]
    have hmax : Nat.max 1 (m + 2) = m + 2 :=
      Nat.le_antisymm (Nat.max_le.mpr ⟨by omega, Nat.le_refl _⟩) (Nat.le_max_right _ _)
    omega
  have hl : (deepDecay m).ldTree = 2 := by
    show (eTree (negLogTree (eTree (EMLTree.towerTree (m + 1))))).ldTree = 2
    rw [ld_eTree, ld_negLog, hL]
    exact Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.le_refl 2, by omega⟩) (Nat.le_max_left _ _)
  show ((deepDecay m).ehTree, (deepDecay m).ldTree) = (m + 3, 2)
  rw [he, hl]

section DeepDecayFloor

open Real

/-- A floor for `deepDecay m` at height `k` forces `m + 1 ≤ k` — `decayFloorUpTo_height_ge`'s
argument run on the single family, so the bound can be read off one tree's measure. -/
theorem floorHeight_of_deepDecay (m k : Nat) (X₁ : Real) (hX₁ : 1 ≤ X₁)
    (h : ∀ x : Real, X₁ ≤ x → exp (-(EMLTree.towerFn k x)) ≤ (deepDecay m).eval x) :
    m + 1 ≤ k := by
  rcases Nat.lt_or_ge m k with hlt | hkm
  · omega
  · have hmono : EMLTree.towerFn k X₁ ≤ EMLTree.towerFn m X₁ := by
      have e : k + (m - k) = m := by omega
      have hh := towerFn_mono k (m - k) hX₁
      rw [e] at hh; exact hh
    have hneg : -(EMLTree.towerFn m X₁) ≤ -(EMLTree.towerFn k X₁) := neg_le_neg_wit hmono
    have hle := le_trans (exp_monotone hneg) (h X₁ (le_refl X₁))
    exact absurd rfl (ne_of_lt (lt_of_lt_of_le (deepDecay_below_floor m hX₁) hle))

/-- **The `log` component cannot be where the floor height comes from.** Any assignment of a floor
height as a function of the polarity measure is forced up by `deepDecay` — and that family moves
the first component only, the second being pinned at `2` for every `m`. -/
theorem deepDecay_forces_first_component (f : Nat × Nat → Nat)
    (hf : ∀ t : EMLTree, ∃ X₁ : Real, 1 ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
        exp (-(EMLTree.towerFn (f (polMeasure t)) x)) ≤ t.eval x) (m : Nat) :
    m + 1 ≤ f (m + 3, 2) := by
  obtain ⟨X₁, hX₁, h⟩ := hf (deepDecay m)
  rw [pol_deepDecay m] at h
  exact floorHeight_of_deepDecay m (f (m + 3, 2)) X₁ hX₁ h

end DeepDecayFloor

/-! ### `gapTarget n c` — approach is not controlled by growth, and the measure over-predicts -/

section GapTarget

open Real

/-- The near-meeting pair sits at `(n + 1, 1)` while the floor its gap needs is height `0`
(`gapTarget_meets_floor`). The measure over-predicts by `n`: it is an upper bound on what the
family needs, not a description of it. -/
theorem pol_gapTarget (n : Nat) (c : Real) : polMeasure (gapTarget n c) = (n + 1, 1) := by
  have he : (gapTarget n c).ehTree = n + 1 := by
    show Nat.max ((EMLTree.towerTree n).ehTree + 1) (EMLTree.const (exp c)).ehTree = n + 1
    rw [eh_towerTree]
    exact Nat.le_antisymm (Nat.max_le.mpr ⟨Nat.le_refl _, by show (0 : Nat) ≤ _; omega⟩)
      (Nat.le_max_left _ _)
  have hl : (gapTarget n c).ldTree = 1 := by
    show Nat.max (EMLTree.towerTree n).ldTree ((EMLTree.const (exp c)).ldTree + 1) = 1
    exact Nat.le_antisymm
      (Nat.max_le.mpr ⟨ld_towerTree_le n, by show (0 : Nat) + 1 ≤ 1; omega⟩)
      (Nat.le_trans (by show (1 : Nat) ≤ (0 : Nat) + 1; omega) (Nat.le_max_right _ _))
  show ((gapTarget n c).ehTree, (gapTarget n c).ldTree) = (n + 1, 1)
  rw [he, hl]

end GapTarget

/-! ### `eTree (eTree A)` — the measure is blind at the hypothesis boundary -/

section Meeting

open Real

/-- The gap tree of the exact-meeting pair `(var, eTree var)`: `exp x − exp x`, identically zero.
This is `exact_meeting_gap_zero`'s pair in the tree form the ladder would recurse on. -/
noncomputable def meetTree : EMLTree := EMLTree.eml EMLTree.var (eTree (eTree EMLTree.var))

/-- A germ that is positive everywhere, `exp (1 − x)`, with the **same** measure. -/
noncomputable def posTree : EMLTree := eTree (negLogTree (eTree EMLTree.var))

theorem meetTree_eval (x : Real) : meetTree.eval x = 0 := by
  show exp (EMLTree.var.eval x) - log ((eTree (eTree EMLTree.var)).eval x) = 0
  rw [eTree_eval, eTree_eval, log_exp]
  mach_ring

theorem posTree_eval (x : Real) : posTree.eval x = exp (1 - x) := by
  show (eTree (negLogTree (eTree EMLTree.var))).eval x = exp (1 - x)
  rw [eTree_eval, negLogTree_eval, eTree_eval, log_exp]
  rfl

theorem posTree_pos (x : Real) : 0 < posTree.eval x := by
  rw [posTree_eval]; exact exp_pos _

theorem pol_meetTree : polMeasure meetTree = (2, 2) := rfl
theorem pol_posTree : polMeasure posTree = (2, 2) := rfl
theorem vec_meetTree : vecMeasure meetTree = (2, (2, (3, 7))) := rfl
theorem vec_posTree : vecMeasure posTree = (2, (2, (3, 7))) := rfl

/-- **Both candidates are blind at the hypothesis boundary.** Two trees with the *same* four-vector
— same `exp`-height, `log`-depth, alternation and size — one identically zero, one positive
everywhere. §3's meeting boundary is invisible to either measure, so the positivity hypothesis has
to be carried by the induction and cannot be recovered from the parameter. Depth is blind here too;
what the pair rules out is the hope that a finer *syntactic* parameter would see the difference. -/
theorem measure_blind_at_meeting :
    polMeasure meetTree = polMeasure posTree ∧
    vecMeasure meetTree = vecMeasure posTree ∧
    (∀ x : Real, meetTree.eval x = 0) ∧ (∀ x : Real, 0 < posTree.eval x) :=
  ⟨rfl, rfl, meetTree_eval, posTree_pos⟩

end Meeting

/-! ## §7 — the reindexing is bookkeeping, and `§9` says to check that before believing otherwise -/

/-- **Two-way.** A depth bound bounds both components; a bound on both components bounds the depth.
So *"`k` from the depth bound alone"* and *"`k` from the polarity pair alone"* are the same
statement, and the candidate cannot be progress on the uniformity by virtue of the reindexing. -/
theorem reindexing_is_two_way (t : EMLTree) (j : Nat) :
    (t.depth ≤ j → t.ehTree ≤ j ∧ t.ldTree ≤ j) ∧
    (t.ehTree + t.ldTree ≤ j → t.depth ≤ j) :=
  ⟨fun h => ⟨Nat.le_trans (EMLTree.ehTree_le_depth t) h,
             Nat.le_trans (EMLTree.ldTree_le_depth t) h⟩,
   fun h => Nat.le_trans (EMLTree.depth_le_eh_add_ld t) h⟩

end MachLib
