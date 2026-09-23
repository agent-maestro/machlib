import MachLib.EMLPolarityMeasure

/-!
# A germ-invariant parameter cannot descend through EML syntax — at all

`EmlGermApproachResearch.md` §5 lists two untried candidates: **(3)** a Hardy-field
valuation / comparability class in place of a height integer, and **(4)** a well-founded
**relation on germs** rather than a function of the tree. §4's width paragraph singles (4) out as
the one route `EMLPolarityMeasure`'s obstruction *"does not reach, because (4) quantifies over
functions `EMLTree → W`, so a relation is outside it by construction."*

**That reading is wrong, and this file says why by proof.** A relation on germs used to carry a
structural induction *is* a `WfDescent` — take `W := Real → Real` and `μ := EMLTree.eval`. The
germ is a function of the tree. What distinguishes the candidate is not that it escapes the class;
it is that its measure is **germ-invariant**: trees with the same germ get the same value.

And germ-invariance is exactly what kills it, one step earlier and far harder than `recipTree`
does.

## The obstruction

`posEmbed t` is a §3 fixture already in the corpus, built to re-embed a tree so its right child is
positive everywhere. `posEmbed_eval` records that it **does not change the germ**:
`(posEmbed t).eval x = t.eval x`, at every `x`, for every `t`. It is also four `eml` edges above
`t` — two left, two right — so in any `WfDescent` the four edges give

```
μ t  ≺  μ (eTree t)  ≺  μ (negLogTree (eTree t))  ≺  μ (eTree (negLogTree (eTree t)))  ≺  μ (posEmbed t)
```

If `μ` is germ-invariant the last term **is** `μ t`, and that is a 4-cycle. Well-foundedness
refutes it. So:

```
no_germInvariant_wfDescent :  (m : WfDescent) → GermInvariant m.μ → False
```

> **No germ-invariant measure strictly descends to both children of an `eml` node, in any
> well-founded order whatever.** The class is EMPTY — not merely unable to price the reciprocal.

Three things follow immediately, and they are what closes §5's candidates 3 and 4:

* a well-founded **relation on germs** descending to both children does not exist
  (`no_germDescent`) — candidate (4);
* neither does a **valuation / comparability class** used the same way, since any such parameter
  reads the germ and nothing else (`no_heightModel_wfDescent` states it for the corpus's own
  `HeightModel`, whose `eh` already takes a germ) — candidate (3), in its descent reading;
* and the natural repair — *"require descent only where the germs actually differ"* — fails too
  (`no_germDescentNe`), because the four germs in the `posEmbed var` cycle are pairwise distinct
  and the cycle survives. That repair is checked here rather than left as a hope.

## Why this is stronger than `recip_not_below`, and not a restatement of it

`recip_not_below` needs an extra hypothesis — that the measure prices the reciprocal cheaply —
and the reciprocal costs two edges. This needs **no hypothesis about any construction**: the
contradiction is between germ-invariance and descent alone. `posEmbed` is what `recipTree` is not:
a germ **identity**, not a germ transformation.

It also closes a class `EMLLadderMeasure` and `EMLPolarityMeasure` both list as untouched — *"a
measure descending on **one** side only, the other side carried by a different argument"* — in its
germ-invariant form, and by an even cheaper argument. `flatLeft` is the depth-1 tree
`exp 0 − log (exp 1) = 0`, whose germ is its own **left** child's; `flatRight` is
`exp 0 − log 1 = 1`, whose germ is its own **right** child's. A well-founded relation is
irreflexive, so one-sided germ descent dies on a constant node, with no cycle longer than
`no_cycle2`.

And **guarded** one-sided descent — the only germ-invariant shape those two witnesses leave
standing — dies as well (`§5b`), on two-edge cycles with a distinct intermediate germ:
`var → eTree var → selfLeftNode var` on the left, and
`negGerm → rightStep1 → rightStep2` on the right, where `negGerm` is
`1 − exp (exp x)`, negative at **every** real, so totalised `log` erases it as a *function* and
not merely on a ray. The grammar makes these easy: an `eml` node's other child is unconstrained,
so one edge from a germ `g` can reach a germ engineered to come back.

**So the closure is complete.** Both children or one, guarded or not: **no germ-invariant
parameter descends anywhere.**

## Both verdicts, as the corpus requires

An emptiness theorem is vacuous unless the shape it is about is inhabited. It is:

* `wfDescent_inhabited` — `polDescent` is a `WfDescent`, so the structure is not empty and the
  contradiction is caused by the added hypothesis and nothing else;
* `polMeasure_not_germInvariant` — and the hypothesis really is what `polDescent` lacks:
  `posEmbed var` and `var` have the *same germ* and polarity measures `(2, 3)` and `(0, 0)`.

So the same instrument returns both verdicts: **inhabited when indexed by the tree, empty when
indexed by the germ**, with `posEmbed` the single witness separating the two.

## Scope

**Bounds nothing, discharges nothing, assumes nothing.** No axiom; the `DecayFloor` ⇄
`EmlGermApproach` ⇄ `GrowthEnvelope` row stays open. This is a route-closure in the sense §5 uses
the word, and it is a negative one: it says candidates 3 and 4 are not *smaller* than the closed
routes, they are strictly *worse* — the classes they name are empty, where the closed routes'
classes were merely unable to run the transfer.

What it does **not** close, stated at the width the evidence supports: a relation on **pairs**
`(A, C)` that a peeling step decreases, which is a function of neither germ; a mutual induction
over `(tree, polarity)` with different relations per polarity; and anything non-structural — the
cycle here is built from `eml` edges, so an argument that does not recurse on them is untouched.
-/

namespace MachLib

open Real

/-! ## §1 — germ-invariance, and the missing cycle length -/

/-- **A parameter that reads only the germ.** Trees with the same germ get the same value. This is
what a Hardy-field valuation, a comparability class, and a relation on germs all have in common,
and it is the only property used below. -/
def GermInvariant {W : Sort u} (μ : EMLTree → W) : Prop :=
  ∀ s t : EMLTree, s.eval = t.eval → μ s = μ t

/-- **Invariance under EVENTUAL equality** — the true germ-at-infinity notion, which identifies
strictly more functions than `GermInvariant` does. -/
def EventualGermInvariant {W : Sort u} (μ : EMLTree → W) : Prop :=
  ∀ s t : EMLTree, (∃ X : Real, ∀ x : Real, X ≤ x → s.eval x = t.eval x) → μ s = μ t

/-- **So everything below covers germs-at-infinity a fortiori**, and the weaker hypothesis is
deliberate: equality of functions implies equality on every ray, so a parameter invariant under
eventual equality is `GermInvariant` and the emptiness results apply to it unchanged. Stating the
obstruction at function equality makes it the **stronger** theorem, not a dodge. -/
theorem germInvariant_of_eventual {W : Sort u} (μ : EMLTree → W)
    (h : EventualGermInvariant μ) : GermInvariant μ :=
  fun s t he => h s t ⟨0, fun x _ => congrFun he x⟩

/-- **A producer, and a substantive one.** Eventual positivity — the hypothesis `DecayFloor` and
`EmlGermApproach` both quantify over — depends only on the germ at infinity. So
`EventualGermInvariant` is a predicate something concludes, not a premise with consumers and no
producer, which `tools/hypothesis_audit.py` reports and this corpus treats as an assumption
wearing a hypothesis's clothes. -/
theorem eventualGermInvariant_eventuallyPos :
    EventualGermInvariant
      (fun t : EMLTree => ∃ Y : Real, ∀ x : Real, Y ≤ x → 0 < t.eval x) := by
  intro s t hst
  obtain ⟨X, hX⟩ := hst
  apply propext
  constructor
  · rintro ⟨Y, hY⟩
    refine ⟨max X Y, fun x hx => ?_⟩
    have hxX : X ≤ x := le_trans (le_max_left X Y) hx
    have hxY : Y ≤ x := le_trans (le_max_right X Y) hx
    rw [← hX x hxX]
    exact hY x hxY
  · rintro ⟨Y, hY⟩
    refine ⟨max X Y, fun x hx => ?_⟩
    have hxX : X ≤ x := le_trans (le_max_left X Y) hx
    have hxY : Y ≤ x := le_trans (le_max_right X Y) hx
    rw [hX x hxX]
    exact hY x hxY

/-- A well-founded relation has no 4-cycle. `EMLPolarityMeasure` proves `no_cycle2/3/5`; the
re-embedding needs the even length between them, by the same rotate-into-the-hypothesis trick. -/
theorem no_cycle4 {W : Type} {R : W → W → Prop} (hwf : WellFounded R) :
    ∀ a b c d : W, R a b → R b c → R c d → R d a → False := by
  intro a
  refine hwf.induction (C := fun a => ∀ b c d, R a b → R b c → R c d → R d a → False) a ?_
  intro x ih b c d hxb hbc hcd hdx
  exact ih d hdx x b c hdx hxb hbc hcd

/-! ## §2 — `posEmbed` is a germ identity four edges up -/

/-- **The re-embedding does not move the germ**, as a function equality rather than pointwise —
which is the form a germ-invariant parameter consumes. -/
theorem posEmbed_germ (t : EMLTree) : (posEmbed t).eval = t.eval :=
  funext (fun x => posEmbed_eval t x)

/-- **The four edges.** Two left (`exp`) and two right (`log`), alternating, from `t` up to
`posEmbed t`. Each is a field of `WfDescent` applied at the node that has it as a child; no
arithmetic and no construction-specific lemma is involved. -/
theorem posEmbed_four_steps (m : WfDescent) (t : EMLTree) :
    m.R (m.μ t) (m.μ (eTree t)) ∧
    m.R (m.μ (eTree t)) (m.μ (negLogTree (eTree t))) ∧
    m.R (m.μ (negLogTree (eTree t))) (m.μ (eTree (negLogTree (eTree t)))) ∧
    m.R (m.μ (eTree (negLogTree (eTree t)))) (m.μ (posEmbed t)) :=
  ⟨m.left_lt t (EMLTree.const 1),
   m.right_lt (EMLTree.const 0) (eTree t),
   m.left_lt (negLogTree (eTree t)) (EMLTree.const 1),
   m.right_lt (EMLTree.const 0) (eTree (negLogTree (eTree t)))⟩

/-- **The obstruction, at the width of every well-founded order.** A measure that reads only the
germ cannot strictly descend to both children of an `eml` node — the four-edge re-embedding closes
a cycle on it.

Nothing about `recipTree` is used, and no hypothesis about how any construction is priced. The
contradiction is between germ-invariance and descent. -/
theorem no_germInvariant_wfDescent (m : WfDescent) (hinv : GermInvariant m.μ) : False := by
  obtain ⟨s1, s2, s3, s4⟩ := posEmbed_four_steps m EMLTree.var
  have he : m.μ (posEmbed EMLTree.var) = m.μ EMLTree.var :=
    hinv _ _ (posEmbed_germ EMLTree.var)
  rw [he] at s4
  exact no_cycle4 m.wf _ _ _ _ s1 s2 s3 s4

/-- …and the same obstruction at the germ-at-infinity reading, for the record. -/
theorem no_eventualGermInvariant_wfDescent (m : WfDescent)
    (hinv : EventualGermInvariant m.μ) : False :=
  no_germInvariant_wfDescent m (germInvariant_of_eventual m.μ hinv)

/-! ## §3 — candidate (4): a well-founded relation on germs -/

/-- **`EmlGermApproachResearch.md` §5(4), stated.** A well-founded relation on germs, descending
from an `eml` node's germ to each child's germ — the induction such a relation would carry. -/
structure GermDescent where
  /-- The relation on germs. -/
  R : (Real → Real) → (Real → Real) → Prop
  /-- …which is well-founded, so it supports an induction. -/
  wf : WellFounded R
  /-- An `eml` node's germ is strictly above its left child's. -/
  left_lt : ∀ A B : EMLTree, R A.eval (EMLTree.eml A B).eval
  /-- …and strictly above its right child's. -/
  right_lt : ∀ A B : EMLTree, R B.eval (EMLTree.eml A B).eval

/-- **A relation on germs is not outside `WfDescent`** — it is `WfDescent` at `μ := EMLTree.eval`.
This is the correction §4's width paragraph needs: the germ is a function of the tree. -/
noncomputable def GermDescent.toWfDescent (g : GermDescent) : WfDescent where
  W := Real → Real
  μ := EMLTree.eval
  R := g.R
  wf := g.wf
  left_lt := g.left_lt
  right_lt := g.right_lt

theorem GermDescent.germInvariant (g : GermDescent) : GermInvariant g.toWfDescent.μ :=
  fun _ _ h => h

/-- **Candidate (4) is empty.** -/
theorem no_germDescent (g : GermDescent) : False :=
  no_germInvariant_wfDescent g.toWfDescent g.germInvariant

theorem germDescent_empty : ¬ Nonempty GermDescent := fun h => h.elim no_germDescent

/-! ## §4 — the repair, and why it fails too

*"Then require descent only where the germs actually differ"* — the collision nodes are the ones
an induction has no work to do at, so excluding them is the obvious fix. It does not help: the
four germs in the `posEmbed var` cycle are pairwise distinct along the cycle, so every guarded
edge is still available and the cycle still closes. -/

/-- **A tree is never its own exponential.** `exp_grows_strictly_thm` is unconditional, so this
holds at every `x` and for every tree — it supplies two of the four guards below at once. -/
theorem germ_ne_eTree (t : EMLTree) : t.eval ≠ (eTree t).eval := by
  intro h
  have h0 : t.eval 0 = (eTree t).eval 0 := congrFun h 0
  rw [eTree_eval] at h0
  exact (ne_of_lt (exp_grows_strictly_thm (t.eval 0))) h0

/-- `exp x` and `1 − x` differ — read at `x = 1`, where the second is `0` and the first is `e`. -/
theorem germ_eTreeVar_ne_negLog :
    (eTree EMLTree.var).eval ≠ (negLogTree (eTree EMLTree.var)).eval := by
  intro h
  have h1 : (eTree EMLTree.var).eval 1 = (negLogTree (eTree EMLTree.var)).eval 1 :=
    congrFun h 1
  rw [negLogTree_eval, eTree_eval, log_exp] at h1
  have hz : (1 : Real) - EMLTree.var.eval 1 = 0 := by
    show (1 : Real) - 1 = 0
    mach_ring
  rw [hz] at h1
  exact (ne_of_lt (exp_pos (EMLTree.var.eval 1))) h1.symm

/-- `exp (1 − x)` and `x` differ — read at `x = 0`, where the second is `0` and the first is `e`.
The right-hand side is spelt `posEmbed var` because that is the node the cycle closes on. -/
theorem germ_eTreeNegLog_ne_posEmbed :
    (eTree (negLogTree (eTree EMLTree.var))).eval ≠ (posEmbed EMLTree.var).eval := by
  intro h
  have h0 : (eTree (negLogTree (eTree EMLTree.var))).eval 0
      = (posEmbed EMLTree.var).eval 0 := congrFun h 0
  rw [posEmbed_eval, eTree_eval] at h0
  have hz : EMLTree.var.eval (0 : Real) = 0 := rfl
  rw [hz] at h0
  exact (ne_of_lt (exp_pos ((negLogTree (eTree EMLTree.var)).eval 0))) h0.symm

/-- **The guarded candidate**: descent required only where the node's germ differs from the
child's. -/
structure GermDescentNe where
  /-- The relation on germs. -/
  R : (Real → Real) → (Real → Real) → Prop
  /-- …which is well-founded. -/
  wf : WellFounded R
  /-- Strict descent to the left child, **where the germs differ**. -/
  left_lt : ∀ A B : EMLTree, A.eval ≠ (EMLTree.eml A B).eval →
    R A.eval (EMLTree.eml A B).eval
  /-- …and to the right child, likewise. -/
  right_lt : ∀ A B : EMLTree, B.eval ≠ (EMLTree.eml A B).eval →
    R B.eval (EMLTree.eml A B).eval

/-- **The repair is empty too.** Every guard along the `posEmbed var` cycle is discharged, so the
cycle survives the restriction. Excluding germ collisions does not recover an induction: the cycle
is closed by *one* collision, at its last edge, and the other three edges move the germ. -/
theorem no_germDescentNe (g : GermDescentNe) : False := by
  have s1 := g.left_lt EMLTree.var (EMLTree.const 1) (germ_ne_eTree EMLTree.var)
  have s2 := g.right_lt (EMLTree.const 0) (eTree EMLTree.var) germ_eTreeVar_ne_negLog
  have s3 := g.left_lt (negLogTree (eTree EMLTree.var)) (EMLTree.const 1)
    (germ_ne_eTree (negLogTree (eTree EMLTree.var)))
  have s4 := g.right_lt (EMLTree.const 0) (eTree (negLogTree (eTree EMLTree.var)))
    germ_eTreeNegLog_ne_posEmbed
  have he : (posEmbed EMLTree.var).eval = EMLTree.var.eval := posEmbed_germ EMLTree.var
  rw [show (EMLTree.eml (EMLTree.const 0) (eTree (negLogTree (eTree EMLTree.var))))
      = posEmbed EMLTree.var from rfl, he] at s4
  exact no_cycle4 g.wf _ _ _ _ s1 s2 s3 s4

/-! ## §5 — one-sided germ descent, which `EMLLadderMeasure` lists as untouched

*"A measure descending on **one** side only, the other side carried by a different argument"* is a
class both earlier files leave open. In its germ-invariant form it is empty, and the witness is a
depth-1 tree rather than a four-node re-embedding: an `eml` node whose germ is exactly one of its
children's. -/

/-- `exp 0 − log (exp 1) = 0`: a node whose germ is its own **left** child's. -/
noncomputable def flatLeft : EMLTree :=
  EMLTree.eml (EMLTree.const 0) (EMLTree.const (exp 1))

/-- `exp 0 − log 1 = 1`: a node whose germ is its own **right** child's. -/
noncomputable def flatRight : EMLTree :=
  EMLTree.eml (EMLTree.const 0) (EMLTree.const 1)

theorem flatLeft_germ : flatLeft.eval = (EMLTree.const (0 : Real)).eval := by
  funext x
  show exp ((0 : Real)) - log (exp 1) = (0 : Real)
  rw [exp_zero, log_exp]
  mach_ring

theorem flatRight_germ : flatRight.eval = (EMLTree.const (1 : Real)).eval := by
  funext x
  show exp ((0 : Real)) - log ((1 : Real)) = (1 : Real)
  rw [exp_zero, log_one]
  mach_ring

/-- Germ descent to the **left** child only. -/
structure GermDescentLeft where
  /-- The relation on germs. -/
  R : (Real → Real) → (Real → Real) → Prop
  /-- …which is well-founded. -/
  wf : WellFounded R
  /-- Strict descent to the left child. -/
  left_lt : ∀ A B : EMLTree, R A.eval (EMLTree.eml A B).eval

/-- Germ descent to the **right** child only. -/
structure GermDescentRight where
  /-- The relation on germs. -/
  R : (Real → Real) → (Real → Real) → Prop
  /-- …which is well-founded. -/
  wf : WellFounded R
  /-- Strict descent to the right child. -/
  right_lt : ∀ A B : EMLTree, R B.eval (EMLTree.eml A B).eval

/-- **Left-only germ descent is empty**, refuted by a constant node at depth 1: a well-founded
relation is irreflexive, and `flatLeft`'s germ *is* its left child's. -/
theorem no_germDescentLeft (g : GermDescentLeft) : False := by
  have h := g.left_lt (EMLTree.const 0) (EMLTree.const (exp 1))
  rw [show (EMLTree.eml (EMLTree.const 0) (EMLTree.const (exp 1))) = flatLeft from rfl,
    flatLeft_germ] at h
  exact no_cycle2 g.wf _ _ h h

/-- **Right-only germ descent is empty**, by the mirror node `exp 0 − log 1 = 1`. -/
theorem no_germDescentRight (g : GermDescentRight) : False := by
  have h := g.right_lt (EMLTree.const 0) (EMLTree.const 1)
  rw [show (EMLTree.eml (EMLTree.const 0) (EMLTree.const 1)) = flatRight from rfl,
    flatRight_germ] at h
  exact no_cycle2 g.wf _ _ h h

/-! ## §5b — one-sided AND guarded, which is the last germ-invariant scheme left

`§5`'s witnesses are single nodes whose germ *is* a child's, so the guard of `§4` disposes of
them. The guarded one-sided schemes are therefore not closed by anything above, and they are the
last germ-invariant shape standing. They need a **two-edge cycle on one side** with the
intermediate germ distinct — and the grammar supplies one on each side.

The constructions are the reason: an `eml` node's *other* child is unconstrained, so from any germ
`g` a single edge can reach almost anything, including a germ engineered to return. -/

/-- **Two LEFT edges above `A`, back at `A`'s germ.** `eml (eTree A) (eTree A)` evaluates to
`exp (exp g) − g`; exponentiating it and putting it under the node's `log` subtracts exactly that
from `exp (exp g)`. -/
noncomputable def selfLeftNode (A : EMLTree) : EMLTree :=
  EMLTree.eml (eTree A) (eTree (EMLTree.eml (eTree A) (eTree A)))

theorem selfLeftNode_germ (A : EMLTree) : (selfLeftNode A).eval = A.eval := by
  funext x
  have h1 : (eTree A).eval x = exp (A.eval x) := eTree_eval A x
  have h2 : (EMLTree.eml (eTree A) (eTree A)).eval x = exp (exp (A.eval x)) - A.eval x := by
    show exp ((eTree A).eval x) - log ((eTree A).eval x) = _
    rw [h1, log_exp]
  have h3 : (eTree (EMLTree.eml (eTree A) (eTree A))).eval x
      = exp (exp (exp (A.eval x)) - A.eval x) := by
    rw [eTree_eval, h2]
  show exp ((eTree A).eval x)
      - log ((eTree (EMLTree.eml (eTree A) (eTree A))).eval x) = A.eval x
  rw [h1, h3, log_exp]
  mach_ring

/-- `1 − exp (exp x)`, strictly negative at **every** real — not merely on a ray, which is what
lets totalised `log` erase it as a function rather than as a germ. -/
noncomputable def negGerm : EMLTree :=
  EMLTree.eml (EMLTree.const 0) (eTree (eTree (eTree EMLTree.var)))

theorem negGerm_eval (x : Real) : negGerm.eval x = 1 - exp (exp x) := by
  show exp ((0 : Real)) - log ((eTree (eTree (eTree EMLTree.var))).eval x) = _
  have hv : EMLTree.var.eval x = x := rfl
  rw [exp_zero, eTree_eval, eTree_eval, eTree_eval, log_exp, hv]

theorem negGerm_neg (x : Real) : negGerm.eval x < 0 := by
  rw [negGerm_eval]
  have h1 : (0 : Real) < exp x := exp_pos x
  have h2 : exp (0 : Real) < exp (exp x) := exp_lt h1
  rw [exp_zero] at h2
  have u := add_lt_add_left h2 (1 - exp (exp x) - 1)
  have e1 : (1 - exp (exp x) - 1) + 1 = 1 - exp (exp x) := by mach_ring
  have e2 : (1 - exp (exp x) - 1) + exp (exp x) = 0 := by mach_ring
  rw [e1, e2] at u
  exact u

theorem log_negGerm (x : Real) : log (negGerm.eval x) = 0 :=
  log_nonpos (le_of_lt (negGerm_neg x))

/-- `1 − negGerm`. -/
noncomputable def negGermCap : EMLTree := EMLTree.eml (EMLTree.const 0) (eTree negGerm)

/-- One RIGHT edge above `negGerm`; totalised `log` erases the child, so the germ is
`exp (1 − negGerm)`. -/
noncomputable def rightStep1 : EMLTree := EMLTree.eml negGermCap negGerm

/-- A second RIGHT edge, and the germ is back at `negGerm`'s. -/
noncomputable def rightStep2 : EMLTree := EMLTree.eml (EMLTree.const 0) rightStep1

theorem negGermCap_eval (x : Real) : negGermCap.eval x = 1 - negGerm.eval x := by
  show exp ((0 : Real)) - log ((eTree negGerm).eval x) = _
  rw [exp_zero, eTree_eval, log_exp]

theorem rightStep1_eval (x : Real) : rightStep1.eval x = exp (1 - negGerm.eval x) := by
  show exp (negGermCap.eval x) - log (negGerm.eval x) = _
  rw [negGermCap_eval, log_negGerm]
  mach_ring

theorem rightStep2_germ : rightStep2.eval = negGerm.eval := by
  funext x
  show exp ((0 : Real)) - log (rightStep1.eval x) = _
  rw [exp_zero, rightStep1_eval, log_exp]
  mach_ring

theorem negGerm_ne_rightStep1 : negGerm.eval ≠ rightStep1.eval := by
  intro h
  have h0 : negGerm.eval 0 = rightStep1.eval 0 := congrFun h 0
  rw [rightStep1_eval] at h0
  have hp : (0 : Real) < exp (1 - negGerm.eval 0) := exp_pos _
  rw [← h0] at hp
  exact (ne_of_lt (lt_of_lt_of_le (negGerm_neg 0) (le_of_lt hp))) rfl

theorem rightStep1_ne_rightStep2 : rightStep1.eval ≠ rightStep2.eval := by
  rw [rightStep2_germ]
  intro h
  exact negGerm_ne_rightStep1 h.symm

/-- Left-only germ descent, **guarded** by germ-difference. -/
structure GermDescentLeftNe where
  /-- The relation on germs. -/
  R : (Real → Real) → (Real → Real) → Prop
  /-- …which is well-founded. -/
  wf : WellFounded R
  /-- Strict descent to the left child, where the germs differ. -/
  left_lt : ∀ A B : EMLTree, A.eval ≠ (EMLTree.eml A B).eval →
    R A.eval (EMLTree.eml A B).eval

/-- Right-only germ descent, **guarded** by germ-difference. -/
structure GermDescentRightNe where
  /-- The relation on germs. -/
  R : (Real → Real) → (Real → Real) → Prop
  /-- …which is well-founded. -/
  wf : WellFounded R
  /-- Strict descent to the right child, where the germs differ. -/
  right_lt : ∀ A B : EMLTree, B.eval ≠ (EMLTree.eml A B).eval →
    R B.eval (EMLTree.eml A B).eval

/-- **Empty.** `var → eTree var → selfLeftNode var` is two left edges with intermediate germ
`exp x ≠ x`, ending back at `x`. -/
theorem no_germDescentLeftNe (g : GermDescentLeftNe) : False := by
  have s1 := g.left_lt EMLTree.var (EMLTree.const 1) (germ_ne_eTree EMLTree.var)
  have hg : (eTree EMLTree.var).eval ≠ (selfLeftNode EMLTree.var).eval := by
    rw [selfLeftNode_germ]
    exact Ne.symm (germ_ne_eTree EMLTree.var)
  have s2 := g.left_lt (eTree EMLTree.var)
    (eTree (EMLTree.eml (eTree EMLTree.var) (eTree EMLTree.var))) hg
  rw [show (EMLTree.eml (eTree EMLTree.var)
      (eTree (EMLTree.eml (eTree EMLTree.var) (eTree EMLTree.var))))
      = selfLeftNode EMLTree.var from rfl, selfLeftNode_germ] at s2
  exact no_cycle2 g.wf _ _ s1 s2

/-- **Empty too.** `negGerm → rightStep1 → rightStep2` is two right edges with intermediate germ
`exp (1 − negGerm) > 0 > negGerm`, ending back at `negGerm`. -/
theorem no_germDescentRightNe (g : GermDescentRightNe) : False := by
  have s1 := g.right_lt negGermCap negGerm negGerm_ne_rightStep1
  have s2 := g.right_lt (EMLTree.const 0) rightStep1 rightStep1_ne_rightStep2
  rw [show (EMLTree.eml (EMLTree.const 0) rightStep1) = rightStep2 from rfl,
    rightStep2_germ] at s2
  exact no_cycle2 g.wf _ _ s1 s2

/-! ## §6 — candidate (3): a valuation reads the germ, so it is covered

`EMLHeightInterface`'s `HeightModel.eh` already takes a **germ** (`Real → Real`), deliberately:
*"a height that reads the syntax is a tree measure."* So a Hardy-field valuation or a comparability
class, used as an induction parameter, is a `HeightModel`-shaped object and `§2` applies to it
verbatim. `zeroModel` showed the closure axioms carry no content; this shows the *descent* carries
none either, for **every** model rather than for one badly chosen one. -/

/-- **No height on germs descends through the syntax.** Whatever the model and whatever the
well-founded order on its values, `t ↦ M.eh t.eval` cannot strictly descend to both children.
Candidate (3), in its descent reading, is closed by the same theorem as candidate (4). -/
theorem no_heightModel_wfDescent (M : HeightModel)
    (R : Nat → Nat → Prop) (hwf : WellFounded R)
    (hl : ∀ A B : EMLTree, R (M.eh A.eval) (M.eh (EMLTree.eml A B).eval))
    (hr : ∀ A B : EMLTree, R (M.eh B.eval) (M.eh (EMLTree.eml A B).eval)) : False :=
  no_germInvariant_wfDescent
    ⟨Nat, fun t => M.eh t.eval, R, hwf, hl, hr⟩
    (fun s t h => by show M.eh s.eval = M.eh t.eval; rw [h])

/-! ## §7 — both verdicts, on one instrument

An emptiness result is worthless unless the shape it is about is inhabited, and unless the
hypothesis blamed is the one the inhabitant lacks. Both are checked here. -/

/-- **The shape is inhabited.** `polDescent` is a `WfDescent`, so `no_germInvariant_wfDescent` is
not a theorem about an empty structure — the added hypothesis is what produces the contradiction. -/
theorem wfDescent_inhabited : Nonempty WfDescent := ⟨polDescent⟩

theorem pol_posEmbed_var : polMeasure (posEmbed EMLTree.var) = (2, 3) := rfl

theorem pol_var : polMeasure EMLTree.var = (0, 0) := rfl

/-- **…and the hypothesis is exactly what it lacks.** The corpus's only both-children descent is
not germ-invariant, and `posEmbed` is the witness: same germ, different measure. So the two
verdicts come from one instrument — inhabited when indexed by the tree, empty when indexed by the
germ. -/
theorem polMeasure_not_germInvariant : ¬ GermInvariant polMeasure := by
  intro h
  have hm := h (posEmbed EMLTree.var) EMLTree.var (posEmbed_germ EMLTree.var)
  rw [pol_posEmbed_var, pol_var] at hm
  exact absurd (congrArg Prod.fst hm) (by decide)

/-- The separation stated as one proposition, the way `measure_blind_at_meeting` states its own:
`posEmbed var` and `var` have the **same germ** and **different** polarity measures. The blindness
runs the other way round from `measure_blind_at_meeting` — there two trees shared a measure and
differed as germs; here two trees share a germ and differ in measure. A syntactic parameter and a
germ parameter are not refinements of one another in either direction. -/
theorem polMeasure_sees_what_the_germ_does_not :
    (posEmbed EMLTree.var).eval = EMLTree.var.eval ∧
    polMeasure (posEmbed EMLTree.var) ≠ polMeasure EMLTree.var := by
  refine ⟨posEmbed_germ EMLTree.var, ?_⟩
  intro hm
  rw [pol_posEmbed_var, pol_var] at hm
  exact absurd (congrArg Prod.fst hm) (by decide)

end MachLib
