import MachLib.EMLDeclampEncoder

/-!
# The induction, restructured so the hard node receives what it needs

The sign arc built three things the depth induction can manufacture: eventual continuity
(`EMLEventualContinuity`), eventual log-argument stability (`logArgStable_of_evSign`), and — through
those — a coherent Pfaffian encoding (`EMLDeclampEncoder`). But they were assembled in **two passes**:
the induction ran first, conditional on `SignHardCase`, and stability was derived afterwards from its
output.

That layering is what blocks any attempt to *discharge* the hard node. Anything proved from
`logArgStable_of_evSign (evSign_of_hard h)` already assumes `SignHardCase`, so feeding it back to the
hard node proves `SignHardCase → SignHardCase`.

This module removes the layering. `EvLogArgStable` becomes a **third conjunct of the induction's own
motive**, so at an `eml A B` node it is available from the immediate children's induction hypotheses
alone — and the hard-node obligation is handed it, rather than deriving it from the obligation's own
conclusion.

## Why the children suffice

`LogArgStable (eml A B) a b` needs three things: stability inside `A`, stability inside `B`, and the
sign disjunction for `B` itself. The first two are `ihA.2.2` and `ihB.2.2`; the third is `ihB.1`.
Every node of `eml A B` is either the node itself or a node of a structurally smaller tree, so
nothing about the node's own value is used — which is exactly why there is no circularity.

## What this buys, and what it does not

`SignHardCtsStable` is `SignHardCase` with **two** extra hypotheses, so it is implied by it
(`signHardCtsStable_of_hard`) and nothing is strengthened. What changes is the call site: an argument
at the hard node may now use eventual continuity *and* eventual log-argument stability of the whole
node without re-entering the induction. That is the precondition for any analyticity- or
Hardy-field-based discharge.

It does **not** discharge anything. `SignHardCase` stays open, and the obvious next step —
transporting analyticity from the encoder's barrier to `t.eval` — is currently blocked:
`IsAnalyticOnReals` is an opaque `axiom` with closure rules but **no congruence along pointwise
equality**, and `eml_tree_analytic_on_pos` requires log-argument positivity on all of `(0, ∞)` where
declamping supplies it only per interval. Closing that gap needs a new axiom, which is a decision
about the `AxiomLedger`, not a proof step.
-/

namespace MachLib

open Real

private theorem eml_eval_fun' (A B : EMLTree) :
    (EMLTree.eml A B).eval = fun x => exp (A.eval x) - log (B.eval x) := by
  funext x; rfl

private theorem ray_join2' {X₁ X₂ : Real} (h₁ : 1 ≤ X₁) (h₂ : 1 ≤ X₂) :
    ∃ X : Real, 1 ≤ X ∧ X₁ ≤ X ∧ X₂ ≤ X := by
  rcases lt_total X₁ X₂ with h | h | h
  · exact ⟨X₂, h₂, le_of_lt h, le_refl X₂⟩
  · exact ⟨X₂, h₂, le_of_eq h, le_refl X₂⟩
  · exact ⟨X₁, h₁, le_refl X₁, le_of_lt h⟩

/-- **Eventually log-argument stable** — `LogArgStable` on every interval far enough out. The
conclusion shape of `logArgStable_of_evSign`, promoted here to a conjunct of the motive. -/
def EvLogArgStable (t : EMLTree) : Prop :=
  ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ a b : Real, X₀ ≤ a → a < b → LogArgStable t a b

/-- The `eml` step for the new conjunct, from the children's stability and the **right child's own**
sign verdict. No property of the node's value is used. -/
theorem evLogArgStable_eml {A B : EMLTree}
    (lA : EvLogArgStable A) (lB : EvLogArgStable B) (sB : EvSign B.eval) :
    EvLogArgStable (EMLTree.eml A B) := by
  obtain ⟨XA, hXA1, hA⟩ := lA
  obtain ⟨XB, hXB1, hB⟩ := lB
  obtain ⟨XS, hXS1, hsign⟩ : ∃ X : Real, 1 ≤ X ∧
      ((∀ x : Real, X ≤ x → 0 < B.eval x) ∨ (∀ x : Real, X ≤ x → B.eval x ≤ 0)) := by
    rcases sB with ⟨X, h1, hp⟩ | ⟨X, h1, hn⟩
    · exact ⟨X, h1, Or.inl hp⟩
    · exact ⟨X, h1, Or.inr hn⟩
  obtain ⟨Y, hY1, hYA, hYB⟩ := ray_join2' hXA1 hXB1
  obtain ⟨X₀, hX01, hX0Y, hX0S⟩ := ray_join2' hY1 hXS1
  refine ⟨X₀, hX01, fun a b hab hlt => ?_⟩
  have haA : XA ≤ a := le_trans hYA (le_trans hX0Y hab)
  have haB : XB ≤ a := le_trans hYB (le_trans hX0Y hab)
  have haS : XS ≤ a := le_trans hX0S hab
  refine ⟨hA a b haA hlt, hB a b haB hlt, ?_⟩
  rcases hsign with hp | hn
  · exact Or.inl (fun x hxa _ => hp x (le_of_lt (lt_of_le_of_lt haS hxa)))
  · exact Or.inr (fun x hxa _ => hn x (le_of_lt (lt_of_le_of_lt haS hxa)))

/-- **The hard node, handed both manufactured ingredients.** `SignHardCase` plus eventual continuity
of the node value plus eventual log-argument stability of the whole node.

More hypotheses, same conclusion: implied by `SignHardCase` (`signHardCtsStable_of_hard`), so routing
through it strengthens nothing. Both extra hypotheses are discharged by the induction below at the
point of use. -/
def SignHardCtsStable : Prop :=
  ∀ (A B : EMLTree) (X₀ : Real), 1 ≤ X₀ → (∀ x : Real, X₀ ≤ x → 0 < B.eval x) →
    EvCont (fun x => exp (A.eval x) - log (B.eval x)) →
    EvLogArgStable (EMLTree.eml A B) →
    EvSign (fun x => exp (A.eval x) - log (B.eval x))

/-- **The three-conjunct induction.** Sign, continuity and log-argument stability advance together,
each `eml` step using immediate-children hypotheses only.

The stability conjunct is the new one, and it is what makes the hard node self-contained: at the call
site the obligation receives `EvLogArgStable (eml A B)` rather than having to obtain it from the
obligation's own conclusion. -/
theorem evSignContStable_of_ctsStable (h : SignHardCtsStable) :
    ∀ t : EMLTree, EvSign t.eval ∧ EvCont t.eval ∧ EvLogArgStable t := by
  intro t
  induction t with
  | const c =>
      refine ⟨?_, ?_, ⟨1, le_refl 1, fun _ _ _ _ => True.intro⟩⟩
      · rcases lt_total 0 c with hc | hc | hc
        · exact Or.inl ⟨1, le_refl 1, fun x _ => hc⟩
        · exact Or.inr ⟨1, le_refl 1, fun x _ => le_of_eq hc.symm⟩
        · exact Or.inr ⟨1, le_refl 1, fun x _ => le_of_lt hc⟩
      · refine ⟨1, le_refl 1, fun x _ => ?_⟩
        rw [show (EMLTree.const c).eval = fun _ => c from by funext y; rfl]
        exact continuousAt_const c x
  | var =>
      refine ⟨Or.inl ⟨1, le_refl 1, fun x hx => lt_of_lt_of_le zero_lt_one_ax hx⟩, ?_,
        ⟨1, le_refl 1, fun _ _ _ _ => True.intro⟩⟩
      refine ⟨1, le_refl 1, fun x _ => ?_⟩
      rw [show (EMLTree.var).eval = fun x => x from by funext y; rfl]
      exact hasDerivAt_continuousAt (HasDerivAt_id x)
  | eml A B ihA ihB =>
      obtain ⟨_, cA, lA⟩ := ihA
      obtain ⟨sB, cB, lB⟩ := ihB
      have hc : EvCont (EMLTree.eml A B).eval := evCont_eml_of_evSign_right cA cB sB
      have hl : EvLogArgStable (EMLTree.eml A B) := evLogArgStable_eml lA lB sB
      refine ⟨?_, hc, hl⟩
      rcases sB with ⟨XB, hXB1, hpos⟩ | ⟨XB, hXB1, hnp⟩
      · rw [eml_eval_fun' A B] at hc ⊢
        exact h A B XB hXB1 hpos hc hl
      · refine Or.inl ⟨XB, hXB1, ?_⟩
        intro x hx
        show 0 < exp (A.eval x) - log (B.eval x)
        rw [log_nonpos (hnp x hx)]
        have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
        rw [e]
        exact exp_pos _

/-- `SignHardCase` implies the doubly-enriched form — drop both extra hypotheses. -/
theorem signHardCtsStable_of_hard (h : SignHardCase) : SignHardCtsStable :=
  fun A B X₀ hX₀ hpos _ _ => h A B X₀ hX₀ hpos

/-- Sign-definiteness at every depth, from the enriched obligation. -/
theorem evSign_of_ctsStable (h : SignHardCtsStable) : ∀ t : EMLTree, EvSign t.eval :=
  fun t => (evSignContStable_of_ctsStable h t).1

/-- Eventual continuity, likewise. -/
theorem evCont_of_ctsStable (h : SignHardCtsStable) : ∀ t : EMLTree, EvCont t.eval :=
  fun t => (evSignContStable_of_ctsStable h t).2.1

/-- **And eventual log-argument stability, now produced by the induction itself** rather than derived
from its conclusion. This is the statement whose two-pass derivation caused the circularity. -/
theorem evLogArgStable_of_ctsStable (h : SignHardCtsStable) : ∀ t : EMLTree, EvLogArgStable t :=
  fun t => (evSignContStable_of_ctsStable h t).2.2

end MachLib
