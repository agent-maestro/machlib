/-!
# `lexProd` — well-foundedness of the lexicographic product (the nesting keystone)

The keystone for the chain-2 Khovanskii closure (`ChainExp2SDR.lean`). The obstruction there is that
`lexMeasure` is a *flat* `Nat × Nat` whose second component projects `y₀→0` lossily; the fix is a
*chain-aware* measure whose second component recurses the single-exp measure on the leading
coefficient — i.e. the chain-2 measure becomes `(degreeY₁, (degreeY₀, trueDeg))`, a **nested** lex.

This module proves the general combinator: the lexicographic order on a product of two well-founded
orders is well-founded. Applied repeatedly it gives the well-foundedness of any fixed-depth nested lex
measure (`Nat ×ₗ Nat`, `Nat ×ₗ (Nat ×ₗ Nat)`, …) — the well-founded backbone a chain-`n` measure needs,
without the cross-cutting risk of editing the closed single-exp framework. Pure order theory; `#print
axioms` shows no MachLib axioms.
-/

namespace MachLib.LexProd

variable {α β : Type}

/-- The lexicographic order on `α × β`: first component by `r`, ties broken by `s` on the second. -/
def lexProd (r : α → α → Prop) (s : β → β → Prop) : α × β → α × β → Prop :=
  fun p q => r p.1 q.1 ∨ (p.1 = q.1 ∧ s p.2 q.2)

/-- **The keystone: the lex product of two well-founded orders is well-founded.** Proof: double
well-founded induction (outer on the first component via `hr`, inner on the second via `hs`); any
`lexProd`-predecessor is handled by the appropriate inductive hypothesis. -/
theorem lexProd_wf {r : α → α → Prop} {s : β → β → Prop}
    (hr : WellFounded r) (hs : WellFounded s) : WellFounded (lexProd r s) := by
  refine ⟨fun p => ?_⟩
  obtain ⟨a, b⟩ := p
  exact hr.induction a (C := fun a => ∀ b, Acc (lexProd r s) (a, b))
    (fun a iha b =>
      hs.induction b (C := fun b => Acc (lexProd r s) (a, b))
        (fun b ihb =>
          Acc.intro (a, b) (fun q hq => by
            obtain ⟨a', b'⟩ := q
            rcases hq with h1 | ⟨h1eq, h2⟩
            · exact iha a' h1 b'
            · cases h1eq; exact ihb b' h2))) b

/-- `lexProd` is irreflexive when both component relations are. -/
theorem lexProd_irrefl {r : α → α → Prop} {s : β → β → Prop}
    (hr : ∀ a, ¬ r a a) (hs : ∀ b, ¬ s b b) : ∀ p, ¬ lexProd r s p p := by
  intro p h
  rcases h with h1 | ⟨_, h2⟩
  · exact hr p.1 h1
  · exact hs p.2 h2

/-- `lexProd` is transitive when both component relations are. -/
theorem lexProd_trans {r : α → α → Prop} {s : β → β → Prop}
    (htr : ∀ a b c, r a b → r b c → r a c) (hts : ∀ a b c, s a b → s b c → s a c) :
    ∀ x y z, lexProd r s x y → lexProd r s y z → lexProd r s x z := by
  intro x y z hxy hyz
  rcases hxy with hxy1 | ⟨hxy1eq, hxy2⟩
  · rcases hyz with hyz1 | ⟨hyz1eq, _⟩
    · exact Or.inl (htr _ _ _ hxy1 hyz1)
    · exact Or.inl (hyz1eq ▸ hxy1)
  · rcases hyz with hyz1 | ⟨hyz1eq, hyz2⟩
    · exact Or.inl (hxy1eq ▸ hyz1)
    · exact Or.inr ⟨hxy1eq.trans hyz1eq, hts _ _ _ hxy2 hyz2⟩

/-! ### Instances for the chain-`n` measure: nested `Nat`-lex of any fixed depth. -/

/-- The flat single-exp measure shape `Nat ×ₗ Nat` is well-founded (recovers the existing
`KhovanskiiReduction.lexLT_wf` from the combinator). -/
theorem natPairLex_wf :
    WellFounded (lexProd (· < · : Nat → Nat → Prop) (· < · : Nat → Nat → Prop)) :=
  lexProd_wf Nat.lt_wfRel.wf Nat.lt_wfRel.wf

/-- **The chain-2 measure shape `Nat ×ₗ (Nat ×ₗ Nat)` is well-founded** — the nesting the chain-aware
`lexMeasure` redesign requires (`(degreeY₁, (degreeY₀, trueDeg))`). Built by nesting the combinator. -/
theorem natTripleLex_wf :
    WellFounded (lexProd (· < · : Nat → Nat → Prop)
      (lexProd (· < · : Nat → Nat → Prop) (· < · : Nat → Nat → Prop))) :=
  lexProd_wf Nat.lt_wfRel.wf natPairLex_wf

/-- And chain-3 (`Nat ×ₗ Nat ×ₗ Nat ×ₗ Nat`), to show the nesting continues to any depth. -/
theorem natQuadLex_wf :
    WellFounded (lexProd (· < · : Nat → Nat → Prop)
      (lexProd (· < · : Nat → Nat → Prop)
        (lexProd (· < · : Nat → Nat → Prop) (· < · : Nat → Nat → Prop)))) :=
  lexProd_wf Nat.lt_wfRel.wf natTripleLex_wf

end MachLib.LexProd
