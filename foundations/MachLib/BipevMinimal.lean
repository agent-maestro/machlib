import MachLib.BipevElim

/-!
# Minimal degree — on a budget after all

Step 1 of the three `BipevExpDeriv` listed, and the last. Its docstring calls for "a well-founded
induction on the degree, on relations rather than on lists", and the previous commit flagged it as
the only step in the arc needing genuine well-founded recursion rather than a fuel budget.

**That was wrong, and the correction is cheap.** "Minimal degree" is the least element of a nonempty
set of naturals, and the well-ordering of `ℕ` *is* a budget: strong induction on a degree bound
gives it directly. No custom well-founded relation, no termination measure on relations, nothing the
other twenty-two modules did not already do.

The argument in one line: given a relation of length `≤ n+1`, either some relation has length `≤ n`
— recurse — or none does, in which case the one in hand is already minimal. `Classical.em` decides
which, on a statement about naturals rather than about relations.

## Stated generically

`exists_minimal_length` is about an arbitrary predicate on lists over an arbitrary type. Nothing in
it mentions `bipev`, `exp` or `Real`, which is why it needs neither — its footprint is Lean core
alone. The relation-specific form is a one-line instantiation.

That genericity is not tidiness: it is what makes the lemma's *cost* visible. A minimal-degree
argument that mentioned the relation would have looked like it needed something about relations, and
it does not.
-/

namespace MachLib

open Real

/-! ## A nonempty predicate on lists has a member of minimal length -/

theorem exists_minimal_length {α : Type} (Pr : List α → Prop) :
    ∀ (n : Nat) (Ls : List α), Pr Ls → Ls.length ≤ n →
      ∃ Ms : List α, Pr Ms ∧ ∀ Ns : List α, Pr Ns → Ms.length ≤ Ns.length := by
  intro n
  induction n with
  | zero =>
      intro Ls hL hlen
      refine ⟨Ls, hL, fun Ns _ => ?_⟩
      omega
  | succ n ih =>
      intro Ls hL hlen
      rcases Classical.em (∃ Ns : List α, Pr Ns ∧ Ns.length ≤ n) with ⟨Ns, hN, hNlen⟩ | hno
      · exact ih Ns hN hNlen
      · refine ⟨Ls, hL, fun Ns hNs => ?_⟩
        have hgt : ¬ Ns.length ≤ n := fun h => hno ⟨Ns, hNs, h⟩
        omega

/-- The budget-free form: the length of the list in hand is always enough. -/
theorem exists_minimal_length' {α : Type} (Pr : List α → Prop) {Ls : List α} (h : Pr Ls) :
    ∃ Ms : List α, Pr Ms ∧ ∀ Ns : List α, Pr Ns → Ms.length ≤ Ns.length :=
  exists_minimal_length Pr Ls.length Ls h (Nat.le_refl _)

/-! ## The relation predicate -/

/-- The relation `Σ pⱼ·exp(S x)ʲ = 0` holds on a tail. -/
def EvRel (S : Real → Real) (Ls : List (List Real)) : Prop :=
  ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → bipev Ls x (exp (S x)) = 0

/-- A relation that is genuinely of its stated degree: it holds, and its leading coefficient is not
eventually zero. Without the second clause "minimal degree" is vacuous — padding with zero
coefficients would make every degree achievable. -/
def ProperRel (S : Real → Real) (Ls : List (List Real)) : Prop :=
  EvRel S Ls ∧ ∃ (L₀ : List (List Real)) (A : List Real),
    Ls = L₀ ++ [A] ∧ ¬ EvZeroF (pev A)

/-- **A relation of minimal degree exists**, given any proper relation at all. Step 1, complete. -/
theorem exists_minimal_rel {S : Real → Real} {Ls : List (List Real)} (h : ProperRel S Ls) :
    ∃ Ms : List (List Real), ProperRel S Ms ∧
      ∀ Ns : List (List Real), ProperRel S Ns → Ms.length ≤ Ns.length :=
  exists_minimal_length' (ProperRel S) h

end MachLib
