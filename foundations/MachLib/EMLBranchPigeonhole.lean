import MachLib.EMLTerminationRoute

/-!
# A5 is a COST, not an obstruction — three points beat non-uniform branching

`EMLTerminationRoute.lean`'s `branch_not_uniform` showed `node_pins_a_child`'s disjunct genuinely
moves with `x`, and A5 (*branch uniformity in `x`*) was filed as a newly-identified open obligation.

> ## ⚠ THAT FILING WAS AN OVERSTATEMENT, AND THIS FILE RETRACTS IT.

**The arm's arguments never needed uniformity — they need TWO POINTS.** Two branch classes, three
points, **pigeonhole**: two of any three land in the same class, and on those two the SAME child is
pinned.

`shared_branch_descent` is the statement A5 claimed did not follow:

> ### ONE child, TWO points, and STRICTLY SHALLOWER — from three points, with no uniformity anywhere.

## The cost, and why it is only a cost

Keeping ≥2 points in a consistent class through `d` levels costs `pointBudget d = 2^d + 1` points
(`pointBudget_eq`). **Finite for every fixed `d`, and `(0,∞)` supplies as many distinct points as
anyone wants.** So the price of non-uniform branching is exponentially many points and a disjunction
over which pair survives — **a cost, not an obstruction.**

## ⚠ WHAT IS AND IS NOT PROVED HERE

**Proved:** the ONE-LEVEL descent (`shared_branch_descent`) and the budget recurrence
(`pointBudget_eq`).

**NOT proved:** the `d`-level induction itself. Iterating `shared_branch_descent` down to a leaf
needs list/finite-set bookkeeping this corpus does not have to hand. **`pointBudget` is the count
that induction would need — stating it is not running it.**

**And none of this moves `1/x ∉ EML`.** A2′ — *a NAMED target on the varying-left branch* — is the
real obstacle and is untouched here. Removing an obligation added the same morning is bookkeeping,
not progress.
-/

namespace MachLib
namespace Real

open EMLTree

/-! ## The pigeonhole -/

/-- Two-way sign split. `lt_total` is the three-way axiom this corpus has; the middle case joins the
non-positive side. -/
theorem pos_or_nonpos (v : Real) : 0 < v ∨ v ≤ 0 := by
  rcases lt_total v 0 with h | h | h
  · exact Or.inr (le_of_lt h)
  · exact Or.inr (le_of_eq h)
  · exact Or.inl h

/-- **Pigeonhole: two of any three points share a branch class.** Two classes, three points.

**No hypothesis on the points** — they need not be distinct, positive, or ordered. The conclusion
names which pair by an explicit disjunction rather than a set, so it stays inside the corpus's
Mathlib-free idiom. -/
theorem two_of_three_share_branch (w : EMLTree) (x₁ x₂ x₃ : Real) :
    ∃ a b : Real,
      ((a = x₁ ∧ b = x₂) ∨ (a = x₁ ∧ b = x₃) ∨ (a = x₂ ∧ b = x₃)) ∧
      ((0 < w.eval a ∧ 0 < w.eval b) ∨ (w.eval a ≤ 0 ∧ w.eval b ≤ 0)) := by
  rcases pos_or_nonpos (w.eval x₁) with h1 | h1 <;>
    rcases pos_or_nonpos (w.eval x₂) with h2 | h2 <;>
      rcases pos_or_nonpos (w.eval x₃) with h3 | h3
  · exact ⟨x₁, x₂, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨h1, h2⟩⟩
  · exact ⟨x₁, x₂, Or.inl ⟨rfl, rfl⟩, Or.inl ⟨h1, h2⟩⟩
  · exact ⟨x₁, x₃, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inl ⟨h1, h3⟩⟩
  · exact ⟨x₂, x₃, Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inr ⟨h2, h3⟩⟩
  · exact ⟨x₂, x₃, Or.inr (Or.inr ⟨rfl, rfl⟩), Or.inl ⟨h2, h3⟩⟩
  · exact ⟨x₁, x₃, Or.inr (Or.inl ⟨rfl, rfl⟩), Or.inr ⟨h1, h3⟩⟩
  · exact ⟨x₁, x₂, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨h1, h2⟩⟩
  · exact ⟨x₁, x₂, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨h1, h2⟩⟩

/-! ## The descent A5 said did not follow -/

/-- **ONE child, TWO points, strictly shallower — from three points.**

`branch_not_uniform` is still true: the branch really does move with `x`. **It just does not
matter.** Pigeonhole finds two points sharing a class, `node_pins_a_child`'s two branches pin the
SAME child on both, and that child is a strict subtree either way.

> **This is exactly the functional descent A5 claimed did not follow from `node_pins_a_child`.** It
> follows, at the price of one extra point and a disjunction over which pair survives. -/
theorem shared_branch_descent (u w : EMLTree) {f : Real → Real} (x₁ x₂ x₃ : Real)
    (e : ∀ x : Real, (EMLTree.eml u w).eval x = f x) :
    ∃ (s : EMLTree) (a b : Real),
      s.depth < (EMLTree.eml u w).depth ∧
      ((a = x₁ ∧ b = x₂) ∨ (a = x₁ ∧ b = x₃) ∨ (a = x₂ ∧ b = x₃)) ∧
      ((s.eval a = exp (exp (u.eval a) - f a) ∧ s.eval b = exp (exp (u.eval b) - f b)) ∨
        (s.eval a = log (f a) ∧ s.eval b = log (f b))) := by
  obtain ⟨a, b, hpair, hbranch⟩ := two_of_three_share_branch w x₁ x₂ x₃
  rcases hbranch with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨w, a, b, depth_right_lt u w, hpair,
      Or.inl ⟨pins_right u w ha (e a), pins_right u w hb (e b)⟩⟩
  · exact ⟨u, a, b, depth_left_lt u w, hpair,
      Or.inr ⟨clamped_pins_left ha (e a), clamped_pins_left hb (e b)⟩⟩

/-! ## The point budget

**This is the COUNT the `d`-level induction would need. Stating it is not running it.** -/

/-- Points needed to keep ≥2 in a consistent branch class through `d` levels. Each level halves
(rounding up), so recovering `n` at the next level costs `2n − 1` here. -/
def pointBudget : Nat → Nat
  | 0 => 2
  | (n + 1) => 2 * pointBudget n - 1

/-- **`pointBudget d = 2^d + 1`** — finite for every `d`, and `(0,∞)` has that many points to spare.

**So non-uniform branching costs exponentially many points and nothing else.** That is why A5 is a
cost rather than an obstruction. -/
theorem pointBudget_eq (d : Nat) : pointBudget d = 2 ^ d + 1 := by
  induction d with
  | zero => rfl
  | succ n ih =>
    show 2 * pointBudget n - 1 = 2 ^ (n + 1) + 1
    rw [ih, Nat.pow_succ]
    omega

end Real
end MachLib
