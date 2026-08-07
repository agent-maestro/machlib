import MachLib.EMLNamedTarget

/-!
# The bottom half — every tree has a deepest node, and it has four shapes

A2′ localized to census case 9 and produced the framing: **the naming resource (leaves) sits at the
BOTTOM of the tree, the target resource (`f`) at the TOP, and they do not meet.** Everything in this
arm to date descends from the root. **Nothing has ever looked up from the leaves** — there is no
subtree relation for `EMLTree` anywhere in `MachLib/`.

This file builds the bottom half:

* `IsSub` — the subtree relation, new to this corpus;
* `exists_leaf_pair_node` — **every tree of depth ≥ 1 contains a node whose BOTH children are
  leaves**;
* `leaf_pair_eval_four_shapes` — such a node's value is one of exactly **four** shapes.

## ⚠ AND IT DOES NOT CLOSE CASE 9 — which was pre-registered

`deepest_node_does_not_constrain_root` is the witness: **the same leaf-pair node `eml var var` sits
inside two trees whose root values differ at the same point.** So knowing the deepest node
constrains the root's target **not at all**.

> ### The two halves meet POSITIONALLY, not INFORMATIONALLY.
>
> The descent does arrive at a leaf-child node at its final step — but it arrives carrying an
> **already-unnamed** target, so the naming available there has nothing to attach to.

**Case 9 remains open. `1/x ∉ EML` remains open.** The deliverable here is that *"they do not meet"*
is now a checkable statement rather than a rhetorical one.
-/

namespace MachLib
namespace Real

open EMLTree

/-! ## The subtree relation -/

/-- `IsSub s t` — `s` occurs as a subtree of `t` (reflexively). New to this corpus. -/
inductive IsSub : EMLTree → EMLTree → Prop
  | refl (t : EMLTree) : IsSub t t
  | left {s t₁ t₂ : EMLTree} : IsSub s t₁ → IsSub s (EMLTree.eml t₁ t₂)
  | right {s t₁ t₂ : EMLTree} : IsSub s t₂ → IsSub s (EMLTree.eml t₁ t₂)

/-! ## Every tree of depth ≥ 1 has a node with two leaf children -/

/-- **The deepest node exists.** Structural induction: at `eml t₁ t₂`, either both children are
already leaves — take the node itself — or one has depth ≥ 1 and the IH supplies a leaf-pair node
inside it, lifted by `IsSub.left`/`IsSub.right`.

**No well-founded recursion needed**, which was the pre-registered expectation. -/
theorem exists_leaf_pair_node : ∀ t : EMLTree, 1 ≤ t.depth →
    ∃ u w : EMLTree, u.depth = 0 ∧ w.depth = 0 ∧ IsSub (EMLTree.eml u w) t := by
  intro t
  induction t with
  | const c => intro h; exact absurd h (by simp [EMLTree.depth])
  | var => intro h; exact absurd h (by simp [EMLTree.depth])
  | eml t₁ t₂ ih₁ ih₂ =>
    intro _
    rcases Nat.eq_zero_or_pos t₁.depth with h₁ | h₁
    · rcases Nat.eq_zero_or_pos t₂.depth with h₂ | h₂
      · exact ⟨t₁, t₂, h₁, h₂, IsSub.refl _⟩
      · obtain ⟨u, w, hu, hw, hsub⟩ := ih₂ h₂
        exact ⟨u, w, hu, hw, IsSub.right hsub⟩
    · obtain ⟨u, w, hu, hw, hsub⟩ := ih₁ h₁
      exact ⟨u, w, hu, hw, IsSub.left hsub⟩

/-! ## Four shapes, and no fifth -/

/-- **A node with two leaf children has one of exactly four value functions.** Two parameters at
most, and the first shape is constant-valued.

`exp a − log c` · `exp a − log x` · `exp x − log c` · `exp x − log x` -/
theorem leaf_pair_eval_four_shapes {u w : EMLTree} (hu : u.depth = 0) (hw : w.depth = 0) :
    (∃ a c : Real, ∀ x : Real, (EMLTree.eml u w).eval x = exp a - log c)
    ∨ (∃ a : Real, ∀ x : Real, (EMLTree.eml u w).eval x = exp a - log x)
    ∨ (∃ c : Real, ∀ x : Real, (EMLTree.eml u w).eval x = exp x - log c)
    ∨ (∀ x : Real, (EMLTree.eml u w).eval x = exp x - log x) := by
  rcases depth_zero_cases hu with ⟨a, ha⟩ | ha <;> rcases depth_zero_cases hw with ⟨c, hc⟩ | hc
  · exact Or.inl ⟨a, c, fun x => by rw [ha, hc]; rfl⟩
  · exact Or.inr (Or.inl ⟨a, fun x => by rw [ha, hc]; rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, fun x => by rw [ha, hc]; rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (fun x => by rw [ha, hc]; rfl)))

/-- **The first shape is the constant-valued one** — the only one of the four that does not vary.
Recorded because the census's closed case 7 turns on a constant-valued child. -/
theorem leaf_pair_const_const_is_constant (a c : Real) :
    ∀ x y : Real, (EMLTree.eml (EMLTree.const a) (EMLTree.const c)).eval x
      = (EMLTree.eml (EMLTree.const a) (EMLTree.const c)).eval y :=
  fun _ _ => rfl

/-! ## ⚠ The bottom half does NOT reach the top — the pre-registered witness -/

/-- **`eml var var` is a leaf-pair node of both trees below.** Same deepest node, both sides. -/
theorem shared_deepest_node :
    IsSub (EMLTree.eml EMLTree.var EMLTree.var)
        (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) (EMLTree.const 1))
    ∧ IsSub (EMLTree.eml EMLTree.var EMLTree.var)
        (EMLTree.eml (EMLTree.const 0) (EMLTree.eml EMLTree.var EMLTree.var)) :=
  ⟨IsSub.left (IsSub.refl _), IsSub.right (IsSub.refl _)⟩

/-- **THE WITNESS: the deepest node constrains the root's target NOT AT ALL.**

Both trees contain the same leaf-pair node `eml var var`, and their root values **differ at
`x = 1`**:

* `eml (eml var var) (const 1)` at `1` is `exp (exp 1 − log 1) − log 1 = exp (exp 1)`;
* `eml (const 0) (eml var var)` at `1` is `exp 0 − log (exp 1 − log 1) = 1 − 1 = 0`.

`exp (exp 1) ≠ 0` because `exp` is positive.

> ### So knowing a tree's deepest node tells you nothing about its root value function. The bottom half does not propagate upward on its own.
>
> **This is the pre-registered S3, confirmed.** The two halves meet positionally — the descent does
> reach a leaf-child node at its final step — but **informationally the target arriving there is
> already unnamed**, and nothing here fixes that. **Case 9 stays open.** -/
theorem deepest_node_does_not_constrain_root :
    (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) (EMLTree.const 1)).eval 1
      ≠ (EMLTree.eml (EMLTree.const 0) (EMLTree.eml EMLTree.var EMLTree.var)).eval 1 := by
  have hL : (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) (EMLTree.const 1)).eval 1
      = exp (exp 1) := by
    show exp (exp (1 : Real) - log (1 : Real)) - log (1 : Real) = exp (exp 1)
    rw [log_one]
    have e : exp (1 : Real) - 0 = exp 1 := by mach_ring
    rw [e]
    mach_ring
  have hR : (EMLTree.eml (EMLTree.const 0) (EMLTree.eml EMLTree.var EMLTree.var)).eval 1
      = 0 := by
    show exp (0 : Real) - log (exp (1 : Real) - log (1 : Real)) = 0
    rw [log_one]
    have e : exp (1 : Real) - 0 = exp 1 := by mach_ring
    rw [e, log_exp, exp_zero]
    mach_ring
  have hpos : 0 < exp (exp 1) := exp_pos _
  rw [hL, hR]
  intro hEq
  rw [hEq] at hpos
  exact lt_irrefl_ax 0 hpos

end Real
end MachLib
