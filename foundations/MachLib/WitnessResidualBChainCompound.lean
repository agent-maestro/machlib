import MachLib.WitnessResidualBOneLevelCompound

/-!
# The `≤1` mechanism, iterated to arbitrary depth

Continuation of the general-case attempt. `WitnessResidualBOneLevelCompound.lean` found that a
compound node `eml P (const c)` (`0 < c ≤ 1`) is provably positive for ANY `P` — a second,
independent mechanism alongside `RightChildrenSimplePositive`. That file's closure allowed `T1`'s
own right child `B` exactly ONE level of this compoundness, with `P` required
`RightChildrenSimplePositive`. This file asks the natural next question left open there: does
the `≤1` mechanism iterate — can `B` itself be `eml (eml P' (const c')) (const c)`, arbitrarily
deep, each layer contributing its own `≤1` constant?

**Yes, cleanly.** `GoodPositiveChain n t`: `t` is either a leaf (`var`/positive constant), or
`t = eml P (const c)` (`0 < c ≤ 1`) with `P` satisfying `GoodPositiveChain (n-1)` — a chain of up
to `n` nested `eml _ (const c)` layers, each with its own constant in `(0,1]`, bottoming out in a
simple leaf. Indexed by `Nat` rather than defined by direct structural recursion on `EMLTree`
specifically so the induction stays simple: `Nat`'s well-founded-ness carries the whole proof,
`EMLTree` only ever appears as an opaque existential witness at each layer, never itself
recursed into by the induction tactic — avoids the well-founded-recursion complexity a
`EMLTree`-structural version of this predicate would need (the witness `P` is nested inside an
`∃`, not reached by `EMLTree`'s own constructors the way `induction` expects).

**What this buys.** `no_T1_with_B_chain_compound`: `T1 = eml A B`, `A` `RightChildrenSimplePositive`,
`B` satisfying `GoodPositiveChain n` for ANY `n` — closes the same way every other result in this
arc does. `B` can now be an arbitrarily long chain of `≤1`-bounded compound layers, not just one.

**What this still doesn't do.** Each layer's `P` (the chain's own left branch at that layer) is
restricted to `GoodPositiveChain` (simple, or another `≤1` layer) — NOT the fully general
`RightChildrenSimplePositive` class `WitnessResidualBOneLevelCompound.lean` allowed at its one
layer. The two files are complementary, not one strictly subsuming the other: one trades chain
depth for left-branch generality, the other trades left-branch generality for chain depth. The
fully general case — `B` truly arbitrary — remains exactly where the wall-characterization entry
left it.
-/

namespace MachLib

open MachLib.Real

/-- Chains of up to `n` nested `eml _ (const c)` layers (`0 < c ≤ 1` per layer), bottoming out in
a simple leaf (`var` or a positive constant). -/
def GoodPositiveChain : Nat → EMLTree → Prop
  | 0, t => t = EMLTree.var ∨ ∃ c : Real, t = EMLTree.const c ∧ 0 < c
  | n + 1, t => (t = EMLTree.var ∨ ∃ c : Real, t = EMLTree.const c ∧ 0 < c) ∨
      ∃ P : EMLTree, ∃ c : Real, t = EMLTree.eml P (EMLTree.const c) ∧ 0 < c ∧ c ≤ 1 ∧
        GoodPositiveChain n P

/-- Every node in a `GoodPositiveChain` is provably positive at any `x0 > 0` — the leaf case is
immediate, the chain case is `eml_pos_of_right_const_le_one`, which needs nothing about the
layer's own left branch `P` at all. -/
theorem good_positive_chain_pos (n : Nat) :
    ∀ (t : EMLTree), GoodPositiveChain n t → ∀ x0 : Real, 0 < x0 → 0 < t.eval x0 := by
  induction n with
  | zero =>
    intro t ht x0 hx0
    rcases ht with hvar | ⟨c, hc, hcpos⟩
    · rw [hvar]; exact hx0
    · rw [hc]; exact hcpos
  | succ n _ihn =>
    intro t ht x0 hx0
    rcases ht with hsimple | ⟨P, c, heq, hc0, hc1, _hPgood⟩
    · rcases hsimple with hvar | ⟨c, hc, hcpos⟩
      · rw [hvar]; exact hx0
      · rw [hc]; exact hcpos
    · rw [heq]; exact eml_pos_of_right_const_le_one hc0 hc1 x0

/-- `EMLWitnesses` is free throughout a `GoodPositiveChain`, at any `x0 > 0` — each layer's
`(const c)` right child is trivially witnessed (leaf), the third conjunct is `hc0`, and the
layer's own left branch `P` is handled by the OUTER `Nat` induction's hypothesis, not by
recursing into `EMLTree`'s structure. -/
theorem good_positive_chain_witnesses (n : Nat) :
    ∀ (t : EMLTree), GoodPositiveChain n t → ∀ x0 : Real, 0 < x0 → EMLWitnesses t x0 := by
  induction n with
  | zero =>
    intro t ht x0 _hx0
    rcases ht with hvar | ⟨c, hc, _⟩
    · rw [hvar]; exact eml_witnesses_leaf_var x0
    · rw [hc]; exact eml_witnesses_leaf_const c x0
  | succ n ihn =>
    intro t ht x0 hx0
    rcases ht with hsimple | ⟨P, c, heq, hc0, _hc1, hPgood⟩
    · rcases hsimple with hvar | ⟨c, hc, _⟩
      · rw [hvar]; exact eml_witnesses_leaf_var x0
      · rw [hc]; exact eml_witnesses_leaf_const c x0
    · rw [heq]
      exact ⟨ihn P hPgood x0 hx0, trivial, hc0⟩

/-- `EMLNoCrossingAt` is free throughout a `GoodPositiveChain`, same shape as the witnesses
proof above. -/
theorem good_positive_chain_no_crossing (n : Nat) :
    ∀ (t : EMLTree), GoodPositiveChain n t → ∀ x0 : Real, 0 < x0 → EMLNoCrossingAt t x0 := by
  induction n with
  | zero =>
    intro t ht x0 _hx0
    rcases ht with hvar | ⟨c, hc, _⟩
    · rw [hvar]; trivial
    · rw [hc]; trivial
  | succ n ihn =>
    intro t ht x0 hx0
    rcases ht with hsimple | ⟨P, c, heq, hc0, _hc1, hPgood⟩
    · rcases hsimple with hvar | ⟨c, hc, _⟩
      · rw [hvar]; trivial
      · rw [hc]; trivial
    · rw [heq]
      exact ⟨ihn P hPgood x0 hx0, trivial, ne_of_gt hc0⟩

/-- **The closure, with `B` an arbitrarily deep `≤1`-chain.** Same overall shape and proof
skeleton as `no_T1_with_simple_right_children`/`no_T1_with_B_one_level_compound`; the only
difference is which lemmas supply `B`'s witness/no-crossing/positivity facts. -/
theorem no_T1_with_B_chain_compound
    {A B : EMLTree} {n : Nat} {cs : List Real} (hwf : nestedWF cs)
    (hA : RightChildrenSimplePositive A) (hB : GoodPositiveChain n B)
    (hT1eq : ∀ x, (EMLTree.eml A B).eval x = nestedTarget cs x) :
    False := by
  have hppos : (0 : Real) < pi + pi / (1 + 1) := pi_plus_pi_div_two_pos
  have hwitA : EMLWitnesses A (pi + pi / (1 + 1)) :=
    eml_witnesses_of_right_children_simple_positive A hA _ hppos
  have hwitB : EMLWitnesses B (pi + pi / (1 + 1)) := good_positive_chain_witnesses n B hB _ hppos
  have hBposAll : ∀ x, 0 < x → 0 < B.eval x := fun x hx => good_positive_chain_pos n B hB x hx
  have hwitT1 : EMLWitnesses (EMLTree.eml A B) (pi + pi / (1 + 1)) :=
    ⟨hwitA, hwitB, hBposAll _ hppos⟩
  have hncA : ∀ x, 0 < x → EMLNoCrossingAt A x :=
    fun x hx => eml_no_crossing_of_right_children_simple_positive A hA x hx
  have hncB : ∀ x, 0 < x → EMLNoCrossingAt B x :=
    fun x hx => good_positive_chain_no_crossing n B hB x hx
  have hncAll : ∀ x, 0 < x → EMLNoCrossingAt (EMLTree.eml A B) x :=
    fun x hx => ⟨hncA x hx, hncB x hx, ne_of_gt (hBposAll x hx)⟩
  have hDdAll : ∀ x, HasDerivAt (EMLTree.eml A B).eval (nestedTargetDeriv cs x) x := fun x =>
    HasDerivAt_of_eq (nestedTarget cs) (EMLTree.eml A B).eval (nestedTargetDeriv cs x) x
      (fun y => (hT1eq y).symm) (nestedTarget_hasDerivAt cs hwf x)
  have hvalidon_any_b : ∀ b : Real, 0 < b → EMLPfaffianValidOn (EMLTree.eml A B) 0 b := by
    intro b hb
    rcases lt_total b (pi + pi / (1 + 1)) with hbp | hbp | hbp
    · exact EMLPfaffianValidOn_mono_b (le_of_lt hbp)
        (eml_pfaffian_validon_of_witnesses_backward (EMLTree.eml A B) 0 (pi + pi / (1 + 1)) hppos
          (nestedTargetDeriv cs) (fun x _ _ => hDdAll x) (fun x hx1 _ => hncAll x hx1) hwitT1)
    · rw [hbp]
      exact eml_pfaffian_validon_of_witnesses_backward (EMLTree.eml A B) 0 (pi + pi / (1 + 1))
        hppos (nestedTargetDeriv cs) (fun x _ _ => hDdAll x) (fun x hx1 _ => hncAll x hx1) hwitT1
    · exact eml_pfaffian_validon_of_witnesses_twosided (EMLTree.eml A B) 0 b (pi + pi / (1 + 1))
        hppos hbp (nestedTargetDeriv cs) (fun x _ _ => hDdAll x) (fun x hx1 _ => hncAll x hx1)
        hwitT1
  exact no_tree_eq_nested_target_given_validon cs hwf (EMLTree.eml A B) hT1eq hvalidon_any_b

end MachLib
