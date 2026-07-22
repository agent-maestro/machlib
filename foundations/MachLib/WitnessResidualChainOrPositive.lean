import MachLib.WitnessResidualNonposChainClosure
import MachLib.WitnessResidualRightChildrenEverywherePositive

/-! # Unifying both mechanisms: the non-positive chain can stop anywhere it goes positive

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Follows cont. 47's
clarification that this whole `WitnessResidual*` sub-arc IS the Khovanskii-generalization plan's
remaining half — discharging `EMLPfaffianValidOn`/`hvalidon_any_b` for an arbitrary tree, not a
separate undertaking. This file is the first result to directly connect the two sides of that
half against each other: `RightChildrenEverywherePositive` (cont. 29, the "always positive"
extreme, closing this arc's first two witnesses) and `BChainNonpos`
(`WitnessResidualNonposChainClosure.lean`, cont. 44, the "always non-positive" extreme) were built
as two disjoint special cases. Neither needed the other's machinery — until now.

**The gap in `BChainNonpos`, precisely.** Its induction requires `B ≤ 0` everywhere at EVERY `eml`
node down the tree's left spine, bottoming out at a `const`/`var` leaf. A tree whose spine goes
`≤0, ≤0, ≤0, ...` for a while and then hits a node where the remaining subtree is
`RightChildrenEverywherePositive` was NOT covered — `BChainNonpos` had no way to "hand off" to the
positive-side machinery partway down.

**`BChainOrPositive` closes that gap.** At each `eml A B` node: EITHER the WHOLE remaining subtree
is `RightChildrenEverywherePositive` (closeable immediately — via
`EMLPfaffianValidOn_of_right_children_everywhere_positive` plus `no_tree_eq_nested_target_given_validon`,
the Khovanskii/zero-counting machinery this file's docstring above just reconnected with), OR `B`
is non-positive everywhere and the chain continues into `A` (exactly `BChainNonpos`'s own
reduction, unchanged). `no_tree_eq_nested_target_of_BChainOrPositive` STRICTLY generalizes both
prior results: setting the disjunct to "always right" at every node recovers `BChainNonpos`
exactly; setting it to "left, at the very top" recovers `RightChildrenEverywherePositive`'s own
closure. Any tree mixing the two patterns along its spine — non-positive for a while, then
provably-positive the rest of the way down — is now covered by ONE theorem instead of needing to
match one shape or the other exactly.

**Scope, stated plainly.** This is still not the fully general residual. The escape hatch fires
only when the REMAINING subtree, at the point the chain would otherwise continue, happens to be
FULLY `RightChildrenEverywherePositive` (every right child positive, all the way down, no
exceptions) — a tree that goes non-positive, then positive, then non-positive again further down
is NOT covered (the "positive" branch has no way to hand back to a non-positive continuation,
since `RightChildrenEverywherePositive` itself has no non-positive branch to escape into). The
truly mixed, alternating case remains open, same as before this file.

`sorryAx`-free, verified via a genuinely fresh rebuild. Depends on the arc's standard Khovanskii
trusted base (`IsAnalyticOnReals`/`analytic_*`/`rolle_ct`, via `no_tree_eq_nested_target_given_validon`)
plus the standard `HasDerivAt`/ordered-field foundation — this is the first theorem in the
`WitnessResidualNonposChainClosure`/`CrossingBoundednessBridge` lineage to touch the Khovanskii
side at all (everything built cont. 44-46 was purely elementary). No dependence on
`eml_pfaffian_validon_from_sin_equality` anywhere. -/

namespace MachLib
namespace Real

/-- A tree whose left spine, at every node, EITHER has the whole remaining subtree satisfying
`RightChildrenEverywherePositive` (closeable immediately via the Khovanskii/positivity machinery),
OR has its right child non-positive everywhere (continue the chain into the left child). Strictly
generalizes both `BChainNonpos` (always takes the right disjunct) and
`RightChildrenEverywherePositive` itself (always takes the left disjunct, at the very top). -/
def BChainOrPositive : EMLTree → Prop
  | EMLTree.const _ => True
  | EMLTree.var => True
  | EMLTree.eml A B =>
      RightChildrenEverywherePositive (EMLTree.eml A B) ∨
        ((∀ x : Real, B.eval x ≤ 0) ∧ BChainOrPositive A)

/-- **The unified closure.** No tree satisfying `BChainOrPositive` can equal any member of the
nested-target family — combining the Khovanskii/zero-counting closure
(`no_tree_eq_nested_target_given_validon`, fired when the positive escape hatch applies) with the
non-positive chain's own reduction+recursion (`BChainNonpos`'s mechanism, unchanged) in a single
structural induction. -/
theorem no_tree_eq_nested_target_of_BChainOrPositive :
    ∀ (T : EMLTree), BChainOrPositive T →
      ∀ (cs : List Real), nestedWF cs → (∀ x : Real, T.eval x = nestedTarget cs x) → False := by
  intro T
  induction T with
  | const c => intro _ cs hwf hT1eq; exact const_ne_nestedTarget c cs hwf hT1eq
  | var => intro _ cs hwf hT1eq; exact var_ne_nestedTarget cs hwf hT1eq
  | eml A B ihA _ihB =>
    intro hchain cs hwf hT1eq
    rcases hchain with hpos | ⟨hBnonpos, hAchain⟩
    · have hvalidon : ∀ b : Real, 0 < b → EMLPfaffianValidOn (EMLTree.eml A B) 0 b :=
        fun b _ => EMLPfaffianValidOn_of_right_children_everywhere_positive hpos 0 b
      exact no_tree_eq_nested_target_given_validon cs hwf (EMLTree.eml A B) hT1eq hvalidon
    · have hexpA : ∀ x : Real, Real.exp (A.eval x) = nestedTarget cs x := by
        intro x
        have hred := eml_A_B_eq_exp_A_of_nonpos A B hBnonpos x
        rw [← hred]; exact hT1eq x
      have hcontra_of_le : nestedLo cs ≤ 0 → False := by
        intro hle
        have hx0 := hexpA (-(pi / (1 + 1)))
        rw [nestedTarget_at_neg_pi_div_two cs hwf] at hx0
        have hpos := Real.exp_pos (A.eval (-(pi / (1 + 1))))
        rw [hx0] at hpos
        exact lt_irrefl_ax 0 (lt_of_lt_of_le hpos hle)
      rcases lt_total (nestedLo cs) 0 with hlo | hlo | hlo
      · exact hcontra_of_le (le_of_lt hlo)
      · exact hcontra_of_le (le_of_eq hlo)
      · have hwf0 : nestedWF (0 :: cs) := by
          refine ⟨?_, hwf⟩
          rw [zero_add]; exact hlo
        have hAeq : ∀ x : Real, A.eval x = nestedTarget (0 :: cs) x := by
          intro x
          rw [nestedTarget_cons, zero_add, ← hexpA x, log_exp]
        exact ihA hAchain (0 :: cs) hwf0 hAeq

end Real
end MachLib
