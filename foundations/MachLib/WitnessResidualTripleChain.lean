import MachLib.WitnessResidualChainOrPositive
import MachLib.WitnessResidualCrossingBoundednessBridge

/-! # All three mechanisms unified: positive, crossing, non-positive

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). `BChainOrPositive`
(cont. 48, `WitnessResidualChainOrPositive.lean`) unified two of the three mechanisms this arc has
built: `RightChildrenEverywherePositive` (the Khovanskii escape) and `BChainNonpos`'s own
non-positive reduction. That file's own docstring named the remaining gap precisely: the positive
escape hatch is all-or-nothing over the WHOLE remaining subtree, so a node whose failure to be
`RightChildrenEverywherePositive` is caused specifically by its own immediate right child
GENUINELY CROSSING zero (not failing for some other, deeper reason) had no way to close directly.

**It didn't need a new mechanism — the crossing bridge (cont. 45-46,
`WitnessResidualCrossingBoundednessBridge.lean`) already closes exactly this case, and closes it
MORE directly than the other two escapes**: `no_eml_A_B_eq_nested_target_of_crossing_and_no_crossing`
derives `False` straight from `(eml A B).eval = nestedTarget cs` whenever `B` genuinely crosses
zero on some `[x0,x1]` with `EMLNoCrossingAt` there — no recursion into `A` needed at all, unlike
the other two branches (the positive escape needs the Khovanskii bound; the non-positive branch
needs to recurse one level deeper with a shifted target). Adding it as a third disjunct in the
chain definition was a direct, mechanical extension — no new proof technique, just wiring an
already-existing closure into the induction's crossing branch.

**`BChainTriple`**: at each `eml A B` node, three ways to close instead of two —
`RightChildrenEverywherePositive` (Khovanskii escape, needs the WHOLE remaining subtree),
`B` genuinely crosses zero with `EMLNoCrossingAt` on the crossing interval (crossing-bridge escape,
immediate, needs nothing about `A` or the rest of the tree at all), or `B` non-positive everywhere
(continue the chain into `A`, `BChainNonpos`'s reduction, unchanged). `BChainOrPositive` is exactly
the case where the crossing disjunct is never taken; `BChainNonpos` is exactly the case where
neither of the first two ever is.

**Scope, stated plainly — still not the fully general residual.** The crossing disjunct requires
an EXPLICIT crossing (`B.eval x0 = 0` exactly, `B.eval x1 > 0`, `EMLNoCrossingAt` throughout
`[x0,x1]`) — a `B` that dips non-positive somewhere and rises positive elsewhere WITHOUT a clean
zero crossing at a controllable point (e.g. touching `0` only asymptotically, or having a genuinely
unknown/unverifiable `EMLNoCrossingAt` on the relevant interval) is still not covered by any of the
three mechanisms. This file's contribution is combining what already existed into one theorem, not
discovering new territory — the remaining gap is the same one named at the end of
`WitnessResidualClosureAttempt.lean` (cont. 43): a truly unconstrained `B`, structurally unknown,
with no promise of any of these three specific behaviors.

`sorryAx`-free, verified via a genuinely fresh rebuild. Compiled clean on the first attempt. No
`eml_pfaffian_validon_from_sin_equality` dependence. -/

namespace MachLib
namespace Real

/-- Three ways to close at each node instead of two: `RightChildrenEverywherePositive` (Khovanskii
escape), `B` genuinely crosses zero with `EMLNoCrossingAt` on the crossing interval (crossing-bridge
escape, immediate — no recursion needed), or `B` non-positive everywhere (continue the chain). -/
def BChainTriple : EMLTree → Prop
  | EMLTree.const _ => True
  | EMLTree.var => True
  | EMLTree.eml A B =>
      RightChildrenEverywherePositive (EMLTree.eml A B) ∨
      (∃ x0 x1 : Real, x0 < x1 ∧ B.eval x0 = 0 ∧ 0 < B.eval x1 ∧
        ∀ z : Real, x0 ≤ z → z ≤ x1 → MachLib.EMLNoCrossingAt B z) ∨
      ((∀ x : Real, B.eval x ≤ 0) ∧ BChainTriple A)

/-- **The three-way unified closure.** No tree satisfying `BChainTriple` can equal any member of
the nested-target family — combining the Khovanskii/zero-counting closure, the crossing-bridge
closure, and the non-positive chain's own reduction+recursion in a single structural induction. -/
theorem no_tree_eq_nested_target_of_BChainTriple :
    ∀ (T : EMLTree), BChainTriple T →
      ∀ (cs : List Real), nestedWF cs → (∀ x : Real, T.eval x = nestedTarget cs x) → False := by
  intro T
  induction T with
  | const c => intro _ cs hwf hT1eq; exact const_ne_nestedTarget c cs hwf hT1eq
  | var => intro _ cs hwf hT1eq; exact var_ne_nestedTarget cs hwf hT1eq
  | eml A B ihA _ihB =>
    intro hchain cs hwf hT1eq
    rcases hchain with hpos | ⟨x0, x1, hx0x1, hBx0, hBx1pos, hnc⟩ | ⟨hBnonpos, hAchain⟩
    · have hvalidon : ∀ b : Real, 0 < b → EMLPfaffianValidOn (EMLTree.eml A B) 0 b :=
        fun b _ => EMLPfaffianValidOn_of_right_children_everywhere_positive hpos 0 b
      exact no_tree_eq_nested_target_given_validon cs hwf (EMLTree.eml A B) hT1eq hvalidon
    · exact no_eml_A_B_eq_nested_target_of_crossing_and_no_crossing A B x0 x1 hx0x1 hBx0 hBx1pos
        hnc cs hwf hT1eq
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
