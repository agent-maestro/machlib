import MachLib.EMLDepthTameness

/-!
# The depth-≤2 classification, packaged as a predicate

`depth_le_two_normal_form` (`EMLDepthTameness:5896`) already classifies every depth-≤2 tree:
constant, the identity, or `exp a − log b` with `a` and `b` both in `Depth1Form`. It states that
classification **inline**, about a tree. Depth 1 does not: it has a named predicate `Depth1Form`
together with a one-line wrapper `depth_le_one_form` carrying a tree into it, and that predicate is
what the depth-2 classification itself consumes in its third disjunct.

This file supplies the missing rung of that pattern — `Depth2Form` plus the wrapper — so the depth-3
classification can consume it the same way depth 2 consumes `Depth1Form`.

**Why a predicate rather than the inline statement.** The consumer is a *function*, not a tree: the
depth-3 branch lemmas destructure a node into `exp (a x) − log (b x)` and then need to say "and `a`
is itself a depth-2 shape". There is no tree left at that point to apply `depth_le_two_normal_form`
to. This is exactly why `Depth1Form` exists one level down, and the third disjunct below is where it
is used.

No new mathematics: the wrapper is definitional unfolding, and the proof term is the classification
itself. The content is the packaging, and the packaging is what the next rung is blocked on.
-/

namespace MachLib

open Real

/-- **Normal form at depth ≤ 2, as a predicate on the value function.** Constant, the identity, or
`exp a − log b` with both `a` and `b` in `Depth1Form`. Mirrors `Depth1Form` one level up. -/
def Depth2Form (f : Real → Real) : Prop :=
  (∃ c : Real, ∀ x : Real, 0 < x → f x = c)
  ∨ (∀ x : Real, 0 < x → f x = x)
  ∨ (∃ a b : Real → Real, Depth1Form a ∧ Depth1Form b ∧
      ∀ x : Real, 0 < x → f x = exp (a x) - log (b x))

/-- **Every depth-≤2 tree has `Depth2Form`.** The depth-2 analogue of `depth_le_one_form`; the
classification is `depth_le_two_normal_form`, and this is the wrapper that makes it usable where
only the value function survives. -/
theorem depth_le_two_form (t : EMLTree) (ht : t.depth ≤ 2) : Depth2Form t.eval := by
  -- `depth_le_one_form` needs no unfold because `depth_le_one_classification` already *concludes*
  -- `Depth1Form`. The depth-2 classification states its disjunction inline, so the wrapper has to
  -- open the definition — the one structural difference between the two rungs.
  unfold Depth2Form
  exact depth_le_two_normal_form t ht

end MachLib
