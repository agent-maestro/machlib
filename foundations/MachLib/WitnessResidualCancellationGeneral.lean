import MachLib.WitnessResidualCancellation

/-!
# The cancellation mechanism, generalized: any subtree, any target constant

`WitnessResidualCancellation.lean` exhibited ONE cancellation instance (`A = var`, target `K`)
proving boundedness of a compound tree is compatible with unboundedness of its own subtrees.
This file checks how general that mechanism actually is — the answer turns out to be: **completely
general**. For ANY tree `A` (leaf or arbitrarily compound) and ANY real `c0`, there is a canonical
partner tree making `eml A B` evaluate to EXACTLY `c0`, everywhere — the same two-layer
`log∘exp = id` telescoping the original example used, with `A` substituted in place of `var`
throughout.

**Why this matters for the residual.** The witness-finding residual (`EML_WITNESS_FINDING_
DECISION_2026_07_15.md`) needs a tree `T1` that is bounded above, non-constant, and NOT
`RightChildrenSimplePositive` (has a compound right child somewhere — `RightChildrenSimplePositive`
`T1`, unbounded `T1`, and constant `T1` are all already closed elsewhere in this arc). Every
`eml A B` produced by THIS construction has a compound right child (`B` is never a bare leaf) —
so it always lands outside `RightChildrenSimplePositive` — but it is also always EXACTLY
CONSTANT, never non-constant. This sharpens the open question from "does a bounded, non-constant,
non-simple `T1` exist" to something more pointed: **every INSTANCE of the one cancellation
mechanism actually available lands on a constant, never a genuinely non-constant bounded
function** — real (if not yet conclusive) evidence for the conjecture that EVERY bounded EML tree
is constant, which — if provable in general — would close the residual (hence the axiom) OUTRIGHT
by making its hypothesis vacuous, without ever touching `sin` or `log(c2+sin x)` specifically.

**Honest scope.** This file proves the general construction EXISTS and always cancels exactly —
it does NOT prove the converse (that no OTHER, non-cancellation-shaped construction could give a
bounded non-constant tree). That converse is the actual open question; this is one data point
toward it, not a resolution.
-/

namespace MachLib
namespace Real

/-- The generalized inner layer: `eml A (const (exp c0))` evaluates to `exp(A.eval x) - c0`
exactly, for ANY `A` — the `A = var` case of `cancellation_inner_eval`, with `A.eval x`
substituted for the bare `x` throughout the same one-line `log_exp` argument. -/
theorem eml_cancellation_inner_eval (A : EMLTree) (c0 x : Real) :
    (EMLTree.eml A (EMLTree.const (Real.exp c0))).eval x = Real.exp (A.eval x) - c0 := by
  show Real.exp (A.eval x) - Real.log (Real.exp c0) = Real.exp (A.eval x) - c0
  rw [log_exp]

/-- The generalized middle layer: `eml (eml A (const (exp c0))) (const 1)` evaluates to
`exp(exp(A.eval x) - c0)` exactly. -/
theorem eml_cancellation_middle_eval (A : EMLTree) (c0 x : Real) :
    (EMLTree.eml (EMLTree.eml A (EMLTree.const (Real.exp c0))) (EMLTree.const 1)).eval x
      = Real.exp (Real.exp (A.eval x) - c0) := by
  show Real.exp ((EMLTree.eml A (EMLTree.const (Real.exp c0))).eval x) - Real.log 1 = _
  rw [eml_cancellation_inner_eval]
  have h1 : Real.log 1 = 0 := by
    have := log_exp (0 : Real)
    rwa [exp_zero] at this
  rw [h1]
  have h2 : Real.exp (Real.exp (A.eval x) - c0) - 0 = Real.exp (Real.exp (A.eval x) - c0) := by
    mach_ring
  rw [h2]

/-- **The general cancellation theorem.** For ANY tree `A` and ANY real `c0`, `eml A (eml (eml A
(const (exp c0))) (const 1))` evaluates to EXACTLY `c0`, everywhere — no restriction on `A`
whatsoever (leaf, or arbitrarily deep and compound). The right child of the outer node is NEVER a
bare leaf (it's `eml (eml A (const (exp c0))) (const 1)`), so this tree is never
`RightChildrenSimplePositive` — every instance is a genuine, checkable example of a
non-`RightChildrenSimplePositive` tree, and it is ALWAYS constant. -/
theorem eml_cancellation_general (A : EMLTree) (c0 : Real) :
    ∀ x, (EMLTree.eml A
      (EMLTree.eml (EMLTree.eml A (EMLTree.const (Real.exp c0))) (EMLTree.const 1))).eval x
      = c0 := by
  intro x
  show Real.exp (A.eval x) -
      Real.log ((EMLTree.eml (EMLTree.eml A (EMLTree.const (Real.exp c0))) (EMLTree.const 1)).eval x)
      = c0
  rw [eml_cancellation_middle_eval, log_exp]
  mach_ring

/-- **Sanity check**: `cancellation_theorem` (`A = var`) re-derived as the special case
`eml_cancellation_general EMLTree.var K`, confirming the generalization is equivalent to the
original hand-built instance, not just structurally similar to it. -/
theorem cancellation_theorem_via_general (K : Real) :
    ∀ x, (EMLTree.eml .var (.eml (.eml .var (.const (Real.exp K))) (.const 1))).eval x = K :=
  eml_cancellation_general EMLTree.var K

end Real
end MachLib
