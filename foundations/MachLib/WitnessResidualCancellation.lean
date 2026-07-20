import MachLib.WitnessResidualDepth1

/-!
# Depth-1 boundedness propagation does NOT generalize to depth ≥ 2

Part of the 2026-07-19 continuation of Option D
(`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). `WitnessResidualDepth1.lean` showed: for
`T1 = eml A B` with `A, B` both LEAVES, boundedness of `T1` forces `A` and `B` to be
individually "nice" (constant, or the specific leaf combination fails). The natural next
question: does the same boundedness-propagation argument generalize once `A`, `B` are
allowed to be COMPOUND?

**No — and this file exhibits an explicit counterexample, not just an abstract worry.**
`T1 := eml var (eml (eml var (const (exp K))) (const 1))` — depth 3, both `A = var` and its
`B`-subtree are individually UNBOUNDED — evaluates to the exact CONSTANT `K`, for every real
`x`. Two unbounded ingredients cancel exactly, via `log_exp` twice. This is precisely the
"conspiratorial cancellation" the original witness-finding investigation's round 19 found as
an obstruction ("bounded siblings defeat the invariant") — now made fully explicit and
mechanically checked, not just asserted.

This tree itself is CONSTANT, so it doesn't violate the residual's own hypotheses (which need
`T1` non-constant) — but it proves boundedness of a compound tree is compatible with
unboundedness of its own subtrees, which is exactly what any general depth-≥2 argument for
the residual needs to contend with, rather than assume away.
-/

namespace MachLib
namespace Real

/-- The witness to conspiratorial cancellation: `eml var (const (exp K))` evaluates to
`exp x - K` exactly, via `log_exp`. -/
theorem cancellation_inner_eval (K x : Real) :
    (EMLTree.eml .var (.const (Real.exp K))).eval x = Real.exp x - K := by
  show Real.exp x - Real.log (Real.exp K) = Real.exp x - K
  rw [log_exp]

/-- The middle layer: `eml (eml var (const (exp K))) (const 1)` evaluates to
`exp(exp x - K)` exactly (`log 1 = 0` via `log_exp` at `K := 0`). -/
theorem cancellation_middle_eval (K x : Real) :
    (EMLTree.eml (.eml .var (.const (Real.exp K))) (.const 1)).eval x
      = Real.exp (Real.exp x - K) := by
  show Real.exp ((EMLTree.eml .var (.const (Real.exp K))).eval x) - Real.log 1 = _
  rw [cancellation_inner_eval]
  have h1 : Real.log 1 = 0 := by
    have := log_exp (0 : Real)
    rwa [exp_zero] at this
  rw [h1]
  have : Real.exp (Real.exp x - K) - 0 = Real.exp (Real.exp x - K) := by mach_ring
  rw [this]

/-- **The cancellation theorem.** `T1 := eml var (eml (eml var (const (exp K))) (const 1))`
is a depth-3 EML tree, with `A = var` unbounded and its own `B`-subtree also unbounded
(`exp(exp x - K)` blows up), yet `T1.eval x = K` — an exact CONSTANT — for every `x`. -/
theorem cancellation_theorem (K : Real) :
    ∀ x, (EMLTree.eml .var (.eml (.eml .var (.const (Real.exp K))) (.const 1))).eval x = K := by
  intro x
  show Real.exp x - Real.log ((EMLTree.eml (.eml .var (.const (Real.exp K))) (.const 1)).eval x) = K
  rw [cancellation_middle_eval, log_exp]
  mach_ring

end Real
end MachLib
