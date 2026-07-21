import MachLib.EMLZeroCrossingDomainSplit
import MachLib.FPModel

/-! # A genuine right-child crossing forces unboundedness — closing off the cont. 36 witness hunt

Turns the cont. 36 numeric finding (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`) — that
`nonMonotonicWitness` and a fresh double-crossing construction both turned out unbounded, no
matter how the "absorb the blow-up" wrapping was arranged — into a PROVEN, general fact instead
of accumulated numeric evidence. The mechanism, worked out on paper before any Lean (per house
style): `eml A B := exp(A) - log(B)`. `exp(A) ≥ 0` ALWAYS, for any `A` — it can never go negative,
so it can never cancel `-log(B)`'s divergence to `+∞` as `B → 0⁺`. If `B`'s own closed form lets
`B(x)` be driven to any target value `ε > 0` (which `eml var (const c)` trivially does — it's the
explicit inverse of `log`), then `eml A B` is UNBOUNDED ABOVE, for literally ANY `A` — no
constraint on `A`'s own shape, boundedness, or structure needed at all.

**The witness, fully explicit — no Taylor/derivative bound on `exp` needed.** For target `M`, set
`x_M := log(exp(-(M+1)) + log c)`. Then `exp(x_M) = exp(-(M+1)) + log c` (`exp_log`, valid since
the argument is a sum of two positive reals), so the right child's value works out to EXACTLY
`exp(-(M+1))` — not merely small, but the SPECIFIC value needed, by construction (`eml var
(const c)`'s own definition is the literal algebraic inverse of `log`, so any target value is
reachable in closed form, not just approximated). Then `-log(exp(-(M+1))) = M+1` exactly
(`log_exp`), and `eml A B(x_M) = exp(A.eval x_M) - (-(M+1)) ≥ 0 + (M+1) > M`.

**Why this matters beyond explaining one numeric observation.** This closes off item (2) from
cont. 34/35's scoping in the NEGATIVE, for the whole family of constructions built from this
crossing shape: `nonMonotonicWitness`'s own `N` node is EXACTLY an instance
(`A := eml var (const 1)`, `c := 1+1`, confirmed below as a direct corollary) — so its
unboundedness isn't a coincidence of THIS particular tree, it's forced by the shape, regardless of
what sits to the left. Any future attempt to build a bounded witness with a genuine, continuous,
transversal right-child crossing at a finite point runs into the SAME obstruction — `exp(A)≥0`
can never supply the compensating `-∞` a cancellation would need. Doesn't rule out EVERY possible
crossing shape (a crossing subtree WITHOUT an explicit closed-form inverse might, in principle,
behave differently — not investigated), but rules out the entire class this arc has actually
tried so far (`eml var (const c)`, the only crossing primitive used anywhere in the arc's
constructions). `sorryAx`-free, only foundational `MachLib.Real` ordered-field/exp/log axioms —
verified via a genuinely fresh rebuild. -/

namespace MachLib
namespace Real

/-- **Any tree `eml A (eml var (const c))` (`c>1`) is unbounded ABOVE**, for ANY `A` whatsoever.
Explicit witness: for target `M`, `x_M := log(exp(-(M+1)) + log c)` makes the right child's value
EXACTLY `exp(-(M+1))` (via `exp_log`/the crossing's own invertibility — no Taylor/derivative bound
on `exp` needed at all), so `-log(right child) = M+1`, and `exp(A.eval x_M) ≥ 0` can never cancel
that. -/
theorem eml_A_crossing_var_const_unbounded_above (A : EMLTree) (c : Real) (hc : 1 < c) (M : Real) :
    ∃ x : Real, M < (EMLTree.eml A (EMLTree.eml EMLTree.var (EMLTree.const c))).eval x := by
  have hlogc_pos : 0 < Real.log c := log_pos_of_gt_one hc
  have harg_pos : 0 < Real.exp (-(M + 1)) + Real.log c := add_pos (Real.exp_pos _) hlogc_pos
  let x : Real := Real.log (Real.exp (-(M + 1)) + Real.log c)
  refine ⟨x, ?_⟩
  have hexpx : Real.exp x = Real.exp (-(M + 1)) + Real.log c := Real.exp_log harg_pos
  have hDx : (EMLTree.eml EMLTree.var (EMLTree.const c)).eval x = Real.exp (-(M + 1)) := by
    show Real.exp x - Real.log c = _
    rw [hexpx]
    mach_ring
  have hTx : (EMLTree.eml A (EMLTree.eml EMLTree.var (EMLTree.const c))).eval x
      = Real.exp (A.eval x) - Real.log (Real.exp (-(M + 1))) := by
    show Real.exp (A.eval x) - Real.log ((EMLTree.eml EMLTree.var (EMLTree.const c)).eval x) = _
    rw [hDx]
  rw [hTx, Real.log_exp]
  have hexpA : (0 : Real) ≤ Real.exp (A.eval x) := le_of_lt (Real.exp_pos _)
  have hstep : M + 1 ≤ Real.exp (A.eval x) - -(M + 1) := by
    have h1 : (0 : Real) - -(M + 1) ≤ Real.exp (A.eval x) - -(M + 1) :=
      sub_le_sub_right hexpA (-(M + 1))
    have h2 : (0 : Real) - -(M + 1) = M + 1 := by mach_ring
    rwa [h2] at h1
  have hlt : M < M + 1 := by
    have h := add_lt_add_left zero_lt_one_ax M
    rwa [add_zero] at h
  exact lt_of_lt_of_le hlt hstep

/-- **Confirms the cont. 36 numeric finding**: `nonMonotonicWitness`'s own `N` node
(`WitnessResidualNonMonotonic.lean`) is EXACTLY an instance of the shape above
(`A := eml var (const 1)`, `c := 1+1`) — its unboundedness (found numerically, a slow
log-of-log divergence easy to miss at coarse resolution) is not a fluke of that specific
construction, it's forced. -/
theorem nonMonotonicWitness_N_unbounded_above (M : Real) :
    ∃ x : Real, M < (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
      (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1)))).eval x := by
  have hc : (1 : Real) < 1 + 1 := by
    have h := add_lt_add_left zero_lt_one_ax 1
    rwa [add_zero] at h
  exact eml_A_crossing_var_const_unbounded_above (EMLTree.eml EMLTree.var (EMLTree.const 1))
    (1 + 1) hc M

end Real
end MachLib
