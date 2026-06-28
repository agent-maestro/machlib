import MachLib.SingleExpKhovanskii
import MachLib.KhovanskiiReduction
import MachLib.MultiPolyToPoly
import MachLib.PfaffianFnBound
import MachLib.ChainExp2PathC
import MachLib.MultiPolyReconstruct
import MachLib.PolynomialCanonical
import MachLib.PIDCapstone
import MachLib.CoreModel
import MachLib.FPModel

/-!
# Axiom Audit — Constructive Khovanskii Closure (2026-06-13/14, revised 2026-06-16)

Verify the axiom dependencies of the major theorems shipped today.
Each `#print axioms` invocation lists the transitive axiom closure
of the named theorem. We expect only MachLib's documented foundational
axioms (Real arithmetic, HasDerivAt, Rolle, MVT prerequisites).

Any axiom NOT in MachLib's documented foundations is a finding to
investigate before announcement.

## 2026-06-16 revision

`PfaffianFnBound.khovanskii_chain_step` axiom RETIRED.
`pfaffian_fn_zero_count_bound` is now a thin wrapper around
`KhovanskiiReduction.khovanskii_bound_full` (takes a reduction
witness). This eliminates one classical axiom from the closure.
-/

open MachLib.SingleExpKhovanskii.ExpPoly
open MachLib.PfaffianChainMod

/-! ## ExpPoly track (path iii — parametric capstone) -/

#print axioms expPoly_khovanskii_bound

/-! ## ExpPoly track (path i — auto-bound with propagation) -/

#print axioms expPoly_auto_bound_with_propagation_aux

/-! ## ExpPoly track (path ii — ODE corner case) -/

#print axioms expPoly_ode_no_zeros

/-! ## ExpPoly track (length-1 auto-bound) -/

#print axioms expPoly_zero_count_auto_bound_length_one

/-! ## PfaffianFn track (non-degenerate capstone) -/

#print axioms PfaffianFn.khovanskii_bound_full

/-! ## PfaffianFnBound track (witness-wrapper, post axiom retirement) -/

#print axioms MachLib.PfaffianFnBound.pfaffian_fn_zero_count_bound

/-! ## ExpPoly substrate: ring identity (path-b hand-prove) -/

#print axioms scaledReduction_eval_combine

/-! ## Per-coefficient lemmas (auto-bound substrate) -/

#print axioms coeffStep_degreeUpper_polySimplify_lt
#print axioms coeffStep_eq_const_zero_when_degreeUpper_zero

/-! ## List-level strict descent -/

#print axioms sumSimplifiedDegrees_scaledReductionAux_lt

/-! ## SingleExp chain instance -/

#print axioms SingleExpChain_isCoherentAt
#print axioms SingleExpChain_isTriangular

/-! ## Path-c constructive Khovanskii closure (2026-06-17 audit)

The new constructive framework: PolynomialCanonical (canonicalizer)
+ MultiPolyReconstruct (bridge) + ChainExp2PathC (dispatch +
capstone). Expected axiom footprint: the same MachLib foundations
above, plus `Classical.choice`, `propext`, `Quot.sound` (Lean 4
standard). Anything else is a finding. -/

section PathC

open MachLib.ChainExp2PathC
open MachLib.PolynomialCanonical
open MachLib.MultiPolyReconstruct
open MachLib.PfaffianChainMod

-- The end-to-end capstone (item 1). Captures the full path-c chain.
#print axioms singleExp_khovanskii_bound

-- Generic SDR wrapper (item 2).
#print axioms singleExp_to_generic_sdr

-- Dispatch reducer.
#print axioms PfaffianFn.singleExp_dispatch_step

-- Closed SingleExp ReduceStep constructors.
#print axioms PfaffianFn.singleExp_reduceStep_closed
#print axioms PfaffianFn.singleExp_canonicalTrim_step

-- PfaffianFn-level h_bridge closure (Case-B both components).
#print axioms singleExp_h_bridge_closure

-- The bridge theorem (was previously an axiom; now proven).
#print axioms eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast

-- Polynomial identity theorem (PIT).
#print axioms evalCoeffs_zero_iff_all_zero

-- Strict-degree derivative strict-decrease.
#print axioms polyTrueDegreeStrict_polyDerivativeCoeffs_lt

-- HasDerivAt correspondence for polyDerivativeCoeffs.
#print axioms polyDerivativeCoeffs_hasDerivAt

-- yCoeffsAt length equality (substantive new lemma).
#print axioms yCoeffsAt_length_eq

-- listAddN/Sub/Mul_getLast_eval — the three getLast distributivity lemmas.
#print axioms listAddN_getLast_eval
#print axioms listSubN_getLast_eval
#print axioms listMulN_getLast_eval

end PathC


/-! ## C-243 literal-bridge axioms (2026-06-18 audit)

Three new axioms in MachLib/Basic.lean immediately after
`realOfScientific_pos`. Surfaced by lean_proofs_v1 (monogate-research)
finding F12: 3 of 18 corpus theorems blocked at the gap between
Lean's `OfScientific`-elaborated decimal literals and the `oneR`-based
canonical-sum values. All three are consistent with the standard
`OfScientific` interpretation (m × 10^±e = numerical value); they
add no analytic content, only let canonical-form paths through proofs
of the form `(2.0 : Real) / 2.0 = 1`.

The axioms are minimal in surface — they only mention `oneR`-derived
naturals and the opaque `realOfScientific` carrier. No transcendentals,
no derivatives, no analysis. They appear in `#print axioms` closures
of any theorem that exercises a decimal literal in arithmetic
(downstream of the lean_proofs_v1.2 work, this applies to
cosh_at_zero, smoothstep_bounded, and any future theorem using
`(2.0 : Real)` or `(3.0 : Real)` in division or ordering).

The three new axiom names print cleanly via `#check` to confirm they
are reachable from MachLib's open namespace surface. -/

section C243LiteralBridge

open MachLib.Real

-- Confirm the three new C-243 axioms are accessible and have the
-- expected types. `#check` is sufficient — these have no constructive
-- content beyond what their statement says.
#check @realOfScientific_one_dot_zero
#check @realOfScientific_two_dot_zero
#check @realOfScientific_three_dot_zero

end C243LiteralBridge


/-! ## Verified-numerics pillar (2026-06-27 audit)

The bits→trajectory capstone, the cross-target equivalence layer, and the
consistency model. Expected footprint: the MachLib analytic/Real base above; the
bit-level (RTL) halves are pure Lean-core (`propext`/`Quot.sound` only); and
`intModel` must depend on NONE of MachLib's own axioms — it is the external
ℤ-model witnessing consistency, so anything `MachLib.Real.*` in its closure is a
finding (the `check_consistency_model.sh` gate enforces this). -/

section VerifiedNumerics

open MachLib.Real MachLib.Model

-- The end-to-end capstone: bit-level netlist → finite closed-loop trajectory bound.
#print axioms pid_trajectory_from_bits
-- Its bit-level halves — pure Lean-core (propext/Quot.sound only).
#print axioms MachLib.RTL.fxpid_correct
#print axioms MachLib.RTL.fxpid_trunc_lt_3ulp

-- Cross-target equivalence (e.g. Rust f64 vs WGSL f32 agree within their bounds).
#print axioms cross_target

-- Consistency: the external ℤ-model must use NO MachLib axiom.
#print axioms intModel
-- Faithfulness: enumerates exactly the flagship closure it captures.
#print axioms machlibWitness

end VerifiedNumerics
