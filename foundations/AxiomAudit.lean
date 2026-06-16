import MachLib.SingleExpKhovanskii
import MachLib.KhovanskiiReduction
import MachLib.MultiPolyToPoly
import MachLib.PfaffianFnBound

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
