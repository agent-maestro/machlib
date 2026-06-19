import MachLib.ChainExp2Instance
import MachLib.ChainExp2WFInstance
import MachLib.IterExpChain
import MachLib.InnerKhovanskiiExpListMeasured

/-!
# MachLib.ChainExp2ListMeasuredInstance — chain-2 instance via list-level descent

## Why this file exists

`InnerKhovanskiiExpListMeasured` (in
`InnerKhovanskiiExpListMeasured.lean`) is the framework that demands
list-level strict descent INSTEAD of per-element strict descent.
This file plugs chain-2 into that framework.

The chain-2 instance is parametric over:

1. `chain2Nat : MultiPoly 2 → Nat` — a Nat collapse of the lex-3
   chain-2 measure. The natural candidate is a polynomial encoding
   like `m.1 · B^2 + m.2.1 · B + m.2.2` for a base `B` large enough
   to ensure lex-3 strict descent lifts to Nat strict descent.

2. `length_one_bound` — same shape as the existing parametric chain-2
   instances.

3. `coeffStep_le_hyp` — per-element non-strict descent of the
   chain-2 step under the Nat collapse.

4. `list_scaledReduction_lt_hyp` — list-level strict descent of
   `scaledReductionAux` on chain-2 lists.

This file does NOT discharge these obligations — it provides the
parametric chain-2 plug-in. The discharge is the genuine
mathematical work split into a follow-up file.

## What ships clean here

`chain2_to_ListMeasured` — parametric chain-2 instance plugged into
the list-level Measured framework.

## Path forward (split into clean sub-obligations)

The chain-2 closure under this framework factorises into:

- **Obligation 1**: Choose a Nat collapse `chain2Nat` of the existing
  `chain2Measure : MultiPoly 2 → Nat × Nat × Nat` (defined in
  `ChainExp2WFInstance.lean`). Candidate:
  `chain2Nat g := (chain2Measure g).1 · B^2 + (chain2Measure g).2.1 · B + (chain2Measure g).2.2`
  where `B` exceeds the max possible value of components 2 and 3
  under chain-2 chainTotalDeriv. For polynomial inputs of bounded
  degree, `B` is structurally bounded.

- **Obligation 2**: Prove `coeffStep_le_hyp`. For any `k : Real` and
  `g : MultiPoly 2`, the chain-2 step
  `chainTotalDeriv g + k·y_0·g` has `chain2Nat` ≤ `chain2Nat g`. The
  obstruction at chain-2 (`+1` raise on `degreeY 0`) shows up here
  as a `+B²` raise on `chain2Nat`. Need `B²` to be absorbed by the
  drop in components 2 and 3 from cancellation.

  **Hard but tractable.** The cancellation algebra is known
  (analogous to SingleExp's). The structural bound on B comes from
  the chain-2 chain rule's `y_0 · ∂g/∂y_0 + y_0·y_1 · ∂g/∂y_1` term
  bounded by `degreeY 0 g + degreeY 1 g`.

- **Obligation 3**: Prove `list_scaledReduction_lt_hyp`. This is
  where the genuinely new mathematical content is. Per the
  `InnerKhovanskiiExpListMeasured.lean` docstring:

  > For `length ≥ 2`, the ONE coefficient (y_1-leading) whose
  > chain-2 measure rises by +B² is dominated by the OTHER (length-1)
  > coefficients whose measures drop by the SingleExp-style
  > cancellation.

  **The list-level math** — and the place where chain-2 closure
  finally happens.

  Estimate: ~200-300 lines for Obligations 2 + 3 combined, plus
  whatever structural lemmas on chain-2 chainTotalDeriv haven't been
  shipped yet.

## Status

This file ships the parametric chain-2 instance. The obligations
are next-session work but the FRAMEWORK plug-in is now in place.
Zero new axioms. Zero `sorry`.
-/

namespace MachLib
namespace ChainExp2ListMeasuredInstanceMod

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.InnerKhovanskiiExpMod
open MachLib.InnerKhovanskiiExpListMeasuredMod
open MachLib.ChainExp2InstanceMod

/-! ## Chain-2 instance using the list-level Measured framework -/

/-- Chain-2 plug-in to `InnerKhovanskiiExpListMeasured`. Parametric
over the Nat measure `chain2Nat` and the descent proofs. Once a
follow-up file discharges these obligations, this becomes a concrete
chain-2 closure via list-level descent. -/
noncomputable def chain2_to_ListMeasured
    (chain2Nat : chainExp2_innerKhovanskii_full.T → Nat)
    (length_one_bound :
      ∀ g : chainExp2_innerKhovanskii_full.T, ∀ a b : Real, a < b →
      (∃ x : Real,
        chainExp2_innerKhovanskii_full.eval g x ≠ 0) →
      ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        chainExp2_innerKhovanskii_full.eval g z = 0) →
      zeros.length ≤ chain2Nat g)
    (coeffStep_le_hyp :
      ∀ k : Real, ∀ g : chainExp2_innerKhovanskii_full.T,
        chain2Nat
          (chainExp2_innerKhovanskii_full.add
            (chainExp2_innerKhovanskii_full.derivative g)
            (chainExp2_innerKhovanskii_full.scalarMul k g)) ≤ chain2Nat g)
    (list_scaledReduction_lt_hyp :
      ∀ (coeffs : List chainExp2_innerKhovanskii_full.T) (offset : Nat)
        (hne : coeffs ≠ []),
        chain2Nat (coeffs.getLast hne) > 0 →
        (InnerKhovanskiiExp.scaledReductionAux chainExp2_innerKhovanskii_full
            (natCast (offset + coeffs.length - 1)) coeffs offset).foldr
          (fun (t : chainExp2_innerKhovanskii_full.T) acc => chain2Nat t + acc) 0
        < coeffs.foldr
          (fun (t : chainExp2_innerKhovanskii_full.T) acc => chain2Nat t + acc) 0) :
    InnerKhovanskiiExpListMeasured where
  toInnerKhovanskiiExp := chainExp2_innerKhovanskii_full
  measure := chain2Nat
  length_one_bound := length_one_bound
  coeffStep_le := coeffStep_le_hyp
  list_scaledReduction_lt := list_scaledReduction_lt_hyp

/-! ## The complete chain-2 framework redesign — summary

After this session, the chain-2 closure has THREE clean parametric
plug-ins:

1. `chain2_to_WFR` (in `ChainExp2WFInstance.lean`) — unconditional
   WFR framework. STRUCTURALLY UNSATISFIABLE per the muse analysis;
   shipped only for documentation.

2. `chain2_to_WFRPrecond` (in `ChainExp2WFRPrecondInstance.lean`) —
   precondition-aware WFR framework. Necessary but not sufficient
   per the structural obstruction.

3. `chain2_to_ListMeasured` (this file) — list-level descent
   framework. The MOST PROMISING path because the natural chain-2
   structural argument (chain-rule cancellation on non-leading
   coefficients dominates the +1 raise on the leading coefficient)
   operates at the list level.

All three are PARAMETRIC over the chain-2 closure proofs that
remain genuine mathematical work. The choice of framework determines
the SHAPE of the closure proof; the difficulty of the underlying
math doesn't change.

For next-session work, the recommended path is option 3 (list-level)
because:
- The chain-2 algebra naturally has a list-level character
  (scaledReductionAux ties all coefficients' scalars together)
- The cancellation argument is structurally analogous to SingleExp
  (existing infrastructure carries over)
- The net-descent counting argument is elementary Nat arithmetic
  once the cancellation is established

Estimate for option 3 closure: ~200-300 lines beyond what's already
shipped, splitting roughly: ~50 lines for the `chain2Nat` definition
and structural properties, ~150 lines for `coeffStep_le_hyp` (the
cancellation algebra), ~50 lines for `list_scaledReduction_lt_hyp`
(the net-descent counting).
-/

end ChainExp2ListMeasuredInstanceMod
end MachLib
