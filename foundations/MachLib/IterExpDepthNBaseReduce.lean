import MachLib.IterExpDepthNGraded
import MachLib.IterExpDepthNMeasureEI
import MachLib.ChainExp2Reducer

/-!
# Base reconciliation — the ∀N reduce at depth 2 IS the concrete `chain2Reduce` (∀N base)

The `D(k)`-by-induction bottoms out at `k = 0` (depth 2), where the existing deep result
`chain2MeasureCanonEvalInv_descends` speaks of `chain2Reduce`. This brick shows the ∀N reduce
specialises to it: the depth-2 graded multiplier `gradedTop 0 ⟨1⟩ p + const c` is exactly
`chain2Reduce`'s multiplier `(degreeY₁ p)·y₀ + c`, because `Ffac 0 = prodVarYUpTo 0 = y₀`.

`chainNReduce_zero_eq_chain2Reduce` — `chainNReduce 0 (gradedTop 0 ⟨1⟩ p + const c) p = chain2Reduce c p`.
With `chainNMeasureEI 0 = chain2MeasureCanonEvalInv` (definitional), this transfers the depth-2 descent to
the base of the ∀N induction. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.IterExpTopIdentity
open MachLib.IterExpDepthNReduce
open MachLib.ChainExp2Reducer
open MachLib.ChainExp2CanonMeasure
open MachLib.IterExpDepth3CdegY1

/-- The depth-2 case of the ∀N reduce is exactly the concrete `chain2Reduce`. -/
theorem chainNReduce_zero_eq_chain2Reduce (c : Real) (p : MultiPoly 2) :
    chainNReduce 0 (MultiPoly.add (gradedTop 0 (⟨1, by omega⟩ : Fin 2) p) (MultiPoly.const c)) p
      = chain2Reduce c p := by
  rfl

/-- **The base `D(0)`.** For a depth-2 reducing `p`, the ∀N reduce (with the depth-2 graded multiplier)
strictly lowers `chainNMeasureEI 0`. This IS the deep `chain2MeasureCanonEvalInv_descends`, transported
through `chainNReduce 0 = chain2Reduce` and `chainNMeasureEI 0 = chain2MeasureCanonEvalInv`. -/
theorem chainNReduce_evalinv_descent_base (p : MultiPoly 2)
    (hq_np : coeffCanonZeroB1 (y1top p) = false)
    (hpos : 0 < MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
    (hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)).2 ≠ 0) :
    nestedOrder 2
      (chainNMeasureEI 0 (chainNReduce 0 (MultiPoly.add (gradedTop 0 (⟨1, by omega⟩ : Fin 2) p)
        (MultiPoly.const (MachLib.Real.natCast
          (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))))) p))
      (chainNMeasureEI 0 p) := by
  rw [chainNReduce_zero_eq_chain2Reduce]
  show nestedLT (chain2MeasureCanonEvalInv (chain2Reduce (MachLib.Real.natCast
        (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))) p))
      (chain2MeasureCanonEvalInv p)
  exact chain2MeasureCanonEvalInv_descends p hq_np hpos hnz

end MachLib.IterExpDepthN
