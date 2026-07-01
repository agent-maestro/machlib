import MachLib.ChainExp2SingleExpDescent
import MachLib.ChainExp2Descent

/-!
# Assembling `hsnd` — the canonical inner descent for the correct reduce (htop case)

This wires the single-exp canonical descent (`singleExpMeasureCanon_seReduce_lt`) into
`chain2Reduce_nestedLT_canon_of_snd`, closing the full `nestedLT` descent of the correct reduce
`chain2Reduce` against the canonical measure — **for the case where `lcY₁ p`'s top `y₀`-coefficient is
not canonically zero** (`htop`).

The clean part: choosing the reduce scalar `c = degreeY₀(lcY₁ p)` makes
`lcY₁(chain2Reduce c p)` eval-equal to `seReduce(lcY₁ p)` — the SAME single-exp reduce, on the SAME
`q = lcY₁ p` (no trimmed representative). So `chain2Reduce_lcY1_eval` (the cancellation) plus
eval-invariance of `singleExpMeasureCanon` reduce `hsnd` to the descent theorem directly. No
`chainTotalDeriv` eval-congruence is needed here; that is only required for the phantom-top case
(`degreeY₀(lcY₁ p) > cdegY0(lcY₁ p)`), handled separately.

Path B: ChainExp2SDR + single-exp framework untouched.
-/

namespace MachLib.ChainExp2ReduceDescent

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2Reducer
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2CdegInv
open MachLib.ChainExp2Descent
open MachLib.ChainExp2SingleExpDescent

/-- **The canonical `nestedLT` descent of the correct reduce, htop case.** For `p` whose `y₁`-leading
coefficient has a non-canonically-zero top `y₀`-coefficient, `chain2Reduce (degreeY₀(lcY₁ p)) p`
strictly descends the canonical chain-2 measure. Assembled from `chain2Reduce_nestedLT_canon_of_snd`
(structural reduction to the inner second component) + `chain2Reduce_lcY1_eval` (the cancellation
`lcY₁(reduce) ≡ seReduce(lcY₁ p)`) + eval-invariance + `singleExpMeasureCanon_seReduce_lt` (the
descent). -/
theorem chain2Reduce_nestedLT_canon_htop (p : MultiPoly 2)
    (htop : coeffCanonZeroB (y0top (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)) = false) :
    nestedLT
      (chain2MeasureCanon (chain2Reduce
        (MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))) p))
      (chain2MeasureCanon p) := by
  apply chain2Reduce_nestedLT_canon_of_snd
  -- goal: lexProd (<)(<) (chain2MeasureCanon (chain2Reduce c p)).2 (chain2MeasureCanon p).2
  show LexProd.lexProd (· < · : Nat → Nat → Prop) (· < ·)
        (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (chain2Reduce (MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2)
            (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))) p)))
        (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))
  have hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
               (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) = 0 :=
    MultiPoly.degreeY_leadingCoeffY (⟨1, by omega⟩ : Fin 2) p
  -- lcY₁(chain2Reduce c p) is eval-equal to seReduce(lcY₁ p) (same q, same c).
  have heq : singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
        (chain2Reduce (MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))) p))
      = singleExpMeasureCanon (seReduce (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)) := by
    apply singleExpMeasureCanon_eq_of_eval_eq
    intro x env
    rw [chain2Reduce_lcY1_eval]
    show MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
            (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)) x env
          - MachLib.Real.natCast (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2)
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))
            * MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) x env
        = MultiPoly.eval (seReduce (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)) x env
    unfold seReduce
    rw [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_const]
  rw [heq]
  exact singleExpMeasureCanon_seReduce_lt
    (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) hy1 htop

end MachLib.ChainExp2ReduceDescent
