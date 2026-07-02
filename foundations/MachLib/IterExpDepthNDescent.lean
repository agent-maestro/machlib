import MachLib.IterExpDepthNRecursionFull
import MachLib.IterExpDepthNMeasureSyn

/-!
# Phase C, brick 3b (step 1) — the inner-descent transport (∀N)

The syntactic descent `S(k)`'s inner component must show that the eval-invariant measure of the reduce's
dropped top coefficient equals that of a **lower** reduce — so the inductive hypothesis `D(k−1)` can then
lower it. This file supplies exactly that transport, combining the full-env recursion brick (3a) with the
measure's eval-invariance (Phase B):

`chainNMeasureEI_reduce_inner_eq` — `chainNMeasureEI M (dropLastY (lcY_top (reduce_{M+3} p)))
= chainNMeasureEI M (reduce_{M+2} (dropLastY (lcY_top p)))`.

With this, `S(k)`'s inner descent is just `rw [this]; exact D(k−1)`. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpDepthNReduce

/-- **The inner-descent transport.** The eval-invariant measure of the depth-`(M+3)` graded reduce's
dropped top coefficient equals the measure of the depth-`(M+2)` reduce of `dropLastY (lcY_top p)` (with
multiplier `dropLastY m_rest`). Immediate from the full-env recursion brick + `chainNMeasureEI`'s
eval-invariance. -/
theorem chainNMeasureEI_reduce_inner_eq (M : Nat) (i : Fin (M + 3)) (hi : i.val = M + 2)
    (m_rest p : MultiPoly (M + 3)) (hmr : MultiPoly.degreeY i m_rest = 0) :
    chainNMeasureEI M (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i
        (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p)))
    = chainNMeasureEI M (chainNReduce M (MultiPoly.dropLastY m_rest)
        (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p))) := by
  apply chainNMeasureEI_eq_of_eval_eq M
  intro x env
  exact chainNReduce_dropLastY_recursion_full M i hi m_rest p hmr x env

end MachLib.IterExpDepthN
