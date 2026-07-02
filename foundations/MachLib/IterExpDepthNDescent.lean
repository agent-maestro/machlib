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

/-- **The syntactic descent `S(k)`, given the inner descent.** For the depth-`(M+3)` graded reduce, the
*syntactic* measure `(degreeY_top, chainNMeasureEI M (dropLastY (leadingCoeffY_top ·)))` strictly drops —
provided the inner descent `hInner` holds (the depth-`(M+2)` reduce lowers `chainNMeasureEI M` of
`dropLastY (leadingCoeffY_top p)`; that is exactly `D(M)` applied to the inner polynomial). The top degree
is *preserved* by the reduce (`chainNReduce_fst_preserved`), so the descent rides entirely on the inner
component, which drops via the transport `chainNMeasureEI_reduce_inner_eq` + `hInner`. This isolates the
S-step of the S(k)/D(k) induction from the reducing-hypothesis threading (which supplies `hInner`). -/
theorem chainNReduce_syntactic_descent (M : Nat) (i : Fin (M + 3)) (hi : i.val = M + 2)
    (m_rest p : MultiPoly (M + 3)) (hmr : MultiPoly.degreeY i m_rest = 0)
    (hInner : nestedOrder (M + 2)
      (chainNMeasureEI M (chainNReduce M (MultiPoly.dropLastY m_rest)
        (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p))))
      (chainNMeasureEI M (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p)))) :
    nestedOrder (M + 3)
      (MultiPoly.degreeY i (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p),
       chainNMeasureEI M (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i
         (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p))))
      (MultiPoly.degreeY i p,
       chainNMeasureEI M (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p))) := by
  have hm_top : MultiPoly.degreeY i (MultiPoly.add (gradedTop (M + 1) i p) m_rest) = 0 := by
    show Nat.max (MultiPoly.degreeY i (gradedTop (M + 1) i p)) (MultiPoly.degreeY i m_rest) = 0
    rw [gradedTop_degreeYtop_zero (M + 1) i hi p, hmr]; decide
  refine nestedOrder_of_snd ?_ ?_
  · show MultiPoly.degreeY i (chainNReduce (M + 1)
          (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p) = MultiPoly.degreeY i p
    exact chainNReduce_fst_preserved (M + 1) i hi
      (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p hm_top
  · show nestedOrder (M + 2)
        (chainNMeasureEI M (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i
          (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p))))
        (chainNMeasureEI M (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p)))
    rw [chainNMeasureEI_reduce_inner_eq M i hi m_rest p hmr]
    exact hInner

end MachLib.IterExpDepthN
