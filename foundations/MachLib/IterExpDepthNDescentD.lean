import MachLib.IterExpDepthNDescent
import MachLib.IterExpDepthNCanonBridge

/-!
# Phase C, brick 3b (step 2b) — the eval-invariant descent `D(k)` given the inner descent (∀N)

The eval-invariant measure `chainNMeasureEI (M+1)` descends under the depth-`(M+3)` graded reduce, via the
**phantom / non-phantom split** (the ∀N analog of `chain2MeasureCanonEvalInv_descends`):

* if the reduce result's top `y`-coefficient is **non-phantom**, both the reduce result and `p` have their
  eval-invariant measure equal to the *syntactic* one (Phase C brick 2), so the descent is exactly the
  syntactic descent `S(k)` (`chainNReduce_syntactic_descent`) — fed the inner descent `hInner`;
* if it is **phantom**, the canonical top-degree `cdegYAt` of the reduce strictly drops below `degreeY_top p`
  (`cdegYAt_lt_degreeYAt_of_top`, since the reduce preserves the syntactic top degree), giving a
  first-component descent outright.

`hInner` is `D(M)` applied to the inner polynomial `dropLastY (leadingCoeffY_top p)`; the S(k)/D(k) induction
supplies it. This isolates the D-step from that hypothesis-threading. The literal top index is confined to two
`subst`-based wrappers; the main proof runs at the abstract index. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpDepthNReduce

/-- `chainNMeasureEI (M+1)` in its definitional pair form, at the abstract top index. -/
private theorem chainNMeasureEI_def_at (M : Nat) (i : Fin (M + 3)) (hi : i.val = M + 2)
    (q : MultiPoly (M + 3)) :
    chainNMeasureEI (M + 1) q
      = (cdegYAt i q, chainNMeasureEI M (MultiPoly.dropLastY (canonLcYAt i q))) := by
  have hi' : i = (⟨M + 2, by omega⟩ : Fin (M + 3)) := Fin.ext hi
  rw [hi']
  simp only [chainNMeasureEI]

/-- `chainNMeasureEI (M+1)` in its syntactic pair form on the non-phantom branch, at the abstract top index
(brick 2 lifted off the literal index). -/
private theorem chainNMeasureEI_syn_at (M : Nat) (i : Fin (M + 3)) (hi : i.val = M + 2)
    (q : MultiPoly (M + 3)) (hq : canonZeroB (ytopAt i q) = false) :
    chainNMeasureEI (M + 1) q
      = (MultiPoly.degreeY i q, chainNMeasureEI M (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i q))) := by
  have hi' : i = (⟨M + 2, by omega⟩ : Fin (M + 3)) := Fin.ext hi
  rw [hi'] at hq ⊢
  exact chainNMeasureEI_eq_syntactic_of_nonphantom M q hq

/-- **The eval-invariant descent `D(k)`, given the inner descent.** For the depth-`(M+3)` graded reduce, with
`p` non-phantom and positive top degree, `chainNMeasureEI (M+1)` strictly drops — provided the inner descent
`hInner` (= `D(M)` on `dropLastY (leadingCoeffY_top p)`) holds. -/
theorem chainNReduce_evalinv_descent (M : Nat) (i : Fin (M + 3)) (hi : i.val = M + 2)
    (m_rest p : MultiPoly (M + 3)) (hmr : MultiPoly.degreeY i m_rest = 0)
    (hnp_p : canonZeroB (ytopAt i p) = false)
    (hpos_p : 0 < MultiPoly.degreeY i p)
    (hInner : nestedOrder (M + 2)
      (chainNMeasureEI M (chainNReduce M (MultiPoly.dropLastY m_rest)
        (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p))))
      (chainNMeasureEI M (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p)))) :
    nestedOrder (M + 3)
      (chainNMeasureEI (M + 1) (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p))
      (chainNMeasureEI (M + 1) p) := by
  have hm_top : MultiPoly.degreeY i (MultiPoly.add (gradedTop (M + 1) i p) m_rest) = 0 := by
    show Nat.max (MultiPoly.degreeY i (gradedTop (M + 1) i p)) (MultiPoly.degreeY i m_rest) = 0
    rw [gradedTop_degreeYtop_zero (M + 1) i hi p, hmr]; decide
  rw [chainNMeasureEI_syn_at M i hi p hnp_p]
  by_cases hR_np : canonZeroB (ytopAt i
      (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p)) = false
  · rw [chainNMeasureEI_syn_at M i hi
        (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p) hR_np]
    exact chainNReduce_syntactic_descent M i hi m_rest p hmr hInner
  · have hR_ph : canonZeroB (ytopAt i
        (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p)) = true := by
      cases hb : canonZeroB (ytopAt i
          (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p))
      · exact absurd hb hR_np
      · rfl
    have hRdeg : MultiPoly.degreeY i
          (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p)
        = MultiPoly.degreeY i p :=
      chainNReduce_fst_preserved (M + 1) i hi (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p hm_top
    rw [chainNMeasureEI_def_at M i hi
        (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p)]
    apply nestedOrder_of_fst
    show cdegYAt i (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p)
      < MultiPoly.degreeY i p
    have hlt := cdegYAt_lt_degreeYAt_of_top i
      (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p) hR_ph
      (by rw [hRdeg]; exact hpos_p)
    rw [hRdeg] at hlt; exact hlt

end MachLib.IterExpDepthN
