import MachLib.IterExpDepthNDescent
import MachLib.IterExpDepthNInnerTrim
import MachLib.IterExpDepthNTrimArm

/-!
# Phase D (D3 step ii) — the ∀N capstone: `M5`, the top-level reduce descent, and the four order5 arms

The augmented well-founded measure `M5` and the three `chainNOrder5`-descents the final WF assembly
dispatches to. The ∀N analogs of `IterExpDepth3Capstone`'s `chain3Measure5` / `chain3Reduce_nestedLT`
family:

* `chainNReduce_orderCanon` — the **top-level reduce descent**. The correct graded reduce
  `chainNReduce (M+1) (fullMult (M+1) p) p` strictly lowers `chainNMeasureCanon` — first component
  `degreeY_top` ties (`chainNReduce_fst_preserved`), inner rides Phase C's `chainNReduce_descends` through
  the `chainNReduce_syntactic_descent` transport. Needs only that the inner `q := dropLastY(lcY_top p)` is
  `Reducing M`.
* `chainNMeasure5` / `chainNOrder5` / `chainNOrder5_wf` — the canonical measure augmented with the
  syntactic `degreeY_{top-1}` of `lcY_top p` as an innermost tiebreaker, well-founded via `lexProd`.
* `chainNReduce_order5` / `chainN_degreeYtop_trim_order5` — the reduce and degree-trim descents lift to
  `M5` for free (they drop the FIRST component, `lexProd_of_fst`).
* `innerTrimN_order5` — the inner-trim descent: the first component `chainNMeasureCanon` TIES (top degree
  exactly, inner eval-invariant measure because `lcY_top(innerTrimN p)` eval-equals `lcY_top p`), and the
  second component (`degreeY_{top-1}`) DROPS (`degreeY_dropLeadingYAt_lt`), via `lexProd_of_snd`.

No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.IterExpDepthNReduce
open MachLib.ChainExp2Trim
open MachLib.IterExpDepth3CdegY1

/-- **The top-level reduce descent.** For a `p` whose inner `q := dropLastY(lcY_top p)` is `Reducing M`,
the correct graded reduce strictly lowers `chainNMeasureCanon`. Assembled from the syntactic-descent
transport (`chainNReduce_syntactic_descent`, which ties the top degree and reduces the descent to the
inner one) fed by Phase C's `chainNReduce_descends` (the eval-invariant inner measure descends). ∀N analog
of `chain3Reduce_nestedLT`. -/
theorem chainNReduce_orderCanon (M : Nat) (p : MultiPoly (M + 3))
    (hred : Reducing M (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) :
    chainNOrderCanon M (chainNReduce (M + 1) (fullMult (M + 1) p) p) p := by
  have key := chainNReduce_syntactic_descent M (⟨M + 2, by omega⟩ : Fin (M + 3)) rfl
    (liftLastY (fullMult M (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)))) p
    (degreeY_top_liftLastY _)
    (by rw [dropLastY_liftLastY]
        exact chainNReduce_descends M
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)) hred)
  show nestedOrder (M + 3)
      (chainNMeasureCanon M (chainNReduce (M + 1) (fullMult (M + 1) p) p))
      (chainNMeasureCanon M p)
  simp only [chainNMeasureCanon, fullMult]
  exact key

/-! ### The augmented measure `M5` -/

/-- The augmented depth-`(M+3)` measure: the canonical measure with the syntactic `degreeY_{top-1}` of
`lcY_top p` as an innermost tiebreaker. -/
noncomputable def chainNMeasure5 (M : Nat) (p : MultiPoly (M + 3)) : NestedNat (M + 3) × Nat :=
  (chainNMeasureCanon M p,
   MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 3))
     (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))

/-- The augmented order — `chainNOrderCanon` with the `degreeY_{top-1}` tiebreaker. -/
def chainNOrder5 (M : Nat) : MultiPoly (M + 3) → MultiPoly (M + 3) → Prop :=
  InvImage (LexProd.lexProd (nestedOrder (M + 3)) (· < ·)) (chainNMeasure5 M)

/-- **Well-founded** — `lexProd` of the (well-founded) backbone order with `Nat`'s `<`. -/
theorem chainNOrder5_wf (M : Nat) : WellFounded (chainNOrder5 M) :=
  InvImage.wf (chainNMeasure5 M) (LexProd.lexProd_wf (nestedOrder_wf (M + 3)) Nat.lt_wfRel.wf)

/-- The reduce descent lifts to `M5` for free — it drops the first (`chainNMeasureCanon`) component. -/
theorem chainNReduce_order5 (M : Nat) (p : MultiPoly (M + 3))
    (hred : Reducing M (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) :
    chainNOrder5 M (chainNReduce (M + 1) (fullMult (M + 1) p) p) p :=
  lexProd_of_fst (chainNReduce_orderCanon M p hred)

/-- The `degreeY_top`-trim descent lifts to `M5` for free — it also drops the first component. -/
theorem chainN_degreeYtop_trim_order5 (M : Nat) (p : MultiPoly (M + 3))
    (hd : 0 < MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) p) :
    chainNOrder5 M (dropLeadingYAt (⟨M + 2, by omega⟩ : Fin (M + 3)) p) p :=
  lexProd_of_fst (chainN_degreeYtop_trim_order M p hd)

set_option maxHeartbeats 1600000 in
/-- **The inner-trim M5-descent** — the last shrinking move. For `p` with `degreeY_top p > 0`, positive
`degreeY_{top-1} (lcY_top p)` (`hd1pos`), and a phantom leading `y_{top-1}`-term of `lcY_top p`
(`h_phantom`), `innerTrimN M p` strictly lowers `M5`. The FIRST component `chainNMeasureCanon` TIES —
`degreeY_top` exactly (`degreeYtop_innerTrimN_eq`) and the inner eval-invariant measure because
`lcY_top(innerTrimN p)` is eval-equal to `lcY_top p` (the dropped `y_{top-1}`-term vanishes) — and the
SECOND component (`degreeY_{top-1}`) DROPS (`degreeY_dropLeadingYAt_lt`). Via `lexProd_of_snd`. ∀N analog
of `innerTrim3_order5`. -/
theorem innerTrimN_order5 (M : Nat) (p : MultiPoly (M + 3))
    (hd2pos : 0 < MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)
    (hd1pos : 0 < MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 3))
      (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))
    (h_phantom : ∀ (x : Real) (env : Fin (M + 3) → Real),
      MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨M + 1, by omega⟩ : Fin (M + 3))
        (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)).getLast
        (MultiPoly.yCoeffsAt_nonempty (⟨M + 1, by omega⟩ : Fin (M + 3))
          (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) x env = 0) :
    chainNOrder5 M (innerTrimN M p) p := by
  apply LexProd.lexProd_of_snd
  · -- FIRST component TIES: chainNMeasureCanon (innerTrimN p) = chainNMeasureCanon p
    show chainNMeasureCanon M (innerTrimN M p) = chainNMeasureCanon M p
    have hlceval : ∀ (x : Real) (env : Fin (M + 3) → Real),
        MultiPoly.eval (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) (innerTrimN M p)) x env
          = MultiPoly.eval (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p) x env := by
      intro x env
      rw [leadingCoeffYtop_innerTrimN_eval M p hd2pos x env,
          eval_dropLeadingYAt_of_last_canonically_zero (⟨M + 1, by omega⟩ : Fin (M + 3))
            (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)
            (MultiPoly.yCoeffsAt_nonempty (⟨M + 1, by omega⟩ : Fin (M + 3))
              (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))
            h_phantom x env]
    have hinner : chainNMeasureEI M (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) (innerTrimN M p)))
        = chainNMeasureEI M (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)) :=
      chainNMeasureEI_eq_of_eval_eq M _ _
        (dropLastY_eval_eq_of_topfree _ _
          (MultiPoly.degreeY_leadingCoeffY _ _) (MultiPoly.degreeY_leadingCoeffY _ _) hlceval)
    show (MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) (innerTrimN M p),
          chainNMeasureEI M (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) (innerTrimN M p))))
        = (MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) p,
           chainNMeasureEI M (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)))
    rw [degreeYtop_innerTrimN_eq M p, hinner]
  · -- SECOND component DROPS: degreeY_{top-1} (lcY_top (innerTrimN p)) < degreeY_{top-1} (lcY_top p)
    show MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 3))
          (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) (innerTrimN M p))
        < MultiPoly.degreeY (⟨M + 1, by omega⟩ : Fin (M + 3))
          (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)
    rw [leadingCoeffYtop_innerTrimN_degreeYprev M p hd2pos]
    exact degreeY_dropLeadingYAt_lt (⟨M + 1, by omega⟩ : Fin (M + 3))
      (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p) hd1pos

end MachLib.IterExpDepthN
