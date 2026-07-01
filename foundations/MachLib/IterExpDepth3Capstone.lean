import MachLib.IterExpDepth3MeasureDescent
import MachLib.IterExpDepth3CdegY1
import MachLib.IterExpDepth3Vehicle
import MachLib.IterExpDepth3CapstonePrep
import MachLib.IterExpDepth3InnerTrim
import MachLib.ChainExp2NoZeros

/-!
# Depth-3 capstone (part 1) — the canonical measure, its well-foundedness, and the reduce descent

`chain3MeasureCanon p = (degreeY₂ p, chain2MeasureCanonEvalInv (dropLastY (lcY₂ p)))` — the depth-3
analog of the depth-2 canonical measure, with the *eval-invariant* depth-2 measure on the dropped
leading coefficient as the inner component. This file:

* defines the measure + order + well-foundedness (via the `LexProd` keystone `natQuadLex_wf`);
* proves the **reduce descent** `chain3Reduce_nestedLT`: the correct depth-3 reduce strictly lowers the
  measure — the payoff of the entire arc. First component `degreeY₂` ties (`chain3Reduce_fst_preserved`);
  the inner descends because the dropped leading coefficient of the reduce is (full-env) eval-equal to a
  depth-2 reduce (`chain3Reduce_dropLastY_lcY2_eval_eq_full`), the measure is eval-invariant
  (`chain2MeasureCanonEvalInv_eq_of_eval_eq`), and that depth-2 reduce descends
  (`chain2MeasureCanonEvalInv_descends`).

Path B; no `sorry`.
-/

namespace MachLib.IterExpDepth3Capstone

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpDepth3Descent
open MachLib.IterExpDepth3MeasureDescent
open MachLib.IterExpDepth3CdegY1
open MachLib.IterExpDepth3Vehicle
open MachLib.IterExpDepth3Bridge
open MachLib.ChainExp2Reducer
open MachLib.ChainExp2Bound
open MachLib.ChainExp2NoZeros
open MachLib.ChainExp2CanonMeasure
open MachLib.IterExpDepth3CapstonePrep
open MachLib.IterExpDepth3InnerTrim

/-- The canonical depth-3 measure: `(degreeY₂ p, eval-invariant depth-2 measure of `dropLastY (lcY₂ p))`. -/
noncomputable def chain3MeasureCanon (p : MultiPoly 3) : Nat × (Nat × (Nat × Nat)) :=
  (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p,
   chain2MeasureCanonEvalInv (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)))

/-- The canonical depth-3 order: 4-deep `Nat`-lex pulled back along the measure. -/
def chain3OrderCanon : MultiPoly 3 → MultiPoly 3 → Prop :=
  InvImage (LexProd.lexProd (· < ·) nestedLT) chain3MeasureCanon

/-- **Well-founded** — directly from the `LexProd` keystone `natQuadLex_wf` via `InvImage`. -/
theorem chain3OrderCanon_wf : WellFounded chain3OrderCanon :=
  InvImage.wf chain3MeasureCanon LexProd.natQuadLex_wf

/-- **The depth-3 reduce descent** — the payoff. For a genuinely-reducing `p` (the inner `dropLastY(lcY₂ p)`
non-phantom, positive `y₁`-degree, inner reducible), the correct reduce (with the matching graded
multiplier constant) strictly lowers `chain3MeasureCanon`. -/
theorem chain3Reduce_nestedLT (p : MultiPoly 3)
    (hq_np : coeffCanonZeroB1 (y1top (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))) = false)
    (hpos : 0 < MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)))
    (hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
      (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)))).2 ≠ 0) :
    chain3OrderCanon (chain3Reduce (MachLib.Real.natCast (cdegY0
      (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))))) p) p := by
  apply LexProd.lexProd_of_snd
  · exact chain3Reduce_fst_preserved _ p
  · show nestedLT
        (chain2MeasureCanonEvalInv (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3)
          (chain3Reduce (MachLib.Real.natCast (cdegY0
            (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY
              (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))))) p))))
        (chain2MeasureCanonEvalInv (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)))
    rw [chain2MeasureCanonEvalInv_eq_of_eval_eq _ _
          (fun x e => chain3Reduce_dropLastY_lcY2_eval_eq_full _ p x e)]
    exact chain2MeasureCanonEvalInv_descends _ hq_np hpos hnz

/-- **The depth-3 reduce descent needing ONLY `hnz`** — gaps A + B consolidated. With the inner descent
strengthened to require only `hnz` (non-phantom is free, `degreeY₁ q = 0` handled), the depth-3 reduce
strictly lowers `chain3MeasureCanon` for any `p` whose inner `q := dropLastY(lcY₂ p)` has a non-canon-zero
leading `y₁`-coefficient. This is the form the final WF assembly dispatches to in the reduce case. -/
theorem chain3Reduce_nestedLT_hnz (p : MultiPoly 3)
    (hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
      (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)))).2 ≠ 0) :
    chain3OrderCanon (chain3Reduce (MachLib.Real.natCast (cdegY0
      (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))))) p) p := by
  apply LexProd.lexProd_of_snd
  · exact chain3Reduce_fst_preserved _ p
  · show nestedLT
        (chain2MeasureCanonEvalInv (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3)
          (chain3Reduce (MachLib.Real.natCast (cdegY0
            (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY
              (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))))) p))))
        (chain2MeasureCanonEvalInv (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)))
    rw [chain2MeasureCanonEvalInv_eq_of_eval_eq _ _
          (fun x e => chain3Reduce_dropLastY_lcY2_eval_eq_full _ p x e)]
    exact chain2MeasureCanonEvalInv_descends_hnz _ hnz

/-- **The base bridge.** When `p` is `y₂`-free (`degreeY₂ p = 0`), `chain3Fn p` agrees on the nose with
`chain2Fn (dropLastY p)` at every point (both evaluate the same polynomial data against the same first
two chain values — `dropLastY_eval_IterExp3`), so the *unconditional depth-2 Khovanskii bound* transfers
verbatim. This is the recursion's floor: `degreeY₂ = 0` drops the depth-3 problem to the fully-solved
depth-2 one. -/
theorem chain3Fn_bound_of_degreeY2_zero (p : MultiPoly 3)
    (hd : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p = 0) (a b : Real) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧ (chain3Fn p).eval z ≠ 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain3Fn p).eval z = 0) → zeros.length ≤ N := by
  have heval : ∀ z, (chain3Fn p).eval z = (chain2Fn (MultiPoly.dropLastY p)).eval z := by
    intro z
    show MultiPoly.eval p z ((IterExpChain 3).chainValues z)
       = MultiPoly.eval (MultiPoly.dropLastY p) z ((IterExpChain 2).chainValues z)
    exact dropLastY_eval_IterExp3 p hd z
  obtain ⟨z, hza, hzb, hzne⟩ := hne
  obtain ⟨N, hN⟩ := chain2_khovanskii_bound_unconditional (MultiPoly.dropLastY p) a b hab
    ⟨z, hza, hzb, by rw [← heval]; exact hzne⟩
  refine ⟨N, fun zeros hnd hz => hN zeros hnd (fun z' hz'mem => ?_)⟩
  obtain ⟨ha, hb', hzero⟩ := hz z' hz'mem
  exact ⟨ha, hb', by rw [← heval]; exact hzero⟩

/-- **The degreeY₂-trim, eval-equality.** When the leading `y₂`-coefficient of `p` vanishes on every
environment (a *phantom* `y₂`-top, exactly the depth-3 analog of the depth-2 phantom-`y₁` trim),
`chain3Fn p` agrees on the nose with `chain3Fn (dropLeadingYAt ⟨2⟩ p)` at every point — dropping an
identically-zero leading term changes nothing. Reuses the index-generic trim primitive at `Fin 3`. -/
theorem chain3_degreeY2_trim_eval (p : MultiPoly 3)
    (h_last_zero : ∀ (x : Real) (env : Fin 3 → Real),
       MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
         (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p)) x env = 0) :
    ∀ z : Real, (chain3Fn p).eval z
      = (chain3Fn (MachLib.ChainExp2Trim.dropLeadingYAt (⟨2, by omega⟩ : Fin 3) p)).eval z := by
  intro z
  exact (MachLib.ChainExp2Trim.eval_dropLeadingYAt_of_last_canonically_zero
    (⟨2, by omega⟩ : Fin 3) p (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p)
    h_last_zero z ((IterExpChain 3).chainValues z)).symm

/-- **The degreeY₂-trim, measure descent.** Dropping the leading `y₂`-term strictly lowers the FIRST
(`degreeY₂`, syntactic) component of the depth-3 measure — hence `chain3OrderCanon` — via `lexProd_of_fst`.
This is the depth-3 recursion's `degreeY₂`-shrinking move (mirrors depth-2 `chain2_trim_order`). -/
theorem chain3_degreeY2_trim_order (p : MultiPoly 3)
    (hd2 : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p ≠ 0) :
    chain3OrderCanon (MachLib.ChainExp2Trim.dropLeadingYAt (⟨2, by omega⟩ : Fin 3) p) p := by
  have hlt : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
      (MachLib.ChainExp2Trim.dropLeadingYAt (⟨2, by omega⟩ : Fin 3) p)
    < MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p :=
    MachLib.ChainExp2Trim.degreeY_dropLeadingYAt_lt (⟨2, by omega⟩ : Fin 3) p (Nat.pos_of_ne_zero hd2)
  exact lexProd_of_fst hlt

/-! ### The augmented measure `M5` for the inner-trim

The inner-trim (dropping a phantom leading `y₁`-term of `lcY₂ p`) preserves `chain3MeasureCanon` (it is
eval-invariant) while strictly lowering the *syntactic* `degreeY₁` of the inner `q := dropLastY(lcY₂ p)`.
So it is not a `chain3OrderCanon` descent on its own. `M5` appends that syntactic `degreeY₁ q` as a strictly
less-significant tiebreaker: `M5 p = (chain3MeasureCanon p, degreeY₁ q)`. The reduce and `degreeY₂`-trim,
which drop the FIRST component, lift for free (`lexProd_of_fst`); the inner-trim drops either the first
(if `degreeY₂` drops) or the second (`degreeY₁ q`). -/

/-- The augmented depth-3 measure: the canonical measure with syntactic `degreeY₁ q` as an innermost
tiebreaker. -/
noncomputable def chain3Measure5 (p : MultiPoly 3) : (Nat × (Nat × (Nat × Nat))) × Nat :=
  (chain3MeasureCanon p,
   MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
     (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)))

/-- The augmented order — `chain3OrderCanon` with the `degreeY₁ q` tiebreaker. -/
def chain3Order5 : MultiPoly 3 → MultiPoly 3 → Prop :=
  InvImage (LexProd.lexProd (LexProd.lexProd (· < ·) nestedLT) (· < ·)) chain3Measure5

/-- **Well-founded** — `lexProd` of the (well-founded) canonical order with `Nat`'s `<`. -/
theorem chain3Order5_wf : WellFounded chain3Order5 :=
  InvImage.wf chain3Measure5 (LexProd.lexProd_wf LexProd.natQuadLex_wf Nat.lt_wfRel.wf)

/-- The reduce descent lifts to `M5` for free — it drops the first (`chain3MeasureCanon`) component. -/
theorem chain3Reduce_order5_hnz (p : MultiPoly 3)
    (hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
      (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)))).2 ≠ 0) :
    chain3Order5 (chain3Reduce (MachLib.Real.natCast (cdegY0
      (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))))) p) p :=
  lexProd_of_fst (chain3Reduce_nestedLT_hnz p hnz)

/-- The `degreeY₂`-trim descent lifts to `M5` for free — it also drops the first component. -/
theorem chain3_degreeY2_trim_order5 (p : MultiPoly 3)
    (hd2 : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p ≠ 0) :
    chain3Order5 (MachLib.ChainExp2Trim.dropLeadingYAt (⟨2, by omega⟩ : Fin 3) p) p :=
  lexProd_of_fst (chain3_degreeY2_trim_order p hd2)

/-- **The inner-trim M5-descent** — the last shrinking move. For `p` with `degreeY₂ p > 0`, a phantom
leading `y₁`-term of `lcY₂ p` (`h_phantom`), and positive `y₁`-degree there (`hd1pos`), `innerTrim3 p`
strictly lowers `M5`. The FIRST component `chain3MeasureCanon` TIES — `degreeY₂` exactly
(`degreeY2_innerTrim3_eq`) and the inner eval-invariant measure because `lcY₂(innerTrim3 p)` is eval-equal
to `lcY₂ p` (the dropped `y₁`-term vanishes) — and the SECOND component (`degreeY₁ q`) DROPS
(`degreeY_dropLeadingYAt_lt`). Via `lexProd_of_snd`. -/
theorem innerTrim3_order5 (p : MultiPoly 3)
    (hd2pos : 0 < MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
    (hd1pos : 0 < MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3)
      (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))
    (h_phantom : ∀ (x : Real) (env : Fin 3 → Real),
      MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨1, by omega⟩ : Fin 3)
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)).getLast
        (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 3)
          (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))) x env = 0) :
    chain3Order5 (innerTrim3 p) p := by
  apply LexProd.lexProd_of_snd
  · show chain3MeasureCanon (innerTrim3 p) = chain3MeasureCanon p
    have hdeg : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (innerTrim3 p)
        = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p := degreeY2_innerTrim3_eq p
    have hinner : chain2MeasureCanonEvalInv (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) (innerTrim3 p)))
        = chain2MeasureCanonEvalInv (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) := by
      apply chain2MeasureCanonEvalInv_eq_of_eval_eq
      intro x env2
      have hlcf1 : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
          (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) (innerTrim3 p)) = 0 :=
        MultiPoly.degreeY_leadingCoeffY _ _
      have hlcf2 : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3)
          (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p) = 0 :=
        MultiPoly.degreeY_leadingCoeffY _ _
      have hrestrict : (fun i : Fin 2 =>
          (fun j : Fin 3 => if h : j.val < 2 then env2 ⟨j.val, h⟩ else 0) ⟨i.val, by omega⟩) = env2 := by
        funext i
        show (if h : i.val < 2 then env2 ⟨i.val, h⟩ else 0) = env2 i
        rw [dif_pos i.isLt]
      have hbridge : ∀ (X : MultiPoly 3), MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) X = 0 →
          MultiPoly.eval (MultiPoly.dropLastY X) x env2
            = MultiPoly.eval X x (fun j : Fin 3 => if h : j.val < 2 then env2 ⟨j.val, h⟩ else 0) := by
        intro X hX
        have hev := MultiPoly.eval_dropLastY X hX x
          (fun j : Fin 3 => if h : j.val < 2 then env2 ⟨j.val, h⟩ else 0)
        rwa [hrestrict] at hev
      rw [hbridge _ hlcf1, hbridge _ hlcf2,
          leadingCoeffY2_innerTrim3_eval p hd2pos,
          MachLib.ChainExp2Trim.eval_dropLeadingYAt_of_last_canonically_zero (⟨1, by omega⟩ : Fin 3)
            (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)
            (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 3)
              (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))
            h_phantom]
    show (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (innerTrim3 p),
          chain2MeasureCanonEvalInv (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) (innerTrim3 p))))
        = (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p,
           chain2MeasureCanonEvalInv (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)))
    rw [hdeg, hinner]
  · show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) (innerTrim3 p)))
        < MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))
    rw [degreeY1_dropLastY, degreeY1_dropLastY, leadingCoeffY2_innerTrim3_degreeY1 p hd2pos]
    exact MachLib.ChainExp2Trim.degreeY_dropLeadingYAt_lt (⟨1, by omega⟩ : Fin 3)
      (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p) hd1pos

end MachLib.IterExpDepth3Capstone
