import MachLib.IterExpDepth3CdegY1
import MachLib.ChainExp2NoZeros

/-!
# Depth-3 capstone prep — the `singleExpMeasureCanon` zero facts

Two small, reusable facts the final depth-3 WF assembly needs, both about the *bottom* of the
canonical single-exp measure:

* `smc_const0`  : `singleExpMeasureCanon (const 0) = (0, 0)` — the measure of the zero polynomial.
* `smc_zero_of_eval_zero` : the **converse of `smc2_zero_eval_zero`** — a polynomial that vanishes on
  every environment has canonical single-exp measure `(0, 0)`. (Eval-invariant, so no `y₁`-freeness
  needed.)

These discharge the "single-exp / phantom reduce-result" leaves of the inner descent (gap B) and feed
the non-phantom-from-`hnz` derivation (gap A). Path B; no `sorry`.
-/

namespace MachLib.IterExpDepth3CapstonePrep

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.PolynomialCanonical
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2CdegInv
open MachLib.ChainExp2Reducer
open MachLib.ChainExp2PhantomDescent
open MachLib.ChainExp2NoZeros
open MachLib.IterExpDepth3CdegY1

/-- `singleExpMeasureCanon (const 0) = (0, 0)`: the zero polynomial sits at the bottom of the measure.
Its single `y₀`-coefficient `const 0` is canonically zero, so the reversed `dropWhile` empties —
giving canonical `y₀`-degree `0` and a canonically-zero leading coefficient (`polyTrueDegreeStrict 0`). -/
theorem smc_const0 :
    singleExpMeasureCanon (MultiPoly.const (0 : Real) : MultiPoly 2) = (0, 0) := by
  have hcz : coeffCanonZeroB (MultiPoly.const (0 : Real)) = true := coeffCanonZeroB_const0
  -- The reversed y₀-coefficient list of `const 0` is `[const 0]`, and `dropWhile` empties it.
  have hdw : ((MultiPoly.yCoeffsAt (⟨0, by omega⟩ : Fin 2) (MultiPoly.const (0 : Real))).reverse.dropWhile
      coeffCanonZeroB) = ([] : List (MultiPoly 2)) := by
    show (List.dropWhile coeffCanonZeroB [MultiPoly.const (0 : Real)]) = []
    simp [hcz]
  have h1 : cdegY0 (MultiPoly.const (0 : Real) : MultiPoly 2) = 0 := by
    unfold cdegY0; rw [hdw]; rfl
  have h2 : polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex
      (canonLcY0 (MultiPoly.const (0 : Real) : MultiPoly 2)))) = 0 := by
    have hlc : canonLcY0 (MultiPoly.const (0 : Real) : MultiPoly 2) = MultiPoly.const 0 := by
      unfold canonLcY0; rw [hdw]; rfl
    rw [hlc]
    apply polyTrueDegreeStrict_of_canonicallyZero
    have := coeffCanonZeroB_const0
    unfold coeffCanonZeroB at this
    exact of_decide_eq_true this
  show (cdegY0 (MultiPoly.const (0 : Real) : MultiPoly 2),
        polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex
          (canonLcY0 (MultiPoly.const (0 : Real) : MultiPoly 2))))) = (0, 0)
  rw [h1, h2]

/-- **Converse of `smc2_zero_eval_zero`.** A polynomial that vanishes on every environment has
canonical single-exp measure `(0, 0)` — the measure is eval-invariant, so it agrees with the zero
polynomial's measure. -/
theorem smc_zero_of_eval_zero (q : MultiPoly 2)
    (h : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval q x env = 0) :
    singleExpMeasureCanon q = (0, 0) := by
  rw [singleExpMeasureCanon_eq_of_eval_eq q (MultiPoly.const (0 : Real))
      (fun x env => by rw [h x env]; symm; exact MultiPoly.eval_const 0 x env)]
  exact smc_const0

/-- **`coeffCanonZeroB1 (y1top q) = true ⟹ (smc (lcY₁ q)).2 = 0`** (gap A, the `→` half). A phantom
syntactic-leading `y₁`-coefficient is eval-zero, so its canonical single-exp measure's second component
vanishes: `y1top q ≈eval lcY₁ q`, both `y₁`-free, canon-zero ⟹ eval-zero (the new bridge) ⟹ `smc = (0,0)`. -/
theorem smc2_zero_of_coeffCanonZeroB1_y1top (q : MultiPoly 2)
    (htrue : coeffCanonZeroB1 (y1top q) = true) :
    (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 = 0 := by
  have hyf : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
      (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q) = 0 :=
    MultiPoly.degreeY_leadingCoeffY (⟨1, by omega⟩ : Fin 2) q
  have heval : ∀ (x : Real) (env : Fin 2 → Real),
      MultiPoly.eval (y1top q) x env
        = MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q) x env := by
    intro x env
    show MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).getLast
        (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) q)) x env = _
    exact (eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨1, by omega⟩ : Fin 2) q
      (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) q) x env).symm
  have htop_eq : coeffCanonZeroB1 (y1top q)
      = coeffCanonZeroB1 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q) :=
    coeffCanonZeroB1_eq_of_eval_eq _ _ heval
  rw [htop_eq] at htrue
  rw [smc_zero_of_eval_zero _ (eval_zero_of_coeffCanonZeroB1_yfree _ hyf htrue)]

/-- **Gap A: `hnz ⟹ hq_np`.** A non-canon-zero leading `y₁`-coefficient forces a non-phantom `y1top` —
so the depth-3 reduce descent's `hq_np` hypothesis is FREE in the reduce (`hnz`) case. Contrapositive of
`smc2_zero_of_coeffCanonZeroB1_y1top`. -/
theorem nonphantom_of_hnz (q : MultiPoly 2)
    (hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 ≠ 0) :
    coeffCanonZeroB1 (y1top q) = false := by
  cases hb : coeffCanonZeroB1 (y1top q) with
  | false => rfl
  | true => exact absurd (smc2_zero_of_coeffCanonZeroB1_y1top q hb) hnz

/-- The nested eval-invariant depth-2 measure of the zero polynomial is `(0, (0, 0))` — the bottom.
Mirrors `smc_const0` one level up (`cdegY1`/`canonLcY1`/`coeffCanonZeroB1`). -/
theorem chain2MeasureCanonEvalInv_const0 :
    chain2MeasureCanonEvalInv (MultiPoly.const (0 : Real) : MultiPoly 2) = (0, (0, 0)) := by
  have hcz : coeffCanonZeroB1 (MultiPoly.const (0 : Real)) = true := coeffCanonZeroB1_const0
  have hdw : ((MultiPoly.yCoeffsAt (⟨1, by omega⟩ : Fin 2) (MultiPoly.const (0 : Real))).reverse.dropWhile
      coeffCanonZeroB1) = ([] : List (MultiPoly 2)) := by
    show (List.dropWhile coeffCanonZeroB1 [MultiPoly.const (0 : Real)]) = []
    simp [hcz]
  have h1 : cdegY1 (MultiPoly.const (0 : Real) : MultiPoly 2) = 0 := by
    unfold cdegY1; rw [hdw]; rfl
  have h2 : canonLcY1 (MultiPoly.const (0 : Real) : MultiPoly 2) = MultiPoly.const 0 := by
    unfold canonLcY1; rw [hdw]; rfl
  show (cdegY1 (MultiPoly.const (0 : Real) : MultiPoly 2),
        singleExpMeasureCanon (canonLcY1 (MultiPoly.const (0 : Real) : MultiPoly 2))) = (0, (0, 0))
  rw [h1, h2, smc_const0]

/-- A `y₁`-free `q` with a phantom `y1top` vanishes on every environment: `y1top q ≈eval lcY₁ q = q`
(`leadingCoeffY_eq_self_of_degreeY_zero`), canon-zero ⟹ eval-zero. -/
theorem eval_zero_of_coeffCanonZeroB1_y1top_yfree (q : MultiPoly 2)
    (hyf : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0)
    (htop : coeffCanonZeroB1 (y1top q) = true) :
    ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval q x env = 0 := by
  have hself : MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q = q :=
    leadingCoeffY_eq_self_of_degreeY_zero (⟨1, by omega⟩ : Fin 2) q hyf
  have heval : ∀ (x : Real) (env : Fin 2 → Real),
      MultiPoly.eval (y1top q) x env = MultiPoly.eval q x env := by
    intro x env
    show MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).getLast
        (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) q)) x env = _
    rw [← eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨1, by omega⟩ : Fin 2) q
          (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) q) x env, hself]
  have hqtrue : coeffCanonZeroB1 q = true :=
    ((coeffCanonZeroB1_eq_of_eval_eq (y1top q) q heval).symm).trans htop
  exact eval_zero_of_coeffCanonZeroB1_yfree q hyf hqtrue

/-- **Gap B: the inner descent needs only `hnz`.** Strengthening `chain2MeasureCanonEvalInv_descends` to
drop the `hpos` (`degreeY₁ q > 0`) hypothesis — the single-exp case. When `degreeY₁ q = 0` and the reduce
result is phantom, it is `y₁`-free and hence `≡ 0`, so its measure collapses to `(0, (0, 0))`, which is
`<` the input's `(0, smc q)` because `hnz` gives a nonzero second component. -/
theorem chain2MeasureCanonEvalInv_descends_hnz (q : MultiPoly 2)
    (hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 ≠ 0) :
    nestedLT
      (chain2MeasureCanonEvalInv (chain2Reduce
        (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))) q))
      (chain2MeasureCanonEvalInv q) := by
  have hq_np := nonphantom_of_hnz q hnz
  by_cases hpos : 0 < MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q
  · exact chain2MeasureCanonEvalInv_descends q hq_np hpos hnz
  · have hd0 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q = 0 := by omega
    rw [chain2MeasureCanonEvalInv_eq_chain2MeasureCanon_of_nonphantom q hq_np]
    by_cases hR_np : coeffCanonZeroB1 (y1top (chain2Reduce
        (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))) q)) = false
    · rw [chain2MeasureCanonEvalInv_eq_chain2MeasureCanon_of_nonphantom _ hR_np]
      exact chain2Reduce_nestedLT_canon q hnz
    · have hR_ph : coeffCanonZeroB1 (y1top (chain2Reduce
          (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))) q)) = true := by
        cases hb : coeffCanonZeroB1 (y1top (chain2Reduce
            (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))) q)) with
        | false => exact absurd hb hR_np
        | true => rfl
      have hred_yf : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (chain2Reduce
          (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))) q) = 0 := by
        have h : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (chain2Reduce
            (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))) q)
              = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q :=
          chain2Reduce_fst_preserved
            (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))) q
        rw [h, hd0]
      have hred_zero := eval_zero_of_coeffCanonZeroB1_y1top_yfree _ hred_yf hR_ph
      rw [chain2MeasureCanonEvalInv_eq_of_eval_eq _ (MultiPoly.const (0 : Real))
            (fun x env => by rw [hred_zero x env]; symm; exact MultiPoly.eval_const 0 x env),
          chain2MeasureCanonEvalInv_const0]
      refine LexProd.lexProd_of_snd hd0.symm ?_
      rcases Nat.eq_zero_or_pos (singleExpMeasureCanon
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).1 with ha | ha
      · exact LexProd.lexProd_of_snd ha.symm (Nat.pos_of_ne_zero hnz)
      · exact lexProd_of_fst ha

end MachLib.IterExpDepth3CapstonePrep
