import MachLib.IterExpDepth3CdegY1

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
open MachLib.PolynomialCanonical
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2CdegInv

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

end MachLib.IterExpDepth3CapstonePrep
