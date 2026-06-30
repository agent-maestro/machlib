import MachLib.ChainExp2Reducer
import MachLib.MultiPolyReconstruct

/-!
# Piece 1 — the canonical `y₀`-degree measure (the fix the obstruction demands)

`ChainExp2Reducer.chain2_correctReduce_not_nestedLT` proved (machine-checked) that even the *correct*
reduce `chain2Reduce` does not descend `chain2Measure`, because the inner first component is the
**syntactic** `MultiPoly.degreeY ⟨0⟩` — and the reduce produces `lcY₁` as a non-canonical `sub`/`add` AST
whose `y₀` cancellation is only semantic. The fix is to measure a **canonical** `y₀`-degree instead.

This file builds that canonical inner measure:

* `cdegY0 q` — the canonical `y₀`-degree: drop the trailing **canonically-zero** `y₀`-coefficients
  (`CanonicallyZero` of the coefficient's x-polynomial), the remaining length minus one. Unlike syntactic
  `degreeY ⟨0⟩`, it does not count a leading `y₀`-term that always evaluates to 0.
* `canonLcY0 q` — the corresponding canonical leading `y₀`-coefficient.
* `chain2MeasureCanon` / `chain2OrderCanon` / `chain2OrderCanon_wf` — the canonicalised chain-2 measure
  (first component `degreeY₁` stays syntactic, since the **trim** arm lowers it; only the inner is
  canonicalised) and its well-foundedness (trivially via the `LexProd` keystone).

Status: the **foundation** — definitions, well-foundedness, and the refinement `cdegY0 ≤ degreeY ⟨0⟩`.
The *descent* of `chain2Reduce` under this measure (the `x·y₁` case flipping from the machine-checked
increase to a canonical descent `(0,1) → (0,0)`) is Piece 3 — it needs the `leadingCoeffY`-under-`cTD`
identity + the single-exp canonical descent, not `rfl` (`cdegY0`/`CanonicallyZero` are noncomputable).
Single-exp framework untouched (Path B).
-/

namespace MachLib.ChainExp2CanonMeasure

open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.PolynomialCanonical
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.MultiPolyReconstruct
open MachLib.ChainExp2Reducer

/-- A `y₀`-coefficient is **canonically zero** iff its x-polynomial (via `mP2PFL`, exact because a
`y₀`-coefficient is `y₀`-free) is `CanonicallyZero`. As a `Bool` (noncomputable `Decidable` instance) for
`List.dropWhile`. -/
noncomputable def coeffCanonZeroB (c : MultiPoly 2) : Bool :=
  decide (CanonicallyZero (polyCoeffs (multiPolyToPolyForLex c)))

/-- **Canonical `y₀`-degree.** Drop the trailing (high-power) canonically-zero `y₀`-coefficients, then
take `length − 1`. Refines the syntactic `MultiPoly.degreeY ⟨0⟩`, which counts a phantom leading
`y₀`-term that always evaluates to 0 (the source of `chain2_correctReduce_not_nestedLT`). -/
noncomputable def cdegY0 (q : MultiPoly 2) : Nat :=
  ((yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB).length - 1

/-- The canonical `y₀`-leading coefficient: the last non-canonically-zero `y₀`-coefficient (`const 0` if
all are canonically zero). -/
noncomputable def canonLcY0 (q : MultiPoly 2) : MultiPoly 2 :=
  ((yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB).headD (MultiPoly.const 0)

/-- The **canonical single-exp measure**: `(canonical y₀-degree, canonical x-degree of the canonical
y₀-leading coefficient)`. Replaces the syntactic `singleExpMeasure` that the obstruction defeated. -/
noncomputable def singleExpMeasureCanon (q : MultiPoly 2) : Nat × Nat :=
  (cdegY0 q, polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 q))))

/-- **The canonical chain-2 measure.** First component: `degreeY₁` (kept syntactic — the *trim* arm lowers
it when `lcY₁` is canonically zero, exactly as single-exp does). Inner: the CANONICAL single-exp measure of
`lcY₁`, so a reduce that only *semantically* cancels `y₀` still descends. -/
noncomputable def chain2MeasureCanon (p : MultiPoly 2) : Nat × (Nat × Nat) :=
  (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p,
   singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))

/-- The canonical chain-2 order: nested `Nat`-lex pulled back along `chain2MeasureCanon`. -/
def chain2OrderCanon : MultiPoly 2 → MultiPoly 2 → Prop :=
  InvImage nestedLT chain2MeasureCanon

/-- **The canonical measure is well-founded** — directly from the `LexProd` keystone via `InvImage`
(independent of the measure's internals, so the canonicalisation costs nothing in the WF backbone). -/
theorem chain2OrderCanon_wf : WellFounded chain2OrderCanon :=
  InvImage.wf chain2MeasureCanon LexProd.natTripleLex_wf

/-- A short core fact reused below: `dropWhile` never lengthens a list. -/
private theorem length_dropWhile_le {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.dropWhile p).length ≤ l.length
  | [] => Nat.le_refl 0
  | a :: t => by
    rw [List.dropWhile_cons]
    cases p a with
    | false => exact Nat.le_refl _
    | true => exact Nat.le_trans (length_dropWhile_le p t) (Nat.le_succ _)

/-- **The canonical `y₀`-degree refines the syntactic one:** `cdegY0 q ≤ degreeY ⟨0⟩ q`. (`dropWhile`
only shortens, and `yCoeffsAt` has length `≤ degreeY ⟨0⟩ + 1`.) So the canonical measure never exceeds the
syntactic one — it only *forgets* phantom leading terms. -/
theorem cdegY0_le_degreeY0 (q : MultiPoly 2) :
    cdegY0 q ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := by
  unfold cdegY0
  have h1 :
      ((yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB).length
        ≤ (yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).length :=
    calc ((yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB).length
          ≤ (yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).reverse.length :=
            length_dropWhile_le _ _
      _ = (yCoeffsAt (⟨0, by omega⟩ : Fin 2) q).length := List.length_reverse _
  have h2 := yCoeffsAt_length_le (⟨0, by omega⟩ : Fin 2) q
  omega

/-! ## Structural half against the canonical measure (with the *correct* operator)

The first component of `chain2MeasureCanon` is the same syntactic `degreeY₁` as `chain2Measure`, so the
correct reduce `chain2Reduce` preserves it here too — and the canonical-measure descent collapses to a
single canonical *inner* second-component obligation. This is the Piece-3 structural reduction: what
remains is exactly the canonical inner descent `hsnd` (via the `leadingCoeffY`-under-`cTD` identity +
single-exp canonical descent). -/

/-- First component (`degreeY₁`) preserved by the correct reduce under the **canonical** measure — the
canonical measure keeps `degreeY₁` syntactic, so this is `chain2Reduce_fst_preserved` verbatim. -/
theorem chain2MeasureCanon_fst_chain2Reduce (c : Real) (p : MultiPoly 2) :
    (chain2MeasureCanon (chain2Reduce c p)).1 = (chain2MeasureCanon p).1 :=
  chain2Reduce_fst_preserved c p

/-- **Piece-3 structural reduction.** With the canonical measure, the correct reduce's full `nestedLT`
descent follows from a single canonical *inner* second-component descent `hsnd`
(`singleExpMeasureCanon(lcY₁ ·)`), because the first component is preserved. The remaining open obligation
is exactly `hsnd` — the canonical inner descent. -/
theorem chain2Reduce_nestedLT_canon_of_snd (c : Real) (p : MultiPoly 2)
    (hsnd : LexProd.lexProd (· < · : Nat → Nat → Prop) (· < ·)
              (chain2MeasureCanon (chain2Reduce c p)).2 (chain2MeasureCanon p).2) :
    nestedLT (chain2MeasureCanon (chain2Reduce c p)) (chain2MeasureCanon p) :=
  LexProd.lexProd_of_snd (chain2MeasureCanon_fst_chain2Reduce c p) hsnd

end MachLib.ChainExp2CanonMeasure
