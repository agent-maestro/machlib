import MachLib.MultiPoly
import MachLib.PolynomialCanonical
import MachLib.PfaffianChain
import MachLib.LexProd

/-!
# The chain-aware chain-2 lex measure (the SDR drop-corner fix, step 2)

`ChainExp2SDR.lean`'s closure is blocked because `KhovanskiiReduction.lexMeasure` is a *flat*
`Nat × Nat` whose second component is `polyTrueDegreeStrict(mP2PFL(leadingCoeffY_last))` — and `mP2PFL`
projects `y₀→0`, which is **lossy** for chain-2 (the `y₁`-leading coefficient carries `y₀`). The
counterexample `p = y₀·y₁` has `lcY₁ p = y₀`, `mP2PFL(y₀) = 0`, so the flat measure's second component
reads `0` and the recursion tries to drop a term that is *not* zero at chain values.

The fix (this module): make the second component **chain-aware** — instead of projecting `y₀→0`, score
`lcY₁ p` with the *single-exp* measure (its own `(degreeY₀, trueDeg)`). The chain-2 measure becomes the
**nested** `(degreeY₁, (degreeY₀(lcY₁), trueDeg(...)))` — a `Nat × (Nat × Nat)`, whose well-foundedness
is exactly `LexProd.natTripleLex_wf`. On the counterexample the second component is now `(1, 0) ≠ 0`,
so the measure no longer misfires.

This is a **standalone** definition: it does not touch `KhovanskiiReduction`/`PfaffianChain`, so the
closed/audited single-exp proof is untouched. It supplies the well-founded backbone a chain-2
`StepwiseDecreaseReducer` will recurse on (the remaining, harder, drop-soundness step plugs in here).
-/

namespace MachLib.ChainExp2Measure

open MachLib.MultiPolyMod
open MachLib.PolynomialCanonical
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn

/-- The single-exp measure `(degreeY₀, trueDeg of the y₀-leading coefficient)` of a polynomial `q`.
Applied to `lcY₁ p` (which has no `y₁`), this is exactly the measure single-exp uses on a genuine
SingleExp object — `mP2PFL` is *exact* here because `leadingCoeffY 0 q` is `y`-free. -/
noncomputable def singleExpMeasure (q : MultiPoly 2) : Nat × Nat :=
  (MultiPoly.degreeY (0 : Fin 2) q,
   polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (MultiPoly.leadingCoeffY (0 : Fin 2) q))))

/-- **The chain-aware chain-2 measure.** First component: degree in the top chain variable `y₁`.
Second component: the *single-exp measure of the `y₁`-leading coefficient* — chain-aware, not the lossy
`mP2PFL(y₀)→0` projection. A nested `Nat × (Nat × Nat)`. -/
noncomputable def chain2Measure (p : MultiPoly 2) : Nat × (Nat × Nat) :=
  (MultiPoly.degreeY (1 : Fin 2) p, singleExpMeasure (MultiPoly.leadingCoeffY (1 : Fin 2) p))

/-- The strict order on chain-2 polynomials induced by `chain2Measure`: nested `Nat`-lex pulled back
along the measure. -/
def chain2Order : MultiPoly 2 → MultiPoly 2 → Prop :=
  InvImage (LexProd.lexProd (· < ·) (LexProd.lexProd (· < · : Nat → Nat → Prop) (· < ·))) chain2Measure

/-- **The chain-aware measure is well-founded** — directly from the nesting keystone
`LexProd.natTripleLex_wf` via `InvImage`. This is the well-founded backbone the chain-2 SDR recursion
needs (replacing the flat `lexLT_wf`, which the lossy projection made unsound to recurse on). -/
theorem chain2Order_wf : WellFounded chain2Order :=
  InvImage.wf chain2Measure LexProd.natTripleLex_wf

/-- The second component is genuinely chain-aware: when the `y₁`-leading coefficient has positive
`y₀`-degree, the measure's inner first slot is positive — it does *not* collapse to zero the way the
flat `mP2PFL(y₀)→0` projection does (the source of the unsound drop). This is the property the
drop-soundness step exploits. -/
theorem chain2Measure_inner_pos {p : MultiPoly 2}
    (h : 0 < MultiPoly.degreeY (0 : Fin 2) (MultiPoly.leadingCoeffY (1 : Fin 2) p)) :
    0 < (chain2Measure p).2.1 := h

end MachLib.ChainExp2Measure
