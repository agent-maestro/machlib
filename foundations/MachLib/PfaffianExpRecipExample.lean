import MachLib.PfaffianExpRecipClassW
import MachLib.ExpRationalKhovanskii

/-!
# A concrete witness-enriched chain — inhabitation of `IsExpOrRecipW`

The simplest witness-enriched chain: the depth-1 reciprocal chain `[1/x]` with a
class-shaped relation `(−1)·y₀²`. Nothing in the descent development exercises
`IsExpOrRecipW`'s reciprocal disjunct on a *concrete* chain; this file does,
validating that the class (with its witness, coherence, and positivity
obligations) is genuinely inhabited and usable — the simplest "encoder output".
The witness is `v = x` (`y₀ = 1/x`); coherence is `(1/x)' = −(1/x)²`.
-/

namespace MachLib
namespace PfaffianExpRecipW
open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianGeneralReduce

/-- The concrete depth-1 reciprocal chain `[1/x]` with a class-shaped relation
`(−1)·y₀²`. The simplest witness-enriched chain — validates that
`IsExpOrRecipW`'s reciprocal disjunct is inhabited by a real chain, with witness
`v = x` (`y₀ = 1/x`), coherence, and positivity. -/
noncomputable def recipChainW : PfaffianChain 1 :=
  { evals := fun _ x => 1 / x
  , relations := fun i =>
      MultiPoly.mul (MultiPoly.const (-1)) (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.varY i)) }

/-- `recipChainW` is witness-enriched on any `(a,b) ⊂ (0,∞)`: its only level is
reciprocal with witness `x`. -/
theorem recipChainW_isW (a b : Real) (ha : 0 < a) : IsExpOrRecipW recipChainW a b := by
  intro i
  refine ⟨Or.inr ⟨MultiPoly.const (-1), MultiPoly.varX, ?_, rfl, ?_, ?_, ?_⟩, ?_⟩
  · simp [MultiPoly.degreeY]
  · intro j _; simp [MultiPoly.degreeY]
  · intro x hxa hxb
    have hx : 0 < x := lt_trans_ax ha hxa
    -- evals i x * eval varX x env = (1/x) * x = 1
    show (1 / x) * MultiPoly.eval MultiPoly.varX x (recipChainW.chainValues x) = 1
    show (1 / x) * x = 1
    rw [mul_comm (1 / x) x]; exact mul_div_cancel_left (ne_of_gt hx)
  · intro x hxa hxb
    have hx : 0 < x := lt_trans_ax ha hxa
    show 0 < MultiPoly.eval MultiPoly.varX x (recipChainW.chainValues x)
    exact hx
  · intro j hj
    have h1 := i.isLt; have h2 := j.isLt; omega

/-- `recipChainW` is coherent on `(a,b) ⊂ (0,∞)`: `(1/x)' = −(1/x)²`. -/
theorem recipChainW_coh (a b : Real) (ha : 0 < a) : recipChainW.IsCoherentOn a b := by
  intro x hxa hxb i
  have hx : 0 < x := lt_trans_ax ha hxa
  show HasDerivAt (fun x => 1 / x)
    (MultiPoly.eval (MultiPoly.mul (MultiPoly.const (-1))
      (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.varY i))) x (recipChainW.chainValues x)) x
  have hval : MultiPoly.eval (MultiPoly.mul (MultiPoly.const (-1))
      (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.varY i))) x (recipChainW.chainValues x)
      = -((1 / x) * (1 / x)) := by
    show (-1) * ((1 / x) * (1 / x)) = -((1 / x) * (1 / x))
    mach_ring
  rw [hval]; exact reciprocal_hasDerivAt x hx

/-- `recipChainW` is positive on `(a,b) ⊂ (0,∞)`. -/
theorem recipChainW_pos (a b : Real) (ha : 0 < a) :
    ∀ z, a < z → z < b → ∀ i : Fin 1, 0 < recipChainW.evals i z :=
  fun z hza _ _ => by show 0 < 1 / z; exact div_pos_of_pos_pos one_pos (lt_trans_ax ha hza)

end PfaffianExpRecipW
end MachLib
