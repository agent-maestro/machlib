import MachLib.PfaffianGeneralReduce
import MachLib.IterExpDepthNDegreeX

/-!
# `chainRestrict` relation-degree bounds (general Pfaffian explicit bound, step 4)

For the strengthened multiplier construction the uniform format bound `D` must survive the depth
recursion onto `chainRestrict c`. Since `(chainRestrict c).relations i = dropLastY (c.relations …)`
(`PfaffianGeneralReduce.chainRestrict`) and `dropLastY` preserves `degreeX` (`degreeX_dropLastY`), a bound
`D` on `c`'s relation `degreeX` bounds the restricted chain's too — so the same `D` threads all the way
down. This is the small lemma the strengthened-construction plan (design §4-mult) flagged.
-/

open MachLib.MultiPolyMod MachLib.PfaffianChainMod

namespace MachLib.PfaffianGeneralReduce

/-- The restricted chain's relation `degreeX` equals the parent relation's (`dropLastY` preserves
`degreeX`). -/
theorem degreeX_chainRestrict_relations {N : Nat} (c : PfaffianChain (N + 1)) (i : Fin N) :
    MultiPoly.degreeX ((chainRestrict c).relations i)
      = MultiPoly.degreeX (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) := by
  show MultiPoly.degreeX (MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
      = MultiPoly.degreeX (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
  exact MachLib.IterExpDepthN.degreeX_dropLastY _

/-- **The uniform format bound threads down the depth recursion.** If `D` bounds every relation's
`degreeX` in `c`, it bounds every relation's `degreeX` in `chainRestrict c`. -/
theorem degreeX_chainRestrict_relations_le {N : Nat} (c : PfaffianChain (N + 1)) (D : Nat)
    (h : ∀ i : Fin (N + 1), MultiPoly.degreeX (c.relations i) ≤ D) :
    ∀ i : Fin N, MultiPoly.degreeX ((chainRestrict c).relations i) ≤ D := by
  intro i
  rw [degreeX_chainRestrict_relations]
  exact h _

end MachLib.PfaffianGeneralReduce
