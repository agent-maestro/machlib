import MachLib.ChainExp2PathC
import MachLib.IterExpDepthNBridge

/-!
# MachLib.IterExpChainStructural — structural drop/base bridges for `IterExpChain`

Two chain-level structural facts needed to push the unconditional Khovanskii
bound (`ChainExp2SingleExpUnconditional.singleExp_khovanskii_bound_unconditional`)
past single-exp, through the generic `PfaffianFn` pipeline:

* `IterExpChain_one_eq_SingleExpChain` — the depth-1 tower **is** the single-exp
  chain (`iterExp 0 = exp`, `prodVarYUpTo 0 = varY 0`). Lets the chain-length-1
  remainder of a taller reduction be handed to the SingleExp reducer.
* `IterExpChain_dropLast` — `dropLast (IterExpChain (M+2)) = IterExpChain (M+1)`.
  The iterated-exp tower is closed under the chain-level `dropLast`, so the outer
  chain-length recursion (reduce top var → drop → recurse) stays inside the family.

These are pure structural equalities (funext + the shipped `dropLastY_prodVarYUpTo`
commutation), independent of the descent machinery. They upgrade the existing
*chainValues*-level facts (e.g. `ChainExp2Capstone`'s `(IterExpChain 2).dropLast ~
SingleExpChain`) to full structural `=` on `PfaffianChain`.

NOTE (scope, for the next agent): the *descent* needed to actually instantiate
the generic pipeline for `IterExpChain 2+` lives in a **parallel framework**
(`ChainExp2SDR`/`ChainExp2WFInstance` use a bespoke 3-component `chain2Measure`,
not `PfaffianFn.lexMeasure`). Re-deriving it in the generic form is the remaining
multi-session work; and it is architectural-only (the depth-N iterated-exp bound
`IterExpDepthN.chainN_khovanskii_bound_unconditional` is already axiom-clean by a
separate track). See AXIOM_AUDIT_V2.md §2c.
-/

namespace MachLib
namespace IterExpChainStructural

open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.IterExpChainMod

/-- **The depth-1 iterated-exp tower is the single-exp chain.**
`iterExp 0 = Real.exp` and `prodVarYUpTo 0 = varY 0`, and `Fin 1` is a singleton,
so both fields agree. -/
theorem IterExpChain_one_eq_SingleExpChain :
    IterExpChain 1 = SingleExpChain := by
  have he : (IterExpChain 1).evals = SingleExpChain.evals := by
    funext i x
    have hi : i.val = 0 := by omega
    show (IterExpChain 1).evals i x = Real.exp x
    rw [IterExpChain_evals, hi]
    rfl
  have hr : (IterExpChain 1).relations = SingleExpChain.relations := by
    funext i
    have hi0 : i = 0 := by
      apply Fin.eq_of_val_eq; have := i.isLt; omega
    show (IterExpChain 1).relations i = MultiPoly.varY 0
    rw [IterExpChain_relations, hi0]
    rfl
  calc IterExpChain 1
      = { evals := (IterExpChain 1).evals, relations := (IterExpChain 1).relations } := rfl
    _ = { evals := SingleExpChain.evals, relations := SingleExpChain.relations } := by rw [he, hr]
    _ = SingleExpChain := rfl

/-- **The iterated-exp tower is closed under chain-level `dropLast`.**
`dropLast (IterExpChain (M+2)) = IterExpChain (M+1)`: the evals re-index directly
(`iterExp i.val`), and the relations match via the shipped `dropLastY_prodVarYUpTo`
commutation. -/
theorem IterExpChain_dropLast (M : Nat) :
    PfaffianChain.dropLast (IterExpChain (M + 2)) = IterExpChain (M + 1) := by
  have he : (PfaffianChain.dropLast (IterExpChain (M + 2))).evals
          = (IterExpChain (M + 1)).evals := by
    funext i x; rfl
  have hr : (PfaffianChain.dropLast (IterExpChain (M + 2))).relations
          = (IterExpChain (M + 1)).relations := by
    funext i
    show MultiPoly.dropLastY ((IterExpChain (M + 2)).relations ⟨i.val, by omega⟩)
       = (IterExpChain (M + 1)).relations i
    rw [IterExpChain_relations, IterExpChain_relations]
    exact MachLib.IterExpDepthN.dropLastY_prodVarYUpTo M i.val i.isLt
  calc PfaffianChain.dropLast (IterExpChain (M + 2))
      = { evals := (PfaffianChain.dropLast (IterExpChain (M + 2))).evals,
          relations := (PfaffianChain.dropLast (IterExpChain (M + 2))).relations } := rfl
    _ = { evals := (IterExpChain (M + 1)).evals,
          relations := (IterExpChain (M + 1)).relations } := by rw [he, hr]
    _ = IterExpChain (M + 1) := rfl

end IterExpChainStructural
end MachLib
