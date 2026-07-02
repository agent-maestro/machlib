import MachLib.IterExpDepthNChainEval
import MachLib.IterExpDepthNDescentInduction
import MachLib.IterExpDepthNBridge

/-!
# Phase D (D3a) — coupling the reduce multiplier `fullMult` to the vehicle's multiplier

`chainNReduce (fullMult k p) p = cTD p − fullMult k p · p`, so along the chain the reduce value is
`(chainNFn p)' − eval(fullMult k p)·(chainNFn p)`. The vehicle counts `f' − reductMult·f`. This file
proves the missing link: `eval(fullMult k p)` along the chain is a concrete `Σ dₖ·prodExp + c`
(`reductMultP`, the level degrees extracted recursively from `p`).

* `eval_liftLastY_chain` — `eval (liftLastY x)` along the `(k+3)`-chain = `eval x` along the `(k+2)`-chain;
* `reductMultP k p z` — the reduce multiplier value: `degreeY_top p · prodExp z k + (lower, from
  dropLastY(leadingCoeffY_top p))`;
* `eval_fullMult_eq_reductMultP` — **`eval(fullMult k p) [chain] = reductMultP k p z`**, by induction on
  depth (top graded term via `eval_Ffac_chain`; lower term via `eval_liftLastY_chain` + IH).

No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.IterExpChainMod
open MachLib.IterExpTopIdentity
open MachLib.ChainExp2CanonMeasure

/-- `eval (liftLastY x)` along the `(k+3)`-chain equals `eval x` along the `(k+2)`-chain. -/
theorem eval_liftLastY_chain (k : Nat) (x : MultiPoly (k + 2)) (z : Real) :
    MultiPoly.eval (MultiPoly.liftLastY x) z ((IterExpChain (k + 3)).chainValues z)
      = MultiPoly.eval x z ((IterExpChain (k + 2)).chainValues z) := by
  rw [eval_liftLastY x z ((IterExpChain (k + 3)).chainValues z), chainValues_restrict_eq (k + 1) z]

/-- The reduce multiplier value along the chain, extracted recursively from `p`. -/
noncomputable def reductMultP : (k : Nat) → MultiPoly (k + 2) → Real → Real
  | 0 => fun p z =>
      MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p) * prodExp z 0
        + MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))
  | k + 1 => fun p z =>
      MachLib.Real.natCast (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) p) * prodExp z (k + 1)
        + reductMultP k (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) p)) z

/-- **The coupling.** `eval(fullMult k p)` along the chain is `reductMultP k p z`. -/
theorem eval_fullMult_eq_reductMultP :
    ∀ (k : Nat) (p : MultiPoly (k + 2)) (z : Real),
      MultiPoly.eval (fullMult k p) z ((IterExpChain (k + 2)).chainValues z) = reductMultP k p z
  | 0, p, z => by
      simp only [fullMult, reductMultP, gradedTop, MultiPoly.eval_add, MultiPoly.eval_mul,
        MultiPoly.eval_const, eval_Ffac_chain]
  | k + 1, p, z => by
      simp only [fullMult, reductMultP, gradedTop, MultiPoly.eval_add, MultiPoly.eval_mul,
        MultiPoly.eval_const, eval_Ffac_chain, eval_liftLastY_chain]
      rw [eval_fullMult_eq_reductMultP k]

end MachLib.IterExpDepthN
