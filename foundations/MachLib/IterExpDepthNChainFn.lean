import MachLib.IterExpDepthNCoupling

/-!
# Phase D (D3, step i) — the `chainNFn` wrapper and the reduce-step evaluation

`chainNFn N p` wraps a `MultiPoly N` as a `PfaffianFn` over `IterExpChain N` (the ∀N analog of `chain3Fn`).
The reduce-step connects the reduce to the vehicle's reduce value:

`chainNFn_reduce_eval` — `(chainNFn (chainNReduce (fullMult k p) p)).eval z = (chainNFn p)'.eval z −
reductMultP k p z · (chainNFn p).eval z`. Immediate from `chainNReduce = cTD − m·p` (`eval_sub`/`eval_mul`)
+ the D3a coupling `eval(fullMult) = reductMultP`. This is the `f' − reductMult·f` the Rolle transfer counts.
No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpDepthNReduce

/-- The depth-`N` Pfaffian function wrapping a `MultiPoly N` over `IterExpChain N`. -/
noncomputable def chainNFn (N : Nat) (p : MultiPoly N) : PfaffianFn :=
  { n := N, chain := IterExpChain N, poly := p }

/-- **The reduce-step, ∀N.** The reduce (with the full graded multiplier) evaluates along the chain to
`f' − reductMultP·f` — the reduce value the Rolle transfer counts. -/
theorem chainNFn_reduce_eval (k : Nat) (p : MultiPoly (k + 2)) (z : Real) :
    (chainNFn (k + 2) (chainNReduce k (fullMult k p) p)).eval z
    = (chainNFn (k + 2) p).chainTotalDerivative.eval z
      - reductMultP k p z * (chainNFn (k + 2) p).eval z := by
  show MultiPoly.eval (chainNReduce k (fullMult k p) p) z ((IterExpChain (k + 2)).chainValues z)
    = MultiPoly.eval (chainTotalDeriv (IterExpChain (k + 2)) p) z ((IterExpChain (k + 2)).chainValues z)
      - reductMultP k p z * MultiPoly.eval p z ((IterExpChain (k + 2)).chainValues z)
  unfold chainNReduce
  rw [MultiPoly.eval_sub, MultiPoly.eval_mul, eval_fullMult_eq_reductMultP k p z]

end MachLib.IterExpDepthN
