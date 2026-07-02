import MachLib.IterExpProdDeriv
import MachLib.IterExpTopIdentity

/-!
# Phase D (D3a) — chain-eval connectors: `eval(Ffac k) = prodExp` along the chain

Toward coupling the reduce multiplier `fullMult` to the vehicle's `reductMult`, this file evaluates the
product polynomials along `IterExpChain`:

* `iteratedProd_iterExp` — `iteratedProd (iterExp ·) k = prodExp z k` (the abstract `iteratedProd` at the
  iterated-exponential environment is the concrete product);
* `eval_Ffac_chain` — `eval (Ffac k) z (chainValues z) = prodExp z k`, i.e. the top graded factor
  `y₀·…·y_k` evaluates along the chain to `iterExp 0 z · … · iterExp k z`.

No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.IterExpChainMod
open MachLib.IterExpTopIdentity

/-- `iteratedProd` at the iterated-exponential environment is `prodExp`. -/
theorem iteratedProd_iterExp {N : Nat} (z : Real) :
    ∀ (k : Nat) (hk : k < N), iteratedProd (fun i : Fin N => iterExp i.val z) k hk = prodExp z k
  | 0, _ => rfl
  | k + 1, hk => by
      show iteratedProd (fun i : Fin N => iterExp i.val z) k (Nat.lt_of_succ_lt hk)
            * iterExp (k + 1) z
        = prodExp z k * iterExp (k + 1) z
      rw [iteratedProd_iterExp z k (Nat.lt_of_succ_lt hk)]

/-- **`Ffac k` along the chain is `prodExp z k`.** The top graded factor `y₀·…·y_k` evaluated along
`IterExpChain (k+2)` is `iterExp 0 z · … · iterExp k z`. -/
theorem eval_Ffac_chain (M : Nat) (z : Real) :
    MultiPoly.eval (Ffac M) z ((IterExpChain (M + 2)).chainValues z) = prodExp z M := by
  unfold Ffac
  rw [eval_prodVarYUpTo M (by omega) z ((IterExpChain (M + 2)).chainValues z)]
  exact iteratedProd_iterExp z M (by omega)

end MachLib.IterExpDepthN
