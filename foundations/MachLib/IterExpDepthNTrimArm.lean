import MachLib.IterExpDepthNMeasureCanon
import MachLib.IterExpDepthNChainFn
import MachLib.ChainExp2Trim

/-!
# Phase D (D3 step ii) — the WF induction's degree-trim arm

When the top `y`-coefficient of `p` is *phantom* (vanishes on every environment), dropping it changes
nothing along the chain but strictly lowers the syntactic top degree:

* `chainN_degreeYtop_trim_order` — `dropLeadingYAt` strictly lowers `chainNMeasureCanon`'s first
  (syntactic `degreeY_top`) component, hence `chainNOrderCanon` (via `nestedOrder_of_fst`);
* `chainNFn_degreeYtop_trim_eval` — `chainNFn p` agrees with `chainNFn (dropLeadingYAt p)` on the chain
  (dropping an identically-zero leading term).

∀N analog of `chain3_degreeY2_trim_*`. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2Trim

/-- **Degree-trim, measure descent.** Dropping the leading top term strictly lowers the syntactic
`degreeY_top` — the first component of `chainNMeasureCanon` — hence `chainNOrderCanon`. -/
theorem chainN_degreeYtop_trim_order (m : Nat) (p : MultiPoly (m + 3))
    (hd : 0 < MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p) :
    chainNOrderCanon m (dropLeadingYAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p) p := by
  apply nestedOrder_of_fst
  show MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3))
        (dropLeadingYAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p)
    < MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p
  exact degreeY_dropLeadingYAt_lt (⟨m + 2, by omega⟩ : Fin (m + 3)) p hd

/-- **Degree-trim, eval equality.** A phantom leading top term contributes nothing along the chain. -/
theorem chainNFn_degreeYtop_trim_eval (m : Nat) (p : MultiPoly (m + 3))
    (h_phantom : ∀ (x : Real) (env : Fin (m + 3) → Real),
      MultiPoly.eval ((yCoeffsAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p).getLast
        (yCoeffsAt_nonempty (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) x env = 0) (z : Real) :
    (chainNFn (m + 3) p).eval z
      = (chainNFn (m + 3) (dropLeadingYAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p)).eval z := by
  show MultiPoly.eval p z ((IterExpChain (m + 3)).chainValues z)
    = MultiPoly.eval (dropLeadingYAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p) z
        ((IterExpChain (m + 3)).chainValues z)
  exact (eval_dropLeadingYAt_of_last_canonically_zero (⟨m + 2, by omega⟩ : Fin (m + 3)) p
    (yCoeffsAt_nonempty (⟨m + 2, by omega⟩ : Fin (m + 3)) p) h_phantom z
    ((IterExpChain (m + 3)).chainValues z)).symm

end MachLib.IterExpDepthN
