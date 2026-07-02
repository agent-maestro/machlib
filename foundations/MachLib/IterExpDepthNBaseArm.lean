import MachLib.IterExpDepthNChainFn
import MachLib.IterExpDepthNBridge

/-!
# Phase D (D3 step ii) — the WF induction's base arm: `degreeY_top = 0` drops a level

When `p`'s top variable does not occur (`degreeY_top p = 0`), `chainNFn (k+2) p` agrees on the nose with
`chainNFn (k+1) (dropLastY p)` (both evaluate the same polynomial data — `dropLastY_eval_IterExp`), so the
depth-`(k+1)` bound transfers verbatim. This is the recursion's floor arm, taking the *outer* depth
induction hypothesis. ∀N analog of `chain3Fn_bound_of_degreeY2_zero`. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod

/-- **The base arm.** With `degreeY_top p = 0`, the depth-`(k+1)` bound (the outer IH `IH`) transfers to
`chainNFn (k+2) p`. -/
theorem chainNFn_bound_of_degreeYtop_zero (k : Nat) (p : MultiPoly (k + 2))
    (hd : MultiPoly.degreeY (⟨k + 1, by omega⟩ : Fin (k + 2)) p = 0) (a b : Real) (hab : a < b)
    (hne : ∃ z, a < z ∧ z < b ∧ (chainNFn (k + 2) p).eval z ≠ 0)
    (IH : ∀ (q : MultiPoly (k + 1)) (a' b' : Real), a' < b' →
        (∃ z, a' < z ∧ z < b' ∧ (chainNFn (k + 1) q).eval z ≠ 0) →
        ∃ M, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a' < z ∧ z < b' ∧ (chainNFn (k + 1) q).eval z = 0) → zeros.length ≤ M) :
    ∃ M, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (chainNFn (k + 2) p).eval z = 0) → zeros.length ≤ M := by
  have heval : ∀ z, (chainNFn (k + 2) p).eval z = (chainNFn (k + 1) (MultiPoly.dropLastY p)).eval z := by
    intro z
    show MultiPoly.eval p z ((IterExpChain (k + 2)).chainValues z)
      = MultiPoly.eval (MultiPoly.dropLastY p) z ((IterExpChain (k + 1)).chainValues z)
    exact dropLastY_eval_IterExp k p hd z
  obtain ⟨z, hza, hzb, hzne⟩ := hne
  obtain ⟨M, hM⟩ := IH (MultiPoly.dropLastY p) a b hab ⟨z, hza, hzb, by rw [← heval]; exact hzne⟩
  refine ⟨M, fun zeros hnd hz => hM zeros hnd (fun z' hz'mem => ?_)⟩
  obtain ⟨ha, hb', hzero⟩ := hz z' hz'mem
  exact ⟨ha, hb', by rw [← heval]; exact hzero⟩

end MachLib.IterExpDepthN
