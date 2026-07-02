import MachLib.IterExpDepthNChainFn
import MachLib.IterExpDepthNRolle
import MachLib.IterExpDepthNReductExtract

/-!
# Phase D (D3, step i final) — the reduce arm's Rolle content, ∀N

`chainNFn_reduce_step` — `#zeros(chainNFn p) ≤ N + 1` whenever `N` bounds the zeros of
`chainNFn (chainNReduce (fullMult k p) p)`. This is the "+1 zero per reduce" step wired to the *actual*
reduce, ∀N: the Rolle transfer (`zero_count_vehicleN_transfer`, honest `zero_count_bound_by_deriv`)
instantiated with the extracted degrees `dExtract`/`cExtract`, using the reduce-step
(`chainNFn_reduce_eval`) + the reconciliation (`reductMultP_eq_reductMult`). Mirrors the depth-3
`chain3Fn_reduce_step`. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpDepthNReduce

/-- **The reduce step for the ∀N bound.** `#zeros(chainNFn p) ≤ N + 1` whenever `N` bounds the zeros of
the reduce `chainNFn (chainNReduce (fullMult k p) p)`. -/
theorem chainNFn_reduce_step (k : Nat) (p : MultiPoly (k + 2)) (a b : Real) (hab : a < b) (N : Nat)
    (hN : ∀ zeros' : List Real, zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          (chainNFn (k + 2) (chainNReduce k (fullMult k p) p)).eval z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real, zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ (chainNFn (k + 2) p).eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  refine zero_count_vehicleN_transfer (chainNFn (k + 2) p) (dExtract k p) (cExtract k p) (k + 1)
    a b hab (IterExpChain_isCoherentOn (k + 2) a b) N ?_
  intro zeros' hnodup' hz'
  apply hN zeros' hnodup'
  intro z hzmem
  obtain ⟨haz, hzb, hval⟩ := hz' z hzmem
  refine ⟨haz, hzb, ?_⟩
  rw [chainNFn_reduce_eval, reductMultP_eq_reductMult k p z]
  exact hval

end MachLib.IterExpDepthN
