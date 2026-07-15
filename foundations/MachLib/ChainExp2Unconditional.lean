import MachLib.ChainExp2Capstone
import MachLib.ChainExp2SingleExpUnconditional

/-!
# MachLib.ChainExp2Unconditional — the chain-2 Khovanskii bound, `sdr_other`-free

`ChainExp2Capstone.chain2_khovanskii_bound` proves the depth-2 iterated-exp
Khovanskii bound but threads a vacuous `sdr_other : PfaffianFn.StepwiseDecreaseReducer`
— the same never-invoked total-reducer hypothesis this session removed from the
single-exp bound. Its base case (`base_bound_y1free`) bounds the `y₁`-free reduct
via `singleExp_khovanskii_bound … sdr_other`; swapping in the **unconditional**
`singleExp_khovanskii_bound_unconditional` deletes `sdr_other` from the entire
chain-2 bound.

This is the compositional payoff of the SingleExp work: chain-2 `p`
→ (reduce top var `y₁`, `chain2_reduces_to_y1free`)
→ `y₁`-free single-exp reduct
→ **unconditional** SingleExp bound.

`#print axioms chain2_khovanskii_bound_unconditional` stays clean of
`zero_count_bound_classical` (inherited from both ingredients).
-/

namespace MachLib
namespace ChainExp2Capstone

open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2Bound

/-- **The `y₁`-free base bound, `sdr_other`-free.** Same as `base_bound_y1free`
but the single-exp base case uses the unconditional bound, so no total reducer is
needed. -/
theorem base_bound_y1free_unconditional (g : MultiPoly 2)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) g = 0)
    (a b : Real) (hab : a < b)
    (h_term : ∀ g' k, g'.n = 0 →
       PfaffianFn.IsKhovanskiiReducible
         (⟨1, SingleExpChain, MultiPoly.dropLastY g⟩ : PfaffianFn) g' k →
       ∃ x : Real, g'.eval x ≠ 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn g).eval z = 0) → zeros.length ≤ N := by
  obtain ⟨N, hN⟩ :=
    MachLib.ChainExp2PathC.singleExp_khovanskii_bound_unconditional
      (MultiPoly.dropLastY g) a b hab h_term
  refine ⟨N, fun zeros hnd hz => hN zeros hnd (fun z hzmem => ?_)⟩
  obtain ⟨ha, hb', hzero⟩ := hz z hzmem
  exact ⟨ha, hb', by rw [← chain2Fn_y1free_eval_eq_singleExp g hy1 z]; exact hzero⟩

/-- **Chain-2 Khovanskii bound, unconditional (no `sdr_other`).** For every
chain-2 `p` there is a `y₁`-free reduct `g` and step count such that, given the
genuine terminal non-vanishing condition, `p`'s zeros are finitely bounded —
`#print axioms`-clean of `zero_count_bound_classical`, and with the vacuous
total-reducer hypothesis eliminated. -/
theorem chain2_khovanskii_bound_unconditional (p : MultiPoly 2) (a b : Real) (hab : a < b) :
    ∃ (g : MultiPoly 2) (k : Nat), MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) g = 0 ∧
      ((∀ g' j, g'.n = 0 →
         PfaffianFn.IsKhovanskiiReducible
           (⟨1, SingleExpChain, MultiPoly.dropLastY g⟩ : PfaffianFn) g' j →
         ∃ x : Real, g'.eval x ≠ 0) →
       ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
         (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn p).eval z = 0) → zeros.length ≤ N) := by
  obtain ⟨g, k, hg, hred⟩ := chain2_reduces_to_y1free p
  refine ⟨g, k, hg, fun h_term => ?_⟩
  obtain ⟨N, hN⟩ := base_bound_y1free_unconditional g hg a b hab h_term
  exact ⟨N + k, fun zeros hnd hz => hred a b hab N hN zeros hnd hz⟩

end ChainExp2Capstone
end MachLib
