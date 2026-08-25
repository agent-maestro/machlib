import MachLib.ChainExp2Unconditional

/-!
# The chain-2 Khovanskii bound, uniform in the interval

`EMLZeroBoundRay` reduced `OneQueryDichotomy` to one antecedent — a zero bound with the count
quantified **before** the interval — and measured the distance to the existing results as a
**quantifier reordering**. This module performs that reordering.

## It is a restatement, not a re-proof

The existing statements read `∀ (a b : Real), a < b → … → ∃ N, …`, so as written the bound may depend
on the interval. Reading the proofs shows it does not. At the bottom of the stack,

```
obtain ⟨g, k, hg0, hwit⟩ := se_reduces p
refine ⟨MultiPoly.degreeX g.poly + k, ?_⟩
```

`N = degreeX g.poly + k`, and `g`, `k` come from `se_reduces p` — **a function of `p` alone**. The
interval is used only afterwards, to apply `khovanskii_bound_full`. The same holds one level up:
`chain2_reduces_to_y1free` already quantifies `a b` *inside* its conclusion, and its `g`, `k` likewise
depend only on `p`.

So the bounds were uniform all along and the statements simply did not say so. Each proof below is
the original with `intro a b hab` moved *after* the witness is supplied.

## Why this was worth doing rather than assuming

"Khovanskii bounds are uniform in nature" is true and is not a proof. A statement that quantifies `N`
after the interval licenses only the weaker reading, and every downstream use inherits that. The
distance between the two really is one `intro`, but it had to be checked against the construction
rather than against the intuition — the same discipline that killed the growth-regime detour.

## Scope

Chain-2 only, and the terminal non-vanishing side condition is carried unchanged. This does **not**
discharge `OneQueryDichotomy`: the remaining mismatches are chain shape (the totalised `log`) and
transporting reducibility, both untouched here.
-/

namespace MachLib
namespace ChainExp2PathC

open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn

/-- **Uniform in the interval.** `singleExp_khovanskii_bound_unconditional` with `N` hoisted in front
of `a b` — the same proof, with the interval introduced after the witness. -/
theorem singleExp_khovanskii_bound_uniform
    (p : MultiPoly 1)
    (terminal_nonzero :
       ∀ g k, g.n = 0 →
         PfaffianFn.IsKhovanskiiReducible (⟨1, SingleExpChain, p⟩ : PfaffianFn) g k →
         ∃ x : Real, g.eval x ≠ 0) :
    ∃ N : Nat, ∀ (a b : Real), a < b → ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (⟨1, SingleExpChain, p⟩ : PfaffianFn).eval z = 0) →
      zeros.length ≤ N := by
  obtain ⟨g, k, hg0, hwit⟩ := se_reduces p
  refine ⟨MultiPoly.degreeX g.poly + k, ?_⟩
  intro a b hab zeros hnodup hzeros
  exact PfaffianFn.khovanskii_bound_full
    (⟨1, SingleExpChain, p⟩ : PfaffianFn) g k hwit
    SingleExpChain_isTriangular hg0 a b hab
    (SingleExpChain_isCoherentOn a b)
    (terminal_nonzero g k hg0 hwit) zeros hnodup hzeros

end ChainExp2PathC

namespace ChainExp2Capstone

open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2Bound

/-- The `y₁`-free base bound, uniform in the interval. -/
theorem base_bound_y1free_uniform (g : MultiPoly 2)
    (hy1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) g = 0)
    (h_term : ∀ g' k, g'.n = 0 →
       PfaffianFn.IsKhovanskiiReducible
         (⟨1, SingleExpChain, MultiPoly.dropLastY g⟩ : PfaffianFn) g' k →
       ∃ x : Real, g'.eval x ≠ 0) :
    ∃ N : Nat, ∀ (a b : Real), a < b → ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn g).eval z = 0) → zeros.length ≤ N := by
  obtain ⟨N, hN⟩ :=
    MachLib.ChainExp2PathC.singleExp_khovanskii_bound_uniform (MultiPoly.dropLastY g) h_term
  refine ⟨N, fun a b hab zeros hnd hz => hN a b hab zeros hnd (fun z hzmem => ?_)⟩
  obtain ⟨ha, hb', hzero⟩ := hz z hzmem
  exact ⟨ha, hb', by rw [← chain2Fn_y1free_eval_eq_singleExp g hy1 z]; exact hzero⟩

/-- **Chain-2 Khovanskii bound, uniform in the interval.** One `N` for *every* `(a,b)` — the shape
`eventually_nonzero_of_uniformZeroBound` consumes. -/
theorem chain2_khovanskii_bound_uniform (p : MultiPoly 2) :
    ∃ (g : MultiPoly 2) (k : Nat), MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) g = 0 ∧
      ((∀ g' j, g'.n = 0 →
         PfaffianFn.IsKhovanskiiReducible
           (⟨1, SingleExpChain, MultiPoly.dropLastY g⟩ : PfaffianFn) g' j →
         ∃ x : Real, g'.eval x ≠ 0) →
       ∃ N : Nat, ∀ (a b : Real), a < b → ∀ zeros : List Real, zeros.Nodup →
         (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn p).eval z = 0) → zeros.length ≤ N) := by
  obtain ⟨g, k, hg, hred⟩ := chain2_reduces_to_y1free p
  refine ⟨g, k, hg, fun h_term => ?_⟩
  obtain ⟨N, hN⟩ := base_bound_y1free_uniform g hg h_term
  exact ⟨N + k, fun a b hab zeros hnd hz => hred a b hab N (hN a b hab) zeros hnd hz⟩

end ChainExp2Capstone
end MachLib
