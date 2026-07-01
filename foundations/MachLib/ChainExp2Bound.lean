import MachLib.ChainExp2PolyMultRolle
import MachLib.ChainExp2Reducer
import MachLib.IterExpChain

/-!
# Seam B — the chain-2 zero-count bound (poly-multiplier reduce threaded through the iteration)

`IsKhovanskiiReducible`'s `reduce` constructor uses `scaledReduction` (a CONSTANT multiplier); the chain-2
reduce `chain2Reduce c p = P' − ((degreeY₁ p)·y₀ + c)·P` has a POLYNOMIAL multiplier. Per Path B we do not
touch the closed single-exp framework; instead this file builds a chain-2-specific reducibility witness
`Chain2Reducible` and its zero-count bound, using the (already clean) polynomial-multiplier Rolle transfer
`zero_count_polyMultReduce_transfer`. The reduce step is `#zeros(p) ≤ #zeros(chain2Reduce c p) + 1`; a
`congr` (eval-equal) step (used by trimming) is free; `refl` bottoms out.

`#print axioms`-clean of `zero_count_bound_classical`: the reduce uses `zero_count_bound_by_deriv` (honest
Rolle) only.
-/

namespace MachLib.ChainExp2Bound

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2Reducer
open MachLib.ChainExp2PolyMultRolle

/-- The chain-2 Pfaffian function wrapping a `MultiPoly 2` over `IterExpChain 2`. -/
noncomputable def chain2Fn (p : MultiPoly 2) : PfaffianFn :=
  { n := 2, chain := IterExpChain 2, poly := p }

@[simp] theorem chain2Fn_eval (p : MultiPoly 2) (z : Real) :
    (chain2Fn p).eval z = MultiPoly.eval p z ((IterExpChain 2).chainValues z) := rfl

/-- **The reduce eval-identity.** Along the chain, `chain2Reduce c p` evaluates to exactly the
polynomial-multiplier reduce value that `zero_count_polyMultReduce_transfer` bounds:
`(cTD₂ p) − ((degreeY₁ p)·eˣ + c)·p`. -/
theorem chain2Fn_chain2Reduce_eval (c : Real) (p : MultiPoly 2) (z : Real) :
    (chain2Fn (chain2Reduce c p)).eval z
    = (chain2Fn p).chainTotalDerivative.eval z
      - (MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p) * Real.exp z + c)
        * (chain2Fn p).eval z := by
  show MultiPoly.eval (chain2Reduce c p) z ((IterExpChain 2).chainValues z)
     = MultiPoly.eval (chainTotalDeriv (IterExpChain 2) p) z ((IterExpChain 2).chainValues z)
       - (MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p) * Real.exp z + c)
         * MultiPoly.eval p z ((IterExpChain 2).chainValues z)
  unfold chain2Reduce
  rw [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_add, MultiPoly.eval_mul,
      MultiPoly.eval_const, MultiPoly.eval_const]
  have hy0 : MultiPoly.eval (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)) z
              ((IterExpChain 2).chainValues z) = Real.exp z := by
    show (IterExpChain 2).chainValues z (⟨0, by omega⟩ : Fin 2) = Real.exp z
    rw [IterExpChain_chainValues]; rfl
  rw [hy0]

/-- **Chain-2 reducibility witness.** `Chain2Reducible p g k`: `p` reduces to `g` in `k`
polynomial-multiplier reduce steps (plus any number of free eval-equal `congr` steps, e.g. trims). -/
inductive Chain2Reducible : MultiPoly 2 → MultiPoly 2 → Nat → Prop
  | refl (p : MultiPoly 2) : Chain2Reducible p p 0
  | reduce (p g : MultiPoly 2) (k : Nat) (c : Real)
      (h_next : Chain2Reducible (chain2Reduce c p) g k) : Chain2Reducible p g (k + 1)
  | congr (p p' g : MultiPoly 2) (k : Nat)
      (h_eval : ∀ z : Real, (chain2Fn p).eval z = (chain2Fn p').eval z)
      (h_next : Chain2Reducible p' g k) : Chain2Reducible p g k

/-- **The chain-2 zero-count bound.** If `p` reduces to `g` in `k` reduce steps and `g`'s zeros are
bounded by `N`, then `p`'s zeros are bounded by `N + k`. Each reduce step costs `+1` (Rolle, via the
polynomial-multiplier transfer); eval-equal `congr` steps are free. -/
theorem chain2_zero_count_bound (p g : MultiPoly 2) (k : Nat) (h : Chain2Reducible p g k)
    (a b : Real) (hab : a < b) (N : Nat)
    (hN_bound : ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn g).eval z = 0) → zeros.length ≤ N) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn p).eval z = 0) → zeros.length ≤ N + k := by
  induction h with
  | refl p =>
    intro zeros hnd hz
    have := hN_bound zeros hnd hz
    omega
  | reduce p g k c h_next ih =>
    intro zeros hnd hz
    have hcoh : (chain2Fn p).chain.IsCoherentOn a b := IterExpChain_isCoherentOn 2 a b
    have hstep := zero_count_polyMultReduce_transfer (chain2Fn p)
      (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p) c a b hab hcoh (N + k)
      (by
        intro zeros' hnd' hz'
        apply ih hN_bound zeros' hnd'
        intro z hzmem
        obtain ⟨haz, hzb, hval⟩ := hz' z hzmem
        refine ⟨haz, hzb, ?_⟩
        rw [chain2Fn_chain2Reduce_eval]
        exact hval)
    have := hstep zeros hnd hz
    omega
  | congr p p' g k h_eval h_next ih =>
    intro zeros hnd hz
    apply ih hN_bound zeros hnd
    intro z hzmem
    obtain ⟨haz, hzb, hval⟩ := hz z hzmem
    exact ⟨haz, hzb, by rw [← h_eval z]; exact hval⟩

end MachLib.ChainExp2Bound
