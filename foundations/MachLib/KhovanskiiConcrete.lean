import MachLib.IterExpDepthNExplicit
import MachLib.ChainExp2Bound
import MachLib.PfaffianGeneralBridge
import MachLib.PfaffianExpHard

/-!
# A concrete Khovanskii bound: `e^(e^x) − x·e^x` has at most 47 real zeros

The explicit-bound machinery (`chainN_khovanskii_bound_explicit`, ceiling `Ndep m D`) is stated for an
arbitrary chain-`(m+2)` polynomial. This file instantiates it at a **named transcendental function** to make
the headline tangible — and to back the "at most 47" figure with a machine-checked theorem rather than a
hand-evaluated recurrence.

The barrier is `eexpBarrier = y₁ − x·y₀`, which along the depth-2 tower (`y₀ = eˣ`, `y₁ = e^(eˣ)`) is exactly

  `e^(e^x) − x·e^x`.

It has x-degree 1 and each tower-degree 1, so the explicit ceiling is `Ndep 0 1`, which **computes to 47**
(`Ndep` is a genuine `#eval`-able `Nat` recurrence). Non-vanishing is witnessed at `x = 0`, where the value is
`e^(e^0) = e > 0` (`iterExp_pos`). Grounded in `rolle`; the bound is a literal, and `#print axioms` on the
result stays free of `sorryAx` / `zero_count_bound_classical`.
-/

namespace MachLib.KhovanskiiConcrete

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpDepthN
open MachLib.ChainExp2Bound
open MachLib.IterExpChainMod
open MachLib.PfaffianGeneralReduce

/-- The barrier `y₁ − x·y₀`; along the tower `y₀ = eˣ`, `y₁ = e^(eˣ)` this is `e^(e^x) − x·e^x`. -/
noncomputable def eexpBarrier : MultiPoly 2 :=
  MultiPoly.sub (MultiPoly.varY (⟨1, by omega⟩ : Fin 2))
    (MultiPoly.mul MultiPoly.varX (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))

/-- The barrier evaluated along the tower is the honest function `e^(e^x) − x·e^x`. -/
theorem eexpBarrier_eval (z : Real) :
    (chain2Fn eexpBarrier).eval z = Real.exp (Real.exp z) - z * Real.exp z := by
  rw [chain2Fn_eval]
  show MultiPoly.eval eexpBarrier z ((IterExpChain 2).chainValues z) = _
  unfold eexpBarrier
  rw [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_varX, MultiPoly.eval_varY,
      MultiPoly.eval_varY, IterExpChain_chainValues, IterExpChain_chainValues,
      iterExp_succ, iterExp_zero]

/-- **`e^(e^x) − x·e^x` has at most 47 real zeros on any interval `(a,b)` containing 0.** A machine-checked
instance of the explicit Khovanskii ceiling: the barrier is a degree-1 chain-2 polynomial, so its zero count
is `≤ Ndep 0 1 = 47`. The interval need only contain a non-vanishing point (`x = 0`, value `e > 0`). -/
theorem eexp_barrier_zero_count_le_47 (a b : Real) (hab : a < b) (ha : a < 0) (hb : 0 < b) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (chain2Fn eexpBarrier).eval z = 0) →
      zeros.length ≤ 47 := by
  -- non-vanishing witness at x = 0: e^(e^0) − 0·e^0 = e^(e^0) > 0
  have hne : ∃ z, a < z ∧ z < b ∧ (chain2Fn eexpBarrier).eval z ≠ 0 := by
    refine ⟨0, ha, hb, ?_⟩
    rw [eexpBarrier_eval]
    have h0 : Real.exp (Real.exp 0) - 0 * Real.exp 0 = Real.exp (Real.exp 0) := by mach_ring
    rw [h0]; exact ne_of_gt (Real.exp_pos _)
  have hbound := chainN_khovanskii_bound_explicit 0 eexpBarrier 1 a b hab (by decide) (by decide) hne
  intro zeros hnd hz
  have hle := hbound zeros hnd hz
  have h47 : Ndep 0 1 = 47 := by decide
  rw [h47] at hle; exact hle

/-! ## The mixed exp/log capstone, on a concrete function

The bound above is the pure-exponential (Rolle-only) explicit ceiling. The result the whole `exp_hard` arc
unlocked is broader — the **mixed** exp/log/reciprocal finiteness `eml_eval_boundedZeros_unconditional`. Here
it is on the fundamental exp-minus-log operation applied to `x`. -/

/-- `e^x − log x` as an `EMLTree`: the fundamental `eml` operation (`e^(·) − log(·)`) with both arguments `x`. -/
def emlBarrier : EMLTree := EMLTree.eml EMLTree.var EMLTree.var

/-- The tree evaluates to the honest function `e^x − log x`. -/
theorem emlBarrier_eval (z : Real) : emlBarrier.eval z = Real.exp z - Real.log z := rfl

/-- **`e^x − log x` has finitely many zeros on any interval in the positive reals** — a machine-checked
instance of the FULL mixed exp/log capstone (`eml_eval_boundedZeros_unconditional`, the result the `exp_hard`
closure unlocked). The interval must lie in `(0, ∞)` (so `log x` is defined and its argument stays positive)
and contain `1`, where the value is `e^1 − log 1 = e > 0`. Qualitative (a finite ceiling `K` exists), resting
on `rolle` plus the real-analyticity identity theorem — the honest footprint of the mixed case. -/
theorem eml_barrier_bounded_zeros (a b : Real) (hab : a < b)
    (ha : 0 < a) (h1a : a < 1) (h1b : 1 < b) :
    ∃ K : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ emlBarrier.eval z = 0) → zeros.length ≤ K := by
  refine eml_eval_boundedZeros_unconditional emlBarrier a b hab ?_ ?_
  · -- LogArgPosOn (eml var var) (Icc a b) : both sub-args trivial, and log-arg `x` > 0 on [a,b]
    refine ⟨trivial, trivial, ?_⟩
    intro x hx
    show (0 : Real) < x
    exact MachLib.Real.lt_of_lt_of_le ha hx.1
  · -- non-vanishing at x = 1: e^1 − log 1 = e^1 − 0 = e > 0
    refine ⟨1, h1a, h1b, ?_⟩
    rw [emlBarrier_eval]
    have h : Real.exp 1 - Real.log 1 = Real.exp 1 := by rw [MachLib.Real.log_one]; mach_ring
    rw [h]; exact ne_of_gt (Real.exp_pos 1)

end MachLib.KhovanskiiConcrete
