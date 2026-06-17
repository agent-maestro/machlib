import MachLib.InnerKhovanskiiExp
import MachLib.KhovanskiiReduction
import MachLib.ChainExpPoly

/-!
# MachLib.ChainExp2Instance — chain instance for IterExp 2

This file ships the `InnerKhovanskiiExp` instance that targets
**chain-length-2 Pfaffian functions over `IterExpChain 2`**:

    f(x) = p(x, y_0, y_1)    where y_0 = exp x, y_1 = exp(exp x).

Organized by powers of `y_1 = exp(y_0)`:

    f(x) = Σ_k g_k(x, y_0) · y_1^k = Σ_k g_k(x, y_0) · exp(k · y_0)

— i.e., `Σ_k T_k(x) · exp(k · h(x))` with:
- **Inner type** `T = MultiPoly 1` with chain `SingleExpChain`
  (chain value y_0 = exp x).
- **h(x) = exp x** — the function inside the outer exp factor.
- **h_deriv(x) = exp x** — its derivative (same as h, since
  `(exp x)' = exp x`).
- **scalarMul k g = mul (mul (const k) (varY 0)) g**, so
  `eval (scalarMul k g) x = k · exp(x) · eval g x = k · h_deriv(x) · eval g x`.

### What ships

- `chainExp2InnerKhovanskiiExp : InnerKhovanskiiExp` — the operations
  bundle plus the four eval-correctness axioms.

### What's NOT in this file

The **measured** extension `InnerKhovanskiiExpMeasured` requires a
`measure : MultiPoly 1 → Nat` with `coeffStep_le`, `coeffStep_lt`,
`length_one_bound`. The natural measure is `chainExpPolyAutoBound 1 ∘
multiPolyToChainExpPolyT 1`; the `length_one_bound` axiom would then
delegate to `MultiExp_zero_count_bound_one_explicit` (existing). The
`coeffStep_le` / `coeffStep_lt` axioms are non-trivial: they require
showing that the chain-level-1 auto-bound non-strictly descends under
`coeffStep g k = chainTotalDeriv g + (k · y_0) · g`, and strictly when
`k = 0`. This is genuine SingleExp-Khovanskii-inside-chain work and is
deferred to a follow-up.

The framework instance shipped here is therefore the **algebraic seam**:
the chain-level-2 operations are in scope, derivatives are eval-correct,
and the Rolle vehicle works — but the inductive bound requires the
measured-side axioms to be discharged. -/

namespace MachLib
namespace ChainExp2InstanceMod

open MachLib.Real
open MachLib.MultiPolyMod (MultiPoly)
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.InnerKhovanskiiExpMod (InnerKhovanskiiExp)

/-! ## Operations on T = MultiPoly 1 with SingleExpChain -/

/-- The inner eval: evaluate a `MultiPoly 1` at x with chain value
y_0 = exp x. -/
noncomputable def innerEval (g : MultiPoly 1) (x : Real) : Real :=
  MultiPoly.eval g x (SingleExpChain.chainValues x)

/-- The inner derivative: total derivative w.r.t. x via `chainTotalDeriv`
on `SingleExpChain`. -/
noncomputable def innerDerivative (g : MultiPoly 1) : MultiPoly 1 :=
  PfaffianFn.chainTotalDeriv SingleExpChain g

/-- The inner add: `MultiPoly.add`. -/
noncomputable def innerAdd (g1 g2 : MultiPoly 1) : MultiPoly 1 :=
  MultiPoly.add g1 g2

/-- The inner scalarMul: `mul (mul (const k) (varY 0)) g`. Eval picks
up the `h_deriv(x) = exp x = chainValues x 0` factor automatically. -/
noncomputable def innerScalarMul (k : Real) (g : MultiPoly 1) : MultiPoly 1 :=
  MultiPoly.mul (MultiPoly.mul (MultiPoly.const k) (MultiPoly.varY 0)) g

/-! ## Eval correctness for the four operations -/

theorem innerEval_HasDerivAt (g : MultiPoly 1) (x : Real) :
    HasDerivAt (innerEval g) (innerEval (innerDerivative g) x) x := by
  show HasDerivAt (fun y => MultiPoly.eval g y (SingleExpChain.chainValues y))
                  (MultiPoly.eval (PfaffianFn.chainTotalDeriv SingleExpChain g) x
                                  (SingleExpChain.chainValues x))
                  x
  exact multiPolyHasDerivAt_eval_with_chain SingleExpChain g x
          (SingleExpChain_isCoherentAt x)

theorem innerEval_add (g1 g2 : MultiPoly 1) (x : Real) :
    innerEval (innerAdd g1 g2) x = innerEval g1 x + innerEval g2 x := by
  show MultiPoly.eval (MultiPoly.add g1 g2) x (SingleExpChain.chainValues x)
       = MultiPoly.eval g1 x (SingleExpChain.chainValues x)
       + MultiPoly.eval g2 x (SingleExpChain.chainValues x)
  rfl

theorem innerEval_scalarMul (k : Real) (g : MultiPoly 1) (x : Real) :
    innerEval (innerScalarMul k g) x = k * Real.exp x * innerEval g x := by
  show MultiPoly.eval
         (MultiPoly.mul (MultiPoly.mul (MultiPoly.const k) (MultiPoly.varY 0)) g)
         x (SingleExpChain.chainValues x)
       = k * Real.exp x
         * MultiPoly.eval g x (SingleExpChain.chainValues x)
  -- LHS unfolds: eval (mul A g) = eval A * eval g, where A = mul (const k) (varY 0).
  -- eval A = eval (const k) * eval (varY 0) = k * (chainValues x 0) = k * exp x.
  show (k * SingleExpChain.chainValues x 0)
        * MultiPoly.eval g x (SingleExpChain.chainValues x)
       = k * Real.exp x
         * MultiPoly.eval g x (SingleExpChain.chainValues x)
  -- SingleExpChain.chainValues x 0 = exp x.
  rfl

/-! ## The InnerKhovanskiiExp instance -/

/-- **The chain-length-2 InnerKhovanskiiExp instance.** Sets
`h = exp`, `h_deriv = exp` (since `(exp x)' = exp x`), with inner type
`MultiPoly 1` evaluated against `SingleExpChain`. -/
noncomputable def chainExp2InnerKhovanskiiExp : InnerKhovanskiiExp where
  T := MultiPoly 1
  eval := innerEval
  derivative := innerDerivative
  add := innerAdd
  scalarMul := innerScalarMul
  h := Real.exp
  h_deriv := Real.exp
  eval_HasDerivAt := innerEval_HasDerivAt
  eval_add := innerEval_add
  eval_scalarMul := innerEval_scalarMul
  h_HasDerivAt := HasDerivAt_exp

theorem chainExp2_T :
    chainExp2InnerKhovanskiiExp.T = MultiPoly 1 := rfl

theorem chainExp2_h (x : Real) :
    chainExp2InnerKhovanskiiExp.h x = Real.exp x := rfl

theorem chainExp2_h_deriv (x : Real) :
    chainExp2InnerKhovanskiiExp.h_deriv x = Real.exp x := rfl

theorem chainExp2_eval (g : MultiPoly 1) (x : Real) :
    chainExp2InnerKhovanskiiExp.eval g x =
    MultiPoly.eval g x (SingleExpChain.chainValues x) := rfl

theorem chainExp2_derivative (g : MultiPoly 1) :
    chainExp2InnerKhovanskiiExp.derivative g =
    PfaffianFn.chainTotalDeriv SingleExpChain g := rfl

/-! ## Summary

`chainExp2InnerKhovanskiiExp` is the structural commitment: any
chain-length-2 Pfaffian function over `IterExpChain 2`, organized by
powers of `y_1 = exp(y_0)`, can be expressed as

    evalList chainExp2InnerKhovanskiiExp [g_0, g_1, ..., g_d] x

where each `g_k : MultiPoly 1` is the y_1^k coefficient. The framework's
algebraic machinery — `hasDerivAt_evalAux`, `scaledReductionAux`,
`scaledReductionAux_eval_combine`, the Rolle vehicle `mulNegExpH`, and
`zero_count_scaledReduction_transfer` — is all available on this instance.

Closing the constructive chain-length-2 Khovanskii bound requires
discharging the measured-side axioms (`length_one_bound`, `coeffStep_le`,
`coeffStep_lt`) for `T = MultiPoly 1`. The natural measure is the
chain-level-1 auto-bound `chainExpPolyAutoBound 1 ∘ multiPolyToChainExpPolyT
1`; verifying that this measure descends under `coeffStep g k =
chainTotalDeriv g + (k · y_0) · g` is the remaining substrate work. -/

end ChainExp2InstanceMod
end MachLib
