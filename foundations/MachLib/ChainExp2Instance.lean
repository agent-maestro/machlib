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

/-! ## Parameterized chain-length-2 bound

If a `measure : MultiPoly 1 → Nat` is supplied that satisfies the three
measured-side axioms (`length_one_bound`, `coeffStep_le`, `coeffStep_lt`)
for our operations, then the parametric `auto_bound_with_propagation_aux`
ships the chain-length-2 over IterExp 2 bound directly.

This corollary takes those axioms as **hypotheses** rather than proving
them — see the next section for why the natural candidate (the
chain-level-1 auto-bound) does NOT satisfy `coeffStep_le`. -/

open MachLib.InnerKhovanskiiExpMod
open InnerKhovanskiiExp

theorem chainExp2_bound_via_measured_axioms
    (measure : MultiPoly 1 → Nat)
    (length_one_bound : ∀ g : MultiPoly 1, ∀ a b : Real, a < b →
      (∃ x : Real, innerEval g x ≠ 0) →
      ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ innerEval g z = 0) →
      zeros.length ≤ measure g)
    (coeffStep_le : ∀ k : Real, ∀ g : MultiPoly 1,
      measure (innerAdd (innerDerivative g) (innerScalarMul k g)) ≤ measure g)
    (coeffStep_lt : ∀ g : MultiPoly 1, measure g > 0 →
      measure (innerAdd (innerDerivative g) (innerScalarMul 0 g)) < measure g)
    (M : Nat) (coeffs : List (MultiPoly 1))
    (hM : coeffs.length
            + InnerKhovanskiiExpMeasured.sumMeasure
                { toInnerKhovanskiiExp := chainExp2InnerKhovanskiiExp,
                  measure := measure,
                  length_one_bound := length_one_bound,
                  coeffStep_le := coeffStep_le,
                  coeffStep_lt := coeffStep_lt }
                coeffs ≤ M)
    (h_prop : ∀ coeffs' : List (MultiPoly 1),
       coeffs'.length
         + InnerKhovanskiiExpMeasured.sumMeasure
            { toInnerKhovanskiiExp := chainExp2InnerKhovanskiiExp,
              measure := measure,
              length_one_bound := length_one_bound,
              coeffStep_le := coeffStep_le,
              coeffStep_lt := coeffStep_lt }
            coeffs' ≤ M →
       (∃ x : Real, evalList chainExp2InnerKhovanskiiExp coeffs' x ≠ 0))
    (h_strict_last : ∀ coeffs' : List (MultiPoly 1),
       ∀ (hne_c : coeffs' ≠ []),
       coeffs'.length ≥ 2 →
       coeffs'.length
         + InnerKhovanskiiExpMeasured.sumMeasure
            { toInnerKhovanskiiExp := chainExp2InnerKhovanskiiExp,
              measure := measure,
              length_one_bound := length_one_bound,
              coeffStep_le := coeffStep_le,
              coeffStep_lt := coeffStep_lt }
            coeffs' ≤ M →
       measure (coeffs'.getLast hne_c) > 0)
    (a b : Real) (hab : a < b)
    (zeros : List Real) (hnodup : zeros.Nodup)
    (hzeros : ∀ z ∈ zeros, a < z ∧ z < b ∧
      evalList chainExp2InnerKhovanskiiExp coeffs z = 0) :
    zeros.length ≤ M :=
  InnerKhovanskiiExpMeasured.auto_bound_with_propagation_aux
    { toInnerKhovanskiiExp := chainExp2InnerKhovanskiiExp,
      measure := measure,
      length_one_bound := length_one_bound,
      coeffStep_le := coeffStep_le,
      coeffStep_lt := coeffStep_lt }
    M coeffs hM h_prop h_strict_last a b hab zeros hnodup hzeros

/-! ## Why ALL THREE candidate paths fall short — and what does work

After investigation, the three paths I sketched in an earlier commit
ALL hit the same fundamental obstruction. The framework's
`auto_bound_with_propagation_aux` requires a **Nat-valued measure** with
`coeffStep_le` (non-strict descent for arbitrary k) AND `coeffStep_lt`
(strict descent at k=0). For the chain-level-2 case, no Nat measure can
satisfy both simultaneously.

### Path (a): Algebraic normalization — does NOT close

Even using the existing `multiSimplify` (in MultiPoly.lean) which folds
`mul (const 0) X = const 0`, removes zero summands, etc:

- For k = 0: `scalarMul 0 g = mul (mul (const 0) (varY 0)) g`
  simplifies to `const 0`. Good. So
  `multiSimplify (coeffStep g 0) = multiSimplify (chainTotalDeriv g)`.

- For k ≠ 0: `scalarMul k g = mul (mul (const k) (varY 0)) g`
  does NOT simplify (k is non-zero). So `multiSimplify (coeffStep g k)`
  still contains the y_0-multiplied term and has degreeY 0 = degreeY 0 g
  + 1. Measure (any Nat function of degreeY 0) increases.

multiSimplify rescues k=0 but not general k. coeffStep_le fails.

### Path (b): Lex measure encoded as Nat — does NOT close

Encode `(degreeY 0 g, degreeX (leadingCoeffY 0 g))` as
`measure g = degreeY 0 g * BIG + degreeX (leadingCoeffY 0 g)`
for BIG ≥ max-possible degreeX.

- `chainTotalDeriv g` preserves degreeY 0, drops degreeX of leading by 1
  → measure -= 1 (strict descent at k=0 ✓).

- `(k · y_0) · g` for k ≠ 0: degreeY 0 += 1 → measure += BIG.

So for k ≠ 0, measure(coeffStep g k) = measure(chainTotalDeriv g) +
  measure((k · y_0) · g) (roughly), which exceeds measure g by ≈ BIG.
coeffStep_le fails by a margin of BIG.

The fundamental issue: lex (a, b) encoded as a · BIG + b INCREASES by
BIG when a increases by 1. Any Nat encoding of lex has the same problem.

### Path (c): Framework redesign — open

Replace `measure : T → Nat` with a `WellFoundedRelation T` or product
Nat measure. The induction in `auto_bound_with_propagation_aux` becomes
well-founded induction on T. This captures the lex descent structurally.

This is genuine framework redesign: ~300+ lines reworking the parametric
main theorem's induction, plus a new `auto_bound_with_propagation_aux`
that operates on the well-founded structure. It's the cleanest
mathematical path but takes a separate dedicated session.

### The STRUCTURAL diagnosis

The SingleExp framework's strict-descent argument relies on
`scalarMul k t` being **measure-preserving** for arbitrary k (only
strict at k=0 via the derivative). For SingleExp this holds because
scalarMul is multiplication by a Real constant.

For chain-level extension, scalarMul must multiply by `h_deriv(x)` (a
chain function, not a constant). For `h_deriv = exp = y_0`, this is
multiplication by a chain variable, which structurally raises
degreeY 0. Any Nat measure that captures enough to give strict descent
on the derivative will INCREASE under this y_0 multiplication.

The framework as designed cannot fit chain-level-2 without redesign.

### What this commit ships

- `chainExp2InnerKhovanskiiExp` — the algebraic instance (operations +
  four eval-correctness axioms). Confirmed working: the algebraic
  layer compiles, eval correctness holds, the Rolle vehicle
  (`mulNegExpH`) and `zero_count_scaledReduction_transfer` work
  directly on this instance.

- `chainExp2_bound_via_measured_axioms` — the chain-length-2 bound
  theorem, **parametric over the measure axioms as hypotheses**. Shows
  the framework consumes correctly: if a measure satisfying the three
  axioms ever exists for our operations, `auto_bound_with_propagation_aux`
  ships the bound. As established above, NO Nat-valued measure can
  satisfy the axioms for our `scalarMul = mul (varY 0)` — so this
  parametric theorem is honest scaffolding, NOT a constructive bound.

### What remains open

The constructive chain-length-2 over IterExp 2 bound. The path forward
is framework redesign (path c) — replacing the Nat-valued measure with
a well-founded structure that captures the lex descent without
penalizing y_0 multiplication. This is the next session's work, not
this session's. -/

end ChainExp2InstanceMod
end MachLib
