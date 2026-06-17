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

/-! ## Why the natural measure does NOT work — and what would

The natural candidate measure is `chainExpPolyAutoBound 1 ∘
multiPolyToChainExpPolyT 1`, which is the chain-level-1 auto-bound on
the y_0-decomposition of g. Concretely, for g = Σ p_k(x) · y_0^k (with
degreeY 0 = d), this is `(d+1) + Σ degreeUpper (polySimplify p_k)`.

Under this measure, **neither `coeffStep_le` nor `coeffStep_lt` holds**.
The obstruction is structural:

- `chainTotalDeriv SingleExpChain g` preserves `degreeY 0 g` (chain rule
  on `y_0' = y_0` keeps the y_0-power structure).
- `(k · y_0) · g = mul (mul (const k) (varY 0)) g` shifts every y_0-power
  up by 1, so `degreeY 0` increases by 1.
- Sum: `coeffStep(g, k)` has `degreeY 0 = degreeY 0 g + 1` for any `k`
  (including k = 0), because `yCoeffsAt` operates **purely syntactically**:
  `mul (const 0) X` is NOT folded to `const 0` by `multiPolyToChainExpPolyT`.

Concrete example: for `g = varY 0` (degreeY 0 = 1, measure = 2),
  `coeffStep(g, k) = varY 0 + k · (varY 0)^2`,
  which has `degreeY 0 = 2` and measure ≥ 3 — **strictly larger** than g.

### Three paths forward (each is genuine multi-session work)

1. **Algebraic normalization before measuring.** Define a `multiPolySimplify
   1 : MultiPoly 1 → MultiPoly 1` that folds `mul (const 0) X = const 0`,
   removes zero summands in `add`, etc. — analogous to the existing
   `polySimplify` for `Poly`. Measure becomes `chainExpPolyAutoBound 1 ∘
   multiPolyToChainExpPolyT 1 ∘ multiPolySimplify`. Then `scalarMul 0 t`
   simplifies to `const 0`, leaving only `chainTotalDeriv` contribution
   at k=0. Strict descent on `chainTotalDeriv` requires a lex measure
   (degreeY 0, degreeX of leadingCoeffY 0), not a single Nat.

2. **Lex measure encoded as Nat with bounded blow-up.** Encode
   `(degreeY 0, degreeX of leadingCoeffY 0)` as `degreeY 0 * BIG + degreeX
   leadingCoeffY` for sufficiently large BIG. Requires global bounds on
   `degreeX leadingCoeffY` for all polynomials reachable from initial g
   under the framework's reductions. Tractable for a SPECIFIC starting
   polynomial p but messy as a general structural measure.

3. **Redesign the framework structure.** Replace the strict-descent
   axioms with a different termination measure that captures the lex
   nature directly (e.g., `WellFoundedRelation` on T instead of a Nat
   measure, or product Nat measures). This is the cleanest mathematical
   approach but requires reworking the parametric main theorem's
   induction structure.

### What this commit ships

- `chainExp2InnerKhovanskiiExp` — the algebraic instance (operations +
  four eval-correctness axioms), now augmented with documentation of
  the measure obstruction.

- `chainExp2_bound_via_measured_axioms` — the chain-length-2 bound
  theorem, **parametric over the measure axioms as hypotheses**. Shows
  the framework consumes correctly: if you supply a measure satisfying
  the three axioms, `auto_bound_with_propagation_aux` ships the bound
  directly. Calling code would need to discharge the axioms via one of
  the three paths above.

The constructive chain-length-2 over IterExp 2 bound remains open
pending discharge of the measure axioms via one of the three paths. -/

end ChainExp2InstanceMod
end MachLib
