import MachLib.SingleExpKhovanskii

/-!
# MachLib.InnerKhovanskii — abstract inner-coefficient interface for Khovanskii

The existing `SingleExpKhovanskii` argument bounds the zero count of
`f(x) = Σ_k p_k(x) · exp(k · x)` where each `p_k : Poly`. The full
multi-chain Khovanskii closure (over `IterExpChain N` and similar
non-degenerate chains) requires the **same outer Rolle argument** but
with a richer inner type: instead of `Poly`, the coefficients become
themselves chain-functions of the form `MultiPoly N` evaluated against
lower chain values.

This module defines the **abstract interface** `InnerKhovanskii` that
captures everything the outer Rolle argument needs from the inner
coefficient type. Refactoring the existing SingleExp argument to take
an `InnerKhovanskii` parameter is the **only** clean way to lift the
bound to chain length N+1 without duplicating ~1000 lines of the
strict-descent + Rolle machinery per chain layer.

This file ships:
- The `InnerKhovanskii` structure (the abstract interface).
- A generic `evalAux` parametric over an `InnerKhovanskii`.
- Trivial algebraic eval lemmas (nil, cons).
- The `Poly` instance.

What's NOT in this file (subsequent commits):
- Generic `scaledReductionAux` + eval-combine identity.
- Generic strict-descent on the inner measure.
- The full parametric auto-bound theorem (the chunk that ports the
  existing `expPoly_auto_bound_with_propagation_aux`).

Zero Mathlib dependency. -/

namespace MachLib
namespace InnerKhovanskiiMod

open MachLib.Real
open MachLib.PolynomialEvidence (Poly)
open MachLib.PolynomialRootCount

/-! ## The InnerKhovanskii structure -/

/-- **The abstract inner-coefficient interface for the SingleExp-style
Khovanskii argument.** Captures the operations + correctness axioms
the outer Rolle argument needs from the inner type `T`.

Conceptually `T` is the type of "coefficients in front of `exp(k · x)`":
- For the SingleExp argument, `T = Poly`.
- For the chain-length-(N+1) argument, `T` is a richer type that
  records dependence on the chain values y_0, ..., y_{N-1}.

The structure bundles:
- The inner eval `eval : T → Real → Real`.
- The inner derivative `derivative : T → T` (total derivative w.r.t. x).
- The inner add `add : T → T → T` and inner mul `mul : T → T → T`.
- An inner-const embedding `const : Real → T` for representing the
  scalar `(k − c)` factor that appears in `scaledReductionAux`.
- Correctness lemmas: `eval_HasDerivAt`, `eval_add`, `eval_mul`,
  `eval_const`.

NOT bundled here (deferred to subsequent commits):
- The inner measure + descent axioms (need at the strict-descent stage).
- The inner length-1 zero-count bound (becomes the IH at the chain
  level; will be supplied as a separate axiom or argument). -/
structure InnerKhovanskii where
  /-- The carrier type for inner coefficients. -/
  T : Type
  /-- Eval an inner coefficient at a real point. -/
  eval : T → Real → Real
  /-- Total derivative w.r.t. x. -/
  derivative : T → T
  /-- Inner sum. -/
  add : T → T → T
  /-- Inner product. -/
  mul : T → T → T
  /-- Embed a real constant as an inner coefficient. -/
  const : Real → T
  /-- The inner eval has the inner derivative as its `HasDerivAt`. -/
  eval_HasDerivAt : ∀ t : T, ∀ x : Real,
    HasDerivAt (eval t) (eval (derivative t) x) x
  /-- The inner add evaluates as addition. -/
  eval_add : ∀ t1 t2 : T, ∀ x : Real,
    eval (add t1 t2) x = eval t1 x + eval t2 x
  /-- The inner mul evaluates as multiplication. -/
  eval_mul : ∀ t1 t2 : T, ∀ x : Real,
    eval (mul t1 t2) x = eval t1 x * eval t2 x
  /-- The inner const evaluates to its underlying real. -/
  eval_const : ∀ c : Real, ∀ x : Real,
    eval (const c) x = c

/-! ## Generic evalAux

Generic `evalAux` parametric over an `InnerKhovanskii`. Mirrors
`MachLib.SingleExpKhovanskii.ExpPoly.evalAux` but with the inner type
abstract. -/

namespace InnerKhovanskii

/-- Generic eval-with-offset: `evalAux IK [t_0, ..., t_n] o x =
Σ_k IK.eval t_k x · exp((o + k) · x)`. -/
noncomputable def evalAux (IK : InnerKhovanskii) :
    List IK.T → Nat → Real → Real
  | [],         _, _ => 0
  | t :: rest,  o, x =>
      IK.eval t x * Real.exp ((natCast o) * x) + evalAux IK rest (o + 1) x

theorem evalAux_nil (IK : InnerKhovanskii) (o : Nat) (x : Real) :
    evalAux IK [] o x = 0 := rfl

theorem evalAux_cons (IK : InnerKhovanskii) (t : IK.T)
    (rest : List IK.T) (o : Nat) (x : Real) :
    evalAux IK (t :: rest) o x =
    IK.eval t x * Real.exp ((natCast o) * x) +
    evalAux IK rest (o + 1) x := rfl

/-! ## Generic scaledReductionAux

Mirrors `SingleExpKhovanskii.ExpPoly.scaledReductionAux`: for each
coefficient at offset `o`, transform
`t ↦ derivative t + (o − c) · t` via the inner operations. -/

/-- Generic scaledReductionAux: per-coefficient transformation
`t ↦ IK.add (IK.derivative t) (IK.mul (IK.const ((natCast o) − c)) t)`. -/
noncomputable def scaledReductionAux (IK : InnerKhovanskii)
    (c : Real) : List IK.T → Nat → List IK.T
  | [],         _ => []
  | t :: rest,  o =>
      IK.add (IK.derivative t)
              (IK.mul (IK.const ((natCast o) - c)) t)
      :: scaledReductionAux IK c rest (o + 1)

theorem scaledReductionAux_nil (IK : InnerKhovanskii) (c : Real) (o : Nat) :
    scaledReductionAux IK c [] o = [] := rfl

theorem scaledReductionAux_cons (IK : InnerKhovanskii) (c : Real)
    (t : IK.T) (rest : List IK.T) (o : Nat) :
    scaledReductionAux IK c (t :: rest) o =
    IK.add (IK.derivative t)
            (IK.mul (IK.const ((natCast o) - c)) t)
    :: scaledReductionAux IK c rest (o + 1) := rfl

/-- The length of `scaledReductionAux` matches the input list. -/
theorem length_scaledReductionAux (IK : InnerKhovanskii) (c : Real) :
    ∀ (coeffs : List IK.T) (o : Nat),
    (scaledReductionAux IK c coeffs o).length = coeffs.length := by
  intro coeffs
  induction coeffs with
  | nil => intro _; rfl
  | cons t rest ih =>
    intro o
    show (IK.add (IK.derivative t)
                  (IK.mul (IK.const ((natCast o) - c)) t)
          :: scaledReductionAux IK c rest (o + 1)).length
       = (t :: rest).length
    rw [List.length_cons, List.length_cons, ih (o + 1)]

end InnerKhovanskii

/-! ## The Poly instance

The existing `SingleExpKhovanskii` argument uses `Poly` as the inner
type; we package it as an `InnerKhovanskii`. This unifies the existing
machinery under the abstract interface. -/

/-- The `Poly` instance of `InnerKhovanskii`: uses `Poly.eval`,
`polyDerivative`, `Poly.add`, `Poly.mul`, `Poly.const`. -/
noncomputable def polyInnerKhovanskii : InnerKhovanskii where
  T := Poly
  eval := Poly.eval
  derivative := polyDerivative
  add := Poly.add
  mul := Poly.mul
  const := Poly.const
  eval_HasDerivAt := polyHasDerivAt_eval
  eval_add := fun _ _ _ => rfl
  eval_mul := fun _ _ _ => rfl
  eval_const := fun _ _ => rfl

theorem polyInnerKhovanskii_T :
    polyInnerKhovanskii.T = Poly := rfl

theorem polyInnerKhovanskii_eval (p : Poly) (x : Real) :
    polyInnerKhovanskii.eval p x = Poly.eval p x := rfl

theorem polyInnerKhovanskii_derivative (p : Poly) :
    polyInnerKhovanskii.derivative p = polyDerivative p := rfl

/-! ## Generic-eval equivalence with the existing SingleExp `evalAux`

When `IK = polyInnerKhovanskii`, the generic `evalAux` matches the
existing `SingleExpKhovanskii.ExpPoly.evalAux`. This is the bridge that
lets the future parametric theorem subsume the existing one. -/

theorem polyEvalAux_eq_evalAux :
    ∀ (coeffs : List Poly) (o : Nat) (x : Real),
    InnerKhovanskii.evalAux polyInnerKhovanskii coeffs o x =
    MachLib.SingleExpKhovanskii.ExpPoly.evalAux coeffs o x := by
  intro coeffs
  induction coeffs with
  | nil => intro _ _; rfl
  | cons p rest ih =>
    intro o x
    show Poly.eval p x * Real.exp ((natCast o) * x)
         + InnerKhovanskii.evalAux polyInnerKhovanskii rest (o + 1) x
       = Poly.eval p x * Real.exp ((natCast o) * x)
         + MachLib.SingleExpKhovanskii.ExpPoly.evalAux rest (o + 1) x
    rw [ih (o + 1) x]

theorem polyScaledReductionAux_eq_scaledReductionAux (c : Real) :
    ∀ (coeffs : List Poly) (o : Nat),
    InnerKhovanskii.scaledReductionAux polyInnerKhovanskii c coeffs o =
    MachLib.SingleExpKhovanskii.ExpPoly.scaledReductionAux c coeffs o := by
  intro coeffs
  induction coeffs with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro o
    show Poly.add (polyDerivative p)
                   (Poly.mul (Poly.const ((natCast o) - c)) p)
          :: InnerKhovanskii.scaledReductionAux polyInnerKhovanskii c rest (o + 1)
       = Poly.add (polyDerivative p)
                   (Poly.mul (Poly.const ((natCast o) - c)) p)
          :: MachLib.SingleExpKhovanskii.ExpPoly.scaledReductionAux c rest (o + 1)
    rw [ih (o + 1)]

end InnerKhovanskiiMod
end MachLib
