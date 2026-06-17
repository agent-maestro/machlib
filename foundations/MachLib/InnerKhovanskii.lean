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

/-! ## Generic top-level eval

The generic `evalList` wraps `evalAux` at offset 0, matching the
`ExpPoly.eval` convention. Named `evalList` (not `eval`) to avoid clashing
with the inner `IK.eval` field projection on `IK.T`. -/

namespace InnerKhovanskii

/-- Generic top-level eval: `evalList IK coeffs x = evalAux IK coeffs 0 x`. -/
noncomputable def evalList (IK : InnerKhovanskii) (coeffs : List IK.T)
    (x : Real) : Real :=
  evalAux IK coeffs 0 x

theorem evalList_def (IK : InnerKhovanskii) (coeffs : List IK.T) (x : Real) :
    evalList IK coeffs x = evalAux IK coeffs 0 x := rfl

/-- Length-1 ExpPoly eval reduces to the inner eval (since `exp(0 · x) = 1`). -/
theorem evalList_singleton (IK : InnerKhovanskii) (t : IK.T) (x : Real) :
    evalList IK [t] x = IK.eval t x := by
  show IK.eval t x * Real.exp ((natCast 0) * x)
       + evalAux IK [] (0 + 1) x = IK.eval t x
  show IK.eval t x * Real.exp ((natCast 0) * x) + 0 = IK.eval t x
  rw [show (natCast 0 : Real) = 0 from natCast_zero]
  rw [zero_mul, MachLib.Real.exp_zero, mul_one_ax, add_zero]

/-! ## Generic HasDerivAt for evalAux

`(evalAux IK coeffs o)' x = evalAux IK (scaledReductionAux IK 0 coeffs o) o x`.
This is the parametric port of `SingleExpKhovanskii.hasDerivAt_evalAux`. -/

theorem hasDerivAt_evalAux (IK : InnerKhovanskii) :
    ∀ (coeffs : List IK.T) (o : Nat) (x : Real),
    HasDerivAt (fun y => evalAux IK coeffs o y)
               (evalAux IK (scaledReductionAux IK 0 coeffs o) o x)
               x := by
  intro coeffs
  induction coeffs with
  | nil =>
    intro o x
    show HasDerivAt (fun _ => (0 : Real)) 0 x
    exact HasDerivAt_const 0 x
  | cons t rest ih =>
    intro o x
    show HasDerivAt
          (fun y => IK.eval t y * Real.exp ((natCast o) * y) + evalAux IK rest (o + 1) y)
          (evalAux IK
            (IK.add (IK.derivative t)
                     (IK.mul (IK.const ((natCast o) - 0)) t)
             :: scaledReductionAux IK 0 rest (o + 1))
            o x)
          x
    have hp : HasDerivAt (IK.eval t) (IK.eval (IK.derivative t) x) x :=
      IK.eval_HasDerivAt t x
    have hlinear : HasDerivAt (fun y => (natCast o) * y) (natCast o) x := by
      have hid : HasDerivAt (fun y => y) 1 x := HasDerivAt_id x
      have hconst : HasDerivAt (fun _ : Real => (natCast o)) 0 x :=
        HasDerivAt_const _ x
      have hmul := HasDerivAt_mul (fun _ => (natCast o)) (fun y => y) 0 1 x hconst hid
      have : 0 * x + (natCast o) * 1 = (natCast o) := by
        rw [zero_mul, zero_add, mul_one_ax]
      rw [this] at hmul
      exact hmul
    have hexp_at : HasDerivAt Real.exp (Real.exp ((natCast o) * x)) ((natCast o) * x) :=
      HasDerivAt_exp _
    have hexp_comp := HasDerivAt_comp Real.exp (fun y => (natCast o) * y) (natCast o)
                        (Real.exp ((natCast o) * x)) x hlinear hexp_at
    have hterm := HasDerivAt_mul (IK.eval t) (fun y => Real.exp ((natCast o) * y))
                    (IK.eval (IK.derivative t) x)
                    (Real.exp ((natCast o) * x) * (natCast o)) x hp hexp_comp
    have hsum := HasDerivAt_add (fun y => IK.eval t y * Real.exp ((natCast o) * y))
                   (fun y => evalAux IK rest (o + 1) y)
                   (IK.eval (IK.derivative t) x * Real.exp ((natCast o) * x)
                    + IK.eval t x * (Real.exp ((natCast o) * x) * (natCast o)))
                   (evalAux IK (scaledReductionAux IK 0 rest (o + 1)) (o + 1) x)
                   x hterm (ih (o + 1) x)
    show HasDerivAt _ _ x
    show HasDerivAt
          (fun y => IK.eval t y * Real.exp ((natCast o) * y) + evalAux IK rest (o + 1) y)
          (IK.eval (IK.add (IK.derivative t)
                            (IK.mul (IK.const ((natCast o) - 0)) t)) x
             * Real.exp ((natCast o) * x)
           + evalAux IK (scaledReductionAux IK 0 rest (o + 1)) (o + 1) x)
          x
    -- Rewrite the inner eval via the axioms.
    rw [IK.eval_add, IK.eval_mul, IK.eval_const]
    -- Same ring rearrangement as the Poly case, using the existing helper.
    have hring :
      IK.eval (IK.derivative t) x * Real.exp ((natCast o) * x)
        + IK.eval t x * (Real.exp ((natCast o) * x) * (natCast o))
      = (IK.eval (IK.derivative t) x
          + ((natCast o) - 0) * IK.eval t x)
        * Real.exp ((natCast o) * x) := by
      rw [sub_zero]
      have e_comm := MachLib.SingleExpKhovanskii.ExpPoly.add_mul_local
                       (IK.eval (IK.derivative t) x)
                       ((natCast o) * IK.eval t x)
                       (Real.exp ((natCast o) * x))
      rw [e_comm]
      congr 1
      -- IK.eval t x * (Real.exp(...) * (natCast o)) = (natCast o) * IK.eval t x * Real.exp(...)
      rw [show IK.eval t x * (Real.exp ((natCast o) * x) * (natCast o))
          = (natCast o) * IK.eval t x * Real.exp ((natCast o) * x) from by
        rw [mul_assoc (natCast o) (IK.eval t x) (Real.exp _)]
        rw [show (IK.eval t x) * (Real.exp ((natCast o) * x) * (natCast o))
              = (natCast o) * (IK.eval t x * Real.exp ((natCast o) * x)) from by
          rw [mul_comm (Real.exp _) (natCast o)]
          rw [← mul_assoc]
          rw [mul_comm (IK.eval t x) (natCast o)]
          rw [mul_assoc]]]
    rw [hring] at hsum
    exact hsum

/-! ## Generic scaledReduction_eval_combine

`evalAux IK (scaledReductionAux IK 0 coeffs o) o x + evalAux IK coeffs o x · (-c)
  = evalAux IK (scaledReductionAux IK c coeffs o) o x`.

This is the parametric port of `scaledReduction_eval_combine`. Reuses
`expPoly_step_ring_identity` (a pure Real identity, not Poly-specific). -/

theorem scaledReductionAux_eval_combine (IK : InnerKhovanskii) (c : Real) (x : Real) :
    ∀ (coeffs : List IK.T) (o : Nat),
    evalAux IK (scaledReductionAux IK 0 coeffs o) o x
      + evalAux IK coeffs o x * (-c)
    = evalAux IK (scaledReductionAux IK c coeffs o) o x := by
  intro coeffs
  induction coeffs with
  | nil =>
    intro o
    show (0 : Real) + 0 * (-c) = 0
    rw [zero_mul, zero_add]
  | cons t rest ih =>
    intro o
    have hih := ih (o + 1)
    show (IK.eval (IK.add (IK.derivative t)
                           (IK.mul (IK.const ((natCast o) - 0)) t)) x
            * Real.exp (natCast o * x)
          + evalAux IK (scaledReductionAux IK 0 rest (o + 1)) (o + 1) x)
         + (IK.eval t x * Real.exp (natCast o * x)
            + evalAux IK rest (o + 1) x) * (-c)
       = IK.eval (IK.add (IK.derivative t)
                          (IK.mul (IK.const ((natCast o) - c)) t)) x
            * Real.exp (natCast o * x)
         + evalAux IK (scaledReductionAux IK c rest (o + 1)) (o + 1) x
    rw [← hih]
    rw [IK.eval_add, IK.eval_mul, IK.eval_const]
    rw [IK.eval_add, IK.eval_mul, IK.eval_const]
    exact MachLib.SingleExpKhovanskii.ExpPoly.expPoly_step_ring_identity
            (IK.eval (IK.derivative t) x) (natCast o) (IK.eval t x)
            (Real.exp (natCast o * x))
            (evalAux IK (scaledReductionAux IK 0 rest (o + 1)) (o + 1) x)
            (evalAux IK rest (o + 1) x) c

/-! ## Generic Rolle vehicle and zero-count transfer

`mulNegExpX IK coeffs c x = (evalList IK coeffs x) · exp(-c · x)`. Same zero set
as `evalList IK coeffs`, with HasDerivAt computable via the parametric pieces.

Used as the Rolle vehicle in the parametric transfer theorem. -/

/-- The Rolle vehicle for the parametric SingleExp argument. -/
noncomputable def mulNegExpX (IK : InnerKhovanskii) (coeffs : List IK.T)
    (c : Real) : Real → Real :=
  fun x => evalList IK coeffs x * Real.exp (-c * x)

theorem mulNegExpX_zero_iff (IK : InnerKhovanskii) (coeffs : List IK.T)
    (c x : Real) :
    mulNegExpX IK coeffs c x = 0 ↔ evalList IK coeffs x = 0 := by
  show evalList IK coeffs x * Real.exp (-c * x) = 0 ↔ evalList IK coeffs x = 0
  constructor
  · intro h
    have hexp_ne : Real.exp (-c * x) ≠ 0 := exp_ne_zero _
    rw [mul_comm] at h
    exact MachLib.SingleExpKhovanskii.ExpPoly.mul_eq_zero_of_factor_ne_zero_local
            hexp_ne h
  · intro h
    rw [h, zero_mul]

/-- HasDerivAt for the parametric Rolle vehicle. Same shape as
`hasDerivAt_mulNegExpX_raw` but parametric over IK. -/
theorem hasDerivAt_mulNegExpX_raw (IK : InnerKhovanskii) (coeffs : List IK.T)
    (c x : Real) :
    HasDerivAt (mulNegExpX IK coeffs c)
               (evalAux IK (scaledReductionAux IK 0 coeffs 0) 0 x
                  * Real.exp (-c * x)
                + evalList IK coeffs x * (Real.exp (-c * x) * (-c)))
               x := by
  show HasDerivAt (fun y => evalList IK coeffs y * Real.exp (-c * y))
                  (evalAux IK (scaledReductionAux IK 0 coeffs 0) 0 x
                    * Real.exp (-c * x)
                   + evalList IK coeffs x * (Real.exp (-c * x) * (-c))) x
  have hep : HasDerivAt (evalList IK coeffs)
              (evalAux IK (scaledReductionAux IK 0 coeffs 0) 0 x) x :=
    hasDerivAt_evalAux IK coeffs 0 x
  have hlinear : HasDerivAt (fun y => -c * y) (-c) x := by
    have hid : HasDerivAt (fun y => y) 1 x := HasDerivAt_id x
    have hconst : HasDerivAt (fun _ : Real => -c) 0 x := HasDerivAt_const _ x
    have hmul := HasDerivAt_mul (fun _ => -c) (fun y => y) 0 1 x hconst hid
    have : 0 * x + (-c) * 1 = -c := by rw [zero_mul, zero_add, mul_one_ax]
    rw [this] at hmul
    exact hmul
  have hexp_at : HasDerivAt Real.exp (Real.exp (-c * x)) (-c * x) :=
    HasDerivAt_exp _
  have hexp_comp := HasDerivAt_comp Real.exp (fun y => -c * y) (-c)
                      (Real.exp (-c * x)) x hlinear hexp_at
  exact HasDerivAt_mul (evalList IK coeffs) (fun y => Real.exp (-c * y))
          (evalAux IK (scaledReductionAux IK 0 coeffs 0) 0 x)
          (Real.exp (-c * x) * (-c)) x hep hexp_comp

/-- If the Rolle vehicle has derivative 0 at z, the scaled-reduction at c
also evaluates to 0 at z. Combines `hasDerivAt_mulNegExpX_raw` +
`scaledReductionAux_eval_combine`. -/
theorem scaledReduction_eval_zero_of_aux_deriv_zero
    (IK : InnerKhovanskii) (coeffs : List IK.T) (c z : Real)
    (g'' : Real)
    (hg''_deriv : HasDerivAt (mulNegExpX IK coeffs c) g'' z)
    (hg''_zero : g'' = 0) :
    evalList IK (scaledReductionAux IK c coeffs 0) z = 0 := by
  have hcanonical := hasDerivAt_mulNegExpX_raw IK coeffs c z
  have huniq := HasDerivAt_unique (mulNegExpX IK coeffs c) g''
                  (evalAux IK (scaledReductionAux IK 0 coeffs 0) 0 z
                    * Real.exp (-c * z)
                   + evalList IK coeffs z * (Real.exp (-c * z) * (-c)))
                  z hg''_deriv hcanonical
  have hcan_zero :
      evalAux IK (scaledReductionAux IK 0 coeffs 0) 0 z * Real.exp (-c * z)
        + evalList IK coeffs z * (Real.exp (-c * z) * (-c)) = 0 := by
    rw [← huniq]; exact hg''_zero
  have hfact :
      evalAux IK (scaledReductionAux IK 0 coeffs 0) 0 z * Real.exp (-c * z)
        + evalList IK coeffs z * (Real.exp (-c * z) * (-c))
      = Real.exp (-c * z) * evalList IK (scaledReductionAux IK c coeffs 0) z := by
    rw [show evalList IK (scaledReductionAux IK c coeffs 0) z
          = evalAux IK (scaledReductionAux IK 0 coeffs 0) 0 z
            + evalList IK coeffs z * (-c) from
      (scaledReductionAux_eval_combine IK c z coeffs 0).symm]
    rw [show evalAux IK (scaledReductionAux IK 0 coeffs 0) 0 z * Real.exp (-c * z)
          = Real.exp (-c * z) * evalAux IK (scaledReductionAux IK 0 coeffs 0) 0 z from
      mul_comm _ _]
    rw [show evalList IK coeffs z * (Real.exp (-c * z) * (-c))
          = Real.exp (-c * z) * (evalList IK coeffs z * (-c)) from by
      rw [← mul_assoc, mul_comm (evalList IK coeffs z) (Real.exp _), mul_assoc]]
    rw [← mul_distrib]
  rw [hfact] at hcan_zero
  have hexp_ne : Real.exp (-c * z) ≠ 0 := exp_ne_zero _
  exact MachLib.SingleExpKhovanskii.ExpPoly.mul_eq_zero_of_factor_ne_zero_local
          hexp_ne hcan_zero

/-- **The parametric zero-count transfer (raw form)**: if the Rolle
vehicle's `HasDerivAt`-zero count is ≤ N, the original eval's zero count
is ≤ N + 1. -/
theorem zero_count_scaledReduction_transfer_raw
    (IK : InnerKhovanskii) (coeffs : List IK.T) (c a b : Real) (hab : a < b)
    (N : Nat)
    (h_reduced_bound : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          ∃ f'' : Real, HasDerivAt (mulNegExpX IK coeffs c) f'' z ∧ f'' = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ evalList IK coeffs z = 0) →
      zeros_f.length ≤ N + 1 := by
  intro zeros_f hnodup hzeros
  have hzeros_g : ∀ z ∈ zeros_f, a < z ∧ z < b ∧ mulNegExpX IK coeffs c z = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hfz⟩ := hzeros z hz
    refine ⟨haz, hzb, ?_⟩
    exact (mulNegExpX_zero_iff IK coeffs c z).mpr hfz
  have hdiff : ∀ x : Real, a < x → x < b →
                ∃ f' : Real, HasDerivAt (mulNegExpX IK coeffs c) f' x := by
    intro x _ _
    refine ⟨_, hasDerivAt_mulNegExpX_raw IK coeffs c x⟩
  exact zero_count_bound_by_deriv (mulNegExpX IK coeffs c) a b hab hdiff N
          h_reduced_bound zeros_f hnodup hzeros_g

/-- **The parametric zero-count transfer**: if the scaled reduction's
eval-zero count is ≤ N, the original eval's zero count is ≤ N + 1. -/
theorem zero_count_scaledReduction_transfer
    (IK : InnerKhovanskii) (coeffs : List IK.T) (c a b : Real) (hab : a < b)
    (N : Nat)
    (h_red_bound_eval : ∀ zeros' : List Real,
        zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          evalList IK (scaledReductionAux IK c coeffs 0) z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real,
      zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ evalList IK coeffs z = 0) →
      zeros_f.length ≤ N + 1 := by
  apply zero_count_scaledReduction_transfer_raw IK coeffs c a b hab N
  intro zeros' hnodup' hzeros'_prop
  apply h_red_bound_eval zeros' hnodup'
  intro z hz
  obtain ⟨haz, hzb, g'', hg''_deriv, hg''_zero⟩ := hzeros'_prop z hz
  refine ⟨haz, hzb, ?_⟩
  exact scaledReduction_eval_zero_of_aux_deriv_zero IK coeffs c z g''
          hg''_deriv hg''_zero

end InnerKhovanskii

/-! ## Measured inner-Khovanskii: adds measure + length-1 + descent

`InnerKhovanskiiMeasured` extends `InnerKhovanskii` with:
- `measure : T → Nat`: the per-coefficient inner measure.
- `length_one_bound`: for length-1 ExpPoly `[t]` with a non-zero
  witness, zero count ≤ `measure t`.
- `coeffStep_le`: `measure (add (derivative t) (mul (const k) t)) ≤ measure t`.
- `coeffStep_lt`: when `k = 0` and `measure t > 0`, strict descent.

These are exactly the inner-side axioms the SingleExp argument needs
beyond the algebraic interface. Discharged for `Poly` via existing
results in `SingleExpKhovanskii`. -/

structure InnerKhovanskiiMeasured extends InnerKhovanskii where
  /-- The per-coefficient inner measure. -/
  measure : T → Nat
  /-- Length-1 base case: zero count of `eval t` is bounded by `measure t`. -/
  length_one_bound : ∀ t : T, ∀ a b : Real, a < b →
    (∃ x : Real, eval t x ≠ 0) →
    ∀ zeros : List Real, zeros.Nodup →
    (∀ z ∈ zeros, a < z ∧ z < b ∧ eval t z = 0) →
    zeros.length ≤ measure t
  /-- Non-strict descent: the coeffStep doesn't increase the measure. -/
  coeffStep_le : ∀ k : Real, ∀ t : T,
    measure (add (derivative t) (mul (const k) t)) ≤ measure t
  /-- Strict descent at `k = 0`: the derivative measure-strictly
  decreases when the input has positive measure. -/
  coeffStep_lt : ∀ t : T, measure t > 0 →
    measure (add (derivative t) (mul (const 0) t)) < measure t

namespace InnerKhovanskiiMeasured

open InnerKhovanskii

/-- The sum of inner measures across a coefficient list. -/
noncomputable def sumMeasure (IKM : InnerKhovanskiiMeasured) :
    List IKM.T → Nat
  | []        => 0
  | t :: rest => IKM.measure t + sumMeasure IKM rest

theorem sumMeasure_nil (IKM : InnerKhovanskiiMeasured) :
    sumMeasure IKM [] = 0 := rfl

theorem sumMeasure_cons (IKM : InnerKhovanskiiMeasured) (t : IKM.T)
    (rest : List IKM.T) :
    sumMeasure IKM (t :: rest) = IKM.measure t + sumMeasure IKM rest := rfl

/-- **Non-strict descent**: `sumMeasure (scaledReductionAux c coeffs offset)
≤ sumMeasure coeffs`. Each per-coefficient transform decreases (non-strictly)
via `coeffStep_le`. -/
theorem sumMeasure_scaledReductionAux_le (IKM : InnerKhovanskiiMeasured)
    (c : Real) :
    ∀ (coeffs : List IKM.T) (offset : Nat),
    sumMeasure IKM (scaledReductionAux IKM.toInnerKhovanskii c coeffs offset)
      ≤ sumMeasure IKM coeffs := by
  intro coeffs
  induction coeffs with
  | nil => intro _; exact Nat.le_refl _
  | cons head tail ih =>
    intro offset
    show sumMeasure IKM
          (IKM.add (IKM.derivative head)
                    (IKM.mul (IKM.const ((natCast offset) - c)) head)
           :: scaledReductionAux IKM.toInnerKhovanskii c tail (offset + 1))
       ≤ sumMeasure IKM (head :: tail)
    rw [sumMeasure_cons, sumMeasure_cons]
    have h1 := IKM.coeffStep_le ((natCast offset) - c) head
    have h2 := ih (offset + 1)
    omega

/-- **Strict descent at the LAST coefficient**: with `c = natCast (offset
+ coeffs.length − 1)`, the last coefficient hits `coeffStep_lt` (since
`(natCast offset_last) − c = 0`), so the total measure strictly decreases
when the last coefficient has positive measure. -/
theorem sumMeasure_scaledReductionAux_lt (IKM : InnerKhovanskiiMeasured) :
    ∀ (coeffs : List IKM.T) (offset : Nat) (hne : coeffs ≠ []),
    IKM.measure (coeffs.getLast hne) > 0 →
    sumMeasure IKM
      (scaledReductionAux IKM.toInnerKhovanskii
        (natCast (offset + coeffs.length - 1)) coeffs offset)
      < sumMeasure IKM coeffs := by
  intro coeffs
  induction coeffs with
  | nil => intros _ hne; exact absurd rfl hne
  | cons head tail ih =>
    intros offset _ hlast_pos
    by_cases htail : tail = []
    · -- coeffs = [head]; head IS last.
      subst htail
      have hoff : offset + 1 - 1 = offset := by omega
      have hlast_pos' : IKM.measure head > 0 := hlast_pos
      have hstrict := IKM.coeffStep_lt head hlast_pos'
      show sumMeasure IKM
            (IKM.add (IKM.derivative head)
                     (IKM.mul (IKM.const ((natCast offset : Real) -
                                            (natCast (offset + 1 - 1)))) head)
             :: scaledReductionAux IKM.toInnerKhovanskii
                  (natCast (offset + 1 - 1)) [] (offset + 1))
          < sumMeasure IKM [head]
      rw [hoff]
      have hsub : (natCast offset : Real) - natCast offset = 0 := sub_self _
      rw [hsub]
      -- scaledReductionAux _ _ [] _ = []; sumMeasure [] = 0.
      show IKM.measure (IKM.add (IKM.derivative head)
                                (IKM.mul (IKM.const 0) head))
           + sumMeasure IKM ([] : List IKM.T)
         < IKM.measure head + sumMeasure IKM ([] : List IKM.T)
      rw [sumMeasure_nil]
      omega
    · -- Length ≥ 2: head NOT last; use non-strict for head, IH for tail.
      have htail_ne : tail ≠ [] := htail
      have hgetlast : (head :: tail).getLast (List.cons_ne_nil head tail)
                    = tail.getLast htail_ne := List.getLast_cons htail_ne
      have hlast_pos_tail : IKM.measure (tail.getLast htail_ne) > 0 := by
        rw [← hgetlast]
        exact hlast_pos
      have hlen : (head :: tail).length = tail.length + 1 := rfl
      have hoff_eq : offset + (tail.length + 1) - 1 = (offset + 1) + tail.length - 1 := by omega
      show sumMeasure IKM
            (scaledReductionAux IKM.toInnerKhovanskii
              (natCast (offset + (head :: tail).length - 1))
              (head :: tail) offset)
          < sumMeasure IKM (head :: tail)
      rw [hlen]
      show sumMeasure IKM
            (IKM.add (IKM.derivative head)
                     (IKM.mul (IKM.const ((natCast offset : Real) -
                                            (natCast (offset + (tail.length + 1) - 1)))) head)
             :: scaledReductionAux IKM.toInnerKhovanskii
                  (natCast (offset + (tail.length + 1) - 1)) tail (offset + 1))
          < sumMeasure IKM (head :: tail)
      rw [hoff_eq]
      show IKM.measure (IKM.add (IKM.derivative head)
                                (IKM.mul (IKM.const ((natCast offset : Real)
                                  - (natCast ((offset + 1) + tail.length - 1))))
                                          head))
           + sumMeasure IKM
               (scaledReductionAux IKM.toInnerKhovanskii
                 (natCast ((offset + 1) + tail.length - 1)) tail (offset + 1))
         < IKM.measure head + sumMeasure IKM tail
      have h_head_le := IKM.coeffStep_le
                          ((natCast offset : Real) -
                           (natCast ((offset + 1) + tail.length - 1)))
                          head
      have h_tail_lt := ih (offset + 1) htail_ne hlast_pos_tail
      omega

/-! ## The parametric auto-bound (main theorem)

This is the **port of `expPoly_auto_bound_with_propagation_aux`** to the
parametric interface. Same proof skeleton (strong induction on M),
same propagation/last-positive hypotheses — but with the inner type
abstract and all per-coefficient facts going through `IKM`'s axioms. -/

/-- **Parametric auto-bound with propagation**: takes a propagation
hypothesis `h_prop` (every smaller-measure list has a non-zero witness)
and a strict-last hypothesis `h_strict_last` (last coefficient has
positive inner measure when length ≥ 2). Returns the zero-count
bound in terms of the outer measure
`coeffs.length + sumMeasure IKM coeffs`. -/
theorem auto_bound_with_propagation_aux
    (IKM : InnerKhovanskiiMeasured) :
    ∀ (M : Nat) (coeffs : List IKM.T),
    coeffs.length + sumMeasure IKM coeffs ≤ M →
    (∀ coeffs' : List IKM.T,
       coeffs'.length + sumMeasure IKM coeffs' ≤ M →
       (∃ x, evalList IKM.toInnerKhovanskii coeffs' x ≠ 0)) →
    (∀ coeffs' : List IKM.T,
       ∀ (hne_c : coeffs' ≠ []),
       coeffs'.length ≥ 2 →
       coeffs'.length + sumMeasure IKM coeffs' ≤ M →
       IKM.measure (coeffs'.getLast hne_c) > 0) →
    ∀ (a b : Real), a < b →
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ evalList IKM.toInnerKhovanskii coeffs z = 0) →
      zeros.length ≤ M := by
  intro M
  induction M with
  | zero =>
    intro coeffs hM h_prop _h_strict_last a b _hab zeros _hnodup _hzeros
    have hne := h_prop coeffs hM
    have hlen : coeffs.length = 0 := by
      have h := Nat.zero_le (sumMeasure IKM coeffs)
      omega
    have hempty : coeffs = [] := List.length_eq_zero.mp hlen
    exfalso
    obtain ⟨x, hx⟩ := hne
    apply hx
    rw [hempty]
    show evalAux IKM.toInnerKhovanskii [] 0 x = 0
    rfl
  | succ M' ih =>
    intro coeffs hM h_prop h_strict_last a b hab zeros hnodup hzeros
    have hne := h_prop coeffs hM
    match h_coeffs : coeffs with
    | [] =>
      exfalso
      obtain ⟨x, hx⟩ := hne
      apply hx
      show evalAux IKM.toInnerKhovanskii [] 0 x = 0
      rfl
    | [t] =>
      have hne_t : ∃ x : Real, IKM.eval t x ≠ 0 := by
        obtain ⟨x, hx⟩ := hne
        refine ⟨x, ?_⟩
        rw [← evalList_singleton]
        exact hx
      have hzeros_t : ∀ z ∈ zeros, a < z ∧ z < b ∧ IKM.eval t z = 0 := by
        intro z hz
        obtain ⟨ha, hb', hev⟩ := hzeros z hz
        refine ⟨ha, hb', ?_⟩
        rw [← evalList_singleton]
        exact hev
      have hbnd := IKM.length_one_bound t a b hab hne_t zeros hnodup hzeros_t
      have h_sum_eq : sumMeasure IKM ([t] : List IKM.T) = IKM.measure t := by
        show IKM.measure t + sumMeasure IKM ([] : List IKM.T) = IKM.measure t
        rw [sumMeasure_nil]
        omega
      have h_len : ([t] : List IKM.T).length = 1 := rfl
      rw [h_sum_eq, h_len] at hM
      omega
    | t1 :: t2 :: rest =>
      -- Note: match has substituted `coeffs := t1 :: t2 :: rest` in scope.
      have hne_coeffs : (t1 :: t2 :: rest : List IKM.T) ≠ [] :=
        List.cons_ne_nil _ _
      have hlen_ge_2 : (t1 :: t2 :: rest : List IKM.T).length ≥ 2 := by simp
      have hlast_pos :
          IKM.measure ((t1 :: t2 :: rest : List IKM.T).getLast hne_coeffs) > 0 :=
        h_strict_last (t1 :: t2 :: rest) hne_coeffs hlen_ge_2 hM
      have h_strict := sumMeasure_scaledReductionAux_lt IKM
                         (t1 :: t2 :: rest) 0 hne_coeffs hlast_pos
      have h_offset_eq :
          (0 : Nat) + (t1 :: t2 :: rest : List IKM.T).length - 1
          = (t1 :: t2 :: rest : List IKM.T).length - 1 := by omega
      rw [h_offset_eq] at h_strict
      have h_aux_len :=
        length_scaledReductionAux IKM.toInnerKhovanskii
          (natCast ((t1 :: t2 :: rest : List IKM.T).length - 1))
          (t1 :: t2 :: rest) 0
      have h_measure :
          (scaledReductionAux IKM.toInnerKhovanskii
            (natCast ((t1 :: t2 :: rest : List IKM.T).length - 1))
            (t1 :: t2 :: rest) 0).length
            + sumMeasure IKM
                (scaledReductionAux IKM.toInnerKhovanskii
                  (natCast ((t1 :: t2 :: rest : List IKM.T).length - 1))
                  (t1 :: t2 :: rest) 0)
            ≤ M' := by
        rw [h_aux_len]
        omega
      have h_prop_red : ∀ coeffs' : List IKM.T,
                        coeffs'.length + sumMeasure IKM coeffs' ≤ M' →
                        (∃ x, evalList IKM.toInnerKhovanskii coeffs' x ≠ 0) := by
        intro coeffs' hcoeffs'
        exact h_prop coeffs' (by omega)
      have h_strict_last_red : ∀ coeffs' : List IKM.T,
                                ∀ (hne_c : coeffs' ≠ []),
                                coeffs'.length ≥ 2 →
                                coeffs'.length + sumMeasure IKM coeffs' ≤ M' →
                                IKM.measure (coeffs'.getLast hne_c) > 0 := by
        intro coeffs' hne_c hlen_ge hmeas
        exact h_strict_last coeffs' hne_c hlen_ge (by omega)
      have hred_bound := ih _ h_measure h_prop_red h_strict_last_red a b hab
      have h_transfer := zero_count_scaledReduction_transfer IKM.toInnerKhovanskii
                          (t1 :: t2 :: rest)
                          (natCast ((t1 :: t2 :: rest : List IKM.T).length - 1))
                          a b hab M' hred_bound
      have := h_transfer zeros hnodup hzeros
      omega

end InnerKhovanskiiMeasured

/-! ## The Poly measured-instance

Builds on `polyInnerKhovanskii` by adding `measure = degreeUpper ∘ polySimplify`
and discharging the three measure axioms via existing
`SingleExpKhovanskii` results. -/

open MachLib.SingleExpKhovanskii.ExpPoly (
  expPoly_zero_count_bound_length_one_simplified
  coeffStep_degreeUpper_polySimplify_le
  coeffStep_degreeUpper_polySimplify_lt
)

/-- The Poly measured-instance. `measure p = degreeUpper (polySimplify p)`. -/
noncomputable def polyInnerKhovanskiiMeasured : InnerKhovanskiiMeasured where
  toInnerKhovanskii := polyInnerKhovanskii
  measure := fun p => degreeUpper (polySimplify p)
  length_one_bound := fun p a b hab hne zeros hnodup hzeros => by
    -- The length-1 ExpPoly's eval = Poly.eval (via SingleExp eval_singleton).
    have hne' : ∃ x : Real, (⟨[p]⟩ : MachLib.SingleExpKhovanskii.ExpPoly).eval x ≠ 0 := by
      obtain ⟨x, hx⟩ := hne
      refine ⟨x, ?_⟩
      rw [MachLib.SingleExpKhovanskii.ExpPoly.eval_singleton]
      exact hx
    have hzeros' : ∀ z ∈ zeros, a < z ∧ z < b ∧
                    (⟨[p]⟩ : MachLib.SingleExpKhovanskii.ExpPoly).eval z = 0 := by
      intro z hz
      obtain ⟨ha, hb, hev⟩ := hzeros z hz
      refine ⟨ha, hb, ?_⟩
      rw [MachLib.SingleExpKhovanskii.ExpPoly.eval_singleton]
      exact hev
    exact expPoly_zero_count_bound_length_one_simplified p a b hab hne' zeros
            hnodup hzeros'
  coeffStep_le := fun k p => coeffStep_degreeUpper_polySimplify_le p k
  coeffStep_lt := fun p hpos => by
    have := coeffStep_degreeUpper_polySimplify_lt p hpos
    exact this

theorem polyInnerKhovanskiiMeasured_measure (p : Poly) :
    polyInnerKhovanskiiMeasured.measure p = degreeUpper (polySimplify p) := rfl

/-! ## Specialization back: parametric ⇒ existing Poly bound

The parametric `auto_bound_with_propagation_aux` instantiated at
`polyInnerKhovanskiiMeasured` recovers (essentially) the existing
`expPoly_auto_bound_with_propagation_aux`. -/

theorem auto_bound_specialized_to_poly
    (M : Nat) (ep : MachLib.SingleExpKhovanskii.ExpPoly)
    (hM : ep.coeffs.length +
            MachLib.SingleExpKhovanskii.ExpPoly.sumSimplifiedDegrees ep.coeffs ≤ M)
    (h_prop : ∀ ep' : MachLib.SingleExpKhovanskii.ExpPoly,
       ep'.coeffs.length +
         MachLib.SingleExpKhovanskii.ExpPoly.sumSimplifiedDegrees ep'.coeffs ≤ M →
       (∃ x, ep'.eval x ≠ 0))
    (h_strict_last : ∀ ep' : MachLib.SingleExpKhovanskii.ExpPoly,
       ∀ (hne_coeffs : ep'.coeffs ≠ []),
       ep'.coeffs.length ≥ 2 →
       ep'.coeffs.length +
         MachLib.SingleExpKhovanskii.ExpPoly.sumSimplifiedDegrees ep'.coeffs ≤ M →
       degreeUpper (polySimplify (ep'.coeffs.getLast hne_coeffs)) > 0)
    (a b : Real) (hab : a < b)
    (zeros : List Real) (hnodup : zeros.Nodup)
    (hzeros : ∀ z ∈ zeros, a < z ∧ z < b ∧ ep.eval z = 0) :
    zeros.length ≤ M := by
  -- Convert sumSimplifiedDegrees ⇔ sumMeasure on polyInnerKhovanskiiMeasured.
  have h_sum_eq : ∀ coeffs : List Poly,
      MachLib.SingleExpKhovanskii.ExpPoly.sumSimplifiedDegrees coeffs
      = InnerKhovanskiiMeasured.sumMeasure polyInnerKhovanskiiMeasured coeffs := by
    intro coeffs
    induction coeffs with
    | nil => rfl
    | cons p rest ih =>
      show degreeUpper (polySimplify p)
            + MachLib.SingleExpKhovanskii.ExpPoly.sumSimplifiedDegrees rest
          = degreeUpper (polySimplify p)
            + InnerKhovanskiiMeasured.sumMeasure polyInnerKhovanskiiMeasured rest
      rw [ih]
  -- Convert ExpPoly.eval ⇔ evalList polyInnerKhovanskii.
  have h_eval_eq : ∀ coeffs : List Poly, ∀ x : Real,
      (⟨coeffs⟩ : MachLib.SingleExpKhovanskii.ExpPoly).eval x
      = InnerKhovanskii.evalList polyInnerKhovanskii coeffs x := by
    intro coeffs x
    show MachLib.SingleExpKhovanskii.ExpPoly.evalAux coeffs 0 x
       = InnerKhovanskii.evalAux polyInnerKhovanskii coeffs 0 x
    exact (polyEvalAux_eq_evalAux coeffs 0 x).symm
  -- Repackage h_prop and h_strict_last to the parametric form.
  rw [h_sum_eq] at hM
  have h_prop' : ∀ coeffs' : List Poly,
      coeffs'.length + InnerKhovanskiiMeasured.sumMeasure polyInnerKhovanskiiMeasured coeffs' ≤ M →
      (∃ x, InnerKhovanskii.evalList polyInnerKhovanskii coeffs' x ≠ 0) := by
    intro coeffs' hcoeffs'
    have hsum := h_sum_eq coeffs'
    rw [← hsum] at hcoeffs'
    obtain ⟨x, hx⟩ := h_prop ⟨coeffs'⟩ hcoeffs'
    refine ⟨x, ?_⟩
    rw [← h_eval_eq]
    exact hx
  have h_strict_last' : ∀ coeffs' : List Poly,
      ∀ (hne_c : coeffs' ≠ []),
      coeffs'.length ≥ 2 →
      coeffs'.length + InnerKhovanskiiMeasured.sumMeasure polyInnerKhovanskiiMeasured coeffs' ≤ M →
      polyInnerKhovanskiiMeasured.measure (coeffs'.getLast hne_c) > 0 := by
    intro coeffs' hne_c hlen hmeas
    have hsum := h_sum_eq coeffs'
    rw [← hsum] at hmeas
    show degreeUpper (polySimplify (coeffs'.getLast hne_c)) > 0
    exact h_strict_last ⟨coeffs'⟩ hne_c hlen hmeas
  have hzeros' : ∀ z ∈ zeros, a < z ∧ z < b ∧
      InnerKhovanskii.evalList polyInnerKhovanskii ep.coeffs z = 0 := by
    intro z hz
    obtain ⟨ha, hb, hev⟩ := hzeros z hz
    refine ⟨ha, hb, ?_⟩
    rw [← h_eval_eq]
    exact hev
  exact InnerKhovanskiiMeasured.auto_bound_with_propagation_aux
          polyInnerKhovanskiiMeasured M ep.coeffs hM h_prop' h_strict_last'
          a b hab zeros hnodup hzeros'

end InnerKhovanskiiMod
end MachLib
