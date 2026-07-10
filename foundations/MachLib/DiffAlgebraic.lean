import MachLib.Differentiation
import MachLib.MultiPoly

/-!
# Differentially algebraic functions — the Tier-1 foundation for tower separation

This is the first brick of the differential-algebra layer that Hölder's theorem (Γ is
differentially TRANSCENDENTAL) will sit on top of. Once that layer + Hölder are in
place, Γ separates from the ENTIRE Pfaffian/EML tower in one stroke: every 23-operator
composition is differentially ALGEBRAIC (its Pfaffian chain relations ARE its algebraic
differential equations), so a differentially-transcendental function like Γ cannot be
one — the clean version of "no exp–log operator computes Γ".

## What "differentially algebraic" means

`f` is differentially algebraic if it satisfies a nontrivial ALGEBRAIC differential
equation: some nonzero polynomial `P` in `x` and the jet `(f, f', …, f⁽ⁿ⁾)` vanishes
identically. It is the differential analogue of "algebraic" (an integral polynomial
relation among a value and its derivatives, rather than among powers).

We reuse `MultiPoly (n+1)` (one `x`-variable `varX` + `n+1` jet-variables `varY i`)
for the differential polynomial, and express "P is not the zero polynomial" as
"P evaluates nonzero at some point" (a polynomial over the reals is not identically
zero iff it is the zero polynomial — the semantic form is the convenient one here).

## Status (this file)

- `IsDerivTower` / `IsDiffAlg` — the definitions.
- `exp_isDiffAlg` — **PROVED**: `exp` is differentially algebraic (order 1, the ODE
  `y₁ − y₀ = 0`, i.e. `exp' = exp`), from `HasDerivAt_exp`. Non-vacuity of the predicate.

## Next bricks (the Tier-1 program)

1. **The Pfaffian bridge** `IsExpChainFn f → IsDiffAlg f` (and more generally, every
   Pfaffian-chain function is diff-algebraic): a chain function `p(x, f₁,…,f_r)` and all
   its derivatives lie in `ℝ[x, f₁,…,f_r]` (transcendence degree ≤ r+1), so `r+2` of them
   are algebraically dependent — a nonzero differential polynomial. Needs a small
   transcendence-degree fact; the chain relations supply the ODEs directly.
2. **Hölder's theorem** `¬ IsDiffAlg Real.Gamma`: descent on the functional equation
   `Γ(x+1) = x·Γ(x)` (Mathlib-free restatement). Self-contained — no Picard–Vessiot.
3. **Separation**: `IsDiffAlg (EML tower) ∧ ¬ IsDiffAlg Γ ⟹ Γ ∉ tower`.
-/

namespace MachLib

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly

/-- `d` is a derivative tower for `f` of height `n`: `d 0 = f`, and each `d (i+1)` is the
derivative of `d i` at every point, for `i < n`. So `d i` is the `i`-th derivative of `f`. -/
def IsDerivTower (f : Real → Real) (d : Nat → Real → Real) (n : Nat) : Prop :=
  d 0 = f ∧ ∀ i, i < n → ∀ x : Real, HasDerivAt (d i) (d (i + 1) x) x

/-- **`f` is differentially algebraic.** There is an order `n`, a derivative tower `d`
for `f`, and a differential polynomial `P : MultiPoly (n+1)` (in `x` and the jet
`y₀,…,yₙ`) that is not the zero polynomial yet vanishes on the jet of `f`:
`P(x, f x, f' x, …, f⁽ⁿ⁾ x) = 0` for all `x`. -/
def IsDiffAlg (f : Real → Real) : Prop :=
  ∃ (n : Nat) (d : Nat → Real → Real) (P : MultiPoly (n + 1)),
    IsDerivTower f d n ∧
    (∃ (x : Real) (env : Fin (n + 1) → Real), P.eval x env ≠ 0) ∧
    (∀ x : Real, P.eval x (fun i => d i.val x) = 0)

/-- **`exp` is differentially algebraic** (order 1): it satisfies the algebraic
differential equation `y₁ − y₀ = 0`, i.e. `exp' = exp`. Non-vacuity of `IsDiffAlg`. -/
theorem exp_isDiffAlg : IsDiffAlg exp := by
  -- P = varY 1 − varY 0  (the polynomial `y₁ − y₀`); tower is `exp` at every level.
  refine ⟨1, fun _ => exp, MultiPoly.sub (MultiPoly.varY 1) (MultiPoly.varY 0), ?_, ?_, ?_⟩
  · -- derivative tower: exp' = exp, uniformly (the tower ignores its index)
    exact ⟨rfl, fun _ _ x => HasDerivAt_exp x⟩
  · -- P is not the zero polynomial: at env = (y₀ ↦ 0, y₁ ↦ 1) it evaluates to 1 ≠ 0
    refine ⟨0, fun i => if i = 1 then (1 : Real) else 0, ?_⟩
    simp only [MultiPoly.eval]
    rw [if_neg (show ¬ ((0 : Fin 2) = 1) from by decide)]
    simp only [if_true, sub_zero]
    exact ne_of_gt zero_lt_one_ax
  · -- the relation vanishes on exp's jet: exp x − exp x = 0
    intro x
    simp only [MultiPoly.eval, sub_self]

/-- **`sin` is differentially algebraic** (order 2): it satisfies `y₂ + y₀ = 0`, i.e.
`sin'' + sin = 0`. A second, order-2 witness — and a reminder that the oscillatory
towers ARE differentially algebraic (they are Pfaffian); what separates them from the
exp tower is the ZERO COUNT (`TowerSeparation`), not differential transcendence. -/
theorem sin_isDiffAlg : IsDiffAlg sin := by
  refine ⟨2, (fun k => match k with | 0 => sin | 1 => cos | _ => fun x => -(sin x)),
          MultiPoly.add (MultiPoly.varY 2) (MultiPoly.varY 0), ?_, ?_, ?_⟩
  · -- tower: sin' = cos, cos' = −sin
    refine ⟨rfl, ?_⟩
    intro i hi x
    match i, hi with
    | 0, _ => exact HasDerivAt_sin x
    | 1, _ => exact HasDerivAt_cos x
  · -- nonzero: at env = (y₀ ↦ 1, y₂ ↦ 0) the polynomial y₂ + y₀ evaluates to 1 ≠ 0
    refine ⟨0, fun i => if i = 0 then (1 : Real) else 0, ?_⟩
    simp only [MultiPoly.eval]
    rw [if_neg (show ¬ ((2 : Fin 3) = 0) from by decide)]
    simp only [if_true, zero_add]
    exact ne_of_gt zero_lt_one_ax
  · -- vanishes on sin's jet: (−sin x) + sin x = 0
    intro x
    simp only [MultiPoly.eval]
    mach_ring

end MachLib
