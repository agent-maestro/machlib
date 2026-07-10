import MachLib.Differentiation
import MachLib.MultiPoly
import MachLib.IterExpDepthNChainFn
import MachLib.IterExpChain

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

/-! ## Toward the Pfaffian bridge — derivative-closure of the chain-function class

The bridge `IsChainFnVal f → IsDiffAlg f` factors into two steps:
1. **derivative-closure** — the derivatives of a chain function are all chain functions
   (so `f` has a derivative tower, every level a chain function). PROVED below.
2. **algebraic dependence** — a chain function and its first `r+1` derivatives are `r+2`
   elements of `ℝ[x, f₁,…,f_r]` (transcendence degree ≤ `r+1`), hence satisfy a nonzero
   polynomial relation — a differential polynomial. This step needs a transcendence-degree
   fact (or the monomial-counting pigeonhole) that is NOT yet in the Mathlib-free library;
   it is the one remaining brick. -/

open MachLib.IterExpDepthN
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod

/-- `f` is (pointwise) an iterated-exp chain-function value. No degree bound — `IsDiffAlg`
needs none. (`IsExpChainFn` in `TowerSeparation` is the degree-bounded variant used for
the zero-count separation.) -/
def IsChainFnVal (f : Real → Real) : Prop :=
  ∃ (N : Nat) (p : MultiPoly N), ∀ x : Real, f x = (chainNFn N p).eval x

/-- **Derivative-closure of the chain-function class.** The derivative of an iterated-exp
chain function is again one: it is the chain's own total-derivative polynomial
(`chainTotalDerivative`) over the SAME chain, whose coherence is unconditional
(`IterExpChain_isCoherentAt`). Iterating this hands a full derivative tower whose every
level is a chain function — the structural engine of the Pfaffian→diff-algebraic bridge
(only the algebraic-dependence step then remains). -/
theorem isChainFnVal_deriv {f : Real → Real} (hf : IsChainFnVal f) :
    ∃ g : Real → Real, IsChainFnVal g ∧ ∀ x : Real, HasDerivAt f (g x) x := by
  obtain ⟨N, p, hfeq⟩ := hf
  refine ⟨(chainNFn N p).chainTotalDerivative.eval,
          ⟨N, chainTotalDeriv (IterExpChain N) p, fun _ => rfl⟩, ?_⟩
  intro x
  have hd : HasDerivAt (chainNFn N p).eval ((chainNFn N p).chainTotalDerivative.eval x) x :=
    hasDerivAt_eval_natural (chainNFn N p) x (IterExpChain_isCoherentAt N x)
  rw [funext hfeq]
  exact hd

/-- The `i`-th total-derivative iterate of the chain function `chainNFn N p`. -/
noncomputable def chainDerivIter (N : Nat) (p : MultiPoly N) : Nat → PfaffianFn
  | 0     => chainNFn N p
  | i + 1 => chainTotalDerivative (chainDerivIter N p i)

/-- Every iterate is coherent everywhere: the derivation preserves the underlying chain
(`chainTotalDerivative` keeps `.chain`), whose coherence is unconditional at the base. -/
theorem chainDerivIter_coherent (N : Nat) (p : MultiPoly N) (i : Nat) (x : Real) :
    (chainDerivIter N p i).chain.IsCoherentAt x := by
  induction i with
  | zero => exact IterExpChain_isCoherentAt N x
  | succ k ih => exact ih

/-- **Every chain function has a full derivative tower.** Iterating `isChainFnVal_deriv`
via `chainDerivIter`: for any `IsChainFnVal f` there is a tower `d` with `d 0 = f` and
each `d (i+1)` the derivative of `d i` at every point — the `IsDerivTower` shape that
`IsDiffAlg` consumes. So the Pfaffian bridge `IsChainFnVal f → IsDiffAlg f` reduces to a
SINGLE remaining step: a nonzero polynomial relation among `d 0, …, d (r+1)` (algebraic
dependence of `r+2` elements in the transcendence-degree-`(r+1)` ring `ℝ[x, f₁,…,f_r]`).
(The per-level "each `d i` is itself a chain-function VALUE" refinement is true but needs
a small HEq — `PfaffianFn.chain`'s type depends on `.n` — so it is deferred; the tower's
structural content here needs only coherence.) -/
theorem isChainFnVal_derivTower {f : Real → Real} (hf : IsChainFnVal f) :
    ∃ d : Nat → Real → Real, d 0 = f ∧ (∀ i x, HasDerivAt (d i) (d (i + 1) x) x) := by
  obtain ⟨N, p, hfeq⟩ := hf
  refine ⟨fun i => (chainDerivIter N p i).eval, (funext hfeq).symm, ?_⟩
  intro i x
  exact hasDerivAt_eval_natural (chainDerivIter N p i) x (chainDerivIter_coherent N p i x)

/-! ## The Pfaffian bridge — `IsChainFnVal f → IsDiffAlg f`

The `MultiPoly N`-level derivative iterate `polyDerivIter` stays in a FIXED `MultiPoly N`
(no `.n`-dependent HEq — it is wrapped with `chainNFn N`, whose `.n` is `N` syntactically).
Its jet is exactly the tower `d k = (chainNFn N (polyDerivIter … k)).eval`. The one
non-structural fact — that the `N+2` tower levels satisfy a nonzero polynomial relation —
is the witnessed axiom `chain_algebraic_dependence`. -/

/-- The `i`-th chain-total-derivative iterate at the POLYNOMIAL level (fixed `MultiPoly N`). -/
noncomputable def polyDerivIter (N : Nat) (p : MultiPoly N) : Nat → MultiPoly N
  | 0     => p
  | i + 1 => chainTotalDeriv (IterExpChain N) (polyDerivIter N p i)

/-- **Algebraic dependence of chain-function values** — WITNESSED AXIOM (against Mathlib's
transcendence degree, in `monogate-lean`). Any `N+2` polynomials in the `N+1` generators
`(x, f₁,…,f_N)` of the order-`N` iterated-exp chain satisfy a nonzero polynomial relation
as functions of `x`: they lie in a field of transcendence degree ≤ `N+1`, so `N+2` of them
are algebraically dependent over ℝ. This uses only the TRIVIAL trans-degree upper bound —
no algebraic independence of iterated exponentials (Ax's theorem) is required. -/
axiom chain_algebraic_dependence (N : Nat) (P : Fin (N + 2) → MultiPoly N) :
    ∃ Q : MultiPoly (N + 2),
      (∃ (x : Real) (env : Fin (N + 2) → Real), Q.eval x env ≠ 0) ∧
      ∀ x : Real, Q.eval x (fun i => (P i).eval x ((IterExpChain N).chainValues x)) = 0

/-- **The Pfaffian bridge.** Every iterated-exp chain-function value is differentially
algebraic. Combines the derivative tower (structural, proved) with the algebraic-dependence
axiom (witnessed): the tower gives `d 0 = f` and the derivative chain, and the axiom hands a
nonzero polynomial relation among `d 0, …, d(N+1)` — exactly an `IsDiffAlg` witness of order
`N+1`. Consequently a differentially TRANSCENDENTAL function (Γ, once Hölder is in) cannot be
a chain function — the clean form of "no exp operator computes Γ". -/
theorem isChainFnVal_isDiffAlg {f : Real → Real} (hf : IsChainFnVal f) : IsDiffAlg f := by
  obtain ⟨N, p, hfeq⟩ := hf
  obtain ⟨Q, hQnz, hQrel⟩ := chain_algebraic_dependence N (fun i => polyDerivIter N p i.val)
  refine ⟨N + 1, (fun k => (chainNFn N (polyDerivIter N p k)).eval), Q,
          ⟨(funext hfeq).symm, ?_⟩, hQnz, ?_⟩
  · -- consecutive tower levels are derivative/antiderivative
    intro i _ x
    exact hasDerivAt_eval_natural (chainNFn N (polyDerivIter N p i)) x
      (IterExpChain_isCoherentAt N x)
  · -- the axiom's relation is exactly the jet relation `Q.eval x (d 0 x, …, d(N+1) x) = 0`
    intro x
    exact hQrel x

/-- **The separation, ready for Hölder.** A function that is NOT differentially algebraic
is not an iterated-exp chain-function value. Once `¬ IsDiffAlg Real.Gamma` (Hölder) lands,
this gives `¬ IsChainFnVal Real.Gamma` — Γ is separated from the exp tower. -/
theorem not_isChainFnVal_of_not_isDiffAlg {f : Real → Real} (h : ¬ IsDiffAlg f) :
    ¬ IsChainFnVal f :=
  fun hf => h (isChainFnVal_isDiffAlg hf)

end MachLib
