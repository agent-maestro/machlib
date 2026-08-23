import MachLib.BipevExpDeriv
import MachLib.PolyEvZero

/-!
# Clearing denominators in the differentiated relation

`BipevExpDeriv` differentiates the relation and warns, correctly, that the result is **not the same
shape**: the coefficients of `Σ (pⱼ' + j·S'·pⱼ)·yʲ` contain `S'`, which is *rational*. That is why
`dbipevExp` is an explicit recursion rather than a coefficient family — writing it as a family would
have hidden the distinction.

This file removes the distinction rather than hiding it. Multiplying through by `Q²` turns the
coefficients polynomial:

```
Q²·(pⱼ' + j·S'·pⱼ)  =  Q²·pⱼ' + j·D·pⱼ        where  D = P'Q − PQ'  and  S' = D/Q²
```

and `dcoeffs` is that family. With it the differentiated relation is an ordinary `bipev` over
polynomial coefficient lists, which is the shape the elimination needs and the shape
`cleared_relation_impossible` ultimately consumes.

## The induction carries a correction term

The obvious claim — `Q²·dbipevExp Ls = bipev (dcoeffs …) ` — is **false**, and instructively so.
`dbipevExp` nests its `S'` contributions, so peeling one coefficient shifts every remaining index by
one; the `j·` in the `j·D·pⱼ` term is exactly a count of how many peels a coefficient has survived.
The statement that does induct carries that count explicitly:

```
Q²·dbipevExp Ls x + j·D·(bipev Ls x y)  =  bipev (dcoeffs Q² D j Ls) x y
```

and the `j = 0` instance is the one a caller wants. Getting this wrong is the natural first attempt,
so the corrected form is stated rather than the corollary alone.

**This module is outside `algebraFootprint` by construction** — it mentions `exp` and inherits
`HasDerivAt` through brick four. That is the analytic half, and the boundary drawn in `PolyEvZero`
is where it starts.
-/

namespace MachLib

open Real

/-! ## Evaluating an iterated sum -/

theorem pev_pnsum : ∀ (j : Nat) (Z : List Real) (x : Real),
    pev (pnsum j Z) x = natMul j (pev Z x) := by
  intro j
  induction j with
  | zero => intro Z x; rfl
  | succ k ih =>
      intro Z x
      show pev (padd Z (pnsum k Z)) x = pev Z x + natMul k (pev Z x)
      rw [pev_padd, ih Z x]

/-! ## The cleared coefficient family -/

/-- `Q²·pⱼ' + j·D·pⱼ`, the coefficients of the differentiated relation once denominators are
cleared. The `Nat` argument is the index the tail is currently at. -/
noncomputable def dcoeffs (QQ D : List Real) : Nat → List (List Real) → List (List Real)
  | _, []      => []
  | j, L :: Ls => padd (pmul QQ (pderiv L)) (pnsum j (pmul D L)) :: dcoeffs QQ D (j + 1) Ls

/-- **The differentiated relation, with polynomial coefficients.** Note the correction term: see the
module docstring for why the naive form does not induct. -/
theorem bipev_cleared_deriv : ∀ (Ls : List (List Real)) (QQ D : List Real) (S : Real → Real)
    (S' x : Real) (j : Nat), S' * pev QQ x = pev D x →
    pev QQ x * dbipevExp Ls S S' x + natMul j (pev D x) * bipev Ls x (exp (S x))
      = bipev (dcoeffs QQ D j Ls) x (exp (S x)) := by
  intro Ls
  induction Ls with
  | nil =>
      intro QQ D S S' x j _
      show pev QQ x * 0 + natMul j (pev D x) * 0 = 0
      mach_ring
  | cons L Ls ih =>
      intro QQ D S S' x j hS
      have hrec := ih QQ D S S' x (j + 1) hS
      show pev QQ x * (pev (pderiv L) x
            + ((S' * exp (S x)) * bipev Ls x (exp (S x))
                + exp (S x) * dbipevExp Ls S S' x))
          + natMul j (pev D x) * (pev L x + exp (S x) * bipev Ls x (exp (S x)))
          = pev (padd (pmul QQ (pderiv L)) (pnsum j (pmul D L))) x
            + exp (S x) * bipev (dcoeffs QQ D (j + 1) Ls) x (exp (S x))
      rw [← hrec, pev_padd, pev_pmul, pev_pnsum, pev_pmul]
      show pev QQ x * (pev (pderiv L) x
            + ((S' * exp (S x)) * bipev Ls x (exp (S x))
                + exp (S x) * dbipevExp Ls S S' x))
          + natMul j (pev D x) * (pev L x + exp (S x) * bipev Ls x (exp (S x)))
          = pev QQ x * pev (pderiv L) x + natMul j (pev D x * pev L x)
            + exp (S x) * (pev QQ x * dbipevExp Ls S S' x
              + natMul (j + 1) (pev D x) * bipev Ls x (exp (S x)))
      have hdist : natMul j (pev D x * pev L x) = natMul j (pev D x) * pev L x := by
        rw [natMul_eq (pev D x * pev L x) j, natMul_eq (pev D x) j]
        mach_ring
      have hsucc : natMul (j + 1) (pev D x) = pev D x + natMul j (pev D x) := rfl
      rw [hdist, hsucc, ← hS]
      mach_ring

/-- The `j = 0` instance: what a caller actually has. -/
theorem bipev_cleared_deriv_zero (Ls : List (List Real)) (QQ D : List Real) (S : Real → Real)
    (S' x : Real) (hS : S' * pev QQ x = pev D x) :
    pev QQ x * dbipevExp Ls S S' x = bipev (dcoeffs QQ D 0 Ls) x (exp (S x)) := by
  have h := bipev_cleared_deriv Ls QQ D S S' x 0 hS
  show pev QQ x * dbipevExp Ls S S' x = _
  rw [← h]
  show pev QQ x * dbipevExp Ls S S' x
      = pev QQ x * dbipevExp Ls S S' x + 0 * bipev Ls x (exp (S x))
  mach_ring

end MachLib
