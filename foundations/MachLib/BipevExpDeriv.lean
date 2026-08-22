import MachLib.RatGermDeriv
import MachLib.EMLFTranscendence

/-!
# Brick four, mechanical half: differentiating the relation

The three bricks so far give derivatives of the *pieces*. This differentiates the **relation itself**:
the function `t ↦ bipev Ls t (exp (S t))`, which is the left-hand side of

```
Σⱼ pⱼ(x) · exp(S x)ʲ = 0
```

Horner in `y = exp(S x)`, with polynomial coefficients in `x`. Each Horner step is a product
`y · (rest)`, so the induction is one product rule per coefficient, and `y' = S'·y` (brick two) is
what keeps the differentiated form expressed in the **same** `y` — no new transcendental appears,
which is the entire reason this route exists.

## What the derivative looks like, and what it is not

Classically one writes the differentiated relation as `Σⱼ (pⱼ' + j·S'·pⱼ)·yʲ = 0` and observes it is
"the same shape". **It is not the same shape here**, and the recursion below shows why: the
coefficients now contain `S'`, which is *rational*, not polynomial. Recovering a genuinely polynomial
relation needs the denominators cleared afterwards. Writing `dbipevExp` as an explicit recursion
rather than as a coefficient family is what keeps that distinction visible instead of assumed.

## What remains after this

Everything mechanical in the differential route is now built. What is left is not a brick but the
**mathematical core**:

1. **Minimal degree.** Choose a relation of least degree in `y`; this needs a well-founded induction
   on the degree, on relations rather than on lists.
2. **Elimination.** Combine the original and the differentiated relation to kill the top term.
3. **Nontriviality of the result** — and this is the crux, not bookkeeping. The eliminated relation
   is trivial exactly when `(pⱼ/p_m)' = (j−m)·S'·(pⱼ/p_m)` for every `j`, i.e. when each ratio is a
   constant multiple of `exp((j−m)·S)`. Ruling that out is where a transcendence input is genuinely
   required; it does not follow from the mechanics above.

Step 3 is the honest reason this file claims a half and not a theorem. And the caveat that has not
moved all day: **the positive branch is not this argument** — `F(S) = exp(S) + log(S)` is not `exp`
of anything, so `y' = S'·y` does not hold there at all.
-/

namespace MachLib

open Real

/-- The derivative of `t ↦ bipev Ls t (exp (S t))`, as an explicit recursion.

Not presented as a coefficient family on purpose: the coefficients of the differentiated relation
involve `S'`, which is rational rather than polynomial, and a `List (List Real)` would hide that. -/
noncomputable def dbipevExp : List (List Real) → (Real → Real) → Real → Real → Real
  | [],      _, _,  _ => 0
  | L :: Ls, S, S', x =>
      pev (pderiv L) x
        + ((S' * exp (S x)) * bipev Ls x (exp (S x))
            + exp (S x) * dbipevExp Ls S S' x)

/-- **The relation differentiates**, and stays expressed in the same `y = exp(S x)`. -/
theorem hasDerivAt_bipev_exp : ∀ (Ls : List (List Real)) (S : Real → Real) (S' x : Real),
    HasDerivAt S S' x →
    HasDerivAt (fun t => bipev Ls t (exp (S t))) (dbipevExp Ls S S' x) x := by
  intro Ls
  induction Ls with
  | nil =>
      intro S S' x _
      show HasDerivAt (fun _ => (0 : Real)) (dbipevExp [] S S' x) x
      have e : dbipevExp ([] : List (List Real)) S S' x = 0 := rfl
      rw [e]
      exact HasDerivAt_const 0 x
  | cons L Ls ih =>
      intro S S' x hS
      have hy : HasDerivAt (fun t => exp (S t)) (S' * exp (S x)) x :=
        hasDerivAt_exp_comp_swap hS
      have hrest : HasDerivAt (fun t => bipev Ls t (exp (S t))) (dbipevExp Ls S S' x) x :=
        ih S S' x hS
      have hprod : HasDerivAt (fun t => exp (S t) * bipev Ls t (exp (S t)))
          ((S' * exp (S x)) * bipev Ls x (exp (S x))
            + exp (S x) * dbipevExp Ls S S' x) x :=
        HasDerivAt_mul (fun t => exp (S t)) (fun t => bipev Ls t (exp (S t)))
          (S' * exp (S x)) (dbipevExp Ls S S' x) x hy hrest
      exact HasDerivAt_add (fun t => pev L t)
        (fun t => exp (S t) * bipev Ls t (exp (S t)))
        (pev (pderiv L) x)
        ((S' * exp (S x)) * bipev Ls x (exp (S x)) + exp (S x) * dbipevExp Ls S S' x)
        x (hasDerivAt_pev L x) hprod

/-- **A vanishing relation has a vanishing derivative.** The step that turns "the relation holds on a
tail" into "the differentiated relation holds on that tail" — `HasDerivAt_congr` against the constant
`0`, with the neighbourhood again supplied by finiteness. -/
theorem dbipevExp_eq_zero_of_relation_off_finite
    {Ls : List (List Real)} {S : Real → Real} {S' x : Real} {E : List Real}
    (hS : HasDerivAt S S' x) (hx : x ∉ E)
    (hrel : ∀ y : Real, y ∉ E → bipev Ls y (exp (S y)) = 0) :
    dbipevExp Ls S S' x = 0 := by
  have hzero : HasDerivAt (fun t => bipev Ls t (exp (S t))) 0 x := by
    refine hasDerivAt_of_agrees_off_finite (f := fun _ => (0 : Real)) hx
      (fun y hy => (hrel y hy).symm) (HasDerivAt_const 0 x)
  exact HasDerivAt_unique (fun t => bipev Ls t (exp (S t)))
    (dbipevExp Ls S S' x) 0 x (hasDerivAt_bipev_exp Ls S S' x hS) hzero

end MachLib
