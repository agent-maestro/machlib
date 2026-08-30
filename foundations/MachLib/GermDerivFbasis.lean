import MachLib.GermDeriv
import MachLib.EMLGermSign

/-!
# Differentiating an `F ∘ S` germ relation

`BoundedGermTranscendence` is the last open obligation whose route is written down in the corpus
itself: `EMLFTranscendence`'s own docstring says *"the missing step is
differentiation-preserves-algebraicity, not anything about `exp`"*. This module is the first brick of
that step, and it is the mechanical half.

## Why the growth instruments cannot be used here

`BoundedGermEnvelope.polyEnvelope_of_Fbasis_floor` is a **theorem** saying `F ∘ S` is polynomially
enveloped on the bounded branch. Every exclusion instrument in the corpus
(`not_polyEnvelope_of_ge_exp`, `not_polyEnvelope_of_ge_exp_scaled`, and through them
`FS_not_algebraic_of_ge_linear` / `_of_le_linear` / `Fbasis_not_algebraic`) needs the generator to
outgrow every polynomial. On this branch their hypothesis is provably false, so they are silent —
not by accident of formulation. That is why the route has to be differential.

## What this file proves

If `Σⱼ cⱼ(x)·F(S x)ʲ = 0` on a ray, then differentiating gives a **second** relation on the interior
of that ray:

```
Σⱼ cⱼ′(x)·F(S x)ʲ  +  (exp (S x) + 1/S x)·S′(x) · ∂/∂y[Σⱼ cⱼ(x)·yʲ](F (S x))  =  0
```

Three existing pieces do the work — `gbipev_hasDerivAt` (`GermDeriv`) differentiates a germ-coefficient
relation, `Fbasis_hasDeriv` (`EMLGermSign`) gives `F′ = exp + 1/·` on the positive side, and
`HasDerivAt_comp` chains them.

**The conclusion is on the OPEN ray `X < x`, not `X ≤ x`,** and that is forced rather than sloppy: a
derivative is a local object, and the relation is only known on `[X, ∞)`, so the endpoint has no
two-sided neighbourhood to be differentiated in. `HasDerivAt_congr` needs `|y - x| < δ`, and the
largest δ available at `x` is `x - X`.

## What it does NOT do

It produces a relation, not a contradiction. Turning the pair of relations into one for `exp (S x)`
alone means eliminating `F (S x)` between them, which is where the Euclidean layer (`euclid_lemma`,
`Pdvd`) would come in, and then the *real* base case is needed: `exp ∘ S` transcendental over the
rational functions for non-constant rational `S`. That is **not** `exp_not_algebraic`, which is about
`exp x` and is proved by growth — and growth is exactly what this branch has ruled out. No obligation
is registered here for the residue.
-/

namespace MachLib

open Real

/-- **Chain rule for `F ∘ S` on the positive side.** -/
theorem fbasisComp_hasDerivAt {S : Real → Real} {s x : Real}
    (hS : HasDerivAt S s x) (hpos : 0 < S x) :
    HasDerivAt (fun t => Fbasis (S t)) ((exp (S x) + 1 / S x) * s) x :=
  HasDerivAt_comp Fbasis S s (exp (S x) + 1 / S x) x hS (Fbasis_hasDeriv hpos)

/-- **A function that vanishes on a ray has vanishing derivative in that ray's interior.**

The neighbourhood is `x - X`, which is why the statement is about `X < x`: at the endpoint there is
no two-sided neighbourhood inside the ray. -/
theorem deriv_eq_zero_of_zero_on_ray {f : Real → Real} {X x d : Real}
    (hx : X < x) (hzero : ∀ y : Real, X ≤ y → f y = 0) (hd : HasDerivAt f d x) : d = 0 := by
  have hδ : (0 : Real) < x - X := by
    have h := add_lt_add_left hx (0 - X)
    have l : (0 : Real) - X + X = 0 := by mach_ring
    have r : (0 : Real) - X + x = x - X := by mach_ring
    rw [l, r] at h; exact h
  have hagree : ∃ δ : Real, 0 < δ ∧ ∀ y : Real, abs (y - x) < δ → f y = (fun _ : Real => (0 : Real)) y := by
    refine ⟨x - X, hδ, fun y hy => ?_⟩
    have h1 : -(y - x) ≤ x - X := neg_le_of_abs_le (le_of_lt hy)
    have h2 : x - y ≤ x - X := by
      have e : -(y - x) = x - y := by mach_ring
      rw [e] at h1; exact h1
    have h3 := add_le_add_left h2 (y + X - x)
    have l : y + X - x + (x - y) = X := by mach_mpoly [X, x, y]
    have r : y + X - x + (x - X) = y := by mach_mpoly [X, x, y]
    rw [l, r] at h3
    exact hzero y h3
  have hd0 : HasDerivAt (fun _ : Real => (0 : Real)) d x :=
    HasDerivAt_congr f (fun _ => 0) d x hagree hd
  exact HasDerivAt_unique (fun _ : Real => (0 : Real)) d 0 x hd0 (HasDerivAt_const 0 x)

/-- **The brick: an `F ∘ S` relation differentiates.** -/
theorem fbasis_relation_differentiates {S s : Real → Real} {X : Real}
    (hS : ∀ x : Real, X < x → HasDerivAt S (s x) x)
    (hpos : ∀ x : Real, X ≤ x → 0 < S x)
    (cs es : List (Real → Real))
    (hd : ∀ x : Real, X < x → GDerivAt x cs es)
    (hrel : ∀ x : Real, X ≤ x → gbipev cs x (Fbasis (S x)) = 0) :
    ∀ x : Real, X < x →
      gbipev es x (Fbasis (S x))
        + ((exp (S x) + 1 / S x) * s x) * gydiff cs x (Fbasis (S x)) = 0 := by
  intro x hx
  have hchain : HasDerivAt (fun t => Fbasis (S t)) ((exp (S x) + 1 / S x) * s x) x :=
    fbasisComp_hasDerivAt (hS x hx) (hpos x (le_of_lt hx))
  have hfull := gbipev_hasDerivAt hchain cs es (hd x hx)
  exact deriv_eq_zero_of_zero_on_ray hx hrel hfull

end MachLib
