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

/-! ## Packaging for the descent

`gcancel_top` (`GermRelation`) descends **two relations in one `u`**, so the differentiated form has
to be a single `gbipev` against `u = F ∘ S` rather than a sum of two shapes. `gbipev_gyd`,
`gbipev_gscale` and `gbipev_gadd` do exactly that repackaging, which is why nothing below needs new
arithmetic.

**On specimens.** `gEvRel_fbasis_deriv`'s hypothesis `hrel` is satisfiable only *degenerately* — any
true relation of that form is the zero polynomial, which is precisely the claim the arc is trying to
establish. This is a step **inside a refutation**: its premise is the thing being refuted. A specimen
here would validate the mechanism, not the premise, so none is shipped and this paragraph is here
instead of one. Contrast `zeroList_specimen` and `cutFreeBounds_specimen`, whose premises are
genuinely satisfiable and which therefore *do* carry firing specimens.
-/

/-- The multiplier the chain rule contributes: `F′(S x) · S′(x)`. -/
noncomputable def fbasisChainMul (S s : Real → Real) : Real → Real :=
  fun x => (exp (S x) + 1 / S x) * s x

/-- **The differentiated relation, packaged as a germ relation in the SAME `u`.**

`gcancel_top` descends two relations in one `u`, so the differentiated form has to be a single
`gbipev` against `u = F ∘ S` rather than a sum of two shapes. `gbipev_gyd`, `gbipev_gscale` and
`gbipev_gadd` do exactly that repackaging, which is why no new arithmetic is needed here. -/
theorem fbasis_relation_differentiates_packaged {S s : Real → Real} {X : Real}
    (hS : ∀ x : Real, X < x → HasDerivAt S (s x) x)
    (hpos : ∀ x : Real, X ≤ x → 0 < S x)
    (cs es : List (Real → Real))
    (hd : ∀ x : Real, X < x → GDerivAt x cs es)
    (hrel : ∀ x : Real, X ≤ x → gbipev cs x (Fbasis (S x)) = 0) :
    ∀ x : Real, X < x →
      gbipev (gadd es (gscale (fbasisChainMul S s) (gyd cs))) x (Fbasis (S x)) = 0 := by
  intro x hx
  have h := fbasis_relation_differentiates hS hpos cs es hd hrel x hx
  rw [gbipev_gadd, gbipev_gscale, gbipev_gyd]
  exact h


private theorem lt_add_one_g (a : Real) : a < a + 1 := by
  have v := add_lt_add_left zero_lt_one_ax a
  have e : a + 0 = a := by mach_ring
  rw [e] at v; exact v

/-- **The interface `gcancel_top` consumes.** `GEvRel` wants a CLOSED ray, and the derivative only
exists on the open one, so the threshold moves up by one — `X + 1` is inside the interior of
`[X, ∞)` and inherits `1 ≤ ·` from `X`. -/
theorem gEvRel_fbasis_deriv {S s : Real → Real} {X : Real} (hX1 : 1 ≤ X)
    (hS : ∀ x : Real, X < x → HasDerivAt S (s x) x)
    (hpos : ∀ x : Real, X ≤ x → 0 < S x)
    (cs es : List (Real → Real))
    (hd : ∀ x : Real, X < x → GDerivAt x cs es)
    (hrel : ∀ x : Real, X ≤ x → gbipev cs x (Fbasis (S x)) = 0) :
    GEvRel (fun x => Fbasis (S x)) (gadd es (gscale (fbasisChainMul S s) (gyd cs))) :=
  ⟨X + 1, le_trans hX1 (le_of_lt (lt_add_one_g X)),
   fun x hx => fbasis_relation_differentiates_packaged hS hpos cs es hd hrel x
     (lt_of_lt_of_le (lt_add_one_g X) hx)⟩

/-- **Both relations have the same length**, which is `gcancel_top`'s standing side condition. -/
theorem gadd_gscale_gyd_length {S s : Real → Real} (cs es : List (Real → Real))
    (hlen : cs.length = es.length) :
    (gadd es (gscale (fbasisChainMul S s) (gyd cs))).length = cs.length := by
  have h1 : (gscale (fbasisChainMul S s) (gyd cs)).length = cs.length := by
    rw [gscale_length, gyd_length]
  have h2 : es.length ≤ (gscale (fbasisChainMul S s) (gyd cs)).length := by
    rw [h1]; exact Nat.le_of_eq hlen.symm
  rw [gadd_length_of_le es _ h2, h1]

/-! ## Substituting `exp (S x) = u x - log (S x)`

The packaging above leaves the chain-rule multiplier containing `exp ∘ S`, so the differentiated
relation's coefficients are **not** in the same ring as the original's. That is what this section
fixes, and it is the step that makes the descent mean anything.

`Fbasis` is *definitionally* `exp + log`, so `exp (S x) = u x - log (S x)` needs no lemma — and the
multiplier splits into a part linear in `u` (which raises the `y`-degree by one: the `0 ::`) and a
part free of it. Afterwards **every coefficient is free of `u`**, and both relations live over
`ℝ(x)` extended by `log ∘ S` — the ring in which `no_proper_cleared_relation` speaks.
-/

/-- Multiplying a germ relation's value by `y` is prepending a zero coefficient. -/
theorem gbipev_zeroCons (cs : List (Real → Real)) (x y : Real) :
    gbipev ((fun _ => (0 : Real)) :: cs) x y = y * gbipev cs x y := by
  show (0 : Real) + y * gbipev cs x y = y * gbipev cs x y
  mach_ring

/-- The part of the chain-rule multiplier that survives substituting `exp (S x) = u x - log (S x)`. -/
noncomputable def fbasisSubMul (S s : Real → Real) : Real → Real :=
  fun x => s x * (1 / S x - log (S x))

/-- **The substituted packaging.** `Fbasis (S x) = exp (S x) + log (S x)`, so
`exp (S x) = u x - log (S x)` and the chain-rule multiplier `(exp (S x) + 1/S x)·S′(x)` splits into a
part linear in `u` and a part free of it:

```
(exp (S x) + 1/S x)·s x  =  s x · u x  +  s x · (1/S x - log (S x))
```

The first summand raises the `y`-degree by one — that is the `0 ::` — and the second is an ordinary
coefficient. **Every coefficient of the resulting list is free of `u`**, which is what makes the
descent against the original relation meaningful: both live over the same coefficient ring,
`ℝ(x)` extended by `log ∘ S`. -/
theorem fbasis_relation_substituted {S s : Real → Real} {X : Real}
    (hS : ∀ x : Real, X < x → HasDerivAt S (s x) x)
    (hpos : ∀ x : Real, X ≤ x → 0 < S x)
    (cs es : List (Real → Real))
    (hd : ∀ x : Real, X < x → GDerivAt x cs es)
    (hrel : ∀ x : Real, X ≤ x → gbipev cs x (Fbasis (S x)) = 0) :
    ∀ x : Real, X < x →
      gbipev (gadd es
                (gadd (gscale s ((fun _ => (0 : Real)) :: gyd cs))
                      (gscale (fbasisSubMul S s) (gyd cs)))) x (Fbasis (S x)) = 0 := by
  intro x hx
  have h := fbasis_relation_differentiates hS hpos cs es hd hrel x hx
  rw [gbipev_gadd, gbipev_gadd, gbipev_gscale, gbipev_gscale, gbipev_zeroCons, gbipev_gyd]
  -- `Fbasis (S x) = exp (S x) + log (S x)` is definitional
  have hF : Fbasis (S x) = exp (S x) + log (S x) := rfl
  show gbipev es x (Fbasis (S x))
      + (s x * (Fbasis (S x) * gydiff cs x (Fbasis (S x)))
         + fbasisSubMul S s x * gydiff cs x (Fbasis (S x))) = 0
  show gbipev es x (Fbasis (S x))
      + (s x * (Fbasis (S x) * gydiff cs x (Fbasis (S x)))
         + s x * (1 / S x - log (S x)) * gydiff cs x (Fbasis (S x))) = 0
  rw [hF] at *
  rw [← h]
  mach_mpoly [gbipev es x (exp (S x) + log (S x)), s x, exp (S x), log (S x), 1 / S x,
              gydiff cs x (exp (S x) + log (S x))]

/-! ## Setting up the descent

`gcancel_top` wants **two relations in one `u`, of equal length**. The substituted list is one longer
than the original — the `0 ::` that raises the `y`-degree — but its top slot is identically zero, so
the extra degree is spurious and `gevRel_dropLast` removes it.

Getting that trailing zero out is list surgery, and the ordering of the `gadd` below is chosen for
it: `gadd_append_right` appends on its *second* argument, so putting the one-longer summand there
lets a single application peel the zero. The `(fc)` ordering is value-equal but would need a mirrored
lemma plus an associativity step to reach the same place, so `fbasisDerivList` re-derives from
`fbasis_relation_differentiates` rather than from `fbasis_relation_substituted`.
-/

/-- `gadd` commutes with appending to the **longer** side. Needed because the differentiated
coefficient list is built by `gadd`, and the fact that it ends in a zero has to survive that. -/
theorem gadd_append_right : ∀ (a b : List (Real → Real)) (t : Real → Real),
    a.length ≤ b.length → gadd a (b ++ [t]) = gadd a b ++ [t]
  | [],      b,      t, _ => rfl
  | c :: cs, [],     t, h => by simp at h
  | c :: cs, d :: ds, t, h => by
      show (fun x => c x + d x) :: gadd cs (ds ++ [t]) = (fun x => c x + d x) :: gadd cs ds ++ [t]
      have hlen : cs.length ≤ ds.length := by
        simp only [List.length_cons] at h; omega
      rw [gadd_append_right cs ds t hlen]
      rfl

/-- `gscale` commutes with appending. -/
theorem gscale_append (a : Real → Real) : ∀ (l : List (Real → Real)) (t : Real → Real),
    gscale a (l ++ [t]) = gscale a l ++ [fun x => a x * t x]
  | [],      t => rfl
  | c :: cs, t => by
      show (fun x => a x * c x) :: gscale a (cs ++ [t])
          = (fun x => a x * c x) :: gscale a cs ++ [fun x => a x * t x]
      rw [gscale_append a cs t]
      rfl

/-- **The formal `y`-derivative's list ends in a coefficient that is identically zero.**

`gydiff` has `y`-degree one less than its input, so the top slot of a same-length list must be zero.
Stated with `EvZeroF` rather than syntactic equality because `gadd` builds `fun x => c x + d x`, so
the last entry is `0 + 0` in shape, not the literal zero function.

This is what lets `gevRel_dropLast` cut the differentiated relation back to the original's length —
the step that makes `gcancel_top` applicable, since descending against a *zero* top coefficient is
vacuous. -/
theorem gyd_eq_append_zero : ∀ (c : Real → Real) (cs : List (Real → Real)),
    ∃ (ys : List (Real → Real)) (z : Real → Real),
      gyd (c :: cs) = ys ++ [z] ∧ (∀ x : Real, z x = 0) ∧ ys.length = cs.length
  | c, [] => ⟨[], fun _ => 0, rfl, fun _ => rfl, rfl⟩
  | c, d :: ds => by
      obtain ⟨ys, z, heq, hz, hlen⟩ := gyd_eq_append_zero d ds
      refine ⟨gadd (d :: ds) ((fun _ => (0 : Real)) :: ys), z, ?_, hz, ?_⟩
      · show gadd (d :: ds) ((fun _ => (0 : Real)) :: gyd (d :: ds)) = _
        rw [heq]
        exact gadd_append_right (d :: ds) ((fun _ => (0 : Real)) :: ys) z
          (by simp only [List.length_cons]; omega)
      · rw [gadd_length_of_le (d :: ds) ((fun _ => (0 : Real)) :: ys)
            (by simp only [List.length_cons]; omega)]
        simp only [List.length_cons]
        omega


/-- The substituted coefficient list, with the **longest** summand outermost.

The ordering is not cosmetic. `gadd_append_right` appends on its *second* argument, so putting the
`y`-degree-raising summand (`0 :: gyd cs`, one longer than the rest) there is what lets a single
application peel the trailing zero. `(fc)`'s ordering is value-equal but would need a mirrored
lemma and an associativity step to reach the same place. -/
noncomputable def fbasisDerivList (S s : Real → Real) (cs es : List (Real → Real)) :
    List (Real → Real) :=
  gadd (gadd es (gscale (fbasisSubMul S s) (gyd cs))) (gscale s ((fun _ => (0 : Real)) :: gyd cs))

theorem fbasisDerivList_rel {S s : Real → Real} {X : Real}
    (hS : ∀ x : Real, X < x → HasDerivAt S (s x) x)
    (hpos : ∀ x : Real, X ≤ x → 0 < S x)
    (cs es : List (Real → Real))
    (hd : ∀ x : Real, X < x → GDerivAt x cs es)
    (hrel : ∀ x : Real, X ≤ x → gbipev cs x (Fbasis (S x)) = 0) :
    ∀ x : Real, X < x → gbipev (fbasisDerivList S s cs es) x (Fbasis (S x)) = 0 := by
  intro x hx
  have h := fbasis_relation_differentiates hS hpos cs es hd hrel x hx
  show gbipev (gadd (gadd es (gscale (fbasisSubMul S s) (gyd cs)))
                    (gscale s ((fun _ => (0 : Real)) :: gyd cs))) x (Fbasis (S x)) = 0
  rw [gbipev_gadd, gbipev_gadd, gbipev_gscale, gbipev_gscale, gbipev_zeroCons, gbipev_gyd]
  rw [← h]
  show gbipev es x (Fbasis (S x)) + fbasisSubMul S s x * gydiff cs x (Fbasis (S x))
        + s x * (Fbasis (S x) * gydiff cs x (Fbasis (S x)))
      = gbipev es x (Fbasis (S x))
        + (exp (S x) + 1 / S x) * s x * gydiff cs x (Fbasis (S x))
  show gbipev es x (exp (S x) + log (S x))
        + s x * (1 / S x - log (S x)) * gydiff cs x (exp (S x) + log (S x))
        + s x * ((exp (S x) + log (S x)) * gydiff cs x (exp (S x) + log (S x)))
      = gbipev es x (exp (S x) + log (S x))
        + (exp (S x) + 1 / S x) * s x * gydiff cs x (exp (S x) + log (S x))
  mach_mpoly [gbipev es x (exp (S x) + log (S x)), s x, exp (S x), log (S x), 1 / S x,
              gydiff cs x (exp (S x) + log (S x))]

/-- **The differentiated list ends in an identically-zero coefficient**, so `gevRel_dropLast` can cut
it back to the original relation's length — which is exactly `gcancel_top`'s side condition. -/
theorem fbasisDerivList_append_zero (S s : Real → Real) (c : Real → Real)
    (cs es : List (Real → Real)) (hlen : es.length = (c :: cs).length) :
    ∃ (L : List (Real → Real)) (z : Real → Real),
      fbasisDerivList S s (c :: cs) es = L ++ [z] ∧ (∀ x : Real, z x = 0)
        ∧ L.length = (c :: cs).length := by
  obtain ⟨ys, z, heq, hz, hylen⟩ := gyd_eq_append_zero c cs
  refine ⟨gadd (gadd es (gscale (fbasisSubMul S s) (gyd (c :: cs))))
               (gscale s ((fun _ => (0 : Real)) :: ys)), (fun x => s x * z x), ?_, ?_, ?_⟩
  · show gadd (gadd es (gscale (fbasisSubMul S s) (gyd (c :: cs))))
              (gscale s ((fun _ => (0 : Real)) :: gyd (c :: cs))) = _
    rw [heq]
    show gadd (gadd es (gscale (fbasisSubMul S s) (ys ++ [z])))
              (gscale s (((fun _ => (0 : Real)) :: ys) ++ [z])) = _
    rw [gscale_append s ((fun _ => (0 : Real)) :: ys) z]
    refine gadd_append_right _ _ _ ?_
    rw [gadd_length_of_le es (gscale (fbasisSubMul S s) (ys ++ [z])) ?_, gscale_length,
        gscale_length]
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    · rw [gscale_length, hlen]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  · intro x
    show s x * z x = 0
    rw [hz x]; mach_ring
  · rw [gadd_length_of_le _ _ ?_, gscale_length]
    · simp only [List.length_cons]; omega
    · rw [gscale_length, gadd_length_of_le es (gscale (fbasisSubMul S s) (gyd (c :: cs))) ?_,
          gscale_length, gyd_length]
      · simp only [List.length_cons]; omega
      · rw [gscale_length, gyd_length, hlen]
        exact Nat.le_refl _


private theorem lt_add_one_d (a : Real) : a < a + 1 := by
  have v := add_lt_add_left zero_lt_one_ax a
  have e : a + 0 = a := by mach_ring
  rw [e] at v; exact v

/-- **The descent is set up.** From one relation in `u = F ∘ S` we now have a *second*, of the **same
length**, over the **same coefficient ring** — the two things `gcancel_top` asks for.

Three facts combine: the differentiated relation holds (`fbasisDerivList_rel`), every coefficient of
it is free of `u` (`fbasis_relation_substituted`'s substitution, carried by `fbasisSubMul`), and its
top slot is identically zero so the extra degree is spurious (`fbasisDerivList_append_zero`,
discharged through `gevRel_dropLast`).

What this does **not** decide is whether the descended relation is *proper* — whether its own top
coefficient is eventually non-zero. That is where `EvDom` enters, and it is the next brick. -/
theorem fbasisDeriv_descends {S s : Real → Real} {X : Real} (hX1 : 1 ≤ X)
    (hS : ∀ x : Real, X < x → HasDerivAt S (s x) x)
    (hpos : ∀ x : Real, X ≤ x → 0 < S x)
    (c : Real → Real) (cs es : List (Real → Real))
    (hlen : es.length = (c :: cs).length)
    (hd : ∀ x : Real, X < x → GDerivAt x (c :: cs) es)
    (hrel : ∀ x : Real, X ≤ x → gbipev (c :: cs) x (Fbasis (S x)) = 0) :
    ∃ L : List (Real → Real),
      L.length = (c :: cs).length ∧ GEvRel (fun x => Fbasis (S x)) L := by
  obtain ⟨L, z, heq, hz, hLlen⟩ := fbasisDerivList_append_zero S s c cs es hlen
  refine ⟨L, hLlen, ?_⟩
  refine gevRel_dropLast (c := z) ?_ ⟨1, le_refl 1, fun x _ => hz x⟩
  rw [← heq]
  exact ⟨X + 1, le_trans hX1 (le_of_lt (lt_add_one_d X)),
    fun x hx => fbasisDerivList_rel hS hpos (c :: cs) es hd hrel x
      (lt_of_lt_of_le (lt_add_one_d X) hx)⟩

/-! ## The descent, executed against a MINIMAL relation

The obvious next question is whether the *descended* relation is proper — whether its own top
coefficient is eventually non-zero. It does not have to be answered. Routing through **minimality**
instead sidesteps it entirely: `all_gcoeffs_evZero_of_shorter'` (`GermRelation`) turns *"shorter than
the minimal proper relation"* into *"every coefficient is eventually zero"* while asking nothing about
top coefficients.

So from a minimal proper relation for `u = F ∘ S` the descent yields, for every `i`,

```
m · (L₀)ᵢ  −  d · (ms₀)ᵢ  ≡  0     eventually
```

with `m` the minimal relation's top coefficient and `d` the differentiated one's — a concrete system
over `ℝ(x)` extended by `log ∘ S`.
-/
/-- `gscaleSub` walks both lists in step, so it is no longer than either. -/
theorem gscaleSub_length_le (a b : Real → Real) :
    ∀ cs ds : List (Real → Real), (gscaleSub a b cs ds).length ≤ cs.length
  | [],      _       => Nat.zero_le _
  | c :: cs, []      => Nat.zero_le _
  | c :: cs, d :: ds => by
      show (gscaleSub a b cs ds).length + 1 ≤ cs.length + 1
      exact Nat.succ_le_succ (gscaleSub_length_le a b cs ds)

/-- `fbasisDeriv_descends` for a list given as non-empty rather than as a `cons`. -/
theorem fbasisDeriv_descends' {S s : Real → Real} {X : Real} (hX1 : 1 ≤ X)
    (hS : ∀ x : Real, X < x → HasDerivAt S (s x) x)
    (hpos : ∀ x : Real, X ≤ x → 0 < S x)
    (cs es : List (Real → Real)) (hne : cs ≠ [])
    (hlen : es.length = cs.length)
    (hd : ∀ x : Real, X < x → GDerivAt x cs es)
    (hrel : ∀ x : Real, X ≤ x → gbipev cs x (Fbasis (S x)) = 0) :
    ∃ L : List (Real → Real),
      L.length = cs.length ∧ GEvRel (fun x => Fbasis (S x)) L := by
  obtain ⟨c, cs', rfl⟩ : ∃ c cs', cs = c :: cs' := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons c cs' => exact ⟨c, cs', rfl⟩
  exact fbasisDeriv_descends hX1 hS hpos c cs' es hlen hd hrel

/-- **The minimal-relation descent, in coefficients.**

Assume `u = F ∘ S` satisfies a proper relation *of minimal length*. Differentiating gives a second
relation of the same length (brick 4), `gcancel_top` cancels the two top coefficients, and the result
is strictly shorter — so by minimality **every one of its coefficients is eventually zero**:

```
∀ i,   m · (L₀)ᵢ  −  d · (ms₀)ᵢ   ≡  0     eventually
```

where `m` is the minimal relation's top coefficient and `d` the differentiated one's.

**Properness of the descended relation is never needed**, and that is the point of routing through
minimality rather than through a direct properness argument: `all_gcoeffs_evZero_of_shorter'` turns
"shorter than minimal" into "identically zero" without asking anything about the top coefficient. -/
theorem fbasis_minimal_descent {S s : Real → Real} {X : Real} (hX1 : 1 ≤ X)
    (hS : ∀ x : Real, X < x → HasDerivAt S (s x) x)
    (hpos : ∀ x : Real, X ≤ x → 0 < S x)
    (ms₀ : List (Real → Real)) (m : Real → Real)
    (hmin : ∀ ns : List (Real → Real),
        GProperRel (fun x => Fbasis (S x)) ns → (ms₀ ++ [m]).length ≤ ns.length)
    (es : List (Real → Real)) (hlen : es.length = (ms₀ ++ [m]).length)
    (hd : ∀ x : Real, X < x → GDerivAt x (ms₀ ++ [m]) es)
    (hrel : ∀ x : Real, X ≤ x → gbipev (ms₀ ++ [m]) x (Fbasis (S x)) = 0) :
    ∃ (L₀ : List (Real → Real)) (d : Real → Real),
      L₀.length = ms₀.length ∧
      ∀ c : Real → Real, c ∈ gscaleSub m d ms₀ L₀ → EvZeroF c := by
  have hne : ms₀ ++ [m] ≠ [] := by
    intro h
    exact absurd (congrArg List.length h) (by simp)
  obtain ⟨L, hLlen, hLrel⟩ :=
    fbasisDeriv_descends' hX1 hS hpos (ms₀ ++ [m]) es hne hlen hd hrel
  have hLne : L ≠ [] := by
    intro h
    rw [h] at hLlen
    simp at hLlen
  obtain ⟨L₀, d, hsplit⟩ : ∃ L₀ d, L = L₀ ++ [d] :=
    ⟨L.dropLast, L.getLast hLne, (List.dropLast_concat_getLast hLne).symm⟩
  have hL₀len : L₀.length = ms₀.length := by
    have := hLlen
    rw [hsplit] at this
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  refine ⟨L₀, d, hL₀len, ?_⟩
  have horig : GEvRel (fun x => Fbasis (S x)) (ms₀ ++ [m]) :=
    ⟨X + 1, le_trans hX1 (le_of_lt (lt_add_one_d X)),
     fun x hx => hrel x (le_of_lt (lt_of_lt_of_le (lt_add_one_d X) hx))⟩
  have hdrel : GEvRel (fun x => Fbasis (S x)) (L₀ ++ [d]) := by rw [← hsplit]; exact hLrel
  have hcancel := gcancel_top (u := fun x => Fbasis (S x)) hL₀len.symm horig hdrel
  refine all_gcoeffs_evZero_of_shorter' hmin hcancel ?_
  have hlenSub : (gscaleSub m d ms₀ L₀).length ≤ ms₀.length := gscaleSub_length_le m d ms₀ L₀
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

end MachLib
