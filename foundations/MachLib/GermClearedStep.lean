import MachLib.GermCleared

/-!
# The `gscaleSub` step preserves the clearing invariant — and the denominator does not grow

`GermCleared` supplied the class `ClearsToExp` and discharged two of the three obligations
`ClassMinimality` named. This module discharges the third *consumer-side*: given that the
differentiated relation clears by a single polynomial denominator `pev G`, the `gscaleSub` step's
output clears by **the same** `pev G`.

## Why the denominator does not multiply

The expectation going in was that it would: `gscaleSub` forms products, so denominators should
multiply. They do not, because the step is **not symmetric**. Its shape is

```
gscaleSub cd dtop cs₀ ds₀        entry j  =  cd·(ds₀)ⱼ  −  dtop·(cs₀)ⱼ
```

and `cd` and `cs₀` come from `expCoeffs` — they are `bipev`s already, denominator `1`. Only `dtop`
and `ds₀` come from `gdrel` and carry a denominator. So each product has exactly **one** dirty
factor, and one `pev G` clears both terms:

```
pev G · (cd·dⱼ − b·cⱼ)  =  cd·(pev G·dⱼ)  −  (pev G·b)·cⱼ  =  bipev A·bipev Dⱼ − bipev Bt·bipev Cⱼ
```

which is `bipev (bisub (bimul A Dⱼ) (bimul Bt Cⱼ))`. `gsubNum` is that family.

This matters for the arc, not just for this proof: had denominators multiplied, each descent step
would raise the `Q`-power and the class would need a denominator *bound* to stay usable across a
degree-`d` descent. It needs none. The `Q`-power is fixed once, by the producer, and never moves.

## What this module does **not** do

It does not prove that `gdrel v (expCoeffs S Cs) (expCoeffsD S S' Cs)` clears at all. That is the
producer half, and it is where `S' = (P'Q − PQ')/Q²` and `ratLogDeriv_cleared`'s
`v·(P·Q²) = Q·(P'Q − PQ')` enter. This module states precisely what the producer must deliver — one
polynomial `G`, one `GEvEq` for the whole tail, one `EvEqF` for the top — and nothing more.
-/

namespace MachLib

open Real

/-- **The numerators of the step.** Mirrors `gscaleSub`'s recursion exactly, including its catch-all,
so the two lists stay in lockstep with no length hypothesis. -/
noncomputable def gsubNum (A Bt : List (List Real)) :
    List (List (List Real)) → List (List (List Real)) → List (List (List Real))
  | C :: Cs, D :: Ds => bisub (bimul A D) (bimul Bt C) :: gsubNum A Bt Cs Ds
  | _,       _       => []

/-- **The step clears, by the same denominator it was handed.** `A` is the top coefficient's bipoly,
`Bt` the cleared numerator of `dtop`, and `Ds` the cleared numerators of `ds`. -/
theorem gEvEq_gscaleSub_cleared {S : Real → Real} {G : List Real} {A Bt : List (List Real)}
    {b : Real → Real}
    (hb : EvEqF (fun x => pev G x * b x) (fun x => bipev Bt x (exp (S x)))) :
    ∀ (Cs Ds : List (List (List Real))) (ds : List (Real → Real)),
      GEvEq (gscale (pev G) ds) (expCoeffs S Ds) →
        GEvEq (gscale (pev G)
                (gscaleSub (fun x => bipev A x (exp (S x))) b (expCoeffs S Cs) ds))
              (expCoeffs S (gsubNum A Bt Cs Ds)) := by
  intro Cs
  induction Cs with
  | nil => intro _ _ _; exact trivial
  | cons C Cs ih =>
      intro Ds ds hds
      cases ds with
      | nil =>
          cases Ds with
          | nil => exact trivial
          | cons _ _ => exact absurd hds (by intro hh; cases hh)
      | cons d ds =>
          cases Ds with
          | nil => exact absurd hds (by intro hh; cases hh)
          | cons D Ds =>
              refine ⟨?_, ih Ds ds hds.2⟩
              obtain ⟨X₁, hX₁, h₁⟩ := hb
              obtain ⟨X₂, hX₂, h₂⟩ := hds.1
              obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX₁ hX₂
              refine ⟨X, hX, fun x hx => ?_⟩
              have e1 : pev G x * d x = bipev D x (exp (S x)) := h₂ x (le_trans hle2 hx)
              have e2 : pev G x * b x = bipev Bt x (exp (S x)) := h₁ x (le_trans hle1 hx)
              show pev G x * (bipev A x (exp (S x)) * d x - b x * bipev C x (exp (S x)))
                  = bipev (bisub (bimul A D) (bimul Bt C)) x (exp (S x))
              rw [bipev_bisub, bipev_bimul, bipev_bimul, ← e1, ← e2]
              mach_mpoly [pev G x, bipev A x (exp (S x)), d x, b x, bipev C x (exp (S x))]

/-- **The `hPrd` obligation, consumer side.** One polynomial denominator in, membership of
`ClearsToExp` out. -/
theorem clearsToExp_gscaleSub {S : Real → Real} {G : List Real} {A Bt : List (List Real)}
    {b : Real → Real} {Cs Ds : List (List (List Real))} {ds : List (Real → Real)}
    (hG : ¬ EvZeroF (pev G))
    (hb : EvEqF (fun x => pev G x * b x) (fun x => bipev Bt x (exp (S x))))
    (hds : GEvEq (gscale (pev G) ds) (expCoeffs S Ds)) :
    ClearsToExp S (gscaleSub (fun x => bipev A x (exp (S x))) b (expCoeffs S Cs) ds) :=
  ⟨pev G, gsubNum A Bt Cs Ds, evNonvanish_pev hG, gEvEq_gscaleSub_cleared hb Cs Ds ds hds⟩

end MachLib
