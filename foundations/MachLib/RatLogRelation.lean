import MachLib.RatLogDeriv

/-!
# The caller: `S = P/Q`, `u = log ∘ S`

Every module from `GermRelation` down to `BipevRearrange` is stated for an *arbitrary* germ: an
arbitrary `u` with an arbitrary derivative `v`, an arbitrary exponent `S`, and clearing conditions
carried as hypotheses rather than constructed. This module is where the `S > 0` branch's actual
germs go in, and it is the only module in the chain that knows `S` is literally `P/Q`.

```
minimal_expRel_identity          u := log ∘ S,  v := ratLogDeriv P Q,  S' := ratFnDeriv P Q
        ↓  the germ identity
evRel_relCoeffs                  hclear := ratFnDeriv_cleared_on_tail,  hv := ratLogDeriv_cleared
        ↓  a relation in e^S
all_coeffs_nil_of_relation       pnorm A = []  for every coefficient
```

Nothing here is new mathematics — it is three `exact`s and the tail bookkeeping between them. That
it *is* only that is the point: the clearing conditions were deliberately shaped so the instantiation
would compose, and this module is the receipt.

## One positivity hypothesis, not two nonvanishing ones

`ratLogDeriv_cleared` wants `pev Q x ≠ 0` **and** `pev P x ≠ 0`. The branch's defining hypothesis
already gives the second: `0 < P·(1/Q)` forces `P ≠ 0`, since a product with a zero factor is `0`.
So the caller carries `¬ EvZeroF (pev Q)` and the positivity, and `¬ EvZeroF (pev P)` never has to be
supplied — `ratLogDeriv_cleared_on_tail` is bypassed in favour of the pointwise form for exactly
that reason. One extra line, one fewer hypothesis, and the hypothesis removed is the one a caller
would have found hardest to produce.

## Where `S > 0` is used, and where it stops

Twice, both at `hu`: `log` is totalised, so `HasDerivAt_log_pos` is the only route to the
derivative, and the same positivity then discharges `P ≠ 0`. The identity, the rearrangement and the
coefficient sweep below never see it — that is what `RatLogDeriv` measured and what the registry
pins.
-/

namespace MachLib

open Real

/-- **`S > 0` already says `P ≠ 0`.** A product with a zero factor is `0`, and `0 < 0` is false. -/
private theorem pev_ne_zero_of_ratFn_pos {p q : Real} (h : 0 < p * (1 / q)) : p ≠ 0 := by
  intro hz
  rw [hz, zero_mul] at h
  exact lt_irrefl_ax 0 h

/-- **The two-coefficient identity, at `S = P/Q` and `u = log ∘ S`, is a relation in `e^S`.**

`D` is `P'Q − PQ'` — the cleared numerator of `S'`, forced by `ratFnDeriv_cleared_on_tail` rather
than chosen here. -/
theorem evRel_relCoeffs_ratLog
    {P Q : List Real} {Cs Cs₀ : List (List (List Real))} {Cd Cd1 : List (List Real)} {m : Nat}
    (hQz : ¬ EvZeroF (pev Q))
    (hpos : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → 0 < pev P x * (1 / pev Q x))
    (hmin : ∀ ns : List (Real → Real),
      GProperRel (fun y => Real.log (pev P y * (1 / pev Q y))) ns →
        (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs).length ≤ ns.length)
    (hrel : GEvRel (fun y => Real.log (pev P y * (1 / pev Q y)))
      (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs))
    (hCs : Cs = Cs₀ ++ [Cd]) (hlen0 : Cs₀.length = m + 1) (hCd1 : Cs₀[m]? = some Cd1) :
    EvRel (fun y => pev P y * (1 / pev Q y))
      (relCoeffs P Q (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) m Cd Cd1) := by
  obtain ⟨X₁, hX₁, hq⟩ := pev_ne_zero_on_tail hQz
  obtain ⟨X₂, hX₂, hp⟩ := hpos
  obtain ⟨X, hX, a1, a2⟩ := two_bounds' hX₁ hX₂
  have hS : ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x →
      HasDerivAt (fun y => pev P y * (1 / pev Q y)) (ratFnDeriv P Q x) x :=
    ⟨X₁, hX₁, fun x hx => hasDerivAt_ratFn P Q x (hq x hx)⟩
  have hu : ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x →
      HasDerivAt (fun y => Real.log (pev P y * (1 / pev Q y))) (ratLogDeriv P Q x) x :=
    ⟨X, hX, fun x hx => hasDerivAt_ratLog P Q x (hq x (le_trans a1 hx)) (hp x (le_trans a2 hx))⟩
  have hv : ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x →
      ratLogDeriv P Q x * (pev P x * pev (pmul Q Q) x)
        = pev Q x * pev (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) x :=
    ⟨X, hX, fun x hx => ratLogDeriv_cleared P Q x (hq x (le_trans a1 hx))
      (pev_ne_zero_of_ratFn_pos (hp x (le_trans a2 hx)))⟩
  exact evRel_relCoeffs (ratFnDeriv_cleared_on_tail hQz) hv
    (minimal_expRel_identity (S' := ratFnDeriv P Q) (v := ratLogDeriv P Q)
      hS hu hmin hrel hCs hlen0 hCd1)

/-- **Every coefficient of the rearrangement is the zero polynomial.** The germ identity has become
a syntactic one, and the coefficient sweep can read equations off it.

The pole hypotheses (`hq`, `hPd`, `hQd`, …) enter here and not before: `evRel_relCoeffs_ratLog`
needs only that `Q` is not eventually zero, because a relation is a relation whatever `P` and `Q`
do. It is turning the relation into *nil coefficients* that needs `e^S` to be transcendental, and
that is what the pole at `q` buys. -/
theorem relCoeffs_nil_ratLog {q P Q : List Real}
    {Cs Cs₀ : List (List (List Real))} {Cd Cd1 : List (List Real)} {m : Nat}
    (hq : PIrred q)
    (hchar : ∀ r : Nat, DerivCoprime q r)
    (hcharN : ∀ r : Nat, PNormal (pnsum r (pderiv q)))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hQz : ¬ EvZeroF (pev Q))
    (hpos : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → 0 < pev P x * (1 / pev Q x))
    (hmin : ∀ ns : List (Real → Real),
      GProperRel (fun y => Real.log (pev P y * (1 / pev Q y))) ns →
        (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs).length ≤ ns.length)
    (hrel : GEvRel (fun y => Real.log (pev P y * (1 / pev Q y)))
      (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs))
    (hCs : Cs = Cs₀ ++ [Cd]) (hlen0 : Cs₀.length = m + 1) (hCd1 : Cs₀[m]? = some Cd1) :
    ∀ A : List Real,
      A ∈ relCoeffs P Q (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) m Cd Cd1 →
        pnorm A = [] :=
  all_coeffs_nil_of_relation hq hchar hcharN hPd hPn hQn hQne hQd hQz
    (evRel_relCoeffs_ratLog hQz hpos hmin hrel hCs hlen0 hCd1)

end MachLib
