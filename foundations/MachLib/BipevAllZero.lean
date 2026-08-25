import MachLib.BipevGerm

/-!
# A relation in `e^S` has every coefficient zero

`proper_relation_impossible` says no *proper* relation exists. The `S > 0` coefficient sweep needs
the same fact in a different shape: given **any** eventually-holding relation
`Σⱼ pⱼ(x)·e^(S x)ʲ = 0`, every `pⱼ` is the zero polynomial.

The two are the same statement read from opposite ends, and the bridge is already built. If some
coefficient were not eventually zero, truncating at the last such would produce a proper relation.
`all_coeffs_evZero_of_shorter` performs exactly that descent — it only ever needed a *bound* to
descend against, and when no proper relation exists at all the bound can be anything.

## The vacuous minimality

`all_coeffs_evZero_of_shorter` takes `hmin : ∀ Ns, ProperRel S Ns → ms.length ≤ Ns.length`. With
`proper_relation_impossible` in hand that hypothesis holds **vacuously**, for any `ms` whatever — so
take `ms` longer than the relation and the descent runs with nothing to descend against. No new
induction, no new module of machinery: six lines.

This is what the earlier design note meant by keeping the descent free of `pev`. It was generalised
for the germ layer, and the payment comes back here, in the polynomial layer it started in.
-/

namespace MachLib

open Real

/-- **Every coefficient of a relation in `e^S` is eventually zero.** No properness hypothesis: the
theorem is exactly that properness is impossible. -/
theorem all_coeffs_evZero_of_relation {P Q q : List Real}
    (hq : PIrred q)
    (hchar : ∀ r : Nat, DerivCoprime q (r + 1))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hQz : ¬ EvZeroF (pev Q))
    {Ls : List (List Real)}
    (hrel : EvRel (fun y => pev P y * (1 / pev Q y)) Ls) :
    ∀ A : List Real, A ∈ Ls → EvZeroF (pev A) := by
  refine all_coeffs_evZero_of_shorter'
    (Ms := List.replicate (Ls.length + 1) ([] : List Real))
    (fun Ns h => absurd h (fun hp =>
      proper_relation_impossible hq hchar hPd hPn hQn hQne hQd hQz hp)) hrel ?_
  simp

/-- The polynomial form: **zero as a germ is zero as a polynomial**, coefficient by coefficient.
This is the shape the `S > 0` sweep consumes — it turns a germ identity in `e^S` into an identity
between the syntactic coefficient polynomials. -/
theorem all_coeffs_nil_of_relation {P Q q : List Real}
    (hq : PIrred q)
    (hchar : ∀ r : Nat, DerivCoprime q (r + 1))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hQz : ¬ EvZeroF (pev Q))
    {Ls : List (List Real)}
    (hrel : EvRel (fun y => pev P y * (1 / pev Q y)) Ls) :
    ∀ A : List Real, A ∈ Ls → pnorm A = [] := fun A hA =>
  pnorm_eq_nil_of_evZero
    (all_coeffs_evZero_of_relation hq hchar hPd hPn hQn hQne hQd hQz hrel A hA)

end MachLib
