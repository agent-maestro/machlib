/-
# The germ-derivative descent's entry point, on an interval

`OneQueryLevelSet`'s residue is a relation `Σ N_k(x)·y^k = 0` with `y = Fbasis (S x)` **on a bounded
component**, where no tail reaches. The machinery that eliminates `y` is the germ-derivative descent
in `GermDerivFbasis`, and it was ray-shaped throughout — so it could never touch the residue.

Its *brick*, `fbasis_relation_differentiates`, uses the ray in exactly one place: its final line.
Everything upstream is pointwise. So the twin is the same proof with
`deriv_eq_zero_of_zero_on_ray` swapped out, exactly as in `(gb)`.

## How far this reaches, and where it stops — stated so the next session does not re-derive it

**It stops at the descent's output type.** `fbasisDeriv_descends` concludes
`GEvRel (fun x => Fbasis (S x)) L`, and

    GEvRel u cs  :=  ∃ X, 1 ≤ X ∧ ∀ x ≥ X, gbipev cs x (u x) = 0

is **eventual by definition** (`GermRelation:49`). So the remaining 42 ray-shaped sites in
`GermDerivFbasis` are not a lemma swap: carrying the descent to an interval needs an interval
analogue of the *relation type* — a `GIntervalRel` — and the chain re-proved against it. A parallel
development, not a substitution.

That is a real scoping result. `(ga)`–`(gc)` interval-ised the log junction by swapping two lemmas
because its hypotheses and conclusion were both polynomial identities. This arc's conclusion is an
eventual predicate, and no amount of lemma-swapping changes a definition.
-/
import MachLib.LogRatDerivInterval
import MachLib.GermDerivFbasis

namespace MachLib

open Real

/-- The `g = 0` instance of the interval twin — a function vanishing on `(a,b)` has vanishing
derivative at interior points. -/
theorem deriv_eq_zero_of_zero_on_interval {f : Real → Real} {a b x d : Real}
    (hax : a < x) (hxb : x < b) (hzero : ∀ y : Real, a < y → y < b → f y = 0)
    (hd : HasDerivAt f d x) : d = 0 :=
  deriv_eq_of_eq_on_interval hax hxb hzero hd (HasDerivAt_const 0 x)

/-- **The descent's brick, on an interval.**

`fbasis_relation_differentiates` uses the ray in exactly one place — its final line. Everything
upstream (`fbasisComp_hasDerivAt`, `gbipev_hasDerivAt`) is pointwise, so the twin is the same proof
with `deriv_eq_zero_of_zero_on_ray` swapped out.

This is the entry point of the germ-derivative descent, which is the machinery that eliminates
`y = Fbasis (S x)` from a relation. `OneQueryLevelSet`'s residue is such a relation **on a bounded
component**, where no tail reaches — so a ray-shaped descent could never touch it. -/
theorem fbasis_relation_differentiates_on_interval {S s : Real → Real} {a b : Real}
    (hS : ∀ x : Real, a < x → x < b → HasDerivAt S (s x) x)
    (hpos : ∀ x : Real, a < x → x < b → 0 < S x)
    (cs es : List (Real → Real))
    (hd : ∀ x : Real, a < x → x < b → GDerivAt x cs es)
    (hrel : ∀ x : Real, a < x → x < b → gbipev cs x (Fbasis (S x)) = 0) :
    ∀ x : Real, a < x → x < b →
      gbipev es x (Fbasis (S x))
        + ((exp (S x) + 1 / S x) * s x) * gydiff cs x (Fbasis (S x)) = 0 := by
  intro x hax hxb
  have hchain : HasDerivAt (fun t => Fbasis (S t)) ((exp (S x) + 1 / S x) * s x) x :=
    fbasisComp_hasDerivAt (hS x hax hxb) (hpos x hax hxb)
  have hfull := gbipev_hasDerivAt hchain cs es (hd x hax hxb)
  exact deriv_eq_zero_of_zero_on_interval hax hxb hrel hfull

end MachLib
