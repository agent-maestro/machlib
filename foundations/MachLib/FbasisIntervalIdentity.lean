/-
# Parity: the `Fbasis ∘ S` layer, on a bounded interval

Everything the tail arc can say about `Fbasis ∘ S`'s minimal relation, the interval arc now says on a
bounded component. This is the top of the chain begun in `(gg)`.

The eventual `fbasis_top_two_identity` opens with `two_bounds'`, merging the derivative hypothesis
with the positivity hypothesis. On an interval both already hold on `(a,b)`, so this is the chain rule
handed straight to `minimal_gIntervalRel_identity` — a one-liner.

**The footprint measures it.** 38 axioms against the original's 39: the tail-merge lemma is simply
not in the interval version's dependency closure. Five twins, five times shorter, and here the
difference is visible in `#print axioms` rather than in line count.
-/
import MachLib.GermIntervalIdentity
import MachLib.GermDerivFbasis

namespace MachLib

open Real

/-- **`Fbasis ∘ S`'s top-two-coefficient identity, on a bounded interval.**

The eventual version opens with `two_bounds'`, merging the derivative hypothesis with the positivity
hypothesis. On an interval both already hold on `(a,b)`, so the whole proof is the chain rule handed
straight to `minimal_gIntervalRel_identity` — a **one-liner**, and the fifth twin in this arc to come
out shorter than its original for the same reason.

This puts the interval route at parity with the eventual one: everything the tail arc can say about
`Fbasis ∘ S`'s minimal relation, the interval arc now says on a bounded component. -/
theorem fbasis_top_two_identity_on_interval {S s : Real → Real}
    {cs es cs₀ es₀ : List (Real → Real)} {cd ed cd1 ed1 : Real → Real} {m : Nat} {a b : Real}
    (hS : ∀ x : Real, a < x → x < b → HasDerivAt S (s x) x)
    (hpos : ∀ x : Real, a < x → x < b → 0 < S x)
    (hdd : ∀ x : Real, a < x → x < b → GDerivAt x cs es)
    (hmin : ∀ ns : List (Real → Real),
        GIntervalProperRel (fun t => Fbasis (S t)) ns a b → cs.length ≤ ns.length)
    (hrel : GIntervalRel (fun t => Fbasis (S t)) cs a b)
    (hcs : cs = cs₀ ++ [cd]) (hes : es = es₀ ++ [ed])
    (hlen0 : cs₀.length = m + 1) (hlenes : es₀.length = m + 1)
    (hcd1 : cs₀[m]? = some cd1) (hed1 : es₀[m]? = some ed1) :
    GIntervalZero (fun x => cd x *
        (ed1 x + ((exp (S x) + 1 / S x) * s x) * (natMul (m + 1) 1 * cd x))
      - ed x * cd1 x) a b :=
  minimal_gIntervalRel_identity
    (fun x hax hxb => fbasisComp_hasDerivAt (hS x hax hxb) (hpos x hax hxb))
    hdd hmin hrel hcs hes hlen0 hlenes hcd1 hed1

end MachLib
