/-
# `GIntervalRel` — the germ descent on a bounded component

`(gg)` scoped this and declined to start it: `GEvRel` is **eventual by definition**, so carrying the
descent to a bounded component needs an interval analogue of the *relation type*, not a lemma swap.
This is that development, and the first four rungs went through.

`OneQueryLevelSet`'s residue is a relation on a bounded component of `{S > 0}`, where no tail
reaches. `GEvRel` could only ever speak about a tail, so the descent — the machinery that eliminates
`y = Fbasis (S x)` — could not be pointed at the residue at all. It can now.

## The twins keep coming out SIMPLER than the originals

`gevRel_dropLast` spends most of its proof on `two_bounds'`, merging the relation's tail with the
coefficient's. Its interval twin is a single `gbipev_drop_top` rewrite: both hypotheses live on the
*same* `(a,b)`, so there is nothing to intersect. "Eventually" is a quantifier that must be merged;
an interval is not.

That was not the prediction. `(gg)` expected a parallel development to cost more than the log
junction's two lemma swaps, and per-rung it is costing less — the eventual bookkeeping was a tax the
interval version does not pay.

## Scope

Four rungs: the relation type, the differentiated-list step, dropping a zero top coefficient, and the
descent itself. What is **not** here is the minimality route above it —
`all_gcoeffs_evZero_of_shorter'`, `exists_minimal_grel`, `minimal_grel_identity` — which is stated
over `GProperRel` and `EvZeroF` and needs its own twins before the descent can be run to a
contradiction. This module makes the descent available on a component; it does not close anything.
-/
import MachLib.GermDerivInterval

namespace MachLib

open Real

/-- **A germ relation on a bounded interval.**

`GEvRel u cs := ∃ X, 1 ≤ X ∧ ∀ x ≥ X, gbipev cs x (u x) = 0` is **eventual by definition**, so no
amount of lemma-swapping carries the descent to a bounded component. This is the interval analogue:
same content, no tail. -/
def GIntervalRel (u : Real → Real) (cs : List (Real → Real)) (a b : Real) : Prop :=
  ∀ x : Real, a < x → x < b → gbipev cs x (u x) = 0

/-- **The differentiated list still satisfies the relation, on an interval.**

A direct port of `fbasisDerivList_rel`: its body calls the brick — now
`fbasis_relation_differentiates_on_interval` — and then does pure `mach_mpoly` algebra that never
mentions a ray. -/
theorem fbasisDerivList_rel_on_interval {S s : Real → Real} {a b : Real}
    (hS : ∀ x : Real, a < x → x < b → HasDerivAt S (s x) x)
    (hpos : ∀ x : Real, a < x → x < b → 0 < S x)
    (cs es : List (Real → Real))
    (hd : ∀ x : Real, a < x → x < b → GDerivAt x cs es)
    (hrel : GIntervalRel (fun x => Fbasis (S x)) cs a b) :
    GIntervalRel (fun x => Fbasis (S x)) (fbasisDerivList S s cs es) a b := by
  intro x hax hxb
  have h := fbasis_relation_differentiates_on_interval hS hpos cs es hd hrel x hax hxb
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

/-- **Dropping an identically-zero top coefficient, on an interval.**

The eventual version spends most of its proof on `two_bounds'`, merging the relation's tail with the
coefficient's. On an interval there is nothing to merge — both hypotheses live on the *same* `(a,b)` —
so the proof is the single `gbipev_drop_top` rewrite with no bookkeeping around it.

Worth noting as a pattern: interval twins keep coming out **simpler** than their eventual originals,
because "eventually" is a quantifier that has to be intersected and an interval is not. -/
theorem gIntervalRel_dropLast {u : Real → Real} {cs₀ : List (Real → Real)} {c : Real → Real}
    {a b : Real} (hrel : GIntervalRel u (cs₀ ++ [c]) a b)
    (hc : ∀ x : Real, a < x → x < b → c x = 0) : GIntervalRel u cs₀ a b := by
  intro x hax hxb
  have hb := hrel x hax hxb
  rw [gbipev_drop_top (cs := cs₀) (hc x hax hxb)] at hb
  exact hb

/-- **The descent, on an interval.** The interval twin of `fbasisDeriv_descends`, and the point of
the whole exercise: it yields a shorter relation ON THE COMPONENT, where `GEvRel` could only ever
speak about a tail. -/
theorem fbasisDeriv_descends_on_interval {S s : Real → Real} {a b : Real}
    (hS : ∀ x : Real, a < x → x < b → HasDerivAt S (s x) x)
    (hpos : ∀ x : Real, a < x → x < b → 0 < S x)
    (c : Real → Real) (cs es : List (Real → Real))
    (hlen : es.length = (c :: cs).length)
    (hd : ∀ x : Real, a < x → x < b → GDerivAt x (c :: cs) es)
    (hrel : GIntervalRel (fun x => Fbasis (S x)) (c :: cs) a b) :
    ∃ L : List (Real → Real),
      L.length = (c :: cs).length ∧ GIntervalRel (fun x => Fbasis (S x)) L a b := by
  obtain ⟨L, z, heq, hz, hLlen⟩ := fbasisDerivList_append_zero S s c cs es hlen
  refine ⟨L, hLlen, ?_⟩
  refine gIntervalRel_dropLast (c := z) ?_ (fun x _ _ => hz x)
  rw [← heq]
  exact fbasisDerivList_rel_on_interval hS hpos (c :: cs) es hd hrel

end MachLib
