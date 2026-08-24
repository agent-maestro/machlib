import MachLib.GermRelationClass
import MachLib.GermDerivEntry

/-!
# The two-coefficient identity, with minimality restricted to a class

`GermRelationClass` weakened the descent's `hmin`; this carries the weakening up one level, to the
theorem that actually produces the identity. Same pattern: `Pr` is a parameter, and
`minimal_grel_identity` is recovered below as the `Pr := fun _ => True` instance, so the general form
**subsumes** the specific one.

## The closure obligation is stated at the split, not abstractly

`minimal_grel_identity` obtains `ds₀` and `dtop` *inside* its proof, by splitting `gdrel v cs es`.
A caller cannot name them, so demanding `Pr (gscaleSub cd dtop cs₀ ds₀)` directly would be
unusable. The hypothesis is instead **universally quantified over the split**:

```
hPrd : ∀ ds₀ dtop, gdrel v cs es = ds₀ ++ [dtop] → Pr (gscaleSub cd dtop cs₀ ds₀)
```

which the caller can discharge without knowing which split occurs, because there is only one. This
is the same discipline as `BipevRearrange` taking the clearing conditions rather than the model:
**say what must hold of the thing, not which thing it is.**

## What is still not done

`minimal_expRel_identity` — the `R(x)[E]`-coefficient instantiation — still takes the unrestricted
`hmin`, and no concrete class has been supplied. `positive_branch_impossible` remains a degree-one
statement until both land.
-/

namespace MachLib

open Real

/-- `split_last` and `evZeroF_congr` are `private` in `GermDerivEntry`; both are restated here rather
than un-privatising them, so that module's interface is untouched by a generalisation that lives
outside it. -/
private theorem evZeroF_congr' {f g : Real → Real} (h : EvZeroF f) (he : ∀ x, f x = g x) :
    EvZeroF g := by
  obtain ⟨X, hX, hf⟩ := h
  exact ⟨X, hX, fun x hx => (he x) ▸ hf x hx⟩


private theorem split_last' {α : Type} : ∀ (l : List α) (n : Nat), l.length = n + 1 →
    ∃ (l₀ : List α) (a : α), l = l₀ ++ [a] ∧ l₀.length = n := by
  intro l n hn
  have hne : l ≠ [] := by intro h; rw [h] at hn; simp at hn
  refine ⟨l.dropLast, l.getLast hne, (List.dropLast_concat_getLast hne).symm, ?_⟩
  rw [List.length_dropLast, hn]; omega

/-- **The identity, with minimality restricted to `Pr`.** The only change from
`minimal_grel_identity` is which relations `hmin` must beat. -/
theorem minimal_grel_identity_in {u v : Real → Real} {cs es cs₀ es₀ : List (Real → Real)}
    {cd ed cd1 ed1 : Real → Real} {m : Nat} {Pr : List (Real → Real) → Prop}
    (hu : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → HasDerivAt u (v x) x)
    (hdd : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → GDerivAt x cs es)
    (hdrop : ∀ (fs : List (Real → Real)) (c : Real → Real), Pr (fs ++ [c]) → Pr fs)
    (hPrd : ∀ (ds₀ : List (Real → Real)) (dtop : Real → Real),
      gdrel v cs es = ds₀ ++ [dtop] → Pr (gscaleSub cd dtop cs₀ ds₀))
    (hmin : ∀ ns : List (Real → Real), Pr ns → GProperRel u ns → cs.length ≤ ns.length)
    (hrel : GEvRel u cs)
    (hcs : cs = cs₀ ++ [cd]) (hes : es = es₀ ++ [ed])
    (hlen0 : cs₀.length = m + 1) (hlenes : es₀.length = m + 1)
    (hcd1 : cs₀[m]? = some cd1) (hed1 : es₀[m]? = some ed1) :
    EvZeroF (fun x => cd x * (ed1 x + v x * (natMul (m + 1) 1 * cd x)) - ed x * cd1 x) := by
  have hlen : cs.length = m + 2 := by rw [hcs]; simp [hlen0]
  have hlenE : es.length = m + 2 := by rw [hes]; simp [hlenes]
  have hcsIdx : cs[m + 1]? = some cd := by
    rw [hcs, List.getElem?_append_right (by omega), hlen0]; simp
  have hesTop : es[m + 1]? = some ed := by
    rw [hes, List.getElem?_append_right (by omega), hlenes]; simp
  have hesIdx : es[m]? = some ed1 := by
    rw [hes, List.getElem?_append_left (by omega)]; exact hed1
  have hdrel : GEvRel u (gdrel v cs es) := gEvRel_gdrel hu hdd hrel
  have hdlen : (gdrel v cs es).length = m + 2 := by
    rw [gdrel_length (by rw [hlen, hlenE]), hlen]
  obtain ⟨ds₀, dtop, hsplit, hds0⟩ := split_last' (gdrel v cs es) (m + 1) hdlen
  obtain ⟨bt, hbt, hbtval⟩ := gdrel_getElem_top (v := v) hesTop hlen
  have hdtop : dtop = bt := by
    have : (gdrel v cs es)[m + 1]? = some dtop := by
      rw [hsplit, List.getElem?_append_right (by omega), hds0]; simp
    rw [this] at hbt; exact Option.some_inj.mp hbt
  obtain ⟨b', hb', hb'val⟩ := gdrel_getElem (v := v) hesIdx hcsIdx
  have hds0Idx : ds₀[m]? = some b' := by
    rw [← hb', hsplit, List.getElem?_append_left (by omega)]
  have hgs : GEvRel u (gscaleSub cd dtop cs₀ ds₀) :=
    gcancel_top (by rw [hlen0, hds0]) (hcs ▸ hrel) (hsplit ▸ hdrel)
  have hgslen : (gscaleSub cd dtop cs₀ ds₀).length = m + 1 := by
    rw [gscaleSub_length cd dtop cs₀ ds₀ (by rw [hlen0, hds0]), hlen0]
  have hentry := gscaleSub_getElem cd dtop cs₀ ds₀ m cd1 b' hcd1 hds0Idx
  have hall := all_gcoeffs_evZero_of_shorter_in' hdrop hmin (hPrd ds₀ dtop hsplit) hgs (by omega)
  refine evZeroF_congr' (hall _ (List.mem_of_getElem? hentry)) (fun x => ?_)
  show cd x * b' x - dtop x * cd1 x = _
  rw [hb'val x, hdtop, hbtval x]

/-- **`minimal_grel_identity` is the `Pr := True` instance**, so this is a generalisation rather than
a second theorem to keep in step. -/
theorem minimal_grel_identity_unrestricted {u v : Real → Real}
    {cs es cs₀ es₀ : List (Real → Real)} {cd ed cd1 ed1 : Real → Real} {m : Nat}
    (hu : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → HasDerivAt u (v x) x)
    (hdd : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → GDerivAt x cs es)
    (hmin : ∀ ns : List (Real → Real), GProperRel u ns → cs.length ≤ ns.length)
    (hrel : GEvRel u cs)
    (hcs : cs = cs₀ ++ [cd]) (hes : es = es₀ ++ [ed])
    (hlen0 : cs₀.length = m + 1) (hlenes : es₀.length = m + 1)
    (hcd1 : cs₀[m]? = some cd1) (hed1 : es₀[m]? = some ed1) :
    EvZeroF (fun x => cd x * (ed1 x + v x * (natMul (m + 1) 1 * cd x)) - ed x * cd1 x) :=
  minimal_grel_identity_in (Pr := fun _ => True) hu hdd (fun _ _ _ => trivial)
    (fun _ _ _ => trivial) (fun ns _ hp => hmin ns hp) hrel hcs hes hlen0 hlenes hcd1 hed1

end MachLib
