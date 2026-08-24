import MachLib.ExpCoeffIdentityClass

/-!
# `hmin` is dischargeable from a single witness

(cb)–(cd) made minimality a parameter: `hmin` now ranges over relations satisfying a class predicate
`Pr` rather than over all germ-coefficient lists. That is only worth anything if the restricted
`hmin` can actually be produced, and this module says exactly what it costs — **one witness**.

```
exists_minimal_hmin :
  Pr ms → GProperRel u ms →
    ∃ cs, Pr cs ∧ GProperRel u cs ∧ ∀ ns, Pr ns → GProperRel u ns → cs.length ≤ ns.length
```

Given *any* proper relation in the class, there is a shortest one, and its minimality statement is
`hmin`'s exact shape. `exists_minimal_length'` (`BipevMinimal`) does the work; the only content here
is applying it to the conjunction `Pr ∧ GProperRel` rather than to either alone.

## What this reduces the fourth module to

Before: "supply a class and discharge minimality inside it." After: **supply a class, prove it closed
under `dropLast` and under the `gscaleSub` step, and exhibit one proper relation in it.** The
minimality obligation disappears — it was never the hard part, it just looked like it.

What remains genuinely hard is the *other* direction: `minimal_expRel_identity_in` wants `cs` to be
an `expCoeffs` image, and the minimal element of a class need not be one. A class whose members all
clear to `expCoeffs` images over a common denominator would settle that, and is the shape to try —
`gscaleSub` forms products and differences, so denominators multiply and numerators stay `Bipoly`.
Not attempted here.

## Why the conjunction and not two applications

`exists_minimal_length'` minimises one predicate. Minimising `Pr` first and then `GProperRel` inside
it would give the shortest member of the class, which need not be proper, and then a shortest proper
relation *among lists of that length* — not the shortest proper member. The conjunction is the
statement wanted, and it is the one `hmin` compares against.
-/

namespace MachLib

open Real

/-- **One witness gives `hmin`.** From any proper relation in the class, a shortest one — and its
minimality is exactly the hypothesis (cb)–(cd) take. -/
theorem exists_minimal_hmin {u : Real → Real} {Pr : List (Real → Real) → Prop}
    {ms : List (Real → Real)} (hPr : Pr ms) (hprop : GProperRel u ms) :
    ∃ cs : List (Real → Real), Pr cs ∧ GProperRel u cs ∧
      ∀ ns : List (Real → Real), Pr ns → GProperRel u ns → cs.length ≤ ns.length := by
  obtain ⟨cs, ⟨hcsPr, hcsProp⟩, hmin⟩ :=
    exists_minimal_length' (fun L => Pr L ∧ GProperRel u L) (Ls := ms) ⟨hPr, hprop⟩
  exact ⟨cs, hcsPr, hcsProp, fun ns h1 h2 => hmin ns ⟨h1, h2⟩⟩

/-- The `Pr := True` reading: every germ with a proper relation has a shortest one. Kept because it
is the sanity check that the conjunction did not lose the unrestricted case. -/
theorem exists_minimal_hmin_unrestricted {u : Real → Real} {ms : List (Real → Real)}
    (hprop : GProperRel u ms) :
    ∃ cs : List (Real → Real), GProperRel u cs ∧
      ∀ ns : List (Real → Real), GProperRel u ns → cs.length ≤ ns.length := by
  obtain ⟨cs, _, hcsProp, hmin⟩ := exists_minimal_hmin (Pr := fun _ => True) trivial hprop
  exact ⟨cs, hcsProp, fun ns h => hmin ns trivial h⟩

end MachLib
