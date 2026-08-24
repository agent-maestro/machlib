import MachLib.MinimalityScope

/-!
# Minimality restricted to a class — the weakening `MinimalityScope` says is needed

`MinimalityScope` shows that `hmin`, quantified over **arbitrary** germ-coefficient lists, forces
`m = 0`: every germ has a proper relation of length two, so nothing longer can be minimal. That caps
the whole `S > 0` arc at degree one, while step 1 of the `bf` decomposition produces degree `d`.

The cause is that `hmin` is far stronger than its use. It is applied in exactly **one** place —
`all_gcoeffs_evZero_of_shorter` — and there only to the derived relation and its `dropLast`
truncations, never to an arbitrary list. So it may be restricted to any class closed under
`dropLast`, and the proof is unchanged.

This module states that version. `Pr` is a parameter rather than a fixed class, so the closure
obligation stays with whoever instantiates it; for the `S > 0` arc the class that closes is germs of
the form *(rational in `x`)·(polynomial in `E`)* — `R(x)(E)`, not `R(x)[E]`, because the derivative
coefficients carry `S'`, which is rational.

## Not two versions of one theorem

`all_gcoeffs_evZero_of_shorter'` is recovered below as the `Pr := fun _ => True` instance, so the
existing statement is a **corollary** of this one rather than a sibling. That is the whole reason to
state it here instead of editing `GermRelation` in place: the general form subsumes the specific one
and nothing is left to reconcile.

## What this does *not* yet do

`minimal_grel_identity` and `minimal_expRel_identity` still take the unrestricted `hmin`. Threading
`Pr` through them, and instantiating it at a class for which minimality is dischargeable, is the
remaining work — and until that lands, `positive_branch_impossible` is still a degree-one statement.
This module removes the obstruction at the only place it actually sits; it does not by itself widen
anything.
-/

namespace MachLib

open Real

/-- **The descent, with minimality restricted to a class.** `Pr` need only be closed under dropping
the last coefficient — which is the only way the recursion ever moves. -/
theorem all_gcoeffs_evZero_of_shorter_in {u : Real → Real} {ms : List (Real → Real)}
    {Pr : List (Real → Real) → Prop}
    (hdrop : ∀ (es : List (Real → Real)) (c : Real → Real), Pr (es ++ [c]) → Pr es)
    (hmin : ∀ ns : List (Real → Real), Pr ns → GProperRel u ns → ms.length ≤ ns.length) :
    ∀ (n : Nat) (es : List (Real → Real)), Pr es → es.length ≤ n → GEvRel u es →
      es.length < ms.length → ∀ c : Real → Real, c ∈ es → EvZeroF c := by
  intro n
  induction n with
  | zero =>
      intro es _ hlen _ _ c hc
      cases es with
      | nil => exact absurd hc (by simp)
      | cons _ _ => simp at hlen
  | succ n ih =>
      intro es hPr hlen hrel hlt c hc
      cases hes : es with
      | nil => rw [hes] at hc; exact absurd hc (by simp)
      | cons _ _ =>
          have hne : es ≠ [] := by rw [hes]; simp
          obtain ⟨es₀, c₀, hsplit⟩ : ∃ es₀ c₀, es = es₀ ++ [c₀] :=
            ⟨es.dropLast, es.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
          have hc₀ : EvZeroF c₀ := by
            rcases Classical.em (EvZeroF c₀) with h | h
            · exact h
            · exfalso
              have := hmin es hPr ⟨hrel, es₀, c₀, hsplit, h⟩
              omega
          have hrel₀ : GEvRel u es₀ := by
            rw [hsplit] at hrel
            exact gevRel_dropLast hrel hc₀
          have hlen₀ : es₀.length + 1 = es.length := by rw [hsplit]; simp
          have hPr₀ : Pr es₀ := hdrop es₀ c₀ (hsplit ▸ hPr)
          have hIH := ih es₀ hPr₀ (by omega) hrel₀ (by omega)
          rw [hsplit] at hc
          rcases List.mem_append.mp hc with hm | hm
          · exact hIH c hm
          · have : c = c₀ := by simpa using hm
            rw [this]; exact hc₀

/-- The budget-free form. -/
theorem all_gcoeffs_evZero_of_shorter_in' {u : Real → Real} {ms es : List (Real → Real)}
    {Pr : List (Real → Real) → Prop}
    (hdrop : ∀ (fs : List (Real → Real)) (c : Real → Real), Pr (fs ++ [c]) → Pr fs)
    (hmin : ∀ ns : List (Real → Real), Pr ns → GProperRel u ns → ms.length ≤ ns.length)
    (hPr : Pr es) (hrel : GEvRel u es) (hlt : es.length < ms.length) :
    ∀ c : Real → Real, c ∈ es → EvZeroF c :=
  all_gcoeffs_evZero_of_shorter_in hdrop hmin es.length es hPr (Nat.le_refl _) hrel hlt

/-- **The existing statement is the `Pr := True` instance**, so this is a generalisation rather than
a sibling. -/
theorem all_gcoeffs_evZero_of_shorter_unrestricted {u : Real → Real} {ms es : List (Real → Real)}
    (hmin : ∀ ns : List (Real → Real), GProperRel u ns → ms.length ≤ ns.length)
    (hrel : GEvRel u es) (hlt : es.length < ms.length) :
    ∀ c : Real → Real, c ∈ es → EvZeroF c :=
  all_gcoeffs_evZero_of_shorter_in' (Pr := fun _ => True)
    (fun _ _ _ => trivial) (fun ns _ hp => hmin ns hp) trivial hrel hlt

end MachLib
