/-
# Minimality and vanishing, on a bounded interval

`(gh)` carried the descent to an interval and stopped, saying the minimality route above it —
`all_gcoeffs_evZero_of_shorter'`, `exists_minimal_grel` — was stated over `GProperRel` and `EvZeroF`
and "needs its own twins before the descent can be run to a contradiction."

Those twins are here, and both were cheaper than predicted. Again.

## The predictor is not the shape, it is whether the proof USES the quantifier

Three estimates in a row about this development were wrong in the same direction:

* `(gg)`: "a definition change, so a parallel development, so more work than a lemma swap."
  Per rung it is **less**.
* `(gh)`: minimality "needs its own twins" — `exists_minimal_length'` is generic over any
  `Pr : List α → Prop`, so it is a **statement swap and no new argument**.
* `(gh)`: `all_gcoeffs_evZero_of_shorter'` "delegates to an inductive core that will need porting —
  real work." It ported **verbatim**, first compile.

The useful predictor turns out to be: **does the proof use the eventual quantifier, or merely carry
it?** `gevRel_dropLast` *used* it — merging two tails through `two_bounds'` — and its interval twin
came out shorter, because there is nothing to merge. The induction only *carried* it, so the port is
mechanical. Estimating from "definition change" or "induction" measures the wrong thing.
-/
import MachLib.GermIntervalRel
import MachLib.BipevMinimal

namespace MachLib

open Real

/-- A coefficient that vanishes on the whole interval — the interval twin of `EvZeroF`. -/
def GIntervalZero (c : Real → Real) (a b : Real) : Prop :=
  ∀ x : Real, a < x → x < b → c x = 0

/-- **Genuinely of its stated degree on the interval**: it holds, and its top coefficient does not
vanish identically there. Twin of `GProperRel`. -/
def GIntervalProperRel (u : Real → Real) (cs : List (Real → Real)) (a b : Real) : Prop :=
  GIntervalRel u cs a b ∧ ∃ (cs₀ : List (Real → Real)) (c : Real → Real),
    cs = cs₀ ++ [c] ∧ ¬ GIntervalZero c a b

/-- **Minimality transfers for free.** `exists_minimal_length'` is generic over any
`Pr : List α → Prop` and does not care that the predicate is eventual — so this is the eventual
proof's statement with the predicate swapped, and no new argument at all. -/
theorem exists_minimal_gIntervalRel {u : Real → Real} {cs : List (Real → Real)} {a b : Real}
    (h : GIntervalProperRel u cs a b) :
    ∃ ms : List (Real → Real), GIntervalProperRel u ms a b ∧
      ∀ ns : List (Real → Real), GIntervalProperRel u ns a b → ms.length ≤ ns.length :=
  exists_minimal_length' (fun L => GIntervalProperRel u L a b) h

/-- **Shorter than minimal ⟹ every coefficient vanishes on the interval.**

The eventual proof is structural throughout — minimality, `gevRel_dropLast`, and list splitting — so
this is a direct port with `gIntervalRel_dropLast` in place of its twin. It is the step that lets the
descent run to a contradiction **without ever asking whether the descended relation is proper**. -/
theorem all_gcoeffs_intervalZero_of_shorter {u : Real → Real} {ms : List (Real → Real)}
    {a b : Real}
    (hmin : ∀ ns : List (Real → Real), GIntervalProperRel u ns a b → ms.length ≤ ns.length) :
    ∀ (n : Nat) (es : List (Real → Real)), es.length ≤ n → GIntervalRel u es a b →
      es.length < ms.length → ∀ c : Real → Real, c ∈ es → GIntervalZero c a b := by
  intro n
  induction n with
  | zero =>
      intro es hlen _ _ c hc
      cases es with
      | nil => exact absurd hc (by simp)
      | cons _ _ => simp at hlen
  | succ n ih =>
      intro es hlen hrel hlt c hc
      cases hes : es with
      | nil => rw [hes] at hc; exact absurd hc (by simp)
      | cons _ _ =>
          have hne : es ≠ [] := by rw [hes]; simp
          obtain ⟨es₀, c₀, hsplit⟩ : ∃ es₀ c₀, es = es₀ ++ [c₀] :=
            ⟨es.dropLast, es.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
          have hc₀ : GIntervalZero c₀ a b := by
            rcases Classical.em (GIntervalZero c₀ a b) with h | h
            · exact h
            · exfalso
              have := hmin es ⟨hrel, es₀, c₀, hsplit, h⟩
              omega
          have hrel₀ : GIntervalRel u es₀ a b := by
            rw [hsplit] at hrel
            exact gIntervalRel_dropLast hrel hc₀
          have hlen₀ : es₀.length + 1 = es.length := by rw [hsplit]; simp
          have hIH := ih es₀ (by omega) hrel₀ (by omega)
          rw [hsplit] at hc
          rcases List.mem_append.mp hc with hm | hm
          · exact hIH c hm
          · have hcc : c = c₀ := by simpa using hm
            rw [hcc]; exact hc₀

/-- The budget-free form. -/
theorem all_gcoeffs_intervalZero_of_shorter' {u : Real → Real} {ms es : List (Real → Real)}
    {a b : Real}
    (hmin : ∀ ns : List (Real → Real), GIntervalProperRel u ns a b → ms.length ≤ ns.length)
    (hrel : GIntervalRel u es a b) (hlt : es.length < ms.length) :
    ∀ c : Real → Real, c ∈ es → GIntervalZero c a b :=
  all_gcoeffs_intervalZero_of_shorter hmin es.length es (Nat.le_refl _) hrel hlt

end MachLib
