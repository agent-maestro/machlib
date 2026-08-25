import MachLib.GermClearedBranch

/-!
# The descent, assembled — no proper relation in the class exists, at any degree

Everything above this module is conditional: each takes a *given* relation `Cs` and a minimality
hypothesis about it. This module removes both. It takes **any** proper relation in the class and
derives `False`, so the conclusion is about the germ, not about a particular relation:

```
no_proper_cleared_relation :
  … → ClearsToExp S fs → GProperRel (log ∘ S) fs → False
```

with `S = P/Q`. No `hmin`, no `Cs`, no split, and **no degree bound** — the `m` that (cf)'s
predecessor could only ever instantiate at `0` is now derived from the minimal relation's own length
and is arbitrary.

## The three pieces, and where each `m = 0` obstruction went

1. `exists_minimal_hmin` (cd) turns the given relation into a shortest one **in the class**. This is
   where the `m = 0` collapse used to happen: unrestricted, `gProperRel_witness`'s `[−u, 1]` is
   always available and forces length two. Restricted to `ClearsToExp`, it is not available — that
   is `clears_witness_forces_algebraic` (cf), and it holds because the degree-one theorem already
   refutes `log S ∈ R(x)(e^S)`.
2. `exists_expCoeffs_of_clears` (cf) replaces the minimal member by an `expCoeffs` image of the same
   length, so `positive_branch_impossible_in` gets the syntactic shape it needs without the class
   having to consist of `expCoeffs` images.
3. `positive_branch_impossible_in` (ci) runs the existing sweep, which was always `m`-general.

## Two facts the assembly needed and the corpus did not have

* **A proper relation has length at least two.** `two_le_length_of_gProperRel`. A one-element proper
  relation `[c]` says `c x + u x·0 = 0`, i.e. `c` *is* eventually zero, contradicting properness.
  Without this the split into `Cs₀ ++ [Cd]` with `Cs₀.length = m + 1` has no `m` to name.
* **`hkd` must be quantified.** Its unrestricted sibling takes
  `¬ Pdvd q (pnsum (m + 1) [1])` for the caller's *fixed* `m`. Here `m` is derived from the minimal
  relation, so the caller cannot know it in advance and the hypothesis is taken `∀ r` — the same
  shape `hchar` and `hcharN` already have, and for the same reason.
-/

namespace MachLib

open Real

/-! ## Two small facts -/

private theorem split_last_len {α : Type} : ∀ (l : List α) (n : Nat), l.length = n + 1 →
    ∃ (l₀ : List α) (a : α), l = l₀ ++ [a] ∧ l₀.length = n := by
  intro l n hn
  have hne : l ≠ [] := by intro h; rw [h] at hn; simp at hn
  refine ⟨l.dropLast, l.getLast hne, (List.dropLast_concat_getLast hne).symm, ?_⟩
  rw [List.length_dropLast, hn]; omega

/-- **A proper relation has at least two coefficients.** `[c]` asserts `c x + u x·0 = 0`, which says
`c` is eventually zero — exactly what properness denies. -/
theorem two_le_length_of_gProperRel {u : Real → Real} {cs : List (Real → Real)}
    (h : GProperRel u cs) : 2 ≤ cs.length := by
  obtain ⟨hrel, cs₀, c, hsplit, hcz⟩ := h
  subst hsplit
  cases cs₀ with
  | nil =>
      exfalso
      refine hcz ?_
      obtain ⟨X, hX, hr⟩ := hrel
      refine ⟨X, hX, fun x hx => ?_⟩
      have hb := hr x hx
      have e : gbipev ([] ++ [c]) x (u x) = c x := by
        show c x + u x * 0 = c x
        mach_ring
      rw [e] at hb
      exact hb
  | cons a as =>
      show 2 ≤ (a :: as ++ [c]).length
      simp

/-! ## The assembly -/

/-- **No proper relation in the class exists — at any degree.**

`log(P/Q)` satisfies no proper relation whose coefficients clear, over one common non-vanishing
polynomial denominator, to polynomials in `x` and `e^(P/Q)`. The degree is not bounded and no
minimality hypothesis is taken: both are produced inside. -/
theorem no_proper_cleared_relation {q P Q : List Real}
    (hq : PIrred q)
    (hchar : ∀ r : Nat, DerivCoprime q (r + 1))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hQz : ¬ EvZeroF (pev Q))
    (hpos : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → 0 < pev P x * (1 / pev Q x))
    (hkd : ∀ r : Nat, ¬ Pdvd q (pnsum (r + 1) [(1 : Real)]))
    {fs : List (Real → Real)}
    (hcl : ClearsToExp (fun y => pev P y * (1 / pev Q y)) fs)
    (hprop : GProperRel (fun y => Real.log (pev P y * (1 / pev Q y))) fs) :
    False := by
  -- (1) a shortest relation IN THE CLASS
  obtain ⟨cs, hcsCl, hcsProp, hmin⟩ := exists_minimal_hmin hcl hprop
  -- (2) replace it by an `expCoeffs` image of the same length
  obtain ⟨Cs, hProper, hlenEq⟩ := exists_expCoeffs_of_clears hcsCl hcsProp
  have hminCs : ∀ ns : List (Real → Real),
      ClearsToExp (fun y => pev P y * (1 / pev Q y)) ns →
      GProperRel (fun y => Real.log (pev P y * (1 / pev Q y))) ns →
        (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs).length ≤ ns.length := by
    intro ns h1 h2
    rw [hlenEq]
    exact hmin ns h1 h2
  -- (3) its length names the degree
  have hCslen : 2 ≤ Cs.length := by
    have h2 := two_le_length_of_gProperRel hProper
    rwa [expCoeffs, List.length_map] at h2
  obtain ⟨m, hm⟩ : ∃ m : Nat, Cs.length = m + 2 := ⟨Cs.length - 2, by omega⟩
  obtain ⟨Cs₀, Cd, hCs, hlen0⟩ := split_last_len Cs (m + 1) (by omega)
  have hmlt : m < Cs₀.length := by omega
  -- the top coefficient is not eventually zero, read off properness
  obtain ⟨hrel, ds₀, d, hd, hdne⟩ := hProper
  have hdCd : d = fun x => bipev Cd x (exp (pev P x * (1 / pev Q x))) := by
    have hsplit2 : expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs
        = expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs₀
          ++ [fun x => bipev Cd x (exp (pev P x * (1 / pev Q x)))] := by
      rw [hCs, expCoeffs_concat]
    have hlast : (ds₀ ++ [d]).getLastD (fun _ => 0)
        = (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs₀
            ++ [fun x => bipev Cd x (exp (pev P x * (1 / pev Q x)))]).getLastD (fun _ => 0) := by
      rw [← hd, hsplit2]
    rwa [List.getLastD_concat, List.getLastD_concat] at hlast
  exact positive_branch_impossible_in (Cs := Cs) (Cs₀ := Cs₀) (Cd := Cd) (Cd1 := Cs₀[m]) (m := m)
    hq hchar hPd hPn hQn hQne hQd hQz hpos (hkd m) hminCs hrel hCs hlen0
    (List.getElem?_eq_getElem hmlt) (hdCd ▸ hdne)

end MachLib
