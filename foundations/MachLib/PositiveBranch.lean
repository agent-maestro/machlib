import MachLib.RelCoeffsSweep
import MachLib.RatLogRelation

/-!
# The `S > 0` branch, assembled

`RatLogRelation` turns a minimal relation for `log(P/Q)` into nil coefficients; `RelCoeffsSweep`
turns nil coefficients into a contradiction. This module joins them, and the only real work between
is the **trim**.

```
GEvRel (log ∘ S) (expCoeffs S Cs)          the hypothesis
      ↓  Cs ↦ Cs.map bitrim                expCoeffs unchanged (bw)
relCoeffs_nil_ratLog                        every coefficient nil
      ↓  bitrim_split on Cd and Cd₁
sweep_impossible / sweep_impossible_nil_second
```

## Why properness, and not just minimality

`minimal_expRel_identity` asks for minimality *among proper relations* — it never asks the relation
at hand to be proper. That is deliberate and it is enough for the identity, but it is **not** enough
for the sweep: if `Cd` were the zero germ, every coefficient of `relCoeffs` would be nil for trivial
reasons and no contradiction would follow.

So this theorem takes `¬ EvZeroF` of the top coefficient — `GProperRel`'s second clause — and that
single hypothesis is what makes `bitrim Cd ≠ []`. The fifth arm the sweep would otherwise have needed
does not exist because this hypothesis removes it.
-/

namespace MachLib

open Real

/-- A germ coefficient that is not eventually zero cannot trim away. -/
theorem bitrim_ne_nil_of_not_evZero {S : Real → Real} {Cd : List (List Real)}
    (h : ¬ EvZeroF (fun x => bipev Cd x (exp (S x)))) : bitrim Cd ≠ [] := by
  intro hz
  refine h ⟨1, le_refl 1, fun x _ => ?_⟩
  show bipev Cd x (exp (S x)) = 0
  rw [← bipev_bitrim Cd x (exp (S x)), hz]
  rfl

/-! ## The branch -/

/-- **`log(P/Q)` is not algebraic over `R(x)(e^(P/Q))`**, for `P/Q` with a pole at the irreducible
`q` and positive on a tail. Stated as: no minimal relation with `R(x)[E]` coefficients exists.

Every hypothesis is either the pole data, the branch's positivity, or the relation's own shape. The
last one, `hCdne`, is `GProperRel`'s second clause: without it the sweep has nothing to bite on. -/
theorem positive_branch_impossible {q P Q : List Real}
    {Cs Cs₀ : List (List (List Real))} {Cd Cd1 : List (List Real)} {m : Nat}
    (hq : PIrred q)
    (hchar : ∀ r : Nat, DerivCoprime q (r + 1))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hQz : ¬ EvZeroF (pev Q))
    (hpos : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → 0 < pev P x * (1 / pev Q x))
    (hkd : ¬ Pdvd q (pnsum (m + 1) [(1 : Real)]))
    (hmin : ∀ ns : List (Real → Real),
      GProperRel (fun y => Real.log (pev P y * (1 / pev Q y))) ns →
        (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs).length ≤ ns.length)
    (hrel : GEvRel (fun y => Real.log (pev P y * (1 / pev Q y)))
      (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs))
    (hCs : Cs = Cs₀ ++ [Cd]) (hlen0 : Cs₀.length = m + 1) (hCd1 : Cs₀[m]? = some Cd1)
    (hCdne : ¬ EvZeroF (fun x => bipev Cd x (exp (pev P x * (1 / pev Q x))))) :
    False := by
  -- the trimmed family: `expCoeffs` is literally unchanged, so every relation hypothesis transfers
  have hnil := relCoeffs_nil_ratLog (q := q) (P := P) (Q := Q)
    (Cs := Cs.map bitrim) (Cs₀ := Cs₀.map bitrim) (Cd := bitrim Cd) (Cd1 := bitrim Cd1) (m := m)
    hq hchar hPd hPn hQn hQne hQd hQz hpos
    (by rw [expCoeffs_map_bitrim]; exact hmin)
    (by rw [expCoeffs_map_bitrim]; exact hrel)
    (by rw [hCs, List.map_append]; rfl)
    (by rw [List.length_map]; exact hlen0)
    (by rw [List.getElem?_map, hCd1]; rfl)
  rcases bitrim_split Cd with hCdz | ⟨As, α, hAs, hαn⟩
  · exact absurd hCdz (bitrim_ne_nil_of_not_evZero hCdne)
  · rw [hAs] at hnil
    rcases bitrim_split Cd1 with hC1z | ⟨Bs, β, hBs, hβn⟩
    · rw [hC1z] at hnil
      exact sweep_impossible_nil_second hq hPd hPn hQn hQne hQd hchar rfl hαn hkd hnil
    · rw [hBs] at hnil
      exact sweep_impossible hq hPd hPn hQn hQne hQd hchar rfl hαn hβn hkd hnil

end MachLib
