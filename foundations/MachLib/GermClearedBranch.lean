import MachLib.GermClearedRatLog
import MachLib.RatLogRelation

/-!
# The branch, with minimality restricted to the class

`RatLogRelation` and `PositiveBranch` are the last two layers still taking the **unrestricted**
`hmin`, and neither inspects it — both pass it straight down. So both restate with `Pr` threaded
through, exactly as (cb)–(cd) did for the three layers above them, and the bodies are unchanged
apart from which identity theorem they call.

Restated **beside** the originals rather than edited in place, for the same reason (cb) gave: the
originals stay valid, nothing has to be reconciled, and each `_in` form has its unrestricted sibling
recoverable as an instance.

## What is now concrete

`clearsToExp_hPrd_ratLog` (ch) discharges `hPrd` from `¬ EvZeroF (pev P)` and `¬ EvZeroF (pev Q)`, and
the first of those is **not a new hypothesis** — the branch's positivity already forces it, since a
product with a zero factor is `0`. `not_evZeroF_pev_of_pos` is that step, and it is the reason
`positive_branch_impossible_in` takes no hypothesis its unrestricted sibling did not.
-/

namespace MachLib

open Real

/-! ## Positivity already gives `P ≠ 0` -/

private theorem pev_ne_zero_of_pos {p q : Real} (h : 0 < p * (1 / q)) : p ≠ 0 := by
  intro hz
  rw [hz, zero_mul] at h
  exact lt_irrefl_ax 0 h

/-- **The branch's positivity forces `P` not eventually zero.** No new hypothesis enters with the
class: `clearsToExp_hPrd_ratLog` wants this and the caller already has it. -/
theorem not_evZeroF_pev_of_pos {P Q : List Real}
    (hpos : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → 0 < pev P x * (1 / pev Q x)) :
    ¬ EvZeroF (pev P) := by
  intro hz
  obtain ⟨X₁, hX₁, h₁⟩ := hpos
  obtain ⟨X₂, hX₂, h₂⟩ := hz
  obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX₁ hX₂
  exact pev_ne_zero_of_pos (h₁ X hle1) (h₂ X hle2)

/-! ## The rearrangement, restricted -/

/-- **`evRel_relCoeffs_ratLog`, with `hmin` restricted to `ClearsToExp`.** Body unchanged; only the
identity theorem differs, and `hdrop`/`hPrd` are discharged rather than assumed. -/
theorem evRel_relCoeffs_ratLog_in
    {P Q : List Real} {Cs Cs₀ : List (List (List Real))} {Cd Cd1 : List (List Real)} {m : Nat}
    (hQz : ¬ EvZeroF (pev Q))
    (hpos : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → 0 < pev P x * (1 / pev Q x))
    (hmin : ∀ ns : List (Real → Real),
      ClearsToExp (fun y => pev P y * (1 / pev Q y)) ns →
      GProperRel (fun y => Real.log (pev P y * (1 / pev Q y))) ns →
        (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs).length ≤ ns.length)
    (hrel : GEvRel (fun y => Real.log (pev P y * (1 / pev Q y)))
      (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs))
    (hCs : Cs = Cs₀ ++ [Cd]) (hlen0 : Cs₀.length = m + 1) (hCd1 : Cs₀[m]? = some Cd1) :
    EvRel (fun y => pev P y * (1 / pev Q y))
      (relCoeffs P Q (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) m Cd Cd1) := by
  obtain ⟨X₁, hX₁, hq⟩ := pev_ne_zero_on_tail hQz
  obtain ⟨X₂, hX₂, hp⟩ := hpos
  obtain ⟨X, hX, a1, a2⟩ := two_bounds' hX₁ hX₂
  have hS : ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x →
      HasDerivAt (fun y => pev P y * (1 / pev Q y)) (ratFnDeriv P Q x) x :=
    ⟨X₁, hX₁, fun x hx => hasDerivAt_ratFn P Q x (hq x hx)⟩
  have hu : ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x →
      HasDerivAt (fun y => Real.log (pev P y * (1 / pev Q y))) (ratLogDeriv P Q x) x :=
    ⟨X, hX, fun x hx => hasDerivAt_ratLog P Q x (hq x (le_trans a1 hx)) (hp x (le_trans a2 hx))⟩
  have hv : ∃ Y : Real, 1 ≤ Y ∧ ∀ x : Real, Y ≤ x →
      ratLogDeriv P Q x * (pev P x * pev (pmul Q Q) x)
        = pev Q x * pev (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) x :=
    ⟨X, hX, fun x hx => ratLogDeriv_cleared P Q x (hq x (le_trans a1 hx))
      (pev_ne_zero_of_pos (hp x (le_trans a2 hx)))⟩
  exact evRel_relCoeffs (ratFnDeriv_cleared_on_tail hQz) hv
    (minimal_expRel_identity_in (S' := ratFnDeriv P Q) (v := ratLogDeriv P Q)
      (Pr := ClearsToExp (fun y => pev P y * (1 / pev Q y)))
      hS hu (fun _ _ h => clearsToExp_dropLast h)
      (clearsToExp_hPrd_ratLog hQz (not_evZeroF_pev_of_pos ⟨X₂, hX₂, hp⟩))
      hmin hrel hCs hlen0 hCd1)

/-- **`relCoeffs_nil_ratLog`, restricted.** -/
theorem relCoeffs_nil_ratLog_in {q P Q : List Real}
    {Cs Cs₀ : List (List (List Real))} {Cd Cd1 : List (List Real)} {m : Nat}
    (hq : PIrred q)
    (hchar : ∀ r : Nat, DerivCoprime q (r + 1))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hQz : ¬ EvZeroF (pev Q))
    (hpos : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → 0 < pev P x * (1 / pev Q x))
    (hmin : ∀ ns : List (Real → Real),
      ClearsToExp (fun y => pev P y * (1 / pev Q y)) ns →
      GProperRel (fun y => Real.log (pev P y * (1 / pev Q y))) ns →
        (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs).length ≤ ns.length)
    (hrel : GEvRel (fun y => Real.log (pev P y * (1 / pev Q y)))
      (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs))
    (hCs : Cs = Cs₀ ++ [Cd]) (hlen0 : Cs₀.length = m + 1) (hCd1 : Cs₀[m]? = some Cd1) :
    ∀ A : List Real,
      A ∈ relCoeffs P Q (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) m Cd Cd1 →
        pnorm A = [] :=
  all_coeffs_nil_of_relation hq hchar hPd hPn hQn hQne hQd hQz
    (evRel_relCoeffs_ratLog_in hQz hpos hmin hrel hCs hlen0 hCd1)

/-! ## The branch, restricted -/

/-- **`positive_branch_impossible`, with `hmin` restricted to `ClearsToExp`.** Every hypothesis is
one its unrestricted sibling already had; the `hmin` is strictly weaker. -/
theorem positive_branch_impossible_in {q P Q : List Real}
    {Cs Cs₀ : List (List (List Real))} {Cd Cd1 : List (List Real)} {m : Nat}
    (hq : PIrred q)
    (hchar : ∀ r : Nat, DerivCoprime q (r + 1))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hQz : ¬ EvZeroF (pev Q))
    (hpos : ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → 0 < pev P x * (1 / pev Q x))
    (hkd : ¬ Pdvd q (pnsum (m + 1) [(1 : Real)]))
    (hmin : ∀ ns : List (Real → Real),
      ClearsToExp (fun y => pev P y * (1 / pev Q y)) ns →
      GProperRel (fun y => Real.log (pev P y * (1 / pev Q y))) ns →
        (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs).length ≤ ns.length)
    (hrel : GEvRel (fun y => Real.log (pev P y * (1 / pev Q y)))
      (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs))
    (hCs : Cs = Cs₀ ++ [Cd]) (hlen0 : Cs₀.length = m + 1) (hCd1 : Cs₀[m]? = some Cd1)
    (hCdne : ¬ EvZeroF (fun x => bipev Cd x (exp (pev P x * (1 / pev Q x))))) :
    False := by
  have hnil := relCoeffs_nil_ratLog_in (q := q) (P := P) (Q := Q)
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
