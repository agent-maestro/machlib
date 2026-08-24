import MachLib.GermClearedDrel
import MachLib.RatLogDeriv
import MachLib.BipevTailNonzero

/-!
# `hPrd` at the branch's own germs

`GermClearedDrel` discharged `hPrd` against three *abstract* clearing hypotheses. This module
supplies them for the germs the `S > 0` branch actually has — `S = P/Q` and `u = log ∘ S` — so that
nothing about the class remains parameterised by the time a caller sees it.

The three map onto lemmas that already existed, which is the point: the clearing invariant was
chosen to match what `RatLogDeriv` and `BipevRatFn` already prove, not the other way round.

| abstract hypothesis | discharged by |
| --- | --- |
| `S' x · pev QQ x = pev Dn x` | `ratFn_deriv_cleared`, at `QQ = Q²` |
| `v x · pev (W·QQ) x = pev Nv x` | `ratLogDeriv_cleared`, at `W = P`, `Nv = Q·Dn` |
| `¬ EvZeroF (pev (W·QQ))` | `not_evZeroF_pmul`, from `P` and `Q` |

`W = P` is forced, not chosen: `ratLogDeriv_cleared` clears `v` by `P·Q²` and `ratFn_deriv_cleared`
clears `S'` by `Q²`, and `Q²` divides `P·Q²`. The common denominator is the larger of the two, and
the surplus `P` rides along on the `S'` side inside `biscale`.

## The one lemma that was missing

`not_evZeroF_pmul` — a product of polynomials neither of which is eventually zero is not eventually
zero. The corpus had `pev_dichotomy` and `pev_ne_zero_on_tail` but no product form; stated here via
`EvNonvanish`, where it is two lines, rather than by re-running the dichotomy.
-/

namespace MachLib

open Real

/-! ## Products of denominators -/

theorem not_evZeroF_of_evNonvanish {D : Real → Real} (h : EvNonvanish D) : ¬ EvZeroF D := by
  intro hz
  obtain ⟨X₁, hX₁, h₁⟩ := h
  obtain ⟨X₂, hX₂, h₂⟩ := hz
  obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX₁ hX₂
  exact h₁ X (le_trans hle1 (le_refl X)) (h₂ X (le_trans hle2 (le_refl X)))

/-- **A product of two polynomials neither eventually zero is not eventually zero.** -/
theorem not_evZeroF_pmul {A B : List Real}
    (hA : ¬ EvZeroF (pev A)) (hB : ¬ EvZeroF (pev B)) : ¬ EvZeroF (pev (pmul A B)) := by
  refine not_evZeroF_of_evNonvanish ?_
  obtain ⟨X₁, hX₁, h₁⟩ := evNonvanish_pev hA
  obtain ⟨X₂, hX₂, h₂⟩ := evNonvanish_pev hB
  obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX₁ hX₂
  refine ⟨X, hX, fun x hx => ?_⟩
  rw [pev_pmul]
  exact mul_ne_zero (h₁ x (le_trans hle1 hx)) (h₂ x (le_trans hle2 hx))

/-! ## The branch's clearing data

`Dn` is the cleared numerator of `S'`, and `Nv = Q·Dn` that of `v`. Both are forced by the two
`_cleared` lemmas; neither is a choice made here. -/

/-- `P'Q − PQ'`, the numerator of `S'` over `Q²`. -/
noncomputable def ratNum (P Q : List Real) : List Real :=
  psub (pmul (pderiv P) Q) (pmul P (pderiv Q))

theorem ratFnDeriv_cleared_tail {P Q : List Real} (hQz : ¬ EvZeroF (pev Q)) :
    ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x →
      ratFnDeriv P Q x * pev (pmul Q Q) x = pev (ratNum P Q) x := by
  obtain ⟨X, hX, hq⟩ := pev_ne_zero_on_tail hQz
  exact ⟨X, hX, fun x hx => ratFn_deriv_cleared P Q x (hq x hx)⟩

theorem ratLogDeriv_cleared_pmul {P Q : List Real}
    (hQz : ¬ EvZeroF (pev Q)) (hPz : ¬ EvZeroF (pev P)) :
    EvEqF (fun x => ratLogDeriv P Q x * pev (pmul P (pmul Q Q)) x)
          (fun x => pev (pmul Q (ratNum P Q)) x) := by
  obtain ⟨X₁, hX₁, hq⟩ := pev_ne_zero_on_tail hQz
  obtain ⟨X₂, hX₂, hp⟩ := pev_ne_zero_on_tail hPz
  obtain ⟨X, hX, hle1, hle2⟩ := two_bounds' hX₁ hX₂
  refine ⟨X, hX, fun x hx => ?_⟩
  have h := ratLogDeriv_cleared P Q x (hq x (le_trans hle1 hx)) (hp x (le_trans hle2 hx))
  show ratLogDeriv P Q x * pev (pmul P (pmul Q Q)) x = pev (pmul Q (ratNum P Q)) x
  rw [pev_pmul P (pmul Q Q) x, pev_pmul Q (ratNum P Q) x]
  exact h

/-! ## `hPrd`, fully concrete -/

/-- **The `hPrd` obligation for the `S > 0` branch's own germs.** No clearing hypothesis is left for
a caller — only that `P` and `Q` are not eventually zero, which the branch already carries. -/
theorem clearsToExp_hPrd_ratLog {P Q : List Real}
    {Cs Cs₀ : List (List (List Real))} {Cd : List (List Real)}
    (hQz : ¬ EvZeroF (pev Q)) (hPz : ¬ EvZeroF (pev P)) :
    ∀ (ds₀ : List (Real → Real)) (dtop : Real → Real),
      gdrel (ratLogDeriv P Q)
          (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs)
          (expCoeffsD (fun y => pev P y * (1 / pev Q y)) (ratFnDeriv P Q) Cs) = ds₀ ++ [dtop] →
        ClearsToExp (fun y => pev P y * (1 / pev Q y))
          (gscaleSub (fun x => bipev Cd x (exp (pev P x * (1 / pev Q x)))) dtop
            (expCoeffs (fun y => pev P y * (1 / pev Q y)) Cs₀) ds₀) :=
  clearsToExp_hPrd (W := P) (QQ := pmul Q Q) (Dn := ratNum P Q) (Nv := pmul Q (ratNum P Q))
    (not_evZeroF_pmul hPz (not_evZeroF_pmul hQz hQz))
    (ratFnDeriv_cleared_tail hQz)
    (ratLogDeriv_cleared_pmul hQz hPz)

end MachLib
