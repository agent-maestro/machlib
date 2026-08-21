import MachLib.RatGermShape

/-!
# Feeding the classification into `F` — and why the bounded branch cannot fall to an envelope

`NEXT.md` says: classify, then feed the concrete cases into `F`, and see which evaporate. This is
that step for the **nonzero-floor** branch, and the answer is not the hoped-for evaporation. It is a
structural obstruction, which is more useful than a failed attempt.

## What `F ∘ S` looks like on a floored bounded germ

`ratGerm_eventual_sign` makes the germ one-signed, and the floor makes it bounded away from `0`. So
eventually `S` lives in a compact annulus, `c ≤ |S| ≤ K`, on one side of zero:

* **negative side** — `log₀` vanishes, `F(S) = exp(S)`, and `S < 0` gives `exp(S) < 1`;
* **positive side** — `F(S) = exp(S) + log(S)`, with `exp(S) ≤ exp K` and `log c ≤ log S ≤ log K`.

Either way **`F ∘ S` is bounded.**

## Why that settles the *method* even though it settles no theorem

Every exclusion instrument in this corpus works by **escaping a polynomial envelope**:
`not_polyEnvelope_of_ge_exp`, `not_polyEnvelope_of_ge_exp_scaled`, and through them
`FS_not_algebraic_of_ge_linear` / `_of_le_linear` and `Fbasis_not_algebraic`. Each needs the
generator to outgrow every polynomial.

On this branch `F ∘ S` is not merely polynomially bounded, it is **bounded** — so
`polyEnvelope_of_Fbasis_floor` holds and *every* one of those instruments is silent, not by accident
of formulation but because their hypothesis is false here.

**So the suspicion recorded in `NEXT.md` is confirmed, and sharpened**: the nonzero-finite-limit case
is the survivor, and the reason is now a theorem rather than a hunch. Anything that closes
`BoundedGermTranscendence` on this branch must come from somewhere other than growth — differential
algebra, or a transcendence result about `exp` on a compact set. That is exactly the specimen
`NEXT.md` said would earn bringing such machinery in.
-/

namespace MachLib

open Real

private theorem log_mono_le {a b : Real} (ha : 0 < a) (hab : a ≤ b) : log a ≤ log b := by
  rcases lt_total a b with h | h | h
  · exact le_of_lt (log_lt_log ha h)
  · rw [h]; exact le_refl _
  · exact absurd (lt_of_lt_of_le h hab) (lt_irrefl_ax b)

private theorem exp_le_of_le {a b : Real} (hab : a ≤ b) : exp a ≤ exp b := by
  rcases lt_total a b with h | h | h
  · exact le_of_lt (exp_lt h)
  · rw [h]; exact le_refl _
  · exact absurd (lt_of_lt_of_le h hab) (lt_irrefl_ax b)

/-- **On a floored bounded germ, `F ∘ S` is bounded.** The two sides are genuinely different
computations — the negative one has no logarithm at all, by totalisation — and both land bounded. -/
theorem Fbasis_bounded_of_floor {S : Real → Real} {c K X : Real}
    (hc : 0 < c) (hX : 1 ≤ X)
    (hlo : ∀ x : Real, X ≤ x → c ≤ abs (S x))
    (hhi : ∀ x : Real, X ≤ x → abs (S x) ≤ K)
    (hsign : (∀ x : Real, X ≤ x → 0 < S x) ∨ (∀ x : Real, X ≤ x → S x < 0)) :
    ∃ M : Real, ∀ x : Real, X ≤ x → abs (Fbasis (S x)) ≤ M := by
  rcases hsign with hpos | hneg
  · -- positive side: exp bounded above by exp K, log trapped between log c and log K
    refine ⟨exp K + (abs (log c) + abs (log K)), fun x hx => ?_⟩
    have hSpos := hpos x hx
    have hSc : c ≤ S x := by
      have h := hlo x hx; rw [abs_of_nonneg (le_of_lt hSpos)] at h; exact h
    have hSK : S x ≤ K := by
      have h := hhi x hx; rw [abs_of_nonneg (le_of_lt hSpos)] at h; exact h
    have hexp : exp (S x) ≤ exp K := exp_le_of_le hSK
    have hlogu : log (S x) ≤ abs (log K) :=
      le_trans (log_mono_le hSpos hSK) (le_abs_self (log K))
    have hlogl : 0 - abs (log c) ≤ log (S x) := by
      have h1 : 0 - abs (log c) ≤ log c := by
        rcases lt_total (log c) 0 with h | h | h
        · rw [abs_of_nonpos (le_of_lt h)]
          have e : (0 : Real) - -log c = log c := by mach_ring
          rw [e]; exact le_refl _
        · rw [h, abs_of_nonneg (le_refl (0 : Real))]
          have e : (0 : Real) - 0 = 0 := by mach_ring
          rw [e]; exact le_refl 0
        · rw [abs_of_nonneg (le_of_lt h)]
          have v := add_le_add_wit (le_of_lt h) (le_of_lt h)
          have e : (0 : Real) + 0 = 0 := by mach_ring
          rw [e] at v
          have w := add_le_add_wit v (le_refl (0 - log c))
          have el : (0 : Real) + (0 - log c) = 0 - log c := by mach_ring
          have er : log c + log c + (0 - log c) = log c := by mach_ring
          rw [el, er] at w; exact w
      exact le_trans h1 (log_mono_le hc hSc)
    show abs (exp (S x) + log (S x)) ≤ exp K + (abs (log c) + abs (log K))
    refine le_trans (abs_add _ _) ?_
    refine add_le_add_wit ?_ ?_
    · rw [abs_of_nonneg (le_of_lt (exp_pos _))]; exact hexp
    · rcases lt_total (log (S x)) 0 with h | h | h
      · rw [abs_of_nonpos (le_of_lt h)]
        have e : -log (S x) ≤ abs (log c) := by
          have v := add_le_add_wit hlogl (le_refl (abs (log c) - log (S x)))
          have el : 0 - abs (log c) + (abs (log c) - log (S x)) = 0 - log (S x) := by mach_ring
          have er : log (S x) + (abs (log c) - log (S x)) = abs (log c) := by mach_ring
          rw [el, er] at v
          have e2 : (0 : Real) - log (S x) = -log (S x) := by mach_ring
          rw [e2] at v; exact v
        exact le_trans e (le_add_nonneg' (abs_nonneg (log K)))
      · rw [h, abs_of_nonneg (le_refl (0 : Real))]
        exact add_nonneg (abs_nonneg _) (abs_nonneg _)
      · rw [abs_of_nonneg (le_of_lt h)]
        refine le_trans hlogu ?_
        have v := add_le_add_wit (abs_nonneg (log c)) (le_refl (abs (log K)))
        have e : (0 : Real) + abs (log K) = abs (log K) := by mach_ring
        rw [e] at v; exact v
  · -- negative side: totalisation removes the logarithm entirely
    refine ⟨1, fun x hx => ?_⟩
    have hSneg := hneg x hx
    show abs (exp (S x) + log (S x)) ≤ 1
    rw [log_nonpos (le_of_lt hSneg)]
    have e : exp (S x) + 0 = exp (S x) := by mach_ring
    rw [e, abs_of_nonneg (le_of_lt (exp_pos _))]
    have h0 : exp (S x) ≤ exp 0 := exp_le_of_le (le_of_lt hSneg)
    rw [exp_zero] at h0; exact h0

/-- **Hence every envelope instrument is silent on this branch.** `F ∘ S` has a polynomial envelope
— a constant one — so the hypothesis every exclusion theorem in this corpus needs is false here. -/
theorem polyEnvelope_of_Fbasis_floor {S : Real → Real} {c K X : Real}
    (hc : 0 < c) (hX : 1 ≤ X)
    (hlo : ∀ x : Real, X ≤ x → c ≤ abs (S x))
    (hhi : ∀ x : Real, X ≤ x → abs (S x) ≤ K)
    (hsign : (∀ x : Real, X ≤ x → 0 < S x) ∨ (∀ x : Real, X ≤ x → S x < 0)) :
    PolyEnvelope (fun x => Fbasis (S x)) := by
  obtain ⟨M, hM⟩ := Fbasis_bounded_of_floor hc hX hlo hhi hsign
  refine ⟨abs M, 0, X, abs_nonneg M, hX, fun x hx => ?_⟩
  rw [powNat_zero]
  have e : abs M * 1 = abs M := by mach_ring
  rw [e]
  exact le_trans (hM x hx) (le_abs_self M)

end MachLib
