import MachLib.PolyConstDvd

/-!
# `DerivCoprime` reduces to a nonvanishing statement

The remaining asymmetry. `not_Pdvd_pnsum_one` reduced the composition's second characteristic-zero
input to `natCast n ≠ 0` — pure field content. `DerivCoprime q r` was still a divisibility
statement, and folding it looked like it needed the **leading coefficient** of `pderiv`, which is
index-tracking through the Horner recursion.

It does not. The degree bound only needs that `pderiv` leaves a **trailing zero**:

```
pderiv (L₀ ++ [a])  =  … ++ [0]
```

which is one induction and no index arithmetic. `pnorm` then strips it, so `pnorm (pderiv L)` is
strictly shorter than `L`, and `not_Pdvd_of_length_lt` does the rest. The leading coefficient is
never computed.

## What is left over is exactly the field content

With that, `DerivCoprime q r` reduces to `pnorm (pnsum r (pderiv q)) ≠ []` — "`r·q'` is not the zero
polynomial" — which is the same *shape* as the other input. Both are now nonvanishing statements
about specific polynomials, both false over `𝔽₂`, and neither carries any divisibility content.

`pnsum` commutes with `pderiv` (because `pderiv` is additive), which is what lets the length bound
be applied to `pnsum r (pderiv q)` without a second argument.
-/

namespace MachLib

open Real

/-! ## `pderiv` leaves a trailing zero -/

theorem pderiv_concat_zero : ∀ (cs : List Real) (c : Real),
    ∃ M : List Real, pderiv (c :: cs) = M ++ [0] := by
  intro cs
  induction cs with
  | nil => intro c; exact ⟨[], rfl⟩
  | cons d ds ih =>
      intro c
      obtain ⟨M, hM⟩ := ih d
      refine ⟨padd (d :: ds) ((0 : Real) :: M), ?_⟩
      show padd (d :: ds) ((0 : Real) :: pderiv (d :: ds)) = _
      rw [hM]
      -- lengths agree, so the trailing zero passes through `padd`
      have hlen : (d :: ds).length ≤ ((0 : Real) :: M).length := by
        have h1 : (pderiv (d :: ds)).length = (d :: ds).length := pderiv_length (d :: ds)
        rw [hM] at h1
        simp at h1 ⊢
        omega
      show padd (d :: ds) (((0 : Real) :: M) ++ [0]) = padd (d :: ds) ((0 : Real) :: M) ++ [0]
      exact padd_concat_right (d :: ds) ((0 : Real) :: M) hlen 0

/-- **The derivative is strictly shorter after normalisation.** The degree half of `deg q' < deg q`,
now in the form the divisibility bound consumes. -/
theorem pnorm_pderiv_length_lt (cs : List Real) (c : Real) :
    (pnorm (pderiv (c :: cs))).length < (c :: cs).length := by
  obtain ⟨M, hM⟩ := pderiv_concat_zero cs c
  have hlen : (pderiv (c :: cs)).length = (c :: cs).length := pderiv_length (c :: cs)
  rw [hM] at hlen ⊢
  rw [pnorm_concat_zero M]
  have h1 : (pnorm M).length ≤ M.length := pnorm_length_le M
  simp at hlen ⊢
  omega

/-! ## `pnsum` commutes with `pderiv` -/

theorem pnsum_pderiv : ∀ (r : Nat) (Z : List Real),
    pnsum r (pderiv Z) = pderiv (pnsum r Z) := by
  intro r
  induction r with
  | zero => intro Z; rfl
  | succ k ih =>
      intro Z
      show padd (pderiv Z) (pnsum k (pderiv Z)) = pderiv (padd Z (pnsum k Z))
      rw [pderiv_padd, ih Z]

theorem pnsum_length_succ : ∀ (k : Nat) (Z : List Real),
    (pnsum (k + 1) Z).length = Z.length := by
  intro k
  induction k with
  | zero => intro Z; show (padd Z (pnsum 0 Z)).length = Z.length
            show (padd Z []).length = Z.length
            rw [padd_nil_right]
  | succ j ih =>
      intro Z
      show (padd Z (pnsum (j + 1) Z)).length = Z.length
      exact padd_length_ge Z (pnsum (j + 1) Z) (by rw [ih Z]; exact Nat.le_refl _)

/-! ## The reduction -/

/-- **`DerivCoprime` is a nonvanishing statement.** Given only that `r·q'` is not the zero
polynomial, `q` cannot divide it — by degree, with no leading coefficient computed. -/
theorem derivCoprime_of_ne_zero {q : List Real} (hq : PIrred q) {k : Nat}
    (hne : pnorm (pnsum (k + 1) (pderiv q)) ≠ []) : DerivCoprime q (k + 1) := by
  have hqn := hq.1
  have hqlen := hq.2.1
  have hqne : q ≠ [] := by
    intro h; rw [h] at hqlen; exact Nat.not_succ_le_zero 1 hqlen
  refine not_Pdvd_of_length_lt hqn hqne hne ?_
  rw [pnsum_pderiv]
  have hlen : (pnsum (k + 1) q).length = q.length := pnsum_length_succ k q
  cases hp : pnsum (k + 1) q with
  | nil =>
      exfalso
      rw [hp] at hlen
      apply hqne
      cases hqc : q with
      | nil => rfl
      | cons _ _ => rw [hqc] at hlen; simp at hlen
  | cons a as =>
      have h := pnorm_pderiv_length_lt as a
      -- `cases hp : e` already substituted in the goal; only `hlen` still mentions `pnsum`
      rw [hp] at hlen
      omega

end MachLib
