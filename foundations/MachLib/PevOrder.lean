import MachLib.PevRoots

/-!
# Order of vanishing at a real point — `deflate` iterated to full multiplicity

`PevRoots` divides out **one** root. This divides out **all** of them at a single point: a
coefficient list is identically zero, or it factors as `(x − a)ᵏ · M(x)` with `M(a) ≠ 0`.

## Why this exists

It is the missing brick of the differential route's crux, and naming what that crux actually is
matters, because this file's neighbour `BipevExpDeriv` got it wrong on the first pass. The
eliminated relation there is trivial exactly when `W' = n·S'·W` for `W = pⱼ/pₘ` and `n = m−j ≥ 1`,
which — cleared of denominators with `S = P/Q`, `W = u/v` — is the *polynomial* identity

```
(u'v − uv')·Q² = n·(P'Q − PQ')·u·v
```

There is no transcendental left in it; the `exp` divided out. What refutes it at a real pole of `S`
is an **order-of-vanishing count**: with `r = ord_a Q ≥ 1`, `k = ord_a u`, `l = ord_a v`,

```
ord_a (P'Q − PQ')  =  r − 1        exactly   (uses P(a) ≠ 0 and r ≠ 0 in ℝ)
ord_a (u'v − uv')  ≥  k + l − 1
```

so equating the two sides of the identity gives `k+l−1+2r ≤ r−1+k+l`, i.e. `r ≤ 0`. Every step of
that count needs this factorisation and nothing else — no transcendence input, no algebraicity
predicate, no bivariate polynomial theory. Derivation and symbolic checks:
`monogate-research/exploration/bounded_germ_crux_retyped_2026_08_22/CRUX.md`.

**What this brick does not do.** It is one lemma of that count, not the count. The remaining pieces
are `ord_a` of a product, the two displayed order facts, and the minimal-degree induction over
relations. None of them is built, and this file should not be read as evidence that they are.

## The construction

No new machinery: `pev_deflate` is the division algorithm, `deflate_length` the termination
measure, both already in `PevRoots`. The budget is the list length, exactly as in
`pev_zero_or_root_list` — the *same* induction asking a different question at each step. Where that
theorem asks "is there a root **anywhere**?", this one asks "is `a` **still** a root?", so
`Classical.em` enters on a quantifier-free question rather than an existential one.

The exponent `k` is not asserted to be the order; it is produced **with its witness**, `pev M a ≠ 0`,
which is what makes it the order. Returning the pair rather than a numeric `ord` function is
deliberate — an `ord` that computed without carrying `M` would have to re-derive the non-vanishing
at every use site, and the non-vanishing is the whole content.
-/

namespace MachLib

open Real

/-- **Full factorisation at a point, with a length budget.**

Either `pev L` is identically zero, or `pev L x = (x − a)ᵏ · pev M x` with `pev M a ≠ 0`. -/
theorem pev_ord_factor_budget (a : Real) : ∀ (n : Nat) (L : List Real), L.length ≤ n →
    (∀ x : Real, pev L x = 0) ∨
      ∃ (k : Nat) (M : List Real),
        (∀ x : Real, pev L x = powNat (x - a) k * pev M x) ∧ pev M a ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro L hL
      cases L with
      | nil => exact Or.inl (fun _ => rfl)
      | cons c cs => exact absurd hL (Nat.not_succ_le_zero cs.length)
  | succ n ih =>
      intro L hL
      cases L with
      | nil => exact Or.inl (fun _ => rfl)
      | cons c cs =>
          rcases Classical.em (pev (c :: cs) a = 0) with ha | ha
          · -- `a` is still a root: divide it out, recurse on a strictly shorter list.
            have hlen : (deflate a (c :: cs)).length ≤ n := by
              rw [deflate_length cs a c]
              exact Nat.le_of_succ_le_succ hL
            have hfac : ∀ x : Real,
                pev (c :: cs) x = (x - a) * pev (deflate a (c :: cs)) x := by
              intro x
              have h := pev_deflate (c :: cs) a x
              rw [ha, add_zero] at h
              exact h
            rcases ih (deflate a (c :: cs)) hlen with hz | ⟨k, M, hM, hMa⟩
            · refine Or.inl (fun x => ?_)
              rw [hfac x, hz x, mul_zero]
            · refine Or.inr ⟨k + 1, M, fun x => ?_, hMa⟩
              rw [hfac x, hM x]
              show (x - a) * (powNat (x - a) k * pev M x)
                  = ((x - a) * powNat (x - a) k) * pev M x
              exact (mul_assoc _ _ _).symm
          · -- `a` is not a root: the factorisation is already there with exponent `0`.
            exact Or.inr ⟨0, c :: cs, fun x => (one_mul_thm _).symm, ha⟩

/-- **The budget-free form.** Every coefficient list is identically zero, or factors at `a` as
`(x − a)ᵏ` times something that does not vanish at `a`. -/
theorem pev_ord_factor (a : Real) (L : List Real) :
    (∀ x : Real, pev L x = 0) ∨
      ∃ (k : Nat) (M : List Real),
        (∀ x : Real, pev L x = powNat (x - a) k * pev M x) ∧ pev M a ≠ 0 :=
  pev_ord_factor_budget a L.length L (Nat.le_refl _)

end MachLib
