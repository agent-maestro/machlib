import MachLib.PolyPEq

/-!
# Extended Euclid, and the Bézout identity

The recursion is the classical one, carried on a fuel budget because `pdivmod` shortens the
remainder rather than the list structure:

```
eea A B = (A, 1, 0)                                    when B = 0
eea A B = (g, t, s − t·Q)   where (g,s,t) = eea B R,   R = A − Q·B
```

and the invariant it maintains is `g ≈ s·A + t·B`.

## Why this is now assembly

Every substitution in the step is a `PEq` rewrite, and the pieces were built in earlier modules:
`pdivmod_identity` supplies `A ≈ Q·B + R`, `peq_remainder_of_identity` turns that into
`R ≈ A − Q·B`, and the rest is distributivity and rearrangement. Notably the three laws the step
needs over subtraction — `pmul` distributing on each side, and `X + (Y − Z) ≈ Y + (X − Z)` — are all
**exact list identities**, not `PEq` ones: `psub` is `padd` composed with `pscale (0−1)`, so they
inherit the exact forms already proved. `PEq` is doing bookkeeping here, not carrying weight.

## The one place the fuel matters

`eea` recurses on `(B, R)` with `R.length < B.length`, which `pdivmod_spec'` supplies from
`PNormal B` and `B ≠ []`. `B.length` is therefore always enough fuel, and the canonicity hypotheses
are threaded for exactly that reason — the same place `PolyDivision` needed them, for the same
reason.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## The last few exact laws -/

theorem pscale_one : ∀ L : List Real, pscale 1 L = L := by
  intro L
  induction L with
  | nil => rfl
  | cons a as ih =>
      show (1 * a) :: pscale 1 as = a :: as
      have h : (1 : Real) * a = a := by mach_ring
      rw [h, ih]

theorem pmul_pscale_right : ∀ (X : List Real) (c : Real) (Z : List Real),
    pmul X (pscale c Z) = pscale c (pmul X Z) := by
  intro X
  induction X with
  | nil => intro c Z; rfl
  | cons a as ih =>
      intro c Z
      have hac : a * c = c * a := by mach_ring
      have hc0 : c * 0 = 0 := by mach_ring
      show padd (pscale a (pscale c Z)) ((0 : Real) :: pmul as (pscale c Z))
          = pscale c (padd (pscale a Z) ((0 : Real) :: pmul as Z))
      rw [pscale_padd, pscale_pscale, pscale_pscale, hac, ih c Z]
      show padd (pscale (c * a) Z) ((0 : Real) :: pscale c (pmul as Z))
          = padd (pscale (c * a) Z) ((c * 0) :: pscale c (pmul as Z))
      rw [hc0]

theorem pmul_psub_left (S T B : List Real) :
    pmul (psub S T) B = psub (pmul S B) (pmul T B) := by
  show pmul (padd S (pscale (0 - 1) T)) B = padd (pmul S B) (pscale (0 - 1) (pmul T B))
  rw [pmul_padd_left, pmul_pscale_left]

theorem pmul_psub_right (X Y Z : List Real) :
    pmul X (psub Y Z) = psub (pmul X Y) (pmul X Z) := by
  show pmul X (padd Y (pscale (0 - 1) Z)) = padd (pmul X Y) (pscale (0 - 1) (pmul X Z))
  rw [pmul_padd_right, pmul_pscale_right]

theorem padd_psub_swap (X Y Z : List Real) :
    padd X (psub Y Z) = padd Y (psub X Z) := by
  show padd X (padd Y (pscale (0 - 1) Z)) = padd Y (padd X (pscale (0 - 1) Z))
  rw [padd_left_comm]

theorem peq_pmul_one_left (A : List Real) : PEq (pmul [1] A) A := by
  show pnorm (padd (pscale 1 A) [(0 : Real)]) = pnorm A
  have h := pnorm_padd_concat_zero (pscale 1 A) []
  rw [List.nil_append, padd_nil_right] at h
  rw [h, pscale_one]

/-! ## The recursion -/

/-- Extended Euclid: `(g, s, t)` with `g ≈ s·A + t·B`. -/
noncomputable def eea : Nat → List Real → List Real → List Real × List Real × List Real
  | 0,        A, _ => (A, [1], [])
  | fuel + 1, A, B =>
      if B.length = 0 then (A, [1], [])
      else
        ((eea fuel B (pdivmod A.length A B).2).1,
         (eea fuel B (pdivmod A.length A B).2).2.2,
         psub (eea fuel B (pdivmod A.length A B).2).2.1
              (pmul (eea fuel B (pdivmod A.length A B).2).2.2 (pdivmod A.length A B).1))

theorem eea_zero (A B : List Real) : eea 0 A B = (A, [1], []) := rfl

theorem eea_succ (fuel : Nat) (A B : List Real) :
    eea (fuel + 1) A B =
      if B.length = 0 then (A, [1], [])
      else
        ((eea fuel B (pdivmod A.length A B).2).1,
         (eea fuel B (pdivmod A.length A B).2).2.2,
         psub (eea fuel B (pdivmod A.length A B).2).2.1
              (pmul (eea fuel B (pdivmod A.length A B).2).2.2 (pdivmod A.length A B).1)) := rfl

/-- **The Bézout identity.** `g ≈ s·A + t·B` for the triple extended Euclid returns. -/
theorem eea_bezout : ∀ (fuel : Nat) (A B : List Real), PNormal A → PNormal B → B.length ≤ fuel →
    PEq (eea fuel A B).1
      (padd (pmul (eea fuel A B).2.1 A) (pmul (eea fuel A B).2.2 B)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro A B _ _ hlen
      rw [eea_zero]
      show PEq A (padd (pmul [1] A) (pmul [] B))
      rw [show pmul ([] : List Real) B = [] from rfl, padd_nil_right]
      exact (peq_pmul_one_left A).symm
  | succ fuel ih =>
      intro A B hA hB hlen
      rw [eea_succ]
      by_cases hB0 : B.length = 0
      · rw [if_pos hB0]
        show PEq A (padd (pmul [1] A) (pmul [] B))
        rw [show pmul ([] : List Real) B = [] from rfl, padd_nil_right]
        exact (peq_pmul_one_left A).symm
      · rw [if_neg hB0]
        have hBne : B ≠ [] := by
          intro h; rw [h] at hB0; exact hB0 rfl
        obtain ⟨hev, hnr, hlr⟩ := pdivmod_spec' A B hA hB hBne
        have hfuel : (pdivmod A.length A B).2.length ≤ fuel := by omega
        have hIH := ih B (pdivmod A.length A B).2 hB hnr hfuel
        -- names for the recursive triple
        have hident : PEq A (padd (pmul (pdivmod A.length A B).1 B) (pdivmod A.length A B).2) :=
          pdivmod_identity A.length A B hBne
        have hR := peq_remainder_of_identity hident
        -- g ≈ s·B + t·R ≈ s·B + t·(A − Q·B) ≈ t·A + (s − t·Q)·B
        refine PEq.trans hIH ?_
        refine PEq.trans (peq_padd (PEq.refl _) (peq_pmul (PEq.refl _) hR)) ?_
        rw [pmul_psub_right]
        -- associativity is a `pnorm` equation, so it enters as a PEq step, not a rewrite
        refine PEq.trans
          (peq_padd (PEq.refl _) (peq_psub (PEq.refl _) (pmul_assoc_pnorm _ _ _).symm)) ?_
        rw [padd_psub_swap, ← pmul_psub_left]

end MachLib
