import MachLib.PolyBezout

/-!
# `pmul` commutes, and extended Euclid returns a common divisor

`eea_bezout` proves the identity `g ≈ s·A + t·B`. That is only half of what a gcd is, and Euclid's
lemma needs the other half: `g` divides both inputs. This file supplies it.

## Why commutativity had to be built first

The divisor half turns on `q ∣ B → q ∣ Q·B`. With `B ≈ q·M` that is
`Q·B ≈ Q·(q·M) ≈ (Q·q)·M`, and getting `q` back to the front needs `pmul` to **commute** — the one
ring law this spine had not needed until now.

There is an alternative: flip `Pdvd` to `∃ M, A ≈ M·q`, after which the divisor half needs only
associativity and left-distributivity, both already cheap. That would be the smaller change today
and the wrong one — commutativity is a fact the ring should have on record, `ord_q` will want it,
and a definition chosen to dodge a missing lemma tends to be paid for twice.

## How commutativity is proved

`pmul` recurses on its *first* argument, so `pmul Y (x :: xs)` does not unfold and the naive
induction stalls. The fix is to prove the recursion "from the right" first:

```
pmul X (y :: ys)  ≈  pscale y X + x·(pmul X ys)
```

which is exact except for trailing zeros (`ys = []` makes the two sides differ by one `[0]`), so it
is a `PEq` statement. With it, commutativity is one induction and `padd_left_comm`.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## Congruence for a prepended coefficient -/

theorem peq_cons (c : Real) {U V : List Real} (h : PEq U V) : PEq (c :: U) (c :: V) := by
  show pconsN c (pnorm U) = pconsN c (pnorm V)
  rw [h]

/-! ## The right-hand recursion, and commutativity -/

/-- `pmul` unfolded on its **second** argument. Exact but for trailing zeros — with `ys = []` the
two sides differ by a single `[0]` — so it is stated up to `pnorm`. -/
theorem peq_pmul_cons_right : ∀ (X : List Real) (y : Real) (ys : List Real),
    PEq (pmul X (y :: ys)) (padd (pscale y X) ((0 : Real) :: pmul X ys)) := by
  intro X
  induction X with
  | nil =>
      intro y ys
      show pnorm ([] : List Real) = pnorm (padd (pscale y []) ((0 : Real) :: pmul [] ys))
      show pnorm ([] : List Real) = pnorm [(0 : Real)]
      show ([] : List Real) = pnorm [(0 : Real)]
      rw [pnorm_nil_zero]
  | cons a as ih =>
      intro y ys
      have hay : a * y + 0 = y * a + 0 := by mach_ring
      show PEq ((a * y + 0) :: padd (pscale a ys) (pmul as (y :: ys)))
          ((y * a + 0) :: padd (pscale y as) (pmul (a :: as) ys))
      rw [hay]
      refine peq_cons _ ?_
      refine PEq.trans (peq_padd (PEq.refl _) (ih y ys)) ?_
      show PEq (padd (pscale a ys) (padd (pscale y as) ((0 : Real) :: pmul as ys)))
          (padd (pscale y as) (padd (pscale a ys) ((0 : Real) :: pmul as ys)))
      show pnorm _ = pnorm _
      rw [padd_left_comm]

/-- **`pmul` commutes, up to normalisation.** -/
theorem peq_pmul_comm : ∀ X Y : List Real, PEq (pmul X Y) (pmul Y X) := by
  intro X
  induction X with
  | nil =>
      intro Y
      show pnorm ([] : List Real) = pnorm (pmul Y [])
      rw [pmul_nil_right, pnorm_replicate_zero]
      rfl
  | cons x xs ih =>
      intro Y
      refine PEq.symm (PEq.trans (peq_pmul_cons_right Y x xs) ?_)
      show PEq (padd (pscale x Y) ((0 : Real) :: pmul Y xs))
          (padd (pscale x Y) ((0 : Real) :: pmul xs Y))
      exact peq_padd (PEq.refl _) (peq_cons _ (ih Y).symm)

/-! ## Divisibility of multiples -/

theorem Pdvd_of_peq {q A A' : List Real} (h : PEq A A') (hd : Pdvd q A') : Pdvd q A := by
  obtain ⟨M, hMn, hM⟩ := hd
  exact ⟨M, hMn, Eq.trans h hM⟩

/-- A divisor of `B` divides every multiple of `B`. -/
theorem Pdvd_pmul {q B : List Real} (Q : List Real) (h : Pdvd q B) : Pdvd q (pmul Q B) := by
  obtain ⟨M, _, hM⟩ := h
  refine ⟨pnorm (pmul Q M), pnorm_normal _, ?_⟩
  rw [← pnorm_pmul_right q (pmul Q M)]
  refine PEq.trans (peq_pmul (PEq.refl Q) hM) ?_
  refine PEq.trans (pmul_assoc_pnorm Q q M).symm ?_
  exact PEq.trans (peq_pmul (peq_pmul_comm Q q) (PEq.refl M)) (pmul_assoc_pnorm q Q M)

/-! ## The divisor half of the gcd -/

/-- **Extended Euclid returns a common divisor.** With `eea_bezout`, this is the whole gcd. -/
theorem eea_divides : ∀ (fuel : Nat) (A B : List Real), PNormal A → PNormal B → B.length ≤ fuel →
    Pdvd (eea fuel A B).1 A ∧ Pdvd (eea fuel A B).1 B := by
  intro fuel
  induction fuel with
  | zero =>
      intro A B _ _ hlen
      have hB : B = [] := by
        cases B with
        | nil => rfl
        | cons _ _ => simp at hlen
      rw [eea_zero, hB]
      exact ⟨Pdvd_refl, Pdvd_zero⟩
  | succ fuel ih =>
      intro A B hA hB hlen
      rw [eea_succ]
      by_cases hB0 : B.length = 0
      · have hBnil : B = [] := by
          cases B with
          | nil => rfl
          | cons _ _ => simp at hB0
        rw [if_pos hB0, hBnil]
        exact ⟨Pdvd_refl, Pdvd_zero⟩
      · rw [if_neg hB0]
        have hBne : B ≠ [] := by
          intro h; rw [h] at hB0; exact hB0 rfl
        obtain ⟨hev, hnr, hlr⟩ := pdivmod_spec' A B hA hB hBne
        have hfuel : (pdivmod A.length A B).2.length ≤ fuel := by omega
        obtain ⟨hgB, hgR⟩ := ih B (pdivmod A.length A B).2 hB hnr hfuel
        refine ⟨?_, hgB⟩
        have hident : PEq A (padd (pmul (pdivmod A.length A B).1 B) (pdivmod A.length A B).2) :=
          pdivmod_identity A.length A B hBne
        exact Pdvd_of_peq hident (Pdvd_padd (Pdvd_pmul _ hgB) hgR)

end MachLib
