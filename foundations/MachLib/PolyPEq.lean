import MachLib.PolyDvdAlgebra

/-!
# Equality up to normalisation, as a relation

Every statement in this spine since `PolyCanonical` has been of the form `pnorm X = pnorm Y`, and
the proofs have been threading `pnorm_padd_congr`, `pnorm_pmul_left` and `pnorm_pmul_right` through
rewrites by hand. The Euclid recursion is where that stops scaling: its invariant is a chain of
substitutions into a Bézout identity, and doing those as raw rewrites would be unreadable and
unmaintainable.

So `PEq X Y := pnorm X = pnorm Y` is named, shown to be an equivalence, and shown to be a
**congruence for every operation** — `padd`, `psub`, `pscale`, `pmul`. After that the Euclid step is
ordinary equational reasoning.

## Why this is not a new representation

`PEq` is definitionally `pnorm X = pnorm Y`, not a quotient. Nothing is abstracted, no new type is
introduced, and any `PEq` can be unfolded back to the underlying list equation. The point is only to
stop writing the congruence lemmas out at every use — which is a readability decision, not a
foundational one, and so does not reopen the representation question `PolyCanonical` settled.

## A naming hazard worth recording

The operation congruences are `peq_padd`, `peq_pmul`, … and **not** `PEq.padd`, `PEq.pmul`. Inside
the `PEq` namespace a theorem named `PEq.pscale` shadows `pscale` itself, so the *statement* of the
congruence stops elaborating — `pscale c Y` resolves to the theorem being declared. Same class of
trap as `open Real` shadowing `max`, self-inflicted. Only `PEq.refl`/`symm`/`trans` stay in the
namespace, because nothing collides with those.

## What it costs

One new congruence: `pnorm_pscale_left`, which is the cheapest of the family — `pscale_concat`
already puts a scaled trailing zero in the right shape, and `c·0 = 0` finishes it. The other three
were proved in earlier modules and are reused unchanged.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## The last congruence: `pscale` -/

theorem pnorm_pscale_concat_zero (c : Real) (L : List Real) :
    pnorm (pscale c (L ++ [0])) = pnorm (pscale c L) := by
  have hc0 : c * 0 = 0 := by mach_ring
  rw [pscale_concat, hc0, pnorm_concat_zero]

theorem pnorm_pscale_replicate : ∀ (n : Nat) (c : Real) (L : List Real),
    pnorm (pscale c (L ++ List.replicate n 0)) = pnorm (pscale c L) := by
  intro n
  induction n with
  | zero => intro c L; simp
  | succ k ih =>
      intro c L
      have hsplit : L ++ List.replicate (k + 1) (0 : Real) = (L ++ List.replicate k 0) ++ [0] := by
        rw [List.append_assoc]; congr 1; rw [List.replicate_succ']
      rw [hsplit, pnorm_pscale_concat_zero, ih c L]

theorem pnorm_pscale_left (c : Real) (L : List Real) :
    pnorm (pscale c L) = pnorm (pscale c (pnorm L)) := by
  obtain ⟨n, hn⟩ := pnorm_decomp L
  have h := pnorm_pscale_replicate n c (pnorm L)
  rw [← hn] at h
  exact h

/-- The mirror of `pnorm_padd_congr`, one `padd_comm` away. -/
theorem pnorm_padd_congr_left {X X' : List Real} (Y : List Real) (h : pnorm X = pnorm X') :
    pnorm (padd X Y) = pnorm (padd X' Y) := by
  rw [padd_comm X Y, padd_comm X' Y]
  exact pnorm_padd_congr Y h

/-! ## The relation -/

/-- Equality of the polynomials two coefficient lists denote. Definitionally `pnorm X = pnorm Y` —
a naming convenience, not a quotient. -/
@[reducible] def PEq (X Y : List Real) : Prop := pnorm X = pnorm Y

theorem PEq.refl (X : List Real) : PEq X X := rfl
theorem PEq.symm {X Y : List Real} (h : PEq X Y) : PEq Y X := Eq.symm h
theorem PEq.trans {X Y Z : List Real} (h₁ : PEq X Y) (h₂ : PEq Y Z) : PEq X Z := Eq.trans h₁ h₂

/-! ## Congruence for every operation -/

theorem peq_padd {X X' Y Y' : List Real} (hX : PEq X X') (hY : PEq Y Y') :
    PEq (padd X Y) (padd X' Y') :=
  Eq.trans (pnorm_padd_congr X hY) (pnorm_padd_congr_left Y' hX)

theorem peq_pscale (c : Real) {Y Y' : List Real} (hY : PEq Y Y') :
    PEq (pscale c Y) (pscale c Y') := by
  show pnorm (pscale c Y) = pnorm (pscale c Y')
  rw [pnorm_pscale_left c Y, pnorm_pscale_left c Y', hY]

theorem peq_pmul {X X' Y Y' : List Real} (hX : PEq X X') (hY : PEq Y Y') :
    PEq (pmul X Y) (pmul X' Y') := by
  show pnorm (pmul X Y) = pnorm (pmul X' Y')
  rw [pnorm_pmul_left X Y, hX, ← pnorm_pmul_left X' Y,
      pnorm_pmul_right X' Y, hY, ← pnorm_pmul_right X' Y']

theorem peq_psub {X X' Y Y' : List Real} (hX : PEq X X') (hY : PEq Y Y') :
    PEq (psub X Y) (psub X' Y') :=
  peq_padd hX (peq_pscale (0 - 1) hY)

/-! ## The ring laws, restated in the relation -/

theorem peq_padd_comm (X Y : List Real) : PEq (padd X Y) (padd Y X) := by
  show pnorm _ = pnorm _; rw [padd_comm]

theorem peq_padd_assoc (X Y Z : List Real) :
    PEq (padd (padd X Y) Z) (padd X (padd Y Z)) := by
  show pnorm _ = pnorm _; rw [padd_assoc]

theorem peq_pmul_assoc (X Y Z : List Real) :
    PEq (pmul (pmul X Y) Z) (pmul X (pmul Y Z)) := pmul_assoc_pnorm X Y Z

theorem peq_pmul_padd_left (X Y M : List Real) :
    PEq (pmul (padd X Y) M) (padd (pmul X M) (pmul Y M)) := by
  show pnorm _ = pnorm _; rw [pmul_padd_left]

theorem peq_pmul_padd_right (Z M N : List Real) :
    PEq (pmul Z (padd M N)) (padd (pmul Z M) (pmul Z N)) := by
  show pnorm _ = pnorm _; rw [pmul_padd_right]

/-! ## Subtraction cancels

The one fact the Euclid step needs beyond the ring laws: the division identity gives
`A ≈ Q·B + R`, and the step wants `R ≈ A − Q·B`. -/

theorem peq_psub_padd_cancel (U R : List Real) : PEq (psub (padd U R) U) R := by
  show pnorm (padd (padd U R) (pscale (0 - 1) U)) = pnorm R
  rw [padd_comm U R, padd_assoc, padd_neg_self]
  have h := pnorm_padd_replicate U.length R []
  rw [List.nil_append, padd_nil_right] at h
  exact h

/-- `R ≈ A − Q·B` from `A ≈ Q·B + R`, which is the form `pdivmod_identity` supplies. -/
theorem peq_remainder_of_identity {A U R : List Real} (h : PEq A (padd U R)) :
    PEq R (psub A U) :=
  PEq.trans (peq_psub_padd_cancel U R).symm (peq_psub h.symm (PEq.refl U))

end MachLib
