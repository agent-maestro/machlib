import MachLib.PolyPowDeriv

/-!
# The pole-order count

`ord_q(P'Q − PQ') = r − 1` exactly, for `Q ≈ qʳ·Q̃` with `q ∤ P` and `q ∤ Q̃`. This is the step
`CRUX.md` §3 runs on, and the reason the whole Euclid spine exists.

## What it costs beyond the field axioms

Exactly one named hypothesis, `DerivCoprime q r` — `q ∤ r·q'` — which is false over `𝔽₂` and true
for irreducible `q` in characteristic zero. Everything else here is field-axiom-only.

## The shape

With `r = m+1`, the power rule gives `Q' ≈ qᵐ·(T·Q̃ + q·Q̃')` where `T = r·q'`, and `P'Q ≈ qᵐ·(P'·(q·Q̃))`.
So `D ≈ qᵐ·E` with

```
E = P'·(q·Q̃) − P·(T·Q̃ + q·Q̃')
```

and `q ∤ E` because modulo `q` it is `−P·T·Q̃`, whose three factors `q` all fails to divide —
`q ∤ P` by hypothesis, `q ∤ T` by `DerivCoprime`, `q ∤ Q̃` by hypothesis — so Euclid's lemma applied
twice finishes. **The `qᵐ` is exact, not a bound**, which is what makes the count a strict inequality
rather than a tautology.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## The derivative respects `PEq` -/

theorem peq_pderiv_concat_zero : ∀ L : List Real,
    PEq (pderiv (L ++ [0])) (pderiv L) := by
  intro L
  induction L with
  | nil =>
      show pnorm (pderiv [(0 : Real)]) = pnorm (pderiv [])
      show pnorm (padd ([] : List Real) ((0 : Real) :: pderiv [])) = pnorm []
      show pnorm [(0 : Real)] = pnorm []
      rw [pnorm_nil_zero]
      rfl
  | cons c cs ih =>
      show PEq (pderiv (c :: (cs ++ [0]))) (pderiv (c :: cs))
      show PEq (padd (cs ++ [0]) ((0 : Real) :: pderiv (cs ++ [0])))
               (padd cs ((0 : Real) :: pderiv cs))
      show pnorm _ = pnorm _
      rw [pnorm_padd_left_concat_zero]
      refine pnorm_padd_congr cs ?_
      show pconsN (0 : Real) (pnorm (pderiv (cs ++ [0])))
          = pconsN (0 : Real) (pnorm (pderiv cs))
      rw [ih]

theorem peq_pderiv_replicate : ∀ (n : Nat) (L : List Real),
    PEq (pderiv (L ++ List.replicate n 0)) (pderiv L) := by
  intro n
  induction n with
  | zero => intro L; simp
  | succ k ih =>
      intro L
      have hsplit : L ++ List.replicate (k + 1) (0 : Real) = (L ++ List.replicate k 0) ++ [0] := by
        rw [List.append_assoc]; congr 1; rw [List.replicate_succ']
      rw [hsplit]
      exact PEq.trans (peq_pderiv_concat_zero _) (ih L)

theorem pnorm_pderiv_left (L : List Real) :
    pnorm (pderiv L) = pnorm (pderiv (pnorm L)) := by
  obtain ⟨n, hn⟩ := pnorm_decomp L
  have h := peq_pderiv_replicate n (pnorm L)
  rw [← hn] at h
  exact h

theorem peq_pderiv {X Y : List Real} (h : PEq X Y) : PEq (pderiv X) (pderiv Y) := by
  show pnorm (pderiv X) = pnorm (pderiv Y)
  rw [pnorm_pderiv_left X, pnorm_pderiv_left Y, h]

/-! ## Rearrangement and divisibility helpers -/

theorem peq_pmul_left_comm (X Y Z : List Real) :
    PEq (pmul X (pmul Y Z)) (pmul Y (pmul X Z)) :=
  PEq.trans (pmul_assoc_pnorm X Y Z).symm
    (PEq.trans (peq_pmul (peq_pmul_comm X Y) (PEq.refl Z)) (pmul_assoc_pnorm Y X Z))

theorem Pdvd_pscale {q B : List Real} (c : Real) (h : Pdvd q B) : Pdvd q (pscale c B) := by
  obtain ⟨M, _, hM⟩ := h
  refine ⟨pnorm (pscale c M), pnorm_normal _, ?_⟩
  rw [← pnorm_pmul_right q (pscale c M), pmul_pscale_right]
  exact peq_pscale c hM

theorem Pdvd_psub {q A B : List Real} (hA : Pdvd q A) (hB : Pdvd q B) : Pdvd q (psub A B) :=
  Pdvd_padd hA (Pdvd_pscale (0 - 1) hB)

/-- `q` divides any product it appears in on the left. -/
theorem Pdvd_pmul_self (q X : List Real) : Pdvd q (pmul q X) := by
  refine Pdvd_of_peq (peq_pmul_comm q X) ?_
  exact Pdvd_pmul X Pdvd_refl

/-- `X − (X − Y) ≈ Y`. -/
theorem peq_psub_psub_self (X Y : List Real) : PEq (psub X (psub X Y)) Y := by
  have hinv : ((0 : Real) - 1) * (0 - 1) = 1 := by mach_ring
  show pnorm (padd X (pscale (0 - 1) (padd X (pscale (0 - 1) Y)))) = pnorm Y
  rw [pscale_padd, pscale_pscale, hinv, pscale_one, ← padd_assoc, padd_neg_self]
  have h := pnorm_padd_replicate X.length Y []
  rw [List.nil_append, padd_nil_right] at h
  rw [padd_comm]
  exact h

/-- `(X + Y) − Y ≈ X`. -/
theorem peq_padd_psub_right (X Y : List Real) : PEq (psub (padd X Y) Y) X := by
  refine PEq.trans (peq_psub (peq_padd_comm X Y) (PEq.refl Y)) ?_
  exact peq_psub_padd_cancel Y X

/-! ## The derivative of `qʳ·Q̃` -/

theorem peq_pderiv_ppow_mul {q Q Qt : List Real} (m : Nat)
    (hQ : PEq Q (pmul (ppow q (m + 1)) Qt)) :
    PEq (pderiv Q)
      (pmul (ppow q m)
        (padd (pmul (pnsum (m + 1) (pderiv q)) Qt) (pmul q (pderiv Qt)))) := by
  refine PEq.trans (peq_pderiv hQ) ?_
  refine PEq.trans (peq_pderiv_pmul (ppow q (m + 1)) Qt) ?_
  rw [pmul_padd_right]
  refine peq_padd ?_ ?_
  · -- (q^(m+1))' · Q̃ ≈ q^m · (T · Q̃)
    refine PEq.trans (peq_pmul (peq_pderiv_ppow q m) (PEq.refl Qt)) ?_
    exact pmul_assoc_pnorm (ppow q m) (pnsum (m + 1) (pderiv q)) Qt
  · -- q^(m+1) · Q̃' ≈ q^m · (q · Q̃')
    show PEq (pmul (pmul q (ppow q m)) (pderiv Qt)) _
    refine PEq.trans (pmul_assoc_pnorm q (ppow q m) (pderiv Qt)) ?_
    exact peq_pmul_left_comm q (ppow q m) (pderiv Qt)

/-! ## The count -/

/-- **`ord_q(P'Q − PQ') = r − 1`, exactly.** Stated in factorisation form, which with `ord_unique`
pins the order. The `qᵐ` is exact: `q ∤ E`. -/
theorem ord_deriv_cross {q P Q Qt : List Real} {m : Nat} (hq : PIrred q)
    (hPd : ¬ Pdvd q P) (hQtd : ¬ Pdvd q Qt) (hT : DerivCoprime q (m + 1))
    (hPn : PNormal P)
    (hQ : PEq Q (pmul (ppow q (m + 1)) Qt)) :
    ∃ E : List Real, ¬ Pdvd q E ∧
      PEq (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) (pmul (ppow q m) E) := by
  -- names
  refine ⟨psub (pmul (pderiv P) (pmul q Qt))
              (pmul P (padd (pmul (pnsum (m + 1) (pderiv q)) Qt) (pmul q (pderiv Qt)))), ?_, ?_⟩
  · -- q does not divide E, because modulo q it is −P·T·Q̃
    intro hE
    have hA1 : Pdvd q (pmul (pderiv P) (pmul q Qt)) :=
      Pdvd_of_peq (peq_pmul_left_comm (pderiv P) q Qt) (Pdvd_pmul_self q _)
    have hA3 : Pdvd q (pmul P (pmul q (pderiv Qt))) :=
      Pdvd_of_peq (peq_pmul_left_comm P q (pderiv Qt)) (Pdvd_pmul_self q _)
    -- P·(T·Q̃) = A1 − E − P·(q·Q̃')
    have hsplit : Pdvd q (pmul P (pmul (pnsum (m + 1) (pderiv q)) Qt)) := by
      refine Pdvd_of_peq ?_ (Pdvd_psub (Pdvd_psub hA1 hE) hA3)
      refine PEq.trans ?_ (peq_psub (peq_psub_psub_self (pmul (pderiv P) (pmul q Qt))
          (pmul P (padd (pmul (pnsum (m + 1) (pderiv q)) Qt) (pmul q (pderiv Qt))))).symm
          (PEq.refl (pmul P (pmul q (pderiv Qt)))))
      rw [pmul_padd_right]
      exact (peq_padd_psub_right (pmul P (pmul (pnsum (m + 1) (pderiv q)) Qt))
        (pmul P (pmul q (pderiv Qt)))).symm
    -- Euclid twice
    exact hQtd (euclid_lemma' hq hT (euclid_lemma hq hPn hPd hsplit))
  · -- the factorisation itself
    refine PEq.trans (peq_psub (peq_pmul (PEq.refl (pderiv P)) hQ)
        (peq_pmul (PEq.refl P) (peq_pderiv_ppow_mul m hQ))) ?_
    rw [pmul_psub_right]
    refine peq_psub ?_ (peq_pmul_left_comm P (ppow q m) _)
    show PEq (pmul (pderiv P) (pmul (pmul q (ppow q m)) Qt)) _
    refine PEq.trans (peq_pmul (PEq.refl (pderiv P))
      (PEq.trans (pmul_assoc_pnorm q (ppow q m) Qt)
        (peq_pmul_left_comm q (ppow q m) Qt))) ?_
    exact peq_pmul_left_comm (pderiv P) (ppow q m) (pmul q Qt)

end MachLib
