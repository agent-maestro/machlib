import MachLib.PolyFactor
import MachLib.PolyPEq
import MachLib.PolyMulDegree

/-!
# Towards lowest terms: the two steps a cancellation induction needs

`no_rational_logarithm` wants an irreducible `q` with `q ∣ Q` and `q ∤ P` — i.e. `P/Q` in lowest
terms at `q`. Reaching that is a cancellation with termination, and these are its two substantive
steps. Both turned out to be assemblies of existing `PolyPEq` and `PolyMulDegree` lemmas.

* **`cross_lift_of_common_factor`** — the cross-multiplied identity survives cancelling a common
  factor. Seven `PEq.trans` steps, every one an existing congruence.
* **`cofactor_length_lt`** — the cofactor is strictly shorter, because `PIrred q` carries
  `2 ≤ q.length` and `pmul_length` is exact on non-empty normal lists. This is what terminates the
  recursion.

## A note on how these were scoped

`(fv)` recorded these as "bookkeeping with named ingredients, not research", declined to build them
at the end of a long session, and they then took about twenty minutes. The estimate held **because it
was made from what the corpus contains** rather than from the shape of the argument — the same
discipline whose absence produced seven false absences the day before. `(fw)` records the sharpest of
those: a by-statement search that *errored* and was read as empty.
-/

namespace MachLib

theorem cross_lift_of_common_factor {P Q P₁ Q₁ P' Q' q : List Real}
    (hP : PEq P (pmul q P₁)) (hQ : PEq Q (pmul q Q₁))
    (h : PEq (pmul P₁ Q') (pmul P' Q₁)) :
    PEq (pmul P Q') (pmul P' Q) := by
  refine PEq.trans (peq_pmul hP (PEq.refl Q')) ?_
  refine PEq.trans (peq_pmul_assoc q P₁ Q') ?_
  refine PEq.trans (peq_pmul (PEq.refl q) h) ?_
  refine PEq.trans (PEq.symm (peq_pmul_assoc q P' Q₁)) ?_
  refine PEq.trans (peq_pmul (peq_pmul_comm q P') (PEq.refl Q₁)) ?_
  refine PEq.trans (peq_pmul_assoc P' q Q₁) ?_
  exact peq_pmul (PEq.refl P') (PEq.symm hQ)

/-- **The cofactor is strictly shorter.** `Q ≈ q·Q₁` with `q` irreducible (so `2 ≤ q.length`) forces
`Q₁.length < Q.length`, which is what makes the cancellation terminate. -/
theorem cofactor_length_lt {q Q Q₁ : List Real} (hq : PIrred q)
    (hQn : PNormal Q) (hQ₁n : PNormal Q₁) (hQ₁ne : Q₁ ≠ [])
    (hQ : PEq Q (pmul q Q₁)) : Q₁.length < Q.length := by
  have hqne : q ≠ [] := by
    intro h; rw [h] at hq; exact absurd hq.2.1 (by simp)
  have hEq : Q = pmul q Q₁ := by
    have h1 : pnorm Q = Q := pnorm_eq_self Q hQn
    have h2 : pnorm (pmul q Q₁) = pmul q Q₁ :=
      pnorm_eq_self _ (pmul_normal hq.1 hQ₁n hqne hQ₁ne)
    rw [← h1, hQ, h2]
  rw [hEq, pmul_length q Q₁ hqne hQ₁ne]
  have h2q : 2 ≤ q.length := hq.2.1
  have h1Q : 1 ≤ Q₁.length := by
    cases Q₁ with
    | nil => exact absurd rfl hQ₁ne
    | cons _ _ => simp
  omega

/-! ## The reduction itself

Either the fraction collapses to a polynomial (`Q'` a unit — the case a *bounded* germ excludes
downstream, since a bounded polynomial is constant), or an irreducible factor of the denominator
survives that does not divide the numerator: exactly `no_rational_logarithm`'s `hq` / `hQd` / `hPd`.

Stated **cross-multiplied**, so the induction stays algebraic and the `pev` bookkeeping happens once
at the call site rather than at every recursive step.

One trap worth naming: `pmul q []` is a list of **zeros**, not `[]`. `pnorm_replicate_zero` is what
collapses it, and reaching for `pmul_nil_right` alone gives a type mismatch — the only failure in
building this induction, and a reminder that "the zero polynomial" has more than one representation
here.
-/


/-- A cofactor of a non-zero product is non-zero. -/
theorem cofactor_pnorm_ne {q X A : List Real} (hA : pnorm A ≠ [])
    (hAX : PEq A (pmul q X)) : pnorm X ≠ [] := by
  intro hX
  refine hA ?_
  have h0 : PEq X [] := by show pnorm X = pnorm []; rw [hX]; rfl
  have h1 : PEq (pmul q X) (pmul q []) := peq_pmul (PEq.refl q) h0
  -- `pmul q []` is a list of ZEROS, not `[]`; `pnorm` is what collapses it
  have h2 : pnorm (pmul q ([] : List Real)) = [] := by
    rw [pmul_nil_right q, pnorm_replicate_zero]
  show pnorm A = pnorm []
  have h3 : pnorm (pmul q X) = [] := Eq.trans h1 h2
  exact Eq.trans hAX h3

/-- **Full coprimality.** Strip common irreducible factors until none remain; termination is
`cofactor_length_lt`, and each cancellation is transported by `cross_lift_of_common_factor`.

This is the form `no_rational_logarithm`'s `hlow` wants — `hlow` fixes the irreducible from the
*other* fraction, so a witness-producing statement ("some irreducible survives") cannot supply it and
a universally quantified one must. Stripping to exhaustion costs no more than stripping once: the
induction is the same, and only the branch condition changes. -/
theorem exists_coprime_representative : ∀ (n : Nat) (P Q : List Real), Q.length ≤ n →
    PNormal P → PNormal Q → pnorm P ≠ [] → pnorm Q ≠ [] →
    ∃ P' Q' : List Real, PNormal P' ∧ PNormal Q' ∧ pnorm P' ≠ [] ∧ pnorm Q' ≠ [] ∧
      PEq (pmul P Q') (pmul P' Q) ∧
      ∀ q : List Real, PIrred q → Pdvd q Q' → ¬ Pdvd q P' := by
  intro n
  induction n with
  | zero =>
      intro P Q hlen _ _ _ hQz
      cases Q with
      | nil => exact absurd rfl hQz
      | cons _ _ => exact absurd hlen (Nat.not_succ_le_zero _)
  | succ n ih =>
      intro P Q hlen hPn hQn hPz hQz
      by_cases hcom : ∃ q : List Real, PIrred q ∧ Pdvd q Q ∧ Pdvd q P
      · obtain ⟨q, hq, ⟨Q₁, hQ₁n, hQ₁⟩, ⟨P₁, hP₁n, hP₁⟩⟩ := hcom
        have hPeq : PEq P (pmul q P₁) := hP₁
        have hQeq : PEq Q (pmul q Q₁) := hQ₁
        have hP₁z : pnorm P₁ ≠ [] := cofactor_pnorm_ne hPz hPeq
        have hQ₁z : pnorm Q₁ ≠ [] := cofactor_pnorm_ne hQz hQeq
        have hQ₁ne : Q₁ ≠ [] := by intro h; rw [h] at hQ₁z; exact hQ₁z rfl
        have hlt : Q₁.length < Q.length := cofactor_length_lt hq hQn hQ₁n hQ₁ne hQeq
        obtain ⟨P', Q', hP'n, hQ'n, hP'z, hQ'z, hcross, hcop⟩ :=
          ih P₁ Q₁ (by omega) hP₁n hQ₁n hP₁z hQ₁z
        exact ⟨P', Q', hP'n, hQ'n, hP'z, hQ'z,
          cross_lift_of_common_factor hPeq hQeq hcross, hcop⟩
      · refine ⟨P, Q, hPn, hQn, hPz, hQz, PEq.refl _, ?_⟩
        intro q hq hqQ hqP
        exact hcom ⟨q, hq, hqQ, hqP⟩

/-- One surviving irreducible, or the fraction is a polynomial — the corollary of coprimality that
splits on whether the reduced denominator still has a factor at all. The unit branch is where a
*bounded* germ is eventually used, and nothing here discharges it. -/
theorem exists_irred_not_dividing (n : Nat) (P Q : List Real) (hlen : Q.length ≤ n)
    (hPn : PNormal P) (hQn : PNormal Q) (hPz : pnorm P ≠ []) (hQz : pnorm Q ≠ []) :
    ∃ P' Q' : List Real, PNormal P' ∧ PNormal Q' ∧ pnorm P' ≠ [] ∧ pnorm Q' ≠ [] ∧
      PEq (pmul P Q') (pmul P' Q) ∧
      (Q'.length ≤ 1 ∨ ∃ q : List Real, PIrred q ∧ Pdvd q Q' ∧ ¬ Pdvd q P') := by
  obtain ⟨P', Q', hP'n, hQ'n, hP'z, hQ'z, hcross, hcop⟩ :=
    exists_coprime_representative n P Q hlen hPn hQn hPz hQz
  refine ⟨P', Q', hP'n, hQ'n, hP'z, hQ'z, hcross, ?_⟩
  by_cases h2 : 2 ≤ Q'.length
  · obtain ⟨q, hq, hqQ'⟩ := exists_irred_divisor' Q' hQ'n h2
    exact Or.inr ⟨q, hq, hqQ', hcop q hq hqQ'⟩
  · exact Or.inl (by omega)

/-! ## Meeting the consumer's shape

`no_rational_logarithm` does not take "an irreducible factor of the denominator"; it takes the
**exact multiplicity**, `PEq Q (pmul (ppow q (r+1)) Qt)` with `¬ Pdvd q Qt`. The reduction above
delivers only `Pdvd q Q'`. `exists_ord_factor` supplies the maximal power, and the one step it does
*not* supply is that the power is positive — which is where `Pdvd q Q'` gets spent.

Restating the reduction in the consumer's own shape is the point of `lowest_terms_with_ord`: it is
what makes the remaining gap between the two halves readable as a hypothesis list rather than as
prose.
-/


theorem exists_pos_ord_factor {q A : List Real} (hq : PIrred q)
    (hAn : PNormal A) (hAne : A ≠ []) (hdvd : Pdvd q A) :
    ∃ (r : Nat) (M : List Real), PNormal M ∧ M ≠ [] ∧ ¬ Pdvd q M ∧
      PEq A (pmul (ppow q (r + 1)) M) := by
  obtain ⟨k, M, hMn, hMne, hMd, hA⟩ := exists_ord_factor A.length q A hq hAn hAne (Nat.le_refl _)
  cases k with
  | zero =>
      exact absurd (Pdvd_of_peq (PEq.trans hA (peq_pmul_one_left M)).symm hdvd) hMd
  | succ r => exact ⟨r, M, hMn, hMne, hMd, hA⟩

/-- **The representation half, in the consumer's own shape.** -/
theorem lowest_terms_with_ord {P Q : List Real}
    (hPn : PNormal P) (hQn : PNormal Q) (hPz : pnorm P ≠ []) (hQz : pnorm Q ≠ []) :
    ∃ P' Q' : List Real, PNormal P' ∧ PNormal Q' ∧ pnorm P' ≠ [] ∧ pnorm Q' ≠ [] ∧
      PEq (pmul P Q') (pmul P' Q) ∧
      (Q'.length ≤ 1 ∨ ∃ (q Qt : List Real) (r : Nat), PIrred q ∧ ¬ Pdvd q P' ∧
        ¬ Pdvd q Qt ∧ PEq Q' (pmul (ppow q (r + 1)) Qt)) := by
  obtain ⟨P', Q', hP'n, hQ'n, hP'z, hQ'z, hcross, hlast⟩ :=
    exists_irred_not_dividing Q.length P Q (Nat.le_refl _) hPn hQn hPz hQz
  refine ⟨P', Q', hP'n, hQ'n, hP'z, hQ'z, hcross, ?_⟩
  rcases hlast with h | ⟨q, hq, hqQ', hqP'⟩
  · exact Or.inl h
  · have hQ'ne : Q' ≠ [] := by intro h; rw [h] at hQ'z; exact hQ'z rfl
    obtain ⟨r, Qt, _, _, hQtd, hQfac⟩ := exists_pos_ord_factor hq hQ'n hQ'ne hqQ'
    exact Or.inr ⟨q, Qt, r, hq, hqP', hQtd, hQfac⟩

end MachLib
