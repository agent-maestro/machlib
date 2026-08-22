import MachLib.PolyIrred

/-!
# An irreducible factor exists, and `ord_q` is additive

The two remaining pieces of the Euclid spine.

## No FTA anywhere

"Every nonconstant polynomial has an irreducible factor" is often reached for via factorisation into
linear and quadratic pieces — which over `ℝ` is the fundamental theorem of algebra, and is *not*
available here (nor needed). The elementary argument suffices: induct on a degree budget; either the
polynomial is irreducible and divides itself, or it factors into two nonconstants, the left of which
is strictly shorter and has an irreducible factor by induction.

Note what that does to `CRUX.md` §4, which costed this step as needing real FTA and a division
routine for quadratics. It needs neither, and the degree of the factor is never inspected.

## Where Euclid's lemma is spent

`ord_pmul` is the whole reason the previous module exists. Given `A ≈ qʲ·M` and `B ≈ qˡ·N` with `q`
dividing neither cofactor, the product is `q^(j+l)·(M·N)` — and the *only* difficulty is showing `q`
still fails to divide `M·N`. That is exactly Euclid's lemma, applied once.

## What is deliberately not proved here

That the exponent is **unique**. `ord_pmul` is the additivity of a *given* factorisation, which is
what a pole-order count over an equation between two products needs on each side. Making `ord_q` a
function requires cancellation (`q·X ≈ q·Y → X ≈ Y`, which follows from degree additivity, not from
anything new) and is a separate step; nothing here should be read as supplying it.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## An irreducible factor, by minimal degree -/

theorem exists_irred_divisor : ∀ (n : Nat) (B : List Real), PNormal B → 2 ≤ B.length →
    B.length ≤ n → ∃ q : List Real, PIrred q ∧ Pdvd q B := by
  intro n
  induction n with
  | zero => intro B _ h2 hn; omega
  | succ n ih =>
      intro B hB h2 hn
      by_cases hfac : ∃ X Y : List Real,
          PNormal X ∧ PNormal Y ∧ 2 ≤ X.length ∧ 2 ≤ Y.length ∧ PEq B (pmul X Y)
      · obtain ⟨X, Y, hXn, hYn, hX2, hY2, hXY⟩ := hfac
        have hXne : X ≠ [] := by intro h; rw [h] at hX2; simp at hX2
        have hYne : Y ≠ [] := by intro h; rw [h] at hY2; simp at hY2
        have hcanon : pnorm (pmul X Y) = pmul X Y :=
          pnorm_eq_self _ (pmul_normal hXn hYn hXne hYne)
        have hEq : B = pmul X Y := Eq.trans (Eq.trans (pnorm_eq_self B hB).symm hXY) hcanon
        have hlen : B.length = X.length + Y.length - 1 := by
          rw [congrArg List.length hEq, pmul_length X Y hXne hYne]
        have hXn' : X.length ≤ n := by omega
        obtain ⟨q, hqI, hqX⟩ := ih X hXn hX2 hXn'
        exact ⟨q, hqI, Pdvd_trans hqX ⟨Y, hYn, hXY⟩⟩
      · refine ⟨B, ⟨hB, h2, ?_⟩, Pdvd_refl⟩
        intro X Y hXn hYn hXne hYne hXY
        by_cases hX1 : X.length = 1
        · exact Or.inl hX1
        · by_cases hY1 : Y.length = 1
          · exact Or.inr hY1
          · exfalso
            have hX1' : 1 ≤ X.length := by
              cases X with
              | nil => exact absurd rfl hXne
              | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
            have hY1' : 1 ≤ Y.length := by
              cases Y with
              | nil => exact absurd rfl hYne
              | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
            have hX2 : 2 ≤ X.length := by omega
            have hY2 : 2 ≤ Y.length := by omega
            exact hfac ⟨X, Y, hXn, hYn, hX2, hY2, hXY⟩

/-- The budget-free form: `B.length` is always enough. -/
theorem exists_irred_divisor' (B : List Real) (hB : PNormal B) (h2 : 2 ≤ B.length) :
    ∃ q : List Real, PIrred q ∧ Pdvd q B :=
  exists_irred_divisor B.length B hB h2 (Nat.le_refl _)

/-! ## Powers -/

noncomputable def ppow (q : List Real) : Nat → List Real
  | 0     => [1]
  | k + 1 => pmul q (ppow q k)

theorem peq_ppow_add : ∀ (q : List Real) (j l : Nat),
    PEq (ppow q (j + l)) (pmul (ppow q j) (ppow q l)) := by
  intro q j
  induction j with
  | zero =>
      intro l
      rw [show 0 + l = l from by omega]
      show PEq (ppow q l) (pmul [(1 : Real)] (ppow q l))
      exact (peq_pmul_one_left (ppow q l)).symm
  | succ j ih =>
      intro l
      show PEq (ppow q (j + 1 + l)) (pmul (pmul q (ppow q j)) (ppow q l))
      rw [show j + 1 + l = (j + l) + 1 from by omega]
      show PEq (pmul q (ppow q (j + l))) _
      refine PEq.trans (peq_pmul (PEq.refl q) (ih l)) ?_
      exact (pmul_assoc_pnorm q (ppow q j) (ppow q l)).symm

/-! ## The `q`-adic factorisation -/

/-- **Every nonzero polynomial factors as `qᵏ · M` with `q ∤ M`.** -/
theorem exists_ord_factor : ∀ (n : Nat) (q A : List Real), PIrred q → PNormal A → A ≠ [] →
    A.length ≤ n →
    ∃ (k : Nat) (M : List Real), PNormal M ∧ M ≠ [] ∧ ¬ Pdvd q M ∧ PEq A (pmul (ppow q k) M) := by
  intro n
  induction n with
  | zero =>
      intro q A _ _ hAne hn
      exfalso
      cases A with
      | nil => exact hAne rfl
      | cons _ _ => simp at hn
  | succ n ih =>
      intro q A hq hA hAne hn
      by_cases hd : Pdvd q A
      · obtain ⟨M0, hM0n, hM0⟩ := hd
        have hqn := hq.1
        have hqlen := hq.2.1
        have hqne : q ≠ [] := by
          intro h; rw [h] at hqlen; exact Nat.not_succ_le_zero 1 hqlen
        have hM0ne : M0 ≠ [] := by
          intro hnil
          rw [hnil, pmul_nil_right, pnorm_replicate_zero, pnorm_eq_self A hA] at hM0
          exact hAne hM0
        have hcanon : pnorm (pmul q M0) = pmul q M0 :=
          pnorm_eq_self _ (pmul_normal hqn hM0n hqne hM0ne)
        have hEq : A = pmul q M0 := Eq.trans (Eq.trans (pnorm_eq_self A hA).symm hM0) hcanon
        have hlen : A.length = q.length + M0.length - 1 := by
          rw [congrArg List.length hEq, pmul_length q M0 hqne hM0ne]
        have hM0n' : M0.length ≤ n := by omega
        obtain ⟨k, M, hMn, hMne, hMd, hM⟩ := ih q M0 hq hM0n hM0ne hM0n'
        refine ⟨k + 1, M, hMn, hMne, hMd, ?_⟩
        refine PEq.trans hM0 ?_
        refine PEq.trans (peq_pmul (PEq.refl q) hM) ?_
        show PEq (pmul q (pmul (ppow q k) M)) (pmul (pmul q (ppow q k)) M)
        exact (pmul_assoc_pnorm q (ppow q k) M).symm
      · exact ⟨0, A, hA, hAne, hd, (peq_pmul_one_left A).symm⟩

/-! ## Additivity — where Euclid's lemma is spent -/

/-- **`ord_q` is additive on products.** The exponents add, and the cofactor stays coprime to `q` —
the second half being exactly Euclid's lemma. -/
theorem ord_pmul {q A B M N : List Real} {j l : Nat} (hq : PIrred q)
    (hMn : PNormal M) (hMd : ¬ Pdvd q M) (hA : PEq A (pmul (ppow q j) M))
    (hNd : ¬ Pdvd q N) (hB : PEq B (pmul (ppow q l) N)) :
    ¬ Pdvd q (pmul M N) ∧ PEq (pmul A B) (pmul (ppow q (j + l)) (pmul M N)) := by
  refine ⟨fun hdvd => hNd (euclid_lemma hq hMn hMd hdvd), ?_⟩
  refine PEq.trans (peq_pmul hA hB) ?_
  -- (qʲ·M)·(qˡ·N) ≈ (qʲ·qˡ)·(M·N)
  refine PEq.trans (pmul_assoc_pnorm (ppow q j) M (pmul (ppow q l) N)) ?_
  refine PEq.trans (peq_pmul (PEq.refl (ppow q j))
      (PEq.trans (pmul_assoc_pnorm M (ppow q l) N).symm
        (PEq.trans (peq_pmul (peq_pmul_comm M (ppow q l)) (PEq.refl N))
          (pmul_assoc_pnorm (ppow q l) M N)))) ?_
  refine PEq.trans (pmul_assoc_pnorm (ppow q j) (ppow q l) (pmul M N)).symm ?_
  exact peq_pmul (peq_ppow_add q j l).symm (PEq.refl (pmul M N))

end MachLib
