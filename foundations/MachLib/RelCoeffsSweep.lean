import MachLib.BipolyTrim
import MachLib.BipevComposition

/-!
# The sweep: choosing between the three readings

`RelCoeffsLead` reads the top coefficient off `relCoeffs` in three cases, `RelCoeffsLand` and
`RelCoeffsEqCase` close each of them, and `BipolyTrim` supplies the `As ++ [α]` shape they all need.
This module does the remaining work: **decide which case applies** and discharge the side conditions
the landings carry.

The decision is `Nat.lt_trichotomy` on `|Bs|` against `|As|`, plus a fourth arm for `Cd₁` trimming
away entirely.

## The side conditions are discharged here, not assumed

Each landing carries its nonvanishing and characteristic-zero inputs as hypotheses, deliberately, so
that the algebra stayed inside the spine. This module is outside the spine and pays them:

* `pnorm X ≠ []` from `¬ Pdvd q X` — everything divides the zero polynomial, so a nonzero-divisibility
  hypothesis already says the thing is nonzero;
* `pnorm D ≠ []` from `ord_deriv_cross`'s witness, which is coprime to `q` and therefore nonzero;
* `¬ Pdvd q ((b−a)·1)` from `not_Pdvd_pnsum_one'`, which proves `n·1 > 0` and costs the order axioms.

That last one is exactly why the landings did not discharge it themselves.
-/

namespace MachLib

open Real

/-! ## The transfer `BipolyTrim` could not state

`expCoeffs` mentions `exp`, so this cannot live in the algebra spine — see (bw), where putting it
there was tried and the ledger convicted it. -/

/-- **Trimming every coefficient leaves the germ-coefficient list literally unchanged.** -/
theorem expCoeffs_map_bitrim (S : Real → Real) (Cs : List (List (List Real))) :
    expCoeffs S (Cs.map bitrim) = expCoeffs S Cs := by
  show (Cs.map bitrim).map (fun C => fun x => bipev C x (exp (S x)))
      = Cs.map (fun C => fun x => bipev C x (exp (S x)))
  rw [List.map_map]
  refine congrArg (fun f => Cs.map f) ?_
  funext C x
  exact bipev_bitrim C x (exp (S x))

/-! ## Side conditions -/

/-- Everything divides the zero polynomial, so `¬ Pdvd q X` already says `X` is nonzero. -/
theorem pnorm_ne_nil_of_not_Pdvd {q X : List Real} (h : ¬ Pdvd q X) : pnorm X ≠ [] := by
  intro hz
  refine h (Pdvd_of_peq ?_ Pdvd_zero)
  show pnorm X = pnorm ([] : List Real)
  rw [hz]; rfl

/-! ## The fourth reading: `Cd₁` trims away entirely -/

theorem bimul_nil_right : ∀ X : List (List Real),
    bimul X [] = List.replicate X.length [] := by
  intro X
  induction X with
  | nil => rfl
  | cons A As ih =>
      show biadd (biscale A []) (([] : List Real) :: bimul As []) = _
      show biadd [] (([] : List Real) :: bimul As []) = _
      show ([] : List Real) :: bimul As [] = _
      rw [ih]
      rfl

/-! ## The dispatcher -/

/-- **The sweep, for a relation whose two top coefficients both survive trimming.** The three
readings are selected by `Nat.lt_trichotomy` on the two `E`-degrees, and every side condition the
landings carry is discharged here. -/
theorem sweep_impossible {q P Q D : List Real} {m : Nat}
    {As Bs : List (List Real)} {α β : List Real}
    (hq : PIrred q)
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hchar : ∀ r : Nat, DerivCoprime q (r + 1))
    (hDdef : D = psub (pmul (pderiv P) Q) (pmul P (pderiv Q)))
    (hαn : pnorm α ≠ []) (hβn : pnorm β ≠ [])
    (hkd : ¬ Pdvd q (pnsum (m + 1) [(1 : Real)]))
    (hnil : ∀ A : List Real, A ∈ relCoeffs P Q D m (As ++ [α]) (Bs ++ [β]) → pnorm A = []) :
    False := by
  subst hDdef
  have hPne : pnorm P ≠ [] := pnorm_ne_nil_of_not_Pdvd hPd
  have hQnn : pnorm Q ≠ [] := by rw [pnorm_eq_self _ hQn]; exact hQne
  have hkn : pnorm (pnsum (m + 1) [(1 : Real)]) ≠ [] := pnorm_ne_nil_of_not_Pdvd hkd
  -- `D` is nonzero because its `q`-adic witness is coprime to `q`
  have hDn : pnorm (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) ≠ [] := by
    obtain ⟨r, Qt, _, _, hQtd, hQfac⟩ :=
      exists_ord_factor Q.length q Q hq hQn hQne (Nat.le_refl _)
    cases r with
    | zero => exact absurd (Pdvd_of_peq (PEq.trans hQfac (peq_pmul_one_left Qt)).symm hQd) hQtd
    | succ r' =>
        obtain ⟨Ec, hEcd, hEc⟩ :=
          ord_deriv_cross hq hPd hQtd (hchar r') hPn hQfac
        intro hz
        refine pnorm_ne_nil_of_not_Pdvd hEcd (pmul_nil_cancel' (pnorm_ppow_ne_nil hq r') ?_)
        refine PEq.trans hEc.symm ?_
        show pnorm (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) = pnorm ([] : List Real)
        rw [hz]; rfl
  rcases Nat.lt_trichotomy Bs.length As.length with hlt | heq | hgt
  · -- `a > b`: `K·α²` alone at the top
    obtain ⟨Z, hZ⟩ := relCoeffs_top_gt (P := P) (m := m) (β := β) hlt
    exact top_gt_impossible hαn hQnn hDn hkn (pnorm_top_of_all_nil hZ hnil)
  · -- `a = b`: the logarithmic count
    obtain ⟨Z, hZ⟩ := relCoeffs_top_eq (P := P) (m := m) heq.symm
    rw [heq] at hZ
    exact top_eq_impossible hq hPd hPn hQn hQne hQd hchar rfl hαn hβn hPne hQnn hkd
      (pnorm_top_of_all_nil hZ hnil)
  · -- `a < b`: the exponential count, through the other branch's landing
    obtain ⟨Z, hZ⟩ := relCoeffs_top_lt (P := P) (m := m) hgt
    exact top_le_impossible hq hPd hPn hQn hQne hQd hchar rfl (Nat.le_of_lt hgt)
      hαn hβn hPne (not_Pdvd_pnsum_one' hq (by omega)) (pnorm_top_of_all_nil hZ hnil)

/-! ## The fourth arm: `Cd₁` is the zero germ

The subtracted product does **not** vanish when `Cd₁ = []` — `bimul X [] = replicate |X| []` — so it
is a run of `[]` entries of length `a+1` against `T₁`'s `2a+1`. For `a ≥ 1` that is a strict gap and
the top is `α·(K·α)` exactly; at `a = 0` the two coincide and the top picks up a `pmul [0-1] []`
tail, which is `pnorm`-nil. Both give a top **`PEq` to** `α·(K·α)`, and `top_gt_impossible` consumes
`pnorm _ = []`, which is `PEq`-invariant — so the arm costs a reading and no new landing. -/

theorem relCoeffs_top_of_nil_second {P Q D : List Real} {m : Nat}
    {As : List (List Real)} {α : List Real} :
    ∃ (Z : List (List Real)) (t : List Real),
      relCoeffs P Q D m (As ++ [α]) [] = Z ++ [t]
        ∧ PEq t (pmul α (pmul (relK Q D m) α)) := by
  obtain ⟨Z1, hZ1⟩ := bimul_concat As (biscale (relK Q D m) As) α (pmul (relK Q D m) α)
  have hl1 : Z1.length = As.length + (biscale (relK Q D m) As).length := by
    have h := bimul_length (As ++ [α]) (biscale (relK Q D m) As ++ [pmul (relK Q D m) α])
      (by simp) (by simp)
    rw [hZ1] at h
    simp at h
    omega
  have hT1 : bimul (As ++ [α])
      (biadd (biscale P (dcoeffs (pmul Q Q) D 0 [])) (biscale (relK Q D m) (As ++ [α])))
      = Z1 ++ [pmul α (pmul (relK Q D m) α)] := by
    show bimul (As ++ [α]) (biadd [] (biscale (relK Q D m) (As ++ [α]))) = _
    show bimul (As ++ [α]) (biscale (relK Q D m) (As ++ [α])) = _
    rw [biscale_concat]; exact hZ1
  have hT2 : bimul (biscale P (dcoeffs (pmul Q Q) D 0 (As ++ [α]))) []
      = List.replicate (As.length + 1) [] := by
    rw [bimul_nil_right, biscale_dcoeffs_length]
    simp
  rw [relCoeffs_unfold, hT1, hT2]
  rw [biscale_length] at hl1
  by_cases hA : As.length = 0
  · -- both sides have length one: the tails add, and the added one is `pnorm`-nil
    have hz : Z1 = [] := List.eq_nil_of_length_eq_zero (by rw [hl1, hA])
    have hrep : List.replicate (As.length + 1) ([] : List Real) = [] ++ [([] : List Real)] := by
      rw [hA]; rfl
    refine ⟨bisub [] [], padd (pmul α (pmul (relK Q D m) α)) (pmul [0 - 1] []), ?_, ?_⟩
    · rw [hz, hrep]
      exact bisub_concat_both [] [] rfl _ _
    · show pnorm (padd (pmul α (pmul (relK Q D m) α)) (pmul [0 - 1] []))
          = pnorm (pmul α (pmul (relK Q D m) α))
      rw [pmul_nil_right]
      have h := pnorm_padd_replicate ([(0 : Real) - 1]).length
        (pmul α (pmul (relK Q D m) α)) []
      rw [List.nil_append, padd_nil_right] at h
      exact h
  · -- a strict gap: the subtracted run never reaches the top
    refine ⟨bisub Z1 (List.replicate (As.length + 1) []), pmul α (pmul (relK Q D m) α),
      ?_, PEq.refl _⟩
    refine bisub_concat_left _ _ ?_ _
    rw [List.length_replicate, hl1]
    omega

/-- **The fourth arm of the dispatcher.** -/
theorem sweep_impossible_nil_second {q P Q D : List Real} {m : Nat}
    {As : List (List Real)} {α : List Real}
    (hq : PIrred q)
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hchar : ∀ r : Nat, DerivCoprime q (r + 1))
    (hDdef : D = psub (pmul (pderiv P) Q) (pmul P (pderiv Q)))
    (hαn : pnorm α ≠ [])
    (hkd : ¬ Pdvd q (pnsum (m + 1) [(1 : Real)]))
    (hnil : ∀ A : List Real, A ∈ relCoeffs P Q D m (As ++ [α]) [] → pnorm A = []) :
    False := by
  subst hDdef
  have hQnn : pnorm Q ≠ [] := by rw [pnorm_eq_self _ hQn]; exact hQne
  have hkn : pnorm (pnsum (m + 1) [(1 : Real)]) ≠ [] := pnorm_ne_nil_of_not_Pdvd hkd
  have hDn : pnorm (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) ≠ [] := by
    obtain ⟨r, Qt, _, _, hQtd, hQfac⟩ :=
      exists_ord_factor Q.length q Q hq hQn hQne (Nat.le_refl _)
    cases r with
    | zero => exact absurd (Pdvd_of_peq (PEq.trans hQfac (peq_pmul_one_left Qt)).symm hQd) hQtd
    | succ r' =>
        obtain ⟨Ec, hEcd, hEc⟩ :=
          ord_deriv_cross hq hPd hQtd (hchar r') hPn hQfac
        intro hz
        refine pnorm_ne_nil_of_not_Pdvd hEcd (pmul_nil_cancel' (pnorm_ppow_ne_nil hq r') ?_)
        refine PEq.trans hEc.symm ?_
        show pnorm (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) = pnorm ([] : List Real)
        rw [hz]; rfl
  obtain ⟨Z, t, hZ, ht⟩ := relCoeffs_top_of_nil_second (P := P) (Q := Q)
    (D := psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) (m := m) (As := As) (α := α)
  exact top_gt_impossible hαn hQnn hDn hkn (Eq.trans ht.symm (pnorm_top_of_all_nil hZ hnil))

end MachLib
