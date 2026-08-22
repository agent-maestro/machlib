import MachLib.PolyFactor

/-!
# Cancellation, and uniqueness of the `q`-adic exponent

`PolyFactor` proved additivity of a *given* factorisation and said explicitly that uniqueness was
not supplied. This file supplies it, so `ord_q` is well defined and exponents can be **compared
across an equation** — which is what the pole-order count actually does.

## Cancellation comes from degree additivity, not from anything new

`c·X ≈ c·Y → X ≈ Y` reduces to `c·Z ≈ 0 → Z ≈ 0`, and that is `pmul_normal` plus `pmul_length`: for
canonical nonempty `c` and `Z`, the product is canonical of length `|c| + |Z| − 1 ≥ 1`, hence not the
zero polynomial. No integral-domain axiom is invoked — the absence of zero divisors was already spent
once, in `pmul_normal`, and this is that same fact used a second time.

## Uniqueness

If `A ≈ qʲ·M ≈ qˡ·N` with `q` dividing neither cofactor and `j ≤ l`, cancelling `qʲ` gives
`M ≈ q^(l−j)·N`. Were `l > j` that exhibits `q ∣ M`, contradicting the hypothesis. So `j = l`.
Cancelling `qʲ` needs `ppow q j` canonical and nonempty, which is one induction each.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## Subtraction identities -/

theorem peq_psub_self (Z : List Real) : PEq (psub Z Z) [] := by
  show pnorm (padd Z (pscale (0 - 1) Z)) = pnorm []
  rw [padd_neg_self, pnorm_replicate_zero]
  rfl

theorem peq_padd_psub_left (X Y : List Real) : PEq (padd (psub X Y) Y) X := by
  show pnorm (padd (padd X (pscale (0 - 1) Y)) Y) = pnorm X
  rw [padd_assoc, padd_comm (pscale (0 - 1) Y) Y, padd_neg_self]
  have h := pnorm_padd_replicate Y.length X []
  rw [List.nil_append, padd_nil_right] at h
  exact h

/-! ## Cancellation -/

/-- A nonzero multiple of a nonzero polynomial is nonzero — `pmul_normal` and `pmul_length` again. -/
theorem pmul_eq_nil_cancel {c Z : List Real} (hc : PNormal c) (hcne : c ≠ [])
    (h : PEq (pmul c Z) []) : PEq Z [] := by
  show pnorm Z = []
  rcases Classical.em (pnorm Z = []) with hz | hz
  · exact hz
  · exfalso
    have hcanon : pnorm (pmul c (pnorm Z)) = pmul c (pnorm Z) :=
      pnorm_eq_self _ (pmul_normal hc (pnorm_normal Z) hcne hz)
    have hlen : (pmul c (pnorm Z)).length = c.length + (pnorm Z).length - 1 :=
      pmul_length c (pnorm Z) hcne hz
    have hc1 : 1 ≤ c.length := by
      cases c with
      | nil => exact absurd rfl hcne
      | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
    have hz1 : 1 ≤ (pnorm Z).length := by
      cases hzl : pnorm Z with
      | nil => rw [hzl] at hz; exact absurd rfl hz
      | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
    have hnil : pmul c (pnorm Z) = [] := by
      rw [← hcanon, ← pnorm_pmul_right c Z]
      exact h
    rw [hnil] at hlen
    simp at hlen
    omega

theorem peq_pmul_cancel_left {c X Y : List Real} (hc : PNormal c) (hcne : c ≠ [])
    (h : PEq (pmul c X) (pmul c Y)) : PEq X Y := by
  have hzero : PEq (pmul c (psub X Y)) [] := by
    rw [pmul_psub_right]
    exact PEq.trans (peq_psub h (PEq.refl (pmul c Y))) (peq_psub_self (pmul c Y))
  have hXY : PEq (psub X Y) [] := pmul_eq_nil_cancel hc hcne hzero
  refine PEq.trans (peq_padd_psub_left X Y).symm ?_
  exact PEq.trans (peq_padd hXY (PEq.refl Y)) (PEq.refl Y)

/-! ## Powers are canonical and nonzero -/

theorem ppow_normal {q : List Real} (hq : PNormal q) (hqne : q ≠ []) :
    ∀ k : Nat, PNormal (ppow q k) ∧ ppow q k ≠ [] := by
  intro k
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · show PNormal [(1 : Real)]
        intro c hc
        have h1 : (1 : Real) = c := by simpa using hc
        rw [← h1]; exact one_ne_zero
      · show ([1] : List Real) ≠ []
        simp
  | succ k ih =>
      obtain ⟨hkn, hkne⟩ := ih
      refine ⟨pmul_normal hq hkn hqne hkne, ?_⟩
      intro hnil
      have hlen : (pmul q (ppow q k)).length = q.length + (ppow q k).length - 1 :=
        pmul_length q (ppow q k) hqne hkne
      have hq1 : 1 ≤ q.length := by
        cases q with
        | nil => exact absurd rfl hqne
        | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
      have hk1 : 1 ≤ (ppow q k).length := by
        cases hkl : ppow q k with
        | nil => rw [hkl] at hkne; exact absurd rfl hkne
        | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
      show False
      have hlen' : (ppow q (k + 1)).length = q.length + (ppow q k).length - 1 := hlen
      rw [hnil] at hlen'
      simp at hlen'
      omega

/-! ## The exponent is unique -/

theorem ord_unique_le {q A M N : List Real} (hq : PIrred q) {j l : Nat} (hjl : j ≤ l)
    (hMd : ¬ Pdvd q M) (hA : PEq A (pmul (ppow q j) M))
    (hB : PEq A (pmul (ppow q l) N)) : j = l := by
  have hqn := hq.1
  have hqlen := hq.2.1
  have hqne : q ≠ [] := by
    intro h; rw [h] at hqlen; exact Nat.not_succ_le_zero 1 hqlen
  obtain ⟨hjn, hjne⟩ := ppow_normal hqn hqne j
  -- cancel qʲ from both factorisations
  have hpow : PEq (ppow q l) (pmul (ppow q j) (ppow q (l - j))) := by
    have he : j + (l - j) = l := by omega
    have h := peq_ppow_add q j (l - j)
    rw [he] at h
    exact h
  have hsplit : PEq (pmul (ppow q l) N) (pmul (ppow q j) (pmul (ppow q (l - j)) N)) :=
    PEq.trans (peq_pmul hpow (PEq.refl N))
      (pmul_assoc_pnorm (ppow q j) (ppow q (l - j)) N)
  have hcancel : PEq M (pmul (ppow q (l - j)) N) :=
    peq_pmul_cancel_left hjn hjne (PEq.trans hA.symm (PEq.trans hB hsplit))
  -- if the leftover exponent were positive, `q` would divide `M`
  rcases Nat.eq_zero_or_pos (l - j) with h0 | hpos
  · omega
  · exfalso
    obtain ⟨m, hm⟩ : ∃ m, l - j = m + 1 := ⟨l - j - 1, by omega⟩
    refine hMd ⟨pnorm (pmul (ppow q m) N), pnorm_normal _, ?_⟩
    rw [← pnorm_pmul_right q (pmul (ppow q m) N)]
    refine PEq.trans hcancel ?_
    rw [hm]
    show PEq (pmul (pmul q (ppow q m)) N) (pmul q (pmul (ppow q m) N))
    exact pmul_assoc_pnorm q (ppow q m) N

/-- **The `q`-adic exponent is unique**, so `ord_q` is well defined and exponents may be compared
across an equation — which is what a pole-order count does. -/
theorem ord_unique {q A M N : List Real} {j l : Nat} (hq : PIrred q)
    (hMd : ¬ Pdvd q M) (hNd : ¬ Pdvd q N)
    (hA : PEq A (pmul (ppow q j) M)) (hB : PEq A (pmul (ppow q l) N)) : j = l := by
  rcases Nat.le_total j l with h | h
  · exact ord_unique_le hq h hMd hA hB
  · exact (ord_unique_le hq h hNd hB hA).symm

end MachLib
