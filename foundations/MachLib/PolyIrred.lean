import MachLib.PolyGcd

/-!
# Irreducibility, and Euclid's lemma

`PIrred q` says `q` is nonconstant and admits no factorisation into two nonconstant polynomials.
That is the *factorisation* form, not the "every divisor is a unit or an associate" form, and the
choice matters: the divisor form would have to be assumed, whereas the factorisation form **derives**
it (`Pdvd_irred_dichotomy`) from `pmul_length` — degree is additive, so a factor of a degree-`n`
polynomial is either constant or cofactor-constant.

## Units, canonically

A unit is a canonical list of length **one**. Canonicity does the work: a length-one canonical list
is `[u]` with `u ≠ 0`, which is exactly a nonzero constant, so no separate nonvanishing side
condition is ever carried. Likewise "associate of `q`" is just "same length as `q`".

## The shape of Euclid's lemma

With the gcd complete, `q ∤ a` and `q ∣ ab ⟹ q ∣ b` is assembly:

* `eea` on `(q, a)` returns `g` with `g ≈ s·q + t·a`, `g ∣ q` and `g ∣ a`;
* `g ∣ q` plus irreducibility forces `g` to be a unit **or** an associate of `q`;
* the associate branch would give `q ∣ a`, which is excluded by hypothesis — so `g` is a unit;
* scaling the Bézout identity by `g`'s inverse gives `1 ≈ s'·q + t'·a`, and multiplying by `b`
  writes `b` as `q·(…) + t'·(ab)`, both terms divisible by `q`.

Every step is a `PEq` rewrite over lemmas already proved. Nothing new is needed about polynomials.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## `eea` returns a canonical polynomial -/

theorem eea_normal : ∀ (fuel : Nat) (A B : List Real), PNormal A → PNormal B → B.length ≤ fuel →
    PNormal (eea fuel A B).1 := by
  intro fuel
  induction fuel with
  | zero => intro A B hA _ _; rw [eea_zero]; exact hA
  | succ fuel ih =>
      intro A B hA hB hlen
      rw [eea_succ]
      by_cases hB0 : B.length = 0
      · rw [if_pos hB0]; exact hA
      · rw [if_neg hB0]
        have hBne : B ≠ [] := by intro h; rw [h] at hB0; exact hB0 rfl
        obtain ⟨_, hnr, hlr⟩ := pdivmod_spec' A B hA hB hBne
        exact ih B (pdivmod A.length A B).2 hB hnr (by omega)

/-! ## Units and irreducibility -/

/-- A unit: a canonical list of length one, i.e. a nonzero constant. Canonicity supplies the
nonvanishing, so no side condition travels with this. -/
def PUnit (u : List Real) : Prop := u.length = 1

/-- **Irreducible**: canonical, nonconstant, and not a product of two nonconstants. -/
def PIrred (q : List Real) : Prop :=
  PNormal q ∧ 2 ≤ q.length ∧
    ∀ X Y : List Real, PNormal X → PNormal Y → X ≠ [] → Y ≠ [] →
      PEq q (pmul X Y) → X.length = 1 ∨ Y.length = 1

/-- **Unit or associate**, derived rather than assumed: degree is additive, so a divisor of an
irreducible is constant or has a constant cofactor. -/
theorem Pdvd_irred_dichotomy {q d : List Real} (hq : PIrred q)
    (hd : PNormal d) (hdne : d ≠ []) (h : Pdvd d q) : d.length = 1 ∨ d.length = q.length := by
  obtain ⟨hqn, hqlen, hfac⟩ := hq
  obtain ⟨M, hMn, hM⟩ := h
  have hMne : M ≠ [] := by
    intro hnil
    rw [hnil, pmul_nil_right, pnorm_replicate_zero, pnorm_eq_self q hqn] at hM
    rw [hM] at hqlen
    simp at hqlen
  rcases hfac d M hd hMn hdne hMne hM with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ?_
    have hcanon : pnorm (pmul d M) = pmul d M := pnorm_eq_self _ (pmul_normal hd hMn hdne hMne)
    have hlen : q.length = (pmul d M).length := by
      rw [← pnorm_eq_self q hqn, hM, hcanon]
    rw [hlen, pmul_length d M hdne hMne, h1]
    have : 1 ≤ d.length := by
      cases d with
      | nil => exact absurd rfl hdne
      | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
    omega

/-! ## Scaling by an inverse -/

theorem one_div_ne_zero {c : Real} (hc : c ≠ 0) : 1 / c ≠ 0 := by
  intro h
  have h1 : c * (1 / c) = 1 := mul_inv c hc
  rw [h] at h1
  have h0 : c * 0 = 0 := by mach_ring
  rw [h0] at h1
  exact zero_ne_one_ax h1

theorem peq_pmul_singleton_right {X : List Real} (hX : X ≠ []) (c : Real) :
    PEq (pmul X [c]) (pscale c X) := by
  refine PEq.trans (peq_pmul_comm X [c]) ?_
  rw [pmul_singleton c X hX]

/-- An associate of `q` divides `q` back: if `q ≈ c·d` with `c ≠ 0`, then `q ∣ d`. -/
theorem Pdvd_of_associate {q d : List Real} (hqne : q ≠ []) {c : Real} (hc : c ≠ 0)
    (h : PEq q (pscale c d)) : Pdvd q d := by
  refine ⟨[1 / c], ?_, ?_⟩
  · intro b hb
    have hb1 : 1 / c = b := by simpa using hb
    rw [← hb1]; exact one_div_ne_zero hc
  · refine Eq.trans ?_ (peq_pmul_singleton_right hqne (1 / c)).symm
    refine Eq.trans ?_ (peq_pscale (1 / c) h).symm
    rw [pscale_pscale]
    have hinv : (1 / c) * c = 1 := by
      rw [mul_comm]; exact mul_inv c hc
    rw [hinv, pscale_one]

/-! ## Euclid's lemma -/

/-- **`q` irreducible, `q ∤ a`, `q ∣ ab` ⟹ `q ∣ b`.** -/
theorem euclid_lemma {q a b : List Real} (hq : PIrred q) (ha : PNormal a)
    (hnd : ¬ Pdvd q a) (hab : Pdvd q (pmul a b)) : Pdvd q b := by
  have hqn := hq.1
  have hqlen := hq.2.1
  have hqne : q ≠ [] := by
    intro h; rw [h] at hqlen; exact Nat.not_succ_le_zero 1 hqlen
  have hbez := eea_bezout a.length q a hqn ha (Nat.le_refl _)
  obtain ⟨hgq, hga⟩ := eea_divides a.length q a hqn ha (Nat.le_refl _)
  have hgn := eea_normal a.length q a hqn ha (Nat.le_refl _)
  have hgne : (eea a.length q a).1 ≠ [] := by
    intro hnil
    obtain ⟨M, _, hM⟩ := hgq
    rw [hnil, show pmul ([] : List Real) M = [] from rfl, pnorm_eq_self q hqn] at hM
    rw [hM] at hqlen; exact Nat.not_succ_le_zero 1 hqlen
  rcases Pdvd_irred_dichotomy hq hgn hgne hgq with hunit | hassoc
  · -- `g` is a unit `[u]`; scale the Bézout identity by `1/u`
    obtain ⟨u, hu⟩ : ∃ u, (eea a.length q a).1 = [u] := by
      cases hgl : (eea a.length q a).1 with
      | nil => rw [hgl] at hgne; exact absurd rfl hgne
      | cons c cs =>
          cases cs with
          | nil => exact ⟨c, rfl⟩
          | cons d ds => rw [hgl] at hunit; simp at hunit
    have hune : u ≠ 0 := hgn u (by rw [hu]; rfl)
    have hinv : (1 / u) * u = 1 := by rw [mul_comm]; exact mul_inv u hune
    -- 1 ≈ s'·q + t'·a
    have hone : PEq [(1 : Real)]
        (padd (pmul (pscale (1 / u) (eea a.length q a).2.1) q)
              (pmul (pscale (1 / u) (eea a.length q a).2.2) a)) := by
      have h := peq_pscale (1 / u) hbez
      rw [hu] at h
      show pnorm [(1 : Real)] = _
      rw [show pscale (1 / u) [u] = [(1 / u) * u] from rfl, hinv] at h
      rw [h, pscale_padd, pmul_pscale_left, pmul_pscale_left]
    -- b ≈ (s'·q)·b + (t'·a)·b, and `q` divides both summands
    have hb1 : PEq b (padd (pmul (pmul (pscale (1 / u) (eea a.length q a).2.1) q) b)
                          (pmul (pmul (pscale (1 / u) (eea a.length q a).2.2) a) b)) := by
      refine PEq.trans (peq_pmul_one_left b).symm ?_
      refine PEq.trans (peq_pmul hone (PEq.refl b)) ?_
      show pnorm _ = pnorm _
      rw [pmul_padd_left]
    refine Pdvd_of_peq hb1 (Pdvd_padd ?_ ?_)
    · refine Pdvd_of_peq (peq_pmul_comm _ b) ?_
      exact Pdvd_pmul b (Pdvd_pmul _ Pdvd_refl)
    · refine Pdvd_of_peq (pmul_assoc_pnorm _ a b) ?_
      exact Pdvd_pmul _ hab
  · -- `g` is an associate of `q`, which would give `q ∣ a` — excluded by hypothesis
    exfalso
    obtain ⟨M, hMn, hM⟩ := hgq
    have hMne : M ≠ [] := by
      intro hnil
      rw [hnil, pmul_nil_right, pnorm_replicate_zero, pnorm_eq_self q hqn] at hM
      rw [hM] at hqlen; exact Nat.not_succ_le_zero 1 hqlen
    have hcanon : pnorm (pmul (eea a.length q a).1 M) = pmul (eea a.length q a).1 M :=
      pnorm_eq_self _ (pmul_normal hgn hMn hgne hMne)
    have hMlen : M.length = 1 := by
      -- term-level composition: rewriting `q` here would also hit the `q` inside `eea a.length q a`
      have hEq : q = pmul (eea a.length q a).1 M :=
        Eq.trans (Eq.trans (pnorm_eq_self q hqn).symm hM) hcanon
      have hlen : q.length = (pmul (eea a.length q a).1 M).length := congrArg List.length hEq
      rw [pmul_length _ M hgne hMne] at hlen
      have h1 : 1 ≤ M.length := by
        cases M with
        | nil => exact absurd rfl hMne
        | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
      omega
    obtain ⟨c, hc⟩ : ∃ c, M = [c] := by
      cases hMl : M with
      | nil => rw [hMl] at hMne; exact absurd rfl hMne
      | cons c cs =>
          cases cs with
          | nil => exact ⟨c, rfl⟩
          | cons d ds => rw [hMl] at hMlen; simp at hMlen
    have hcne : c ≠ 0 := hMn c (by rw [hc]; rfl)
    have hassoc' : PEq q (pscale c (eea a.length q a).1) := by
      refine Eq.trans hM ?_
      rw [hc]
      exact peq_pmul_singleton_right hgne c
    exact hnd (Pdvd_trans (Pdvd_of_associate hqne hcne hassoc') hga)

end MachLib
