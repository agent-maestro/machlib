import MachLib.PolyPoleOrder

/-!
# The companion bound, and comparing exponents across an equation

Two ingredients remain between `ord_deriv_cross` and the contradiction `CRUX.md` §3 derives.

## The derivative drops the order by at most one

`ord_q(X) ≥ k+1 ⟹ ord_q(X') ≥ k`, and it is a **one-liner** from `peq_pderiv_ppow_mul`: that lemma
already exhibits `X'` as `qᵏ·(…)`, so the divisibility is read straight off the factorisation rather
than re-derived. Worth noting because the companion bound looked like separate work when the count
was planned, and is not.

## The companion bound

`ord_q(u'v − uv') ≥ k + l − 1` then needs no derivative reasoning at all: `q^(k−1) ∣ u'` and
`qˡ ∣ v` give `q^(k+l−1) ∣ u'v`; `qᵏ ∣ u` and `q^(l−1) ∣ v'` give the same for `uv'`; and `Pdvd` is
closed under subtraction. Note this direction needs **no coprimality** — unlike `ord_deriv_cross`,
which is exact and therefore does.

## Comparing exponents

`q^a ∣ X` and `X ≈ q^b·W` with `q ∤ W` gives `a ≤ b`. The proof is `exists_ord_factor` on the
cofactor followed by `ord_unique`: whatever power of `q` hides in the cofactor pushes `a` up to
exactly `b`. This is where uniqueness earns its place — without it the count could only conclude
`≤` in the wrong direction.
-/

namespace MachLib

open Real

attribute [local instance] Classical.propDecidable

/-! ## Divisibility by powers -/

theorem Pdvd_ppow_pmul {q A B : List Real} {a b : Nat}
    (hA : Pdvd (ppow q a) A) (hB : Pdvd (ppow q b) B) :
    Pdvd (ppow q (a + b)) (pmul A B) := by
  obtain ⟨M, _, hM⟩ := hA
  obtain ⟨N, _, hN⟩ := hB
  refine ⟨pnorm (pmul M N), pnorm_normal _, ?_⟩
  rw [← pnorm_pmul_right (ppow q (a + b)) (pmul M N)]
  refine PEq.trans (peq_pmul hM hN) ?_
  -- (qᵃ·M)·(qᵇ·N) ≈ q^(a+b)·(M·N)
  refine PEq.trans (pmul_assoc_pnorm (ppow q a) M (pmul (ppow q b) N)) ?_
  refine PEq.trans (peq_pmul (PEq.refl (ppow q a)) (peq_pmul_left_comm M (ppow q b) N)) ?_
  refine PEq.trans (pmul_assoc_pnorm (ppow q a) (ppow q b) (pmul M N)).symm ?_
  exact peq_pmul (peq_ppow_add q a b).symm (PEq.refl (pmul M N))

theorem Pdvd_ppow_of_peq {q X Xt : List Real} {a : Nat}
    (h : PEq X (pmul (ppow q a) Xt)) : Pdvd (ppow q a) X :=
  ⟨pnorm Xt, pnorm_normal _, by
    rw [← pnorm_pmul_right (ppow q a) Xt]; exact h⟩

/-- Everything is divisible by `q⁰ = [1]`. -/
theorem Pdvd_one (A : List Real) : Pdvd (ppow q 0) A := by
  refine ⟨pnorm A, pnorm_normal _, ?_⟩
  show pnorm A = pnorm (pmul [(1 : Real)] (pnorm A))
  rw [peq_pmul_one_left (pnorm A), pnorm_idem]

/-- Divisibility by a power weakens to any smaller power. -/
theorem Pdvd_ppow_mono {q X : List Real} {a b : Nat} (hab : b ≤ a)
    (h : Pdvd (ppow q a) X) : Pdvd (ppow q b) X := by
  obtain ⟨M, _, hM⟩ := h
  refine ⟨pnorm (pmul (ppow q (a - b)) M), pnorm_normal _, ?_⟩
  show pnorm X = pnorm (pmul (ppow q b) (pnorm (pmul (ppow q (a - b)) M)))
  rw [← pnorm_pmul_right (ppow q b) (pmul (ppow q (a - b)) M)]
  refine PEq.trans hM ?_
  have he : b + (a - b) = a := by omega
  refine PEq.trans (peq_pmul ?_ (PEq.refl M)) (pmul_assoc_pnorm (ppow q b) (ppow q (a - b)) M)
  have h2 := peq_ppow_add q b (a - b)
  rw [he] at h2
  exact h2

/-! ## The derivative drops the order by at most one -/

/-- **`ord_q(X) ≥ k+1 ⟹ ord_q(X') ≥ k`** — read straight off the power-rule factorisation. -/
theorem ord_deriv_drop {q X Xt : List Real} {k : Nat}
    (h : PEq X (pmul (ppow q (k + 1)) Xt)) : Pdvd (ppow q k) (pderiv X) :=
  Pdvd_ppow_of_peq (peq_pderiv_ppow_mul k h)

/-- The order-`0` case too: `q⁰` divides every derivative, vacuously. -/
theorem ord_deriv_drop' {q X Xt : List Real} {k : Nat}
    (h : PEq X (pmul (ppow q k) Xt)) : Pdvd (ppow q (k - 1)) (pderiv X) := by
  cases k with
  | zero => exact Pdvd_one (pderiv X)
  | succ j =>
      have he : (j + 1) - 1 = j := by omega
      rw [he]
      exact ord_deriv_drop h

/-! ## The companion bound -/

/-- **`ord_q(u'v − uv') ≥ k + l − 1`** for **arbitrary** `k, l`, truncated subtraction included.

Stated generally on purpose. An earlier draft required `k, l ≥ 1` to dodge `Nat` subtraction, which
would have been a real restriction rather than a cosmetic one: in the relation the count is aimed at,
`u` and `v` are coefficient polynomials with no reason to be divisible by `q` at all. No coprimality
is required — this direction is a bound, not an identity. -/
theorem ord_cross_lower {q u v ut vt : List Real} {k l : Nat}
    (hu : PEq u (pmul (ppow q k) ut)) (hv : PEq v (pmul (ppow q l) vt)) :
    Pdvd (ppow q (k + l - 1)) (psub (pmul (pderiv u) v) (pmul u (pderiv v))) := by
  have h1 : Pdvd (ppow q ((k - 1) + l)) (pmul (pderiv u) v) :=
    Pdvd_ppow_pmul (ord_deriv_drop' hu) (Pdvd_ppow_of_peq hv)
  have h2 : Pdvd (ppow q (k + (l - 1))) (pmul u (pderiv v)) :=
    Pdvd_ppow_pmul (Pdvd_ppow_of_peq hu) (ord_deriv_drop' hv)
  refine Pdvd_psub (Pdvd_ppow_mono ?_ h1) (Pdvd_ppow_mono ?_ h2) <;> omega

/-! ## Comparing exponents across an equation -/

/-- **`q^a ∣ X` and `X ≈ q^b·W` with `q ∤ W` gives `a ≤ b`.** Uniqueness of the exponent is what
makes this an inequality in the useful direction. -/
theorem ord_le_of_dvd {q X W : List Real} {a b : Nat} (hq : PIrred q)
    (hdvd : Pdvd (ppow q a) X) (hW : PEq X (pmul (ppow q b) W)) (hWd : ¬ Pdvd q W) : a ≤ b := by
  obtain ⟨Y, hYn, hY⟩ := hdvd
  have hqn := hq.1
  have hqlen := hq.2.1
  have hqne : q ≠ [] := by
    intro h; rw [h] at hqlen; exact Nat.not_succ_le_zero 1 hqlen
  obtain ⟨hpn, hpne⟩ := ppow_normal hqn hqne a
  rcases Classical.em (Y = []) with hYnil | hYne
  · -- X is the zero polynomial, so W is too — contradicting `q ∤ W`
    exfalso
    rw [hYnil, pmul_nil_right, pnorm_replicate_zero] at hY
    have hWz : PEq (pmul (ppow q b) W) [] := by
      show pnorm (pmul (ppow q b) W) = pnorm []
      rw [← hW, hY]; rfl
    obtain ⟨hbn, hbne⟩ := ppow_normal hqn hqne b
    exact hWd (Pdvd_of_peq (pmul_eq_nil_cancel hbn hbne hWz) Pdvd_zero)
  · -- factor the cofactor; uniqueness pins a + s = b
    obtain ⟨s, M, hMn, hMne, hMd, hM⟩ := exists_ord_factor Y.length q Y hq hYn hYne (Nat.le_refl _)
    have hXas : PEq X (pmul (ppow q (a + s)) M) := by
      refine PEq.trans hY ?_
      refine PEq.trans (peq_pmul (PEq.refl (ppow q a)) hM) ?_
      refine PEq.trans (pmul_assoc_pnorm (ppow q a) (ppow q s) M).symm ?_
      exact peq_pmul (peq_ppow_add q a s).symm (PEq.refl M)
    have : a + s = b := ord_unique hq hMd hWd hXas hW
    omega

/-! ## Chaining orders without carrying canonicity

`ord_pmul` needs its first cofactor canonical, for `euclid_lemma`. Chaining it three times would
drag a `PNormal` hypothesis along for every intermediate product. Instead the cofactor is normalised
at each step: `Pdvd` depends only on `pnorm`, so replacing a cofactor by its normal form changes
neither the divisibility nor the factorisation. -/

theorem Pdvd_pnorm {q M : List Real} (h : ¬ Pdvd q M) : ¬ Pdvd q (pnorm M) := by
  intro hd
  exact h (Pdvd_of_peq (pnorm_idem M).symm hd)

/-- `ord_pmul` with the cofactor normalised on the way out. -/
theorem ord_pmul_norm {q A B M N : List Real} (hq : PIrred q) {j l : Nat}
    (hMd : ¬ Pdvd q M) (hA : PEq A (pmul (ppow q j) M))
    (hNd : ¬ Pdvd q N) (hB : PEq B (pmul (ppow q l) N)) :
    ∃ W : List Real, ¬ Pdvd q W ∧ PNormal W ∧ PEq (pmul A B) (pmul (ppow q (j + l)) W) := by
  have hA' : PEq A (pmul (ppow q j) (pnorm M)) := by
    show pnorm A = pnorm (pmul (ppow q j) (pnorm M))
    rw [← pnorm_pmul_right (ppow q j) M]
    exact hA
  obtain ⟨hcop, hfac⟩ :=
    ord_pmul hq (pnorm_normal M) (Pdvd_pnorm hMd) hA' hNd hB
  refine ⟨pnorm (pmul (pnorm M) N), Pdvd_pnorm hcop, pnorm_normal _, ?_⟩
  show pnorm (pmul A B) = pnorm (pmul (ppow q (j + l)) (pnorm (pmul (pnorm M) N)))
  rw [← pnorm_pmul_right (ppow q (j + l)) (pmul (pnorm M) N)]
  exact hfac

/-! ## The contradiction

`CRUX.md` §3's count, assembled. The left side of the identity carries `q^(k+l+1+2(m+1))`; the right
side has **exact** order `m + (k+1) + (l+1)`. Equating them forces
`k+l+2m+3 ≤ k+l+m+2`, i.e. `m+1 ≤ 0`, which is false. -/

/-- **The pole-order contradiction.** No real-pole hypothesis, no FTA, arbitrary irreducible `q`;
the only input beyond the field axioms is `DerivCoprime`. -/
theorem pole_order_contradiction {q P Q Qt u ut v vt Nc : List Real} (hq : PIrred q)
    {k l m : Nat}
    (hu : PEq u (pmul (ppow q k) ut)) (hutd : ¬ Pdvd q ut)
    (hv : PEq v (pmul (ppow q l) vt)) (hvtd : ¬ Pdvd q vt)
    (hQ : PEq Q (pmul (ppow q (m + 1)) Qt)) (hQtd : ¬ Pdvd q Qt)
    (hNd : ¬ Pdvd q Nc)
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hT : DerivCoprime q (m + 1)) (hTn : PNormal (pnsum (m + 1) (pderiv q)))
    (hident : PEq (pmul (psub (pmul (pderiv u) v) (pmul u (pderiv v))) (pmul Q Q))
                  (pmul (pmul Nc (psub (pmul (pderiv P) Q) (pmul P (pderiv Q)))) (pmul u v))) :
    False := by
  -- LEFT: q^(k+l+1) divides the cross term, q^(2(m+1)) divides Q²
  have hQQ : Pdvd (ppow q ((m + 1) + (m + 1))) (pmul Q Q) :=
    Pdvd_ppow_pmul (Pdvd_ppow_of_peq hQ) (Pdvd_ppow_of_peq hQ)
  have hLeft : Pdvd (ppow q ((k + l - 1) + ((m + 1) + (m + 1))))
      (pmul (psub (pmul (pderiv u) v) (pmul u (pderiv v))) (pmul Q Q)) :=
    Pdvd_ppow_pmul (ord_cross_lower hu hv) hQQ
  -- RIGHT: exact order m + (k+1) + (l+1)
  obtain ⟨E, hEd, hE⟩ := ord_deriv_cross hq hPd hQtd hT hPn hTn hQ
  have hN0 : PEq Nc (pmul (ppow q 0) Nc) := (peq_pmul_one_left Nc).symm
  obtain ⟨W1, hW1d, hW1n, hW1⟩ := ord_pmul_norm hq hNd hN0 hEd hE
  obtain ⟨W2, hW2d, hW2n, hW2⟩ := ord_pmul_norm hq hW1d hW1 hutd hu
  obtain ⟨W3, hW3d, _, hW3⟩ := ord_pmul_norm hq hW2d hW2 hvtd hv
  -- reassociate the right side into ((N·D)·u)·v
  have hRight : PEq (pmul (pmul Nc (psub (pmul (pderiv P) Q) (pmul P (pderiv Q)))) (pmul u v))
      (pmul (ppow q (((0 + m) + k) + l)) W3) :=
    PEq.trans (pmul_assoc_pnorm (pmul Nc _) u v).symm hW3
  -- compare
  have hdvd : Pdvd (ppow q ((k + l - 1) + ((m + 1) + (m + 1))))
      (pmul (pmul Nc (psub (pmul (pderiv P) Q) (pmul P (pderiv Q)))) (pmul u v)) :=
    Pdvd_of_peq hident.symm hLeft
  have hle := ord_le_of_dvd hq hdvd hRight hW3d
  omega

/-! ## The form a caller can actually use

`pole_order_contradiction` asks for `Q`'s `q`-adic factorisation explicitly. A caller coming from the
differential route does not have one — what it has is *"`q` is an irreducible factor of the reduced
denominator"*, i.e. `q ∣ Q` and `q ∤ P`. `exists_ord_factor` closes that gap, and the exponent's
positivity comes free: if the exponent were `0` then `Q ≈ Q̃` and `q` would not divide `Q` after all.

The characteristic-zero input is quantified over `r` here rather than fixed, because the exponent is
produced by the proof and not known to the caller. For irreducible `q` over a characteristic-zero
field it holds for every `r ≥ 1`; over `𝔽₂` it fails, which is the same boundary as everywhere else
in this arc. -/

/-- **The count, in caller-facing form.** Needs only that `q` is an irreducible factor of `Q` that
does not divide `P` — no explicit `q`-adic factorisation. -/
theorem cleared_relation_impossible {q P Q u ut v vt Nc : List Real} (hq : PIrred q)
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hchar : ∀ r : Nat, DerivCoprime q r)
    (hcharN : ∀ r : Nat, PNormal (pnsum r (pderiv q)))
    {k l : Nat}
    (hu : PEq u (pmul (ppow q k) ut)) (hutd : ¬ Pdvd q ut)
    (hv : PEq v (pmul (ppow q l) vt)) (hvtd : ¬ Pdvd q vt)
    (hNd : ¬ Pdvd q Nc)
    (hident : PEq (pmul (psub (pmul (pderiv u) v) (pmul u (pderiv v))) (pmul Q Q))
                  (pmul (pmul Nc (psub (pmul (pderiv P) Q) (pmul P (pderiv Q)))) (pmul u v))) :
    False := by
  obtain ⟨s, Qt, hQtn, hQtne, hQtd, hQfac⟩ :=
    exists_ord_factor Q.length q Q hq hQn hQne (Nat.le_refl _)
  cases s with
  | zero =>
      -- exponent 0 would mean `q ∤ Q`, contradicting the hypothesis
      exact hQtd (Pdvd_of_peq (PEq.trans hQfac (peq_pmul_one_left Qt)).symm hQd)
  | succ m =>
      exact pole_order_contradiction hq hu hutd hv hvtd hQfac hQtd hNd hPd hPn
        (hchar (m + 1)) (hcharN (m + 1)) hident

end MachLib
