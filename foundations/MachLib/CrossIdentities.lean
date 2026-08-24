import MachLib.RelCoeffsLand

/-!
# Three identities about the cross-difference, and a common-factor split

The `a = b` case of the sweep needs things the other two did not, and they are all about
`W(u,v) = u'v − uv'` — the cross-difference, or Wronskian, of two polynomials.

```
psub_padd_padd            (A+B) − (C+E) = (A−C) + (B−E)                 syntactic
peq_dtop_cross            at EQUAL indices the D terms cancel: Q²·W(v,u)
peq_cross_common_factor   W(cA, cB) ≈ c²·W(A,B)                          no q' term survives
exists_common_ord_split   a common q-power off both, leaving lowest terms at q
```

## Why `a = b` needs a homogeneity lemma and `a ≤ b` did not

`cleared_relation_impossible` consumes the two `q`-adic factorisations **separately**;
`no_rational_logarithm_scaled` consumes a *fraction in lowest terms*, because its `q ∣ D` branch runs
`ord_deriv_cross`, which needs one side coprime to `q` to pin the order exactly. A lower bound is not
enough there: with `ord α = a` and `ord β = b` both positive, `ord_cross_lower` gives only
`a + b + r ≤ r + 2a`, i.e. `b ≤ a`, and no contradiction.

So the common factor has to come off, and taking it off means transporting the equation — which is
`peq_cross_common_factor`. **The `q'` term does not survive**: expanding `W(cA, cB)` gives
`c·c'·A·B` twice with opposite signs, and those cancel identically before any divisibility argument
starts. That is why the transport is an unconditional identity rather than an order estimate.

## `peq_dtop_cross` versus `coeff_identity`

`coeff_identity` is the `m ≠ j` statement of the same four-term split, and it says what follows when
the difference **vanishes**. The `a = b` case cannot use it: there the difference is not zero, it is
`K·α²`. So the lemma needed is the one that says what the difference **is**, and at equal indices
that is `Q²·(v'u − vu')` with no multiple of `D` left over.
-/

namespace MachLib

open Real

/-! ## Subtraction across a pair of sums -/

/-- `(A+B) − (C+E) = (A−C) + (B−E)` — syntactically, since `padd_assoc`, `padd_comm` and
`pscale_padd` are equalities rather than `PEq`s. Both cross-difference lemmas below are this
regrouping plus a cancellation. -/
theorem psub_padd_padd (A B C E : List Real) :
    psub (padd A B) (padd C E) = padd (psub A C) (psub B E) := by
  show padd (padd A B) (pscale (0 - 1) (padd C E))
      = padd (padd A (pscale (0 - 1) C)) (padd B (pscale (0 - 1) E))
  rw [pscale_padd, padd_assoc, padd_assoc,
      ← padd_assoc B (pscale (0 - 1) C) (pscale (0 - 1) E),
      padd_comm B (pscale (0 - 1) C),
      padd_assoc (pscale (0 - 1) C) B (pscale (0 - 1) E)]

/-- Regrouping four factors: the two inner ones swap places. -/
theorem peq_pmul_regroup (p r t u : List Real) :
    PEq (pmul (pmul p r) (pmul t u)) (pmul (pmul p t) (pmul r u)) := by
  refine PEq.trans (pmul_assoc_pnorm p r (pmul t u)) ?_
  refine PEq.trans (peq_pmul (PEq.refl p) (pmul_assoc_pnorm r t u).symm) ?_
  refine PEq.trans (peq_pmul (PEq.refl p) (peq_pmul (peq_pmul_comm r t) (PEq.refl u))) ?_
  refine PEq.trans (peq_pmul (PEq.refl p) (pmul_assoc_pnorm t r u)) ?_
  exact (pmul_assoc_pnorm p t (pmul r u)).symm

/-- The outer factors swap: regroup, commute, regroup back. -/
theorem peq_pmul_swap_outer (w x y z : List Real) :
    PEq (pmul (pmul w x) (pmul y z)) (pmul (pmul y x) (pmul w z)) :=
  PEq.trans (peq_pmul_regroup w x y z)
    (PEq.trans (peq_pmul (peq_pmul_comm w y) (PEq.refl (pmul x z)))
      (peq_pmul_regroup y x w z).symm)

/-! ## The two cross-difference identities -/

/-- **At equal indices the `D` terms cancel identically.** The `dcoeffs` cross-difference is
`Q²·(uv' − u'v)` with no multiple of `D` left over — unconditionally, no hypothesis at all. -/
theorem peq_dtop_cross (QQ D u v : List Real) (n : Nat) :
    PEq (psub (pmul (padd (pmul QQ (pderiv v)) (pnsum n (pmul D v))) u)
              (pmul v (padd (pmul QQ (pderiv u)) (pnsum n (pmul D u)))))
        (pmul QQ (psub (pmul u (pderiv v)) (pmul (pderiv u) v))) := by
  rw [pmul_padd_left, pmul_padd_right, psub_padd_padd]
  have hD : PEq (psub (pmul (pnsum n (pmul D v)) u) (pmul v (pnsum n (pmul D u)))) [] :=
    PEq.trans (peq_psub (peq_T2 D u v n) (peq_T4 D u v n)) (peq_psub_self _)
  refine PEq.trans (peq_padd (PEq.refl _) hD) ?_
  rw [padd_nil_right, pmul_psub_right]
  exact peq_psub (peq_T1 QQ u v) (peq_T3 QQ u v)

/-- **The cross-difference is homogeneous of degree two.** `W(cA, cB) ≈ c²·W(A,B)` — and note what
is *absent*: the two `c·c'·A·B` terms cancel identically, so no derivative of `c` survives. That is
what makes a common factor removable with no divisibility hypothesis at all. -/
theorem peq_cross_common_factor (c A B : List Real) :
    PEq (psub (pmul (pderiv (pmul c A)) (pmul c B)) (pmul (pmul c A) (pderiv (pmul c B))))
        (pmul (pmul c c) (psub (pmul (pderiv A) B) (pmul A (pderiv B)))) := by
  have hL : PEq (pmul (pderiv (pmul c A)) (pmul c B))
      (padd (pmul (pmul (pderiv c) A) (pmul c B)) (pmul (pmul c (pderiv A)) (pmul c B))) := by
    refine PEq.trans (peq_pmul (peq_pderiv_pmul c A) (PEq.refl (pmul c B))) ?_
    rw [pmul_padd_left]
  have hR : PEq (pmul (pmul c A) (pderiv (pmul c B)))
      (padd (pmul (pmul c A) (pmul (pderiv c) B)) (pmul (pmul c A) (pmul c (pderiv B)))) := by
    refine PEq.trans (peq_pmul (PEq.refl (pmul c A)) (peq_pderiv_pmul c B)) ?_
    rw [pmul_padd_right]
  refine PEq.trans (peq_psub hL hR) ?_
  rw [psub_padd_padd]
  have hcross : PEq (psub (pmul (pmul (pderiv c) A) (pmul c B))
                          (pmul (pmul c A) (pmul (pderiv c) B))) [] :=
    PEq.trans (peq_psub (peq_pmul_swap_outer (pderiv c) A c B) (PEq.refl _)) (peq_psub_self _)
  refine PEq.trans (peq_padd hcross (PEq.refl _)) ?_
  rw [pmul_psub_right]
  exact peq_psub (peq_pmul_regroup c (pderiv A) c B) (peq_pmul_regroup c A c (pderiv B))

/-! ## Divisibility is blind to a nonzero scale

The forward direction, `Pdvd_pscale`, is already in `PolyPoleOrder` — found the hard way, by
declaring it here first and having the module system reject the duplicate. Only the reverse is new,
and it needs no `1/c`: scaling by `−1` twice is the identity. -/

/-- Scaling by `−1` is its own inverse, so no `1/c` is needed — the forward direction is
`Pdvd_pscale` (`PolyPoleOrder`), applied twice. -/
theorem Pdvd_of_pscale_neg {q X : List Real} (h : Pdvd q (pscale (0 - 1) X)) : Pdvd q X := by
  have h2 := Pdvd_pscale (0 - 1) h
  rw [pscale_pscale, show (0 - 1) * (0 - 1) = (1 : Real) by mach_ring, pscale_one] at h2
  exact h2

/-! ## The common `q`-power -/

/-- **A common `q`-power, removed from both.** `exists_ord_factor` gives each polynomial its own
`q`-adic factorisation; taking the smaller exponent as the common one leaves a pair not both
divisible by `q` — which is exactly `no_rational_logarithm_scaled`'s `hlow`.

`cleared_relation_impossible` needs none of this: it consumes the two factorisations separately. The
logarithmic count does, because its hypothesis is about a fraction *in lowest terms*. That asymmetry
between the two counts is the whole reason the `a = b` case costs a lemma the `a ≤ b` case did
not. -/
theorem exists_common_ord_split {q A B : List Real} (hq : PIrred q)
    (hA : pnorm A ≠ []) (hB : pnorm B ≠ []) :
    ∃ (s : Nat) (A₁ B₁ : List Real),
      PEq A (pmul (ppow q s) A₁) ∧ PEq B (pmul (ppow q s) B₁)
        ∧ (Pdvd q A₁ → ¬ Pdvd q B₁) := by
  obtain ⟨k, At, _, _, hAtd, hAfac⟩ :=
    exists_ord_factor (pnorm A).length q (pnorm A) hq (pnorm_normal A) hA (Nat.le_refl _)
  obtain ⟨l, Bt, _, _, hBtd, hBfac⟩ :=
    exists_ord_factor (pnorm B).length q (pnorm B) hq (pnorm_normal B) hB (Nat.le_refl _)
  have hAf : PEq A (pmul (ppow q k) At) := PEq.trans (pnorm_idem A).symm hAfac
  have hBf : PEq B (pmul (ppow q l) Bt) := PEq.trans (pnorm_idem B).symm hBfac
  rcases Nat.le_total k l with h | h
  · obtain ⟨d, hd⟩ : ∃ d : Nat, l = k + d := ⟨l - k, by omega⟩
    subst hd
    refine ⟨k, At, pmul (ppow q d) Bt, hAf, ?_, fun hd => absurd hd hAtd⟩
    exact PEq.trans hBf
      (PEq.trans (peq_pmul (peq_ppow_add q k d) (PEq.refl Bt))
        (pmul_assoc_pnorm (ppow q k) (ppow q d) Bt))
  · obtain ⟨d, hd⟩ : ∃ d : Nat, k = l + d := ⟨k - l, by omega⟩
    subst hd
    refine ⟨l, pmul (ppow q d) At, Bt, ?_, hBf, fun _ => hBtd⟩
    exact PEq.trans hAf
      (PEq.trans (peq_pmul (peq_ppow_add q l d) (PEq.refl At))
        (pmul_assoc_pnorm (ppow q l) (ppow q d) At))

end MachLib
