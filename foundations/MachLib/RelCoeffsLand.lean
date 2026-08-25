import MachLib.RelCoeffsLead
import MachLib.BipevCoeffIdentity
import MachLib.PolyPoleCount

/-!
# Two of the three top coefficients are impossible

`RelCoeffsLead` reads the top coefficient off `relCoeffs`; `relCoeffs_nil_ratLog` says it is the zero
polynomial. This module closes the two cases where that is a contradiction with machinery the corpus
already has.

```
a > b   α·(K·α) ≈ 0        four cancellations, and no transcendence lemma at all
a ≤ b   α·(P·β*) ≈ (P·α*)·β   cancel P, then coeff_identity, then the pole count
```

## `a > b` needs nothing

The top coefficient is `(m+1)·Q·D·α²` with no `P` in it, so the whole case is: a product of five
nonzero polynomials is not zero. Four `pmul_eq_nil_cancel`s. It is worth noticing how little this
costs — the case that *looks* like it should need the hard theorem needs none of it, because the
degree gap already removed every term that could cancel against `K·α²`.

## `a ≤ b`, not `a < b`

`coeff_identity` wants `j ≤ m`, and strictness enters only through `¬ Pdvd q ((b−a)·1)`, which is
carried as a hypothesis. So the theorem is stated at `a ≤ b` and the hypothesis does the work
honestly: at `a = b` the multiplier is `pnsum 0 [1] = []`, every irreducible divides it, and the
hypothesis is simply unavailable. Nothing here has to know that — which is why the `a = b` case gets
its own landing rather than a special case inside this one.

## Every nonvanishing and characteristic-zero input is a hypothesis

`pnorm α ≠ []`, `pnorm β ≠ []`, `pnorm P ≠ []`, `¬ Pdvd q ((b−a)·1)`. None is discharged here.
`not_Pdvd_pnsum_one'` would discharge the last, but it costs the order axioms (it proves `n·1 > 0`),
and paying that here would take the module out of the algebra spine for one line. The assembly pays
it, where the order axioms are already present.
-/

namespace MachLib

open Real

/-! ## Cancellation, in the `pnorm` form this arc uses -/

/-- `pmul_eq_nil_cancel` against a `pnorm`-nonzero factor rather than a `PNormal` one. Every
polynomial in this arc arrives as an arbitrary list, so `PNormal` is never in hand and `pnorm _ ≠ []`
always is. -/
theorem pmul_nil_cancel' {c Z : List Real} (hc : pnorm c ≠ []) (h : PEq (pmul c Z) []) :
    PEq Z [] :=
  pmul_eq_nil_cancel (pnorm_normal c) hc
    (PEq.trans (peq_pmul (pnorm_idem c) (PEq.refl Z)) h)

/-- **No zero divisors, at the `pnorm` level.** The contrapositive of the cancellation, and the form
the `a > b` case consumes. -/
theorem pnorm_pmul_ne_nil {A B : List Real} (hA : pnorm A ≠ []) (hB : pnorm B ≠ []) :
    pnorm (pmul A B) ≠ [] := fun h => hB (pmul_nil_cancel' hA h)

/-- `[c]·Y ≈ c·Y` — unconditionally, unlike `pmul_singleton`. At `Y = []` the two sides are `[0]` and
`[]`, which differ as lists and agree after `pnorm`; that is exactly the gap `PEq` exists to close,
and it is why the readings could be left carrying `pmul [0 - 1]`. -/
theorem peq_pmul_singleton_left (c : Real) : ∀ Y : List Real, PEq (pmul [c] Y) (pscale c Y)
  | [] => by
      show pnorm (pmul [c] []) = pnorm (pscale c [])
      rw [pmul_nil_right, pnorm_replicate_zero]
      rfl
  | (y :: ys) => by rw [pmul_singleton c (y :: ys) (by simp)]

/-! ## `a > b` -/

/-- **The `a > b` top coefficient cannot vanish.** No `P`, no pole data, no transcendence — the
degree gap left `(m+1)·Q·D·α²` alone at index `2a`, and a product of nonzero polynomials is
nonzero. -/
theorem top_gt_impossible {Q D α : List Real} {m : Nat}
    (hα : pnorm α ≠ []) (hQ : pnorm Q ≠ []) (hD : pnorm D ≠ [])
    (hN : pnorm (pnsum (m + 1) [(1 : Real)]) ≠ [])
    (htop : pnorm (pmul α (pmul (relK Q D m) α)) = []) : False := by
  have h1 : PEq (pmul (relK Q D m) α) [] := pmul_nil_cancel' hα htop
  have hK : pnorm (relK Q D m) ≠ [] := pnorm_pmul_ne_nil hN (pnorm_pmul_ne_nil hQ hD)
  exact hα (pmul_nil_cancel' hK h1)

/-! ## `a ≤ b` -/

/-- **The `a ≤ b` top coefficient cannot vanish either**, given that `(b−a)·1` is not divisible by
`q`. Cancelling `P` turns the coefficient into `coeff_identity`'s hypothesis verbatim, and the pole
count closes it.

This is the same landing the *other* branch of the arc uses. Nothing about it was built for this
case; `cleared_relation_impossible` takes the two `q`-adic factorisations separately rather than a
lowest-terms pair, so `α` and `β` need no common-factor reduction. -/
theorem top_le_impossible {q P Q D α β : List Real} {a b : Nat}
    (hq : PIrred q)
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hchar : ∀ r : Nat, DerivCoprime q (r + 1))
    (hDdef : D = psub (pmul (pderiv P) Q) (pmul P (pderiv Q)))
    (hab : a ≤ b)
    (hαn : pnorm α ≠ []) (hβn : pnorm β ≠ []) (hPne : pnorm P ≠ [])
    (hNd : ¬ Pdvd q (pnsum (b - a) [(1 : Real)]))
    (htop : pnorm (padd (pmul α (pmul P (dtop Q D b β)))
                        (pmul [0 - 1] (pmul (pmul P (dtop Q D a α)) β))) = []) : False := by
  -- the `pmul [0 - 1]` the reading carries becomes a genuine `psub`
  have h0 : PEq (psub (pmul α (pmul P (dtop Q D b β)))
                      (pmul (pmul P (dtop Q D a α)) β)) [] := by
    show PEq (padd _ (pscale (0 - 1) _)) []
    exact PEq.trans (peq_padd (PEq.refl _) (peq_pmul_singleton_left (0 - 1) _).symm) htop
  have h1 : PEq (pmul α (pmul P (dtop Q D b β))) (pmul (pmul P (dtop Q D a α)) β) :=
    peq_of_psub_nil h0
  -- pull `P` to the front of both sides and cancel it
  have hL : PEq (pmul α (pmul P (dtop Q D b β))) (pmul P (pmul α (dtop Q D b β))) :=
    PEq.trans (pmul_assoc_pnorm α P (dtop Q D b β)).symm
      (PEq.trans (peq_pmul (peq_pmul_comm α P) (PEq.refl _))
        (pmul_assoc_pnorm P α (dtop Q D b β)))
  have h2 : PEq (pmul P (pmul α (dtop Q D b β))) (pmul P (pmul (dtop Q D a α) β)) :=
    PEq.trans hL.symm (PEq.trans h1 (pmul_assoc_pnorm P (dtop Q D a α) β))
  have h3 : PEq (pmul α (dtop Q D b β)) (pmul (dtop Q D a α) β) := by
    refine peq_of_psub_nil (pmul_nil_cancel' hPne ?_)
    rw [pmul_psub_right]
    exact PEq.trans (peq_psub h2 (PEq.refl _)) (peq_psub_self _)
  -- `coeff_identity`'s hypothesis, up to the two commutations
  have h4 : PEq (psub (pmul (dtop Q D b β) α) (pmul β (dtop Q D a α))) [] := by
    refine PEq.trans (peq_psub ?_ ?_) (peq_psub_self (pmul (dtop Q D a α) β))
    · exact PEq.trans (peq_pmul_comm (dtop Q D b β) α) (PEq.trans h3 (PEq.refl _))
    · exact peq_pmul_comm β (dtop Q D a α)
  have h5 := coeff_identity (QQ := pmul Q Q) (u := α) (v := β) (m := b) (j := a) hab h4
  -- the two `q`-adic factorisations, taken independently
  obtain ⟨k, αt, _, _, hαtd, hαfac⟩ :=
    exists_ord_factor (pnorm α).length q (pnorm α) hq (pnorm_normal α) hαn (Nat.le_refl _)
  obtain ⟨l, βt, _, _, hβtd, hβfac⟩ :=
    exists_ord_factor (pnorm β).length q (pnorm β) hq (pnorm_normal β) hβn (Nat.le_refl _)
  subst hDdef
  exact cleared_relation_impossible hq hPd hPn hQn hQne hQd hchar
    (PEq.trans (pnorm_idem α).symm hαfac) hαtd
    (PEq.trans (pnorm_idem β).symm hβfac) hβtd hNd h5

end MachLib
