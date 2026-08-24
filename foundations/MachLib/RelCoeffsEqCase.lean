import MachLib.CrossIdentities
import MachLib.PolyLogDeriv

/-!
# The `a = b` case, reduced to the logarithmic count's identity

The third and last of the sweep's readings. Unlike the other two it does not close in one step: the
top coefficient has to be reshaped into `no_rational_logarithm_scaled`'s `hident`, and that theorem
wants a fraction in *lowest terms*, so the common `q`-power comes off first.

```
eq_case_identity   the reading, cleared of `padd`/`bisub`:  P·Q²·W(β,α) ≈ α·K·α
eq_case_reduced    the same after the common q-power, at α₁, β₁
```

`eq_case_identity` is pure algebra with a single hypothesis — `pnorm P ≠ []`, to cancel `P` — and
`peq_dtop_cross` is what makes it short: at equal indices the `D` terms cancel, so the whole left
side collapses to `Q²·(βα' − β'α)` with no multiple of `D` surviving.
-/

namespace MachLib

open Real

/-- `q^s` is nonzero, in the `pnorm` form the cancellations want. -/
theorem pnorm_ppow_ne_nil {q : List Real} (hq : PIrred q) (s : Nat) : pnorm (ppow q s) ≠ [] := by
  have hqne : q ≠ [] := by
    intro h
    have h2 := hq.2.1
    rw [h] at h2
    simp at h2
  obtain ⟨hn, hne⟩ := ppow_normal hq.1 hqne s
  rw [pnorm_eq_self _ hn]
  exact hne

/-- Scaling by a nonzero constant cannot make a nonzero polynomial vanish. -/
theorem pnorm_pscale_ne_nil {c : Real} (hc : c ≠ 0) {X : List Real} (hX : pnorm X ≠ []) :
    pnorm (pscale c X) ≠ [] := by
  intro h
  refine hX (pmul_nil_cancel' (c := [c]) ?_ ?_)
  · have hn : PNormal [c] := by
      intro y hy
      have : c = y := by simpa using hy
      rw [← this]; exact hc
    rw [pnorm_eq_self _ hn]
    simp
  · exact Eq.trans (peq_pmul_singleton_left c X) h

/-! ## The reading, cleared -/

/-- **The `a = b` top coefficient, as an equation.** `P·Q²·(βα' − β'α) ≈ α·K·α`, with `K = (m+1)·Q·D`.

The `D` terms of the two `dcoeffs` brackets cancel against each other — `peq_dtop_cross` — which is
why nothing but `Q²` multiplies the cross-difference. -/
theorem eq_case_identity {P Q D α β : List Real} {a m : Nat} (hPne : pnorm P ≠ [])
    (htop : pnorm (padd (pmul α (padd (pmul P (dtop Q D a β)) (pmul (relK Q D m) α)))
                        (pmul [0 - 1] (pmul (pmul P (dtop Q D a α)) β))) = []) :
    PEq (pmul P (pmul (pmul Q Q) (psub (pmul β (pderiv α)) (pmul (pderiv β) α))))
        (pmul α (pmul (relK Q D m) α)) := by
  -- the `pmul [0 - 1]` becomes a genuine `psub`, and the difference vanishes
  have h1 : PEq (psub (pmul α (padd (pmul P (dtop Q D a β)) (pmul (relK Q D m) α)))
                      (pmul (pmul P (dtop Q D a α)) β)) [] := by
    show PEq (padd _ (pscale (0 - 1) _)) []
    exact PEq.trans (peq_padd (PEq.refl _) (peq_pmul_singleton_left (0 - 1) _).symm) htop
  have h2 := peq_of_psub_nil h1
  rw [pmul_padd_right] at h2
  -- move the `K·α²` term to the right-hand side
  have h3 : PEq (padd (pmul α (pmul P (dtop Q D a β))) (pmul α (pmul (relK Q D m) α)))
                (padd (pmul (pmul P (dtop Q D a α)) β) []) := by
    rw [padd_nil_right]; exact h2
  have h4 := peq_sub_swap h3
  have hnil : psub (pmul α (pmul (relK Q D m) α)) [] = pmul α (pmul (relK Q D m) α) := by
    show padd (pmul α (pmul (relK Q D m) α)) ([] : List Real) = _
    rw [padd_nil_right]
  rw [hnil] at h4
  -- pull `P` to the front of both terms, then recognise the cross-difference
  have h5 : PEq (pmul P (psub (pmul (dtop Q D a α) β) (pmul α (dtop Q D a β))))
                (pmul α (pmul (relK Q D m) α)) := by
    rw [pmul_psub_right]
    refine PEq.trans (peq_psub (pmul_assoc_pnorm P (dtop Q D a α) β).symm
      (peq_pmul_left_comm P α (dtop Q D a β))) h4
  exact PEq.trans
    (peq_pmul (PEq.refl P) (peq_dtop_cross (pmul Q Q) D β α a).symm) h5

/-! ## Cancelling a common left factor -/

/-- `c·X ≈ c·Y` with `c` nonzero gives `X ≈ Y`. Used twice below — once for the common `q`-power and
once for the `Q` that `Q²` carries against `K`'s single `Q`. -/
theorem peq_cancel_left {c X Y : List Real} (hc : pnorm c ≠ [])
    (h : PEq (pmul c X) (pmul c Y)) : PEq X Y := by
  refine peq_of_psub_nil (pmul_nil_cancel' hc ?_)
  rw [pmul_psub_right]
  exact PEq.trans (peq_psub h (PEq.refl (pmul c Y))) (peq_psub_self _)

/-! ## The equation at the reduced pair -/

/-- **The `a = b` equation, after the common `q`-power comes off and one `Q` cancels.**

Two cancellations, in this order. First `c² = q^(2s)`: it is on both sides because the
cross-difference is homogeneous of degree two (`peq_cross_common_factor`) and `α²` obviously is.
Then a single `Q`: the left carries `Q²` and the right carries `K = (m+1)·Q·D`, so exactly one
survives — and that surviving `Q` is what makes the result `P·Q` rather than `P·Q²`, i.e. the
*logarithmic* count's shape rather than the exponential one's. -/
theorem eq_case_reduced {q P Q D α β : List Real} {m s : Nat} {α₁ β₁ : List Real}
    (hq : PIrred q) (hQne : pnorm Q ≠ [])
    (hαs : PEq α (pmul (ppow q s) α₁)) (hβs : PEq β (pmul (ppow q s) β₁))
    (h : PEq (pmul P (pmul (pmul Q Q) (psub (pmul β (pderiv α)) (pmul (pderiv β) α))))
             (pmul α (pmul (relK Q D m) α))) :
    PEq (pmul (psub (pmul (pderiv α₁) β₁) (pmul α₁ (pderiv β₁))) (pmul P Q))
        (pmul (pmul (pnsum (m + 1) [(1 : Real)]) D) (pmul α₁ α₁)) := by
  have hcc : pnorm (pmul (ppow q s) (ppow q s)) ≠ [] :=
    pnorm_pmul_ne_nil (pnorm_ppow_ne_nil hq s) (pnorm_ppow_ne_nil hq s)
  -- the cross-difference is homogeneous of degree two
  have hW : PEq (psub (pmul β (pderiv α)) (pmul (pderiv β) α))
      (pmul (pmul (ppow q s) (ppow q s))
        (psub (pmul (pderiv α₁) β₁) (pmul α₁ (pderiv β₁)))) := by
    refine PEq.trans ?_ (peq_cross_common_factor (ppow q s) α₁ β₁)
    refine peq_psub ?_ ?_
    · exact PEq.trans (peq_pmul_comm β (pderiv α)) (peq_pmul (peq_pderiv hαs) hβs)
    · exact PEq.trans (peq_pmul_comm (pderiv β) α) (peq_pmul hαs (peq_pderiv hβs))
  -- and so is `α²`
  have hA : PEq (pmul α (pmul (relK Q D m) α))
      (pmul (pmul (ppow q s) (ppow q s)) (pmul α₁ (pmul (relK Q D m) α₁))) := by
    refine PEq.trans (peq_pmul hαs (peq_pmul (PEq.refl (relK Q D m)) hαs)) ?_
    refine PEq.trans (peq_pmul (PEq.refl (pmul (ppow q s) α₁))
      (peq_pmul_left_comm (relK Q D m) (ppow q s) α₁)) ?_
    exact peq_pmul_regroup (ppow q s) α₁ (ppow q s) (pmul (relK Q D m) α₁)
  -- cancel `c²`
  have hL : PEq (pmul (pmul (ppow q s) (ppow q s))
        (pmul P (pmul (pmul Q Q) (psub (pmul (pderiv α₁) β₁) (pmul α₁ (pderiv β₁))))))
      (pmul P (pmul (pmul Q Q) (psub (pmul β (pderiv α)) (pmul (pderiv β) α)))) := by
    refine PEq.trans (peq_pmul_left_comm (pmul (ppow q s) (ppow q s)) P _) ?_
    refine peq_pmul (PEq.refl P) ?_
    refine PEq.trans (peq_pmul_left_comm (pmul (ppow q s) (ppow q s)) (pmul Q Q) _) ?_
    exact peq_pmul (PEq.refl (pmul Q Q)) hW.symm
  have h8 : PEq (pmul P (pmul (pmul Q Q) (psub (pmul (pderiv α₁) β₁) (pmul α₁ (pderiv β₁)))))
      (pmul α₁ (pmul (relK Q D m) α₁)) :=
    peq_cancel_left hcc (PEq.trans hL (PEq.trans h hA))
  -- cancel one `Q`
  have hL2 : PEq (pmul Q (pmul P (pmul Q (psub (pmul (pderiv α₁) β₁) (pmul α₁ (pderiv β₁))))))
      (pmul P (pmul (pmul Q Q) (psub (pmul (pderiv α₁) β₁) (pmul α₁ (pderiv β₁))))) := by
    refine PEq.trans (peq_pmul_left_comm Q P _) ?_
    exact peq_pmul (PEq.refl P) (pmul_assoc_pnorm Q Q _).symm
  have hR2 : PEq (pmul α₁ (pmul (relK Q D m) α₁))
      (pmul Q (pmul (pnsum (m + 1) [(1 : Real)]) (pmul α₁ (pmul D α₁)))) := by
    have hK : PEq (pmul (relK Q D m) α₁)
        (pmul (pnsum (m + 1) [(1 : Real)]) (pmul Q (pmul D α₁))) := by
      refine PEq.trans (pmul_assoc_pnorm (pnsum (m + 1) [(1 : Real)]) (pmul Q D) α₁) ?_
      exact peq_pmul (PEq.refl _) (pmul_assoc_pnorm Q D α₁)
    refine PEq.trans (peq_pmul (PEq.refl α₁) hK) ?_
    refine PEq.trans (peq_pmul_left_comm α₁ (pnsum (m + 1) [(1 : Real)]) _) ?_
    refine PEq.trans (peq_pmul (PEq.refl (pnsum (m + 1) [(1 : Real)]))
      (peq_pmul_left_comm α₁ Q (pmul D α₁))) ?_
    exact peq_pmul_left_comm (pnsum (m + 1) [(1 : Real)]) Q (pmul α₁ (pmul D α₁))
  have h9 : PEq (pmul P (pmul Q (psub (pmul (pderiv α₁) β₁) (pmul α₁ (pderiv β₁)))))
      (pmul (pnsum (m + 1) [(1 : Real)]) (pmul α₁ (pmul D α₁))) :=
    peq_cancel_left hQne (PEq.trans hL2 (PEq.trans h8 hR2))
  -- reshape into the count's form
  refine PEq.trans ?_ (PEq.trans h9 ?_)
  · exact PEq.trans (peq_pmul_comm _ (pmul P Q)) (pmul_assoc_pnorm P Q _)
  · refine PEq.trans (peq_pmul (PEq.refl _) (peq_pmul_left_comm α₁ D α₁)) ?_
    exact (pmul_assoc_pnorm (pnsum (m + 1) [(1 : Real)]) D (pmul α₁ α₁)).symm

/-! ## The landing

`no_rational_logarithm_scaled` wants `(N'·Dd − N·Dd')·(P·Q) ≈ k·D·(Dd·Dd)`; the reduced equation is
`(α₁'β₁ − α₁β₁')·(P·Q) ≈ (m+1)·D·α₁²`. **The sign goes on the denominator**: with `Dd = −α₁` the
square kills it on the right and `N'·Dd − N·Dd'` flips exactly once on the left. Taking `N = −β₁`
instead would have needed `PNormal` of a scaled polynomial; this way only `hDne` and `hlow` see the
scale, and both reduce to `Pdvd_pscale`. -/

/-- Negating both sides of a difference swaps them — an equality, because `(−1)·(−1) = 1` collapses
the double scale and `padd_comm` does the rest. -/
theorem psub_pscale_neg (X Y : List Real) :
    psub (pscale (0 - 1) X) (pscale (0 - 1) Y) = psub Y X := by
  show padd (pscale (0 - 1) X) (pscale (0 - 1) (pscale (0 - 1) Y)) = padd Y (pscale (0 - 1) X)
  rw [pscale_pscale, show (0 - 1) * (0 - 1) = (1 : Real) by mach_ring, pscale_one, padd_comm]

/-- A factor of a nonzero polynomial is nonzero. -/
theorem pnorm_ne_nil_of_factor {A B c : List Real} (hA : pnorm A ≠ [])
    (h : PEq A (pmul c B)) : pnorm B ≠ [] := by
  intro hB
  have hB' : PEq B ([] : List Real) := by
    show pnorm B = pnorm ([] : List Real)
    rw [hB]; rfl
  refine hA (Eq.trans h (Eq.trans (peq_pmul (PEq.refl c) hB') ?_))
  show pnorm (pmul c ([] : List Real)) = pnorm []
  rw [pmul_nil_right]
  exact pnorm_replicate_zero _

/-- **The `a = b` top coefficient cannot vanish.** The last of the three cases, and the only one that
lands on the logarithmic count. -/
theorem top_eq_impossible {q P Q D α β : List Real} {a m : Nat}
    (hq : PIrred q)
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hchar : ∀ r : Nat, DerivCoprime q r)
    (hcharN : ∀ r : Nat, PNormal (pnsum r (pderiv q)))
    (hDdef : D = psub (pmul (pderiv P) Q) (pmul P (pderiv Q)))
    (hαn : pnorm α ≠ []) (hβn : pnorm β ≠ [])
    (hPne : pnorm P ≠ []) (hQnn : pnorm Q ≠ [])
    (hkd : ¬ Pdvd q (pnsum (m + 1) [(1 : Real)]))
    (htop : pnorm (padd (pmul α (padd (pmul P (dtop Q D a β)) (pmul (relK Q D m) α)))
                        (pmul [0 - 1] (pmul (pmul P (dtop Q D a α)) β))) = []) : False := by
  have hneg : (0 - 1 : Real) ≠ 0 := by
    intro h
    refine zero_ne_one_ax ?_
    have e : (0 : Real) - 1 + 1 = 0 + 1 := by rw [h]
    rw [show (0 : Real) - 1 + 1 = 0 by mach_ring, show (0 : Real) + 1 = 1 by mach_ring] at e
    exact e
  obtain ⟨s, α₁, β₁, hαs, hβs, hlow⟩ := exists_common_ord_split hq hαn hβn
  have hα₁ : pnorm α₁ ≠ [] := pnorm_ne_nil_of_factor hαn hαs
  have hred := eq_case_reduced hq hQnn hαs hβs (eq_case_identity hPne htop)
  obtain ⟨r, Qt, _, _, hQtd, hQfac⟩ :=
    exists_ord_factor Q.length q Q hq hQn hQne (Nat.le_refl _)
  cases r with
  | zero => exact hQtd (Pdvd_of_peq (PEq.trans hQfac (peq_pmul_one_left Qt)).symm hQd)
  | succ r' =>
      subst hDdef
      refine no_rational_logarithm_scaled (N := pnorm β₁) (D := pscale (0 - 1) α₁) (k := m + 1)
        hq hchar hcharN hPd hPn (pnorm_normal β₁) hQfac hQtd hkd
        (pnorm_pscale_ne_nil hneg hα₁)
        (fun hd => fun hn => hlow (Pdvd_of_pscale_neg hd)
          (Pdvd_of_peq (pnorm_idem β₁).symm hn)) ?_
      -- the identity, at `N = pnorm β₁` and `Dd = −α₁`
      refine PEq.trans ?_ (PEq.trans hred ?_)
      · -- left side: unfold the scale, swap the difference, drop the `pnorm`
        rw [pderiv_pscale, pmul_pscale_right, pmul_pscale_right, psub_pscale_neg]
        refine peq_pmul ?_ (PEq.refl (pmul P Q))
        refine peq_psub ?_ ?_
        · exact PEq.trans (peq_pmul (pnorm_idem β₁) (PEq.refl (pderiv α₁)))
            (peq_pmul_comm β₁ (pderiv α₁))
        · exact PEq.trans (peq_pmul (peq_pderiv (pnorm_idem β₁)) (PEq.refl α₁))
            (peq_pmul_comm (pderiv β₁) α₁)
      · -- right side: the square kills the sign
        refine peq_pmul (PEq.refl _) ?_
        rw [pmul_pscale_right, pmul_pscale_left, pscale_pscale,
            show (0 - 1) * (0 - 1) = (1 : Real) by mach_ring, pscale_one]

end MachLib
