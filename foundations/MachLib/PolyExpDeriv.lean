import MachLib.PolyLogDeriv

/-!
# `a' = k·S'·a` has no nonzero rational solution

The workhorse of the `S > 0` branch's step 2. The coefficient sweep there produces, for each
coefficient of the numerator and denominator in turn, an equation of the form

```
v' = j·S'·v      (j ≥ 1, v a rational function)
```

whose solutions are `v = c·e^(jS)`. Every one of them must be shown to vanish, and there are as many
as the degree — so this is the lemma the sweep calls repeatedly.

## Why it is proved here rather than deduced from the closed theorem

`proper_relation_impossible` already says `e^(jS)` is not a rational germ, so this *could* be routed
through it. Doing so would first need `a' = jS'a ⟹ a = c·e^(jS)`, which is an
antiderivative-uniqueness step — analysis, and a constant of integration to chase.

The direct route is cheaper **and lands in a better place**: cleared of denominators the equation is

```
(N'D − ND')·Q²  ≈  k·(P'Q − PQ')·(N·D)
```

and the same order count as `no_rational_logarithm` closes it. No analysis, no constant, and the
module stays **field-axiom-only** — so it joins the algebra spine, where the relation theorem cannot.

## The count

At any `q` with `ord_q(S) ≠ 0` — say `q ∤ P` and `q^(r+1) ‖ Q`:

* right side has order `r + ord_q(N) + ord_q(D)`, the `k` contributing `0`;
* left side has order `ord_q(N'D − ND') + 2(r+1)`.

With `α = ord_q(N)`, `β = ord_q(D)` and `N/D` in lowest terms at `q`, the two branches are

* `β = 0`: a lower bound `α − 1` on the left already gives `α + 2r + 1 ≤ r + α`, i.e. `r + 1 ≤ 0`;
* `β ≥ 1`: then `α = 0` and the left order is exactly `β − 1 + 2(r+1)`, against `r + β` — the same
  `r + 1 ≤ 0`.

Both collapse to `r + 1 ≤ 0`, and the surviving `2(r+1)` versus `r` is exactly the `Q²` that the
logarithmic-derivative form does not carry. **That squared denominator is what makes this the easier
of the two counts**, which is worth saying because the analytic statement is the harder of the two.

## The characteristic-zero inputs, both as hypotheses

`DerivCoprime q r` as everywhere in this arc, and `¬ Pdvd q (pnsum k [1])` — i.e. `k·1 ≠ 0`. The
second is a *theorem* over `Real` (`not_Pdvd_pnsum_one'`), but discharging it there costs the order
axioms, so it is carried as a hypothesis to keep this module inside `algebraFootprint`. Same choice,
same reason, as `DerivCoprime`.
-/

namespace MachLib

/-- **No nonzero rational function satisfies `a' = k·S'·a`.** Stated cleared of denominators:
`a = N/D`, `S = P/Q` with a pole of order `r+1` at the irreducible `q`. -/
theorem no_rational_exponential {q P Q Qt N D : List Real} (hq : PIrred q)
    (hchar : ∀ j : Nat, DerivCoprime q j)
    (hcharN : ∀ j : Nat, PNormal (pnsum j (pderiv q)))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P) (hNn : PNormal N)
    {r k : Nat}
    (hQ : PEq Q (pmul (ppow q (r + 1)) Qt)) (hQtd : ¬ Pdvd q Qt)
    (hkd : ¬ Pdvd q (pnsum k [1]))
    (hNne : pnorm N ≠ []) (hDne : pnorm D ≠ [])
    (hlow : Pdvd q D → ¬ Pdvd q N)
    (hident : PEq (pmul (psub (pmul (pderiv N) D) (pmul N (pderiv D))) (pmul Q Q))
                  (pmul (pmul (pnsum k [1]) (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))))
                        (pmul N D))) :
    False := by
  -- `ord_q(P'Q − PQ') = r` exactly, and the `k` factor contributes nothing
  obtain ⟨Ec, hEcd, hEc⟩ := ord_deriv_cross hq hPd hQtd (hchar (r + 1)) hPn (hcharN (r + 1)) hQ
  have hk0 : PEq (pnsum k [1]) (pmul (ppow q 0) (pnsum k [1])) :=
    (peq_pmul_one_left (pnsum k [1])).symm
  obtain ⟨W₁, hW₁d, _, hW₁⟩ := ord_pmul_norm hq hkd hk0 hEcd hEc
  -- `ord_q(Q·Q) = 2(r+1)` exactly
  obtain ⟨WQ, hWQd, _, hWQ⟩ := ord_pmul_norm hq hQtd hQ hQtd hQ
  rcases Classical.em (Pdvd q D) with hDd | hDd
  · -- ── q ∣ D: N is coprime to q, and the left order must be pinned ─────────
    have hNd : ¬ Pdvd q N := hlow hDd
    obtain ⟨b, Dt, _, _, hDtd, hDfac⟩ :=
      exists_ord_factor (pnorm D).length q (pnorm D) hq (pnorm_normal D) hDne (Nat.le_refl _)
    have hD : PEq D (pmul (ppow q b) Dt) := PEq.trans (pnorm_idem D).symm hDfac
    cases b with
    | zero => exact hDtd (Pdvd_of_peq (PEq.trans hD (peq_pmul_one_left Dt)).symm hDd)
    | succ c =>
        obtain ⟨En, hEnd, hEn⟩ :=
          ord_deriv_cross hq hNd hDtd (hchar (c + 1)) hNn (hcharN (c + 1)) hD
        obtain ⟨WL, hWLd, _, hWL⟩ := ord_pmul_norm hq hEnd hEn hWQd hWQ
        have hN0 : PEq N (pmul (ppow q 0) N) := (peq_pmul_one_left N).symm
        obtain ⟨W₂, hW₂d, _, hW₂⟩ := ord_pmul_norm hq hNd hN0 hDtd hD
        obtain ⟨W₃, hW₃d, _, hW₃⟩ := ord_pmul_norm hq hW₁d hW₁ hW₂d hW₂
        -- the LEFT order is the larger one, so it is the left that must divide the right
        have hle := ord_le_of_dvd hq (Pdvd_of_peq hident.symm (Pdvd_ppow_of_peq hWL)) hW₃ hW₃d
        omega
  · -- ── q ∤ D: a lower bound on the left suffices, uniformly in ord_q(N) ────
    have hD0 : PEq D (pmul (ppow q 0) D) := (peq_pmul_one_left D).symm
    obtain ⟨a, Nt, _, _, hNtd, hNfac⟩ :=
      exists_ord_factor (pnorm N).length q (pnorm N) hq (pnorm_normal N) hNne (Nat.le_refl _)
    have hN : PEq N (pmul (ppow q a) Nt) := PEq.trans (pnorm_idem N).symm hNfac
    obtain ⟨W₂, hW₂d, _, hW₂⟩ := ord_pmul_norm hq hNtd hN hDd hD0
    obtain ⟨W₃, hW₃d, _, hW₃⟩ := ord_pmul_norm hq hW₁d hW₁ hW₂d hW₂
    have hLeft : Pdvd (ppow q ((a + 0 - 1) + ((r + 1) + (r + 1))))
        (pmul (psub (pmul (pderiv N) D) (pmul N (pderiv D))) (pmul Q Q)) :=
      Pdvd_ppow_pmul (ord_cross_lower hN hD0) (Pdvd_ppow_of_peq hWQ)
    have hle := ord_le_of_dvd hq (Pdvd_of_peq hident.symm hLeft) hW₃ hW₃d
    omega

end MachLib
