import MachLib.PolyPoleCount
import MachLib.PolyConstDvd

/-!
# `S'/S` is never a rational derivative

The bottom step of the `S > 0` branch, and a classical statement in its own right: for a rational
function `S` with a zero or a pole at an irreducible `q`, the logarithmic derivative `S'/S` is **not**
the derivative of any rational function.

Cleared of denominators — `S = P/Q`, the candidate primitive `N/D` — that reads

```
(N'D − ND')·(P·Q)  ≈  (P'Q − PQ')·(D·D)
```

and the whole content is one order count at `q`, the same instrument as `PolyPoleCount`:

* `ord_q(S'/S) = −1` **exactly**, for any `q` at which `S` has a zero or pole. That is
  `ord_deriv_cross`: `ord_q(P'Q − PQ') = r − 1` when `ord_q(Q) = r`, and `ord_q(PQ) = r`.
* `ord_q(a')` for a rational `a = N/D` is **never** `−1`: it is `ord_q(a) − 1` when `ord_q(a) ≠ 0`,
  and `≥ 0` when `ord_q(a) = 0`. Neither hits `−1`.

Both facts are characteristic-zero: over `𝔽₂` the derivative loses the multiplicity that makes the
first count exact.

## The two branches, and why only one needs exactness

`q ∤ D` — the primitive has no pole at `q`. Then the right side has order exactly `r − 1` while the
left carries `q^r` from the `P·Q` factor alone. A **lower** bound on the left suffices
(`ord_cross_lower`), and it covers every `ord_q(N)` uniformly, including `0`.

`q ∣ D` — then `q ∤ N`, and a lower bound is not enough: it comes out `b + r ≤ r + 2b`, true for
every `b`. The **exact** left-hand order is needed, and `ord_deriv_cross` supplies it. This is the
same asymmetry as in `PolyPoleCount`: two bounds prove nothing, and the count turns on exactly one
side being pinned rather than bounded.
-/

namespace MachLib

/-- The `N ≈ 0` case: a zero primitive forces `S'/S ≈ 0`, which contradicts the exact order. -/
private theorem rhs_ne_zero {q X W : List Real} {b : Nat} (hq : PIrred q)
    (hW : PEq X (pmul (ppow q b) W)) (hWd : ¬ Pdvd q W) : ¬ PEq X [] := by
  intro hz
  -- everything divides the zero polynomial, so `X ≈ 0` gives `q^(b+1) ∣ X`
  have : b + 1 ≤ b := ord_le_of_dvd hq (Pdvd_of_peq hz Pdvd_zero) hW hWd
  omega

/-- **`k·S'/S` is not the derivative of a rational function**, for `k·1 ≠ 0`. `S = P/Q` with `q ∤ P`
and `q^(r+1) ‖ Q` — a genuine pole at `q` — and `N/D` any candidate primitive in lowest terms at `q`.

The `k` is what the `S > 0` coefficient sweep needs: it lands on `w' = −m·S'/S` for the degree `m` of
the relation, not on `w' = S'/S`. The count does not notice — `k·1` is a unit at `q`, contributing
order `0` — which is why this is the general statement and `no_rational_logarithm` is its `k = 1`
instance rather than the other way round. -/
theorem no_rational_logarithm_scaled {q P Q Qt N D : List Real} (hq : PIrred q)
    (hchar : ∀ r : Nat, DerivCoprime q (r + 1))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P) (hNn : PNormal N)
    {r k : Nat}
    (hQ : PEq Q (pmul (ppow q (r + 1)) Qt)) (hQtd : ¬ Pdvd q Qt)
    (hkd : ¬ Pdvd q (pnsum k [1]))
    (hDne : pnorm D ≠ []) (hlow : Pdvd q D → ¬ Pdvd q N)
    (hident : PEq (pmul (psub (pmul (pderiv N) D) (pmul N (pderiv D))) (pmul P Q))
                  (pmul (pmul (pnsum k [1])
                          (psub (pmul (pderiv P) Q) (pmul P (pderiv Q)))) (pmul D D))) :
    False := by
  have hk0 : PEq (pnsum k [1]) (pmul (ppow q 0) (pnsum k [1])) :=
    (peq_pmul_one_left (pnsum k [1])).symm
  -- `ord_q(P'Q − PQ') = r`, exactly. Used by both branches.
  obtain ⟨Ec, hEcd, hEc⟩ := ord_deriv_cross hq hPd hQtd (hchar r) hPn hQ
  have hP0 : PEq P (pmul (ppow q 0) P) := (peq_pmul_one_left P).symm
  rcases Classical.em (Pdvd q D) with hDd | hDd
  · -- ── q ∣ D: the left order must be pinned, not bounded ────────────────────
    have hNd : ¬ Pdvd q N := hlow hDd
    obtain ⟨b, Dt, _, _, hDtd, hDfac⟩ :=
      exists_ord_factor (pnorm D).length q (pnorm D) hq (pnorm_normal D) hDne (Nat.le_refl _)
    have hD : PEq D (pmul (ppow q b) Dt) := PEq.trans (pnorm_idem D).symm hDfac
    cases b with
    | zero => exact hDtd (Pdvd_of_peq (PEq.trans hD (peq_pmul_one_left Dt)).symm hDd)
    | succ c =>
        -- LEFT: ord_q(N'D − ND') = c exactly, and ord_q(P·Q) = r+1 exactly
        obtain ⟨En, hEnd, hEn⟩ :=
          ord_deriv_cross hq hNd hDtd (hchar c) hNn hD
        obtain ⟨W₁, hW₁d, _, hW₁⟩ := ord_pmul_norm hq hPd hP0 hQtd hQ
        obtain ⟨W₂, hW₂d, _, hW₂⟩ := ord_pmul_norm hq hEnd hEn hW₁d hW₁
        -- RIGHT: ord_q(D·D) = 2(c+1) exactly, so ord_q(RHS) = r + 2(c+1)
        obtain ⟨W₃, hW₃d, _, hW₃⟩ := ord_pmul_norm hq hDtd hD hDtd hD
        obtain ⟨Wk, hWkd, _, hWk⟩ := ord_pmul_norm hq hkd hk0 hEcd hEc
        obtain ⟨W₄, hW₄d, _, hW₄⟩ := ord_pmul_norm hq hWkd hWk hW₃d hW₃
        -- both sides exact and equal: the right order divides the left
        have hdvd := Pdvd_of_peq hident (Pdvd_ppow_of_peq hW₄)
        have hle := ord_le_of_dvd hq hdvd hW₂ hW₂d
        omega
  · -- ── q ∤ D: a lower bound on the left suffices, for every ord_q(N) ────────
    have hD0 : PEq D (pmul (ppow q 0) D) := (peq_pmul_one_left D).symm
    -- RIGHT: ord_q(D·D) = 0 exactly, so ord_q(RHS) = r exactly
    obtain ⟨W₃, hW₃d, _, hW₃⟩ := ord_pmul_norm hq hDd hD0 hDd hD0
    obtain ⟨Wk, hWkd, _, hWk⟩ := ord_pmul_norm hq hkd hk0 hEcd hEc
    obtain ⟨W₄, hW₄d, _, hW₄⟩ := ord_pmul_norm hq hWkd hWk hW₃d hW₃
    have hPQ : Pdvd (ppow q (0 + (r + 1))) (pmul P Q) :=
      Pdvd_ppow_pmul (Pdvd_one P) (Pdvd_ppow_of_peq hQ)
    rcases Classical.em (PEq N []) with hNz | hNz
    · -- a zero primitive: everything divides it, so the left side outruns any exact order
      have hc : Pdvd (ppow q 1) (psub (pmul (pderiv N) D) (pmul N (pderiv D))) :=
        Pdvd_psub (Pdvd_ppow_pmul (Pdvd_of_peq (peq_pderiv hNz) Pdvd_zero) (Pdvd_one D))
          (Pdvd_ppow_pmul (Pdvd_of_peq hNz Pdvd_zero) (Pdvd_one (pderiv D)))
      have hle := ord_le_of_dvd hq
        (Pdvd_of_peq hident.symm (Pdvd_ppow_pmul hc hPQ)) hW₄ hW₄d
      omega
    · -- LEFT: q^(a-1) divides the cross term and q^(r+1) divides P·Q — uniform in a
      obtain ⟨a, Nt, _, _, _, hNfac⟩ :=
        exists_ord_factor (pnorm N).length q (pnorm N) hq (pnorm_normal N)
          (fun h => hNz (by show pnorm N = pnorm []; rw [h]; rfl)) (Nat.le_refl _)
      have hN : PEq N (pmul (ppow q a) Nt) := PEq.trans (pnorm_idem N).symm hNfac
      have hLeft : Pdvd (ppow q ((a + 0 - 1) + (0 + (r + 1))))
          (pmul (psub (pmul (pderiv N) D) (pmul N (pderiv D))) (pmul P Q)) :=
        Pdvd_ppow_pmul (ord_cross_lower hN hD0) hPQ
      have hle := ord_le_of_dvd hq (Pdvd_of_peq hident.symm hLeft) hW₄ hW₄d
      omega

/-- **`S'/S` is not the derivative of a rational function** — the `k = 1` instance.

Kept as its own name because it is the statement the analytic argument quotes; the generalisation
was added *beside* it rather than replacing it, and this is now the three-line corollary. -/
theorem no_rational_logarithm {q P Q Qt N D : List Real} (hq : PIrred q)
    (hchar : ∀ r : Nat, DerivCoprime q (r + 1))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P) (hNn : PNormal N)
    {r : Nat}
    (hQ : PEq Q (pmul (ppow q (r + 1)) Qt)) (hQtd : ¬ Pdvd q Qt)
    (hDne : pnorm D ≠ []) (hlow : Pdvd q D → ¬ Pdvd q N)
    (hident : PEq (pmul (psub (pmul (pderiv N) D) (pmul N (pderiv D))) (pmul P Q))
                  (pmul (psub (pmul (pderiv P) Q) (pmul P (pderiv Q))) (pmul D D))) :
    False := by
  refine no_rational_logarithm_scaled (k := 1) hq hchar hPd hPn hNn hQ hQtd ?_ hDne hlow ?_
  · -- `q ∤ 1`: an irreducible has degree ≥ 1, so it divides no unit
    rw [pnsum_one]
    exact not_Pdvd_const hq (by rw [pnorm_specimen_canonical]; simp) (by simp)
  · refine PEq.trans hident (peq_pmul ?_ (PEq.refl (pmul D D)))
    rw [pnsum_one]
    exact (peq_pmul_one_left _).symm

end MachLib
