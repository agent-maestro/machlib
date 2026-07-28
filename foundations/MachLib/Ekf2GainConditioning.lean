import MachLib.Matrix2JosephPSD
import MachLib.DivisionError

/-!
# EKF gain conditioning — the innovation covariance cannot become singular

**Part 2 of the pre-registered 2×2 EKF forward-error bound**
(`../EKF2_FWD_ERROR_PREREGISTRATION.md`). Design decision **D3**: error through `S⁻¹` is controlled
by how far `S = H P Hᵀ + R` is from singular, and *the structural PSD leg supplies that bound* —
`Matrix2JosephPSD` is not adjacent to the forward-error work, it is **load-bearing inside it**.

## A documented deviation from the pre-registration

D3 registered the route `λ_min(S) ≥ λ_min(R)` ⟹ `‖S⁻¹‖ ≤ 1/λ_min(R)`. Assembly turned up a fact
about the *hardware* that changes the right statement: **the emitted filter does not compute
`S⁻¹` via eigenvalues, it inverts a 2×2 by adjugate-over-determinant.** So the quantity that has to
be bounded away from zero is `det S`, and the natural theorem is

    det S  ≥  det R        (`psd2_det_add_ge`, specialised in `ekf2_det_S_lower`)

which is *also tighter here*: for the anchor's `R = diag(0.020004, 0.001999)`,
`det R = 4.00e-05` against `λ_min(R)² = 4.00e-06` — a factor of **10** on the constant that divides
the whole gain error. The PSD leg does exactly the job D3 assigned it; only the norm changed, and it
changed because the silicon picked it. Recorded rather than quietly substituted.

## The chain, all of it from theorems already in this repo

```
  P PSD                                  -- kalman2_joseph_psd, for ANY gain   [banked]
  ⇒ H P Hᵀ PSD                           -- psd2_congruence (G := H)           [banked]
  ⇒ det (H P Hᵀ + R) ≥ det R             -- psd2_det_add_ge                    [this file]
  ⇒ the gain's divisor is bounded below by a KNOWN CONSTANT of the filter's own tuning
```

The middle step is the only new mathematics: **adding a PSD matrix to a PSD matrix cannot decrease
the determinant.** Proven here without eigenvalues, without `sqrt`, and Mathlib-free — the mixed term
`na·rd + nd·ra − 2·nb·rb` is shown nonnegative by squaring rather than by AM-GM on square roots,
which keeps the whole file inside `Real`'s ordered-field axioms.

`sorryAx`-free, zero new axioms.
-/

namespace MachLib.Real

/-- `t² ≤ c²` with `0 ≤ c` gives `t ≤ c`. The square-free replacement for "take square roots". -/
private theorem le_of_mul_self_le {t c : Real} (hc : 0 ≤ c) (h : t * t ≤ c * c) : t ≤ c := by
  rcases lt_total c t with hlt | heq | hgt
  · exfalso
    have htpos : 0 < t := lt_of_le_of_lt hc hlt
    have hsum : 0 < t + c := by
      rcases (le_iff_lt_or_eq 0 c).mp hc with hcpos | hc0
      · exact add_pos htpos hcpos
      · rw [← hc0, show t + 0 = t from by mach_ring]; exact htpos
    have hprod : 0 < (t - c) * (t + c) := mul_pos (sub_pos_of_lt hlt) hsum
    rw [show (t - c) * (t + c) = t * t - c * c from by mach_ring] at hprod
    have hnp : t * t - c * c ≤ 0 := by
      have := add_le_add_both h (le_refl (-(c * c)))
      rw [show c * c + -(c * c) = (0 : Real) from by mach_ring,
          show t * t + -(c * c) = t * t - c * c from by mach_ring] at this
      exact this
    exact lt_irrefl_ax 0 (lt_of_lt_of_le hprod hnp)
  · exact le_of_eq heq.symm
  · exact le_of_lt hgt

/-- The `(1,0)` and `(0,1)` probes: a PSD 2×2 has nonnegative diagonal. -/
theorem psd2_diag_nonneg {a b d : Real} (h : Psd2 a b d) : 0 ≤ a ∧ 0 ≤ d := by
  constructor
  · have k := h 1 0
    rw [show a * (1 * 1) + (1 + 1) * b * (1 * 0) + d * (0 * 0) = a from by mach_ring] at k
    exact k
  · have k := h 0 1
    rw [show a * (0 * 0) + (1 + 1) * b * (0 * 1) + d * (1 * 1) = d from by mach_ring] at k
    exact k

/-- **A PSD 2×2 has nonnegative determinant** — the off-diagonal cannot beat the diagonal.

The `a > 0` case is the `(b, −a)` probe, which evaluates the quadratic form to exactly
`a·(a·d − b²)`. The `a = 0` case is the one that needs care and is where a hand-wave would hide: the
form becomes the *affine* function `t ↦ 2·b·t + d`, and an affine function that is nonnegative
everywhere must have zero slope — instantiated at `t = −(d+1)/(2b)` it would equal `−1`. -/
theorem psd2_det_nonneg {a b d : Real} (h : Psd2 a b d) : 0 ≤ a * d - b * b := by
  have ha : 0 ≤ a := (psd2_diag_nonneg h).1
  rcases (le_iff_lt_or_eq 0 a).mp ha with hapos | ha0
  · -- 0 < a : the (b, −a) probe gives 0 ≤ a * (a*d − b*b), then cancel the positive a
    have k := h b (-a)
    rw [show a * (b * b) + (1 + 1) * b * (b * -a) + d * (-a * -a) = (a * d - b * b) * a
          from by mach_mpoly [a, b, d]] at k
    refine le_of_mul_le_mul_right_pos ?_ hapos
    rw [show (0 : Real) * a = 0 from by mach_mpoly [a]]
    exact k
  · -- a = 0 : the form is affine in x, so its slope must vanish
    have hb : b = 0 := by
      rcases Classical.em (b = 0) with hb0 | hbne
      · exact hb0
      · exfalso
        have h2b : (1 + 1) * b ≠ 0 := by
          intro hz
          exact hbne (by
            have := congrArg (fun z => z * (1 / (1 + 1))) hz
            simp only at this
            rw [show (1 + 1) * b * (1 / (1 + 1)) = b * ((1 + 1) * (1 / (1 + 1)))
                  from by mach_ring, mul_inv (1 + 1) two_ne_zero,
                show b * 1 = b from by mach_ring,
                show (0 : Real) * (1 / (1 + 1)) = 0 from by mach_ring] at this
            exact this)
        have k := h (-(d + 1) * (1 / ((1 + 1) * b))) 1
        rw [← ha0] at k
        rw [show (0 : Real) * (-(d + 1) * (1 / ((1 + 1) * b)) * (-(d + 1) * (1 / ((1 + 1) * b))))
                  + (1 + 1) * b * (-(d + 1) * (1 / ((1 + 1) * b)) * 1) + d * (1 * 1)
              = -((d + 1) * ((1 + 1) * b * (1 / ((1 + 1) * b)))) + d
              from by mach_ring, mul_inv ((1 + 1) * b) h2b,
            show -((d + 1) * 1) + d = -1 from by mach_ring] at k
        have hneg : (-1 : Real) < 0 := by
          have := add_lt_add_left zero_lt_one_ax (-1)
          rw [show (-1 : Real) + 0 = -1 from by mach_ring,
              show (-1 : Real) + 1 = 0 from by mach_ring] at this
          exact this
        exact lt_irrefl_ax 0 (lt_of_le_of_lt k hneg)
    rw [← ha0, hb]
    exact le_of_eq (by mach_ring)

/-- **The mixed term of two PSD forms is nonnegative**: `na·rd + nd·ra ≥ 2·nb·rb`.

`tr(adj N · R) ≥ 0` in disguise, proven WITHOUT square roots. Write `u = na·rd`, `v = nd·ra`, both
`≥ 0`. Then `(2·nb·rb)² = 4·nb²·rb² ≤ 4·(na·nd)·(ra·rd) = 4uv ≤ (u+v)²`, the last step being
`(u−v)² ≥ 0`. Since `u + v ≥ 0`, `le_of_mul_self_le` finishes. Keeping `sqrt` out matters: it would
have dragged the whole gain-conditioning argument into `sqrt`'s own axioms for no gain. -/
theorem psd2_mixed_nonneg {na nb nd ra rb rd : Real}
    (hn : Psd2 na nb nd) (hr : Psd2 ra rb rd) :
    0 ≤ na * rd + nd * ra - (1 + 1) * (nb * rb) := by
  obtain ⟨hna, hnd⟩ := psd2_diag_nonneg hn
  obtain ⟨hra, hrd⟩ := psd2_diag_nonneg hr
  have hdn : 0 ≤ na * nd - nb * nb := psd2_det_nonneg hn
  have hdr : 0 ≤ ra * rd - rb * rb := psd2_det_nonneg hr
  have hu : 0 ≤ na * rd := mul_nonneg hna hrd
  have hv : 0 ≤ nd * ra := mul_nonneg hnd hra
  have hsum : 0 ≤ na * rd + nd * ra := add_nonneg hu hv
  -- (2·nb·rb)² ≤ 4·(na·nd)(ra·rd)
  have hsq1 : ((1 + 1) * (nb * rb)) * ((1 + 1) * (nb * rb))
      ≤ (1 + 1) * (1 + 1) * ((na * nd) * (ra * rd)) := by
    have h1 : nb * nb * (rb * rb) ≤ (na * nd) * (ra * rd) := by
      have hA : nb * nb ≤ na * nd :=
        le_trans (le_of_eq (show nb * nb = 0 + nb * nb from by mach_mpoly [nb]))
          (le_trans (add_le_add_both hdn (le_refl (nb * nb)))
            (le_of_eq (by mach_mpoly [na, nd, nb])))
      have hB : rb * rb ≤ ra * rd :=
        le_trans (le_of_eq (show rb * rb = 0 + rb * rb from by mach_mpoly [rb]))
          (le_trans (add_le_add_both hdr (le_refl (rb * rb)))
            (le_of_eq (by mach_mpoly [ra, rd, rb])))
      exact mul_le_mul' (mul_self_nonneg nb) hA (mul_self_nonneg rb) hB
    rw [show ((1 + 1) * (nb * rb)) * ((1 + 1) * (nb * rb))
          = (1 + 1) * (1 + 1) * (nb * nb * (rb * rb)) from by mach_mpoly [nb, rb]]
    exact mul_le_mul_of_nonneg_left h1 (by
      rw [show (1 + 1) * (1 + 1) = (1 : Real) + 1 + 1 + 1 from by mach_mpoly []]
      exact le_of_lt (add_pos (add_pos (add_pos zero_lt_one_ax zero_lt_one_ax) zero_lt_one_ax)
        zero_lt_one_ax))
  -- 4uv ≤ (u+v)²
  have hsq2 : (1 + 1) * (1 + 1) * ((na * rd) * (nd * ra))
      ≤ (na * rd + nd * ra) * (na * rd + nd * ra) := by
    have hsqd : 0 ≤ (na * rd - nd * ra) * (na * rd - nd * ra) := mul_self_nonneg _
    refine le_trans (le_of_eq (show (1 + 1) * (1 + 1) * ((na * rd) * (nd * ra))
        = (1 + 1) * (1 + 1) * ((na * rd) * (nd * ra)) + 0 from by mach_mpoly [na, rd, nd, ra])) ?_
    exact le_trans (add_le_add_both (le_refl _) hsqd)
      (le_of_eq (by mach_mpoly [na, rd, nd, ra]))
  have hchain : ((1 + 1) * (nb * rb)) * ((1 + 1) * (nb * rb))
      ≤ (na * rd + nd * ra) * (na * rd + nd * ra) := by
    refine le_trans hsq1 (le_trans ?_ hsq2)
    exact le_of_eq (by mach_mpoly [na, nb, nd, ra, rb, rd])
  exact sub_nonneg_of_le (le_of_mul_self_le hsum hchain)

/-- **D3 — adding a PSD matrix cannot decrease the determinant.** `det (N + R) ≥ det R` for PSD `N`
and PSD `R`. The expansion is `det N + (mixed term) ≥ 0 + 0`, so it is exactly `psd2_det_nonneg`
plus `psd2_mixed_nonneg`. -/
theorem psd2_det_add_ge {na nb nd ra rb rd : Real}
    (hn : Psd2 na nb nd) (hr : Psd2 ra rb rd) :
    ra * rd - rb * rb ≤ (na + ra) * (nd + rd) - (nb + rb) * (nb + rb) := by
  have hdn : 0 ≤ na * nd - nb * nb := psd2_det_nonneg hn
  have hmx : 0 ≤ na * rd + nd * ra - (1 + 1) * (nb * rb) := psd2_mixed_nonneg hn hr
  rw [show (na + ra) * (nd + rd) - (nb + rb) * (nb + rb)
        = (ra * rd - rb * rb) + ((na * nd - nb * nb)
          + (na * rd + nd * ra - (1 + 1) * (nb * rb)))
        from by mach_mpoly [na, nb, nd, ra, rb, rd]]
  exact le_trans (le_of_eq (show ra * rd - rb * rb = (ra * rd - rb * rb) + 0
      from by mach_mpoly [ra, rd, rb]))
    (add_le_add_both (le_refl _) (add_nonneg hdn hmx))

/-! ## The EKF instance -/

/-- **`det S ≥ det R` for the EKF innovation covariance.** `S = H P Hᵀ + R` with `P` the (PSD) prior
covariance and `H` the compiler-derived Jacobian — *any* `H`, because `psd2_congruence` holds for any
`G`. So the divisor the gain computation depends on is bounded below by a constant of the filter's
own tuning, independent of the state, the linearisation point, and the accumulated rounding.

This is what makes the gain stage's forward error finite: `fxerr_div_vs_exact`'s `m` hypothesis is
discharged by `det R`, a number chosen when the filter was designed. For the range-bearing anchor
`R = diag(0.020004, 0.001999)`, so `m = det R = 4.00e-05`.

**Why the PSD leg is load-bearing and not decorative:** drop `hP` and there is no lower bound at all
— `det S` could be zero and the gain unbounded. The numerical-robustness theorem and the
forward-error theorem are the same theorem used twice. -/
theorem ekf2_det_S_lower {h00 h01 h10 h11 pa pb pd ra rb rd : Real}
    (hP : Psd2 pa pb pd) (hR : Psd2 ra rb rd) :
    ra * rd - rb * rb
      ≤ ((h00 * h00 * pa + (1 + 1) * (h00 * h01) * pb + h01 * h01 * pd) + ra)
        * ((h10 * h10 * pa + (1 + 1) * (h10 * h11) * pb + h11 * h11 * pd) + rd)
        - ((h00 * h10 * pa + (h00 * h11 + h01 * h10) * pb + h01 * h11 * pd) + rb)
          * ((h00 * h10 * pa + (h00 * h11 + h01 * h10) * pb + h01 * h11 * pd) + rb) :=
  psd2_det_add_ge
    (psd2_congruence (g00 := h00) (g01 := h01) (g10 := h10) (g11 := h11) hP) hR

end MachLib.Real
