import MachLib.NewtonReciprocalDivision
import MachLib.GaussianConjugacy

/-!
# Fixed-point forward error of the scalar Kalman update `kalman_update_1d`

The kernel (monogate-research `.../verilog_simulation_v0/eml/kalman_update_1d.eml`) is

    kalman_update_1d(x_pred, p_pred, z, r) = { let k = p_pred / (p_pred + r);
                                               x_pred + k * (z - x_pred) }

i.e. the **scalar Kalman measurement update** whose posterior mean `x + K·(z − x)` with gain
`K = P/(P+R)` is proven **MMSE-optimal** in `GaussianConjugacy.lean` (`posterior_mean_mmse`). This
file bounds how far the **Q16.16 fixed-point datapath** — which computes the gain by the certified
Newton–Raphson reciprocal (`NewtonReciprocalDivision.lean`, Forge lowers `a/b → a·recip(b)`) — strays
from that exact real update. It is the first kernel to carry the reciprocal error end-to-end into a
composed forward-error bound: the payoff of the `Q_n` division track.

## The datapath and where error enters

Forge lowers the kernel to (Q16.16, `s = 2⁻¹⁶` the grid step):

    s_den = p + r            -- exact (integer add, no truncation)
    recip = eml_reciprocal(s_den)   -- NR: |recip − 1/(p+r)| ≤ E_recip  (the ONLY approximation here)
    k_hw  = qmul(p, recip)   -- one truncation ≤ s
    d     = z − x            -- exact
    kd_hw = qmul(k_hw, d)    -- one truncation ≤ s
    result = x + kd_hw       -- exact

Because the two adds are **exact** in fixed point, the reciprocal sees the exact `p+r` (no `1/s²`
input-error amplification), and the whole error is the reciprocal's `E_recip` plus the two `qmul`
truncations. A three-term triangle split gives the bound below; `E_recip` is supplied by the 2-stage
NR analysis (`nr_reciprocal_2stage` + `nr_reciprocal_abs_error`, `E_recip = ((e_0²+c)²+c)/|p+r|`).

`sorryAx`-free, no new axioms.
-/

namespace MachLib
namespace Real

/-- The reciprocal value `w = 1/(p+r)` kept **abstract** (so `mach_mpoly` never touches the
`1/(p+r)` overlapping atom): the three-term triangle split + per-term abs bounds. -/
private theorem kalman_fwd_error_abs (x p z w recip_e k_hw kd_hw s Erec : Real)
    (hrec : abs (recip_e - w) ≤ Erec)
    (hk : abs (k_hw - p * recip_e) ≤ s)
    (hkd : abs (kd_hw - k_hw * (z - x)) ≤ s) :
    abs ((x + kd_hw) - (x + p * w * (z - x)))
      ≤ s + abs (z - x) * (s + abs p * Erec) := by
  -- split the total error into the two truncations + the reciprocal error, weighted by (z − x)
  have hsplit : (x + kd_hw) - (x + p * w * (z - x))
      = (kd_hw - k_hw * (z - x)) + (z - x) * (k_hw - p * recip_e)
        + (z - x) * (p * (recip_e - w)) := by
    mach_mpoly [x, z, p, w, recip_e, k_hw, kd_hw]
  rw [hsplit]
  refine le_trans (abs_add _ _) ?_
  refine le_trans (add_le_add_both (abs_add _ _) (le_refl _)) ?_
  have hB : abs ((z - x) * (k_hw - p * recip_e)) ≤ abs (z - x) * s := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hk (abs_nonneg _)
  have hC : abs ((z - x) * (p * (recip_e - w))) ≤ abs (z - x) * (abs p * Erec) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hrec (abs_nonneg _)) (abs_nonneg _)
  refine le_trans (add_le_add_both (add_le_add_both hkd hB) hC) ?_
  exact le_of_eq (by mach_mpoly [s, abs (z - x), abs p, Erec])

/-- **Forward error of the fixed-point scalar Kalman update.** With the reciprocal accurate to
`E_recip` (`|recip − 1/(p+r)| ≤ E_recip`) and the two `qmul`s truncating within `s`, the Q16.16
result `x + kd_hw` is within

    s + |z − x|·(s + |p|·E_recip)

of the exact real Kalman update `x + (p/(p+r))·(z − x)`. The bound is *sound*; it is deliberately a
worst-case-magnitude bound (`|z−x|`, `|p|` taken independently), so it runs looser than the measured
error — the honest "sound but conservative" shape of a composed fixed-point certificate. -/
theorem kalman_update_1d_fwd_error
    {x p z r recip_e k_hw kd_hw s Erec : Real}
    (hpr : p + r ≠ 0)
    (hrec : abs (recip_e - 1 / (p + r)) ≤ Erec)
    (hk : abs (k_hw - p * recip_e) ≤ s)
    (hkd : abs (kd_hw - k_hw * (z - x)) ≤ s) :
    abs ((x + kd_hw) - (x + p / (p + r) * (z - x)))
      ≤ s + abs (z - x) * (s + abs p * Erec) := by
  rw [div_def p (p + r) hpr]
  exact kalman_fwd_error_abs x p z (1 / (p + r)) recip_e k_hw kd_hw s Erec hrec hk hkd

/-- **The Kalman update error driven directly by the NR reciprocal's own bound.** Feeding the
2-stage reciprocal's *scaled* error `B = |1 − (p+r)·recip_e|` (`nr_reciprocal_2stage` gives
`B ≤ (e_0²+c)²+c`) through `nr_reciprocal_abs_error` (÷`|p+r|`) supplies `E_recip = B/|p+r|`, so the
whole fixed-point Kalman update inherits a bound in terms of the divisor's reciprocal certificate:

    |kalman_hw − kalman_exact| ≤ s + |z − x|·(s + |p|·B/|p+r|)

This is the end-to-end composition the `Q_n` track was built for — the reciprocal certificate
(`fxerr_recip` / `nr_reciprocal_2stage`) flowing into a real kernel's forward error. The kernel's gain
`k = p/(p+r)` and update `x + k·(z−x)` are exactly the MMSE-optimal `K` and posterior mean proven in
`GaussianConjugacy.posterior_mean_mmse`, so this bounds *the update proven statistically optimal*
against the silicon that computes it. -/
theorem kalman_update_1d_fwd_error_via_nr
    {x p z r recip_e k_hw kd_hw s B : Real}
    (hpr : p + r ≠ 0) (hpos : 0 < abs (p + r))
    (hscaled : abs (1 - (p + r) * recip_e) ≤ B)
    (hk : abs (k_hw - p * recip_e) ≤ s)
    (hkd : abs (kd_hw - k_hw * (z - x)) ≤ s) :
    abs ((x + kd_hw) - (x + p / (p + r) * (z - x)))
      ≤ s + abs (z - x) * (s + abs p * (B / abs (p + r))) :=
  kalman_update_1d_fwd_error hpr
    (nr_reciprocal_abs_error (p + r) recip_e B hpr hpos hscaled) hk hkd

/-! ## The composition — the fixed-point kernel is near-MMSE-OPTIMAL

The flagship claim rests on TWO theorems: (1) the real posterior mean `m(y) = x + K(y−x)` is
MMSE-optimal (`GaussianConjugacy.posterior_mean_mmse`), and (2) the Q16.16 kernel output is within `ε`
of that real mean (`kalman_update_1d_fwd_error`). Those do NOT compose to "the fixed-point kernel is
near-optimal" for free — the join must be *proved*, not asserted. It is proved here, and cleanly,
because the CONDITIONAL MSE of any point estimate `c` of `X | Y=y` is *exactly* `τ² + (c − m(y))²` (the
parallel-axis factorization, `posteriorMSE_tendsto` — no cross term, since `m` is the conditional
mean). So the fixed-point estimate `ĉ = kalman_hw`, with `|ĉ − m| ≤ ε`, has conditional MSE sandwiched:

    τ²  ≤  τ² + (ĉ − m)²  ≤  τ² + ε².

The lower bound is optimality (`posterior_mean_mmse`); the upper is the finite-precision excess risk,
`≤ ε²`. This is the machine-checked link the headline needs. -/

/-- **Near-MMSE-optimality of the fixed-point Kalman estimate.** Given `|kalman_hw − m(y)| ≤ ε` (the
Q16.16 forward error, `kalman_update_1d_fwd_error`), the estimate's conditional MSE `τ² + (kalman_hw −
m)²` lies in `[τ², τ² + ε²]`: at least the MMSE optimum `τ²`, and at most `ε²` above it. `m = postMean`
(= the kernel's exact value, `postMean_eq_kalman`); `τ² = postVar`. The excess risk of the *implemented*
estimator over the *provably optimal* one is therefore `≤ ε²`. -/
theorem kalman_update_1d_conditional_mse_near_optimal
    (x_pred p_pred z r kalman_hw ε : Real) (hε : 0 ≤ ε)
    (hfwd : abs (kalman_hw - (x_pred + p_pred / (p_pred + r) * (z - x_pred))) ≤ ε) :
    postVar p_pred r
        ≤ postVar p_pred r
          + (kalman_hw - postMean x_pred p_pred r z) * (kalman_hw - postMean x_pred p_pred r z)
      ∧ postVar p_pred r
          + (kalman_hw - postMean x_pred p_pred r z) * (kalman_hw - postMean x_pred p_pred r z)
        ≤ postVar p_pred r + ε * ε := by
  have hd : abs (kalman_hw - postMean x_pred p_pred r z) ≤ ε := by
    rw [postMean_eq_kalman]; exact hfwd
  refine ⟨posterior_mean_mmse x_pred p_pred r z kalman_hw, add_le_add_left ?_ _⟩
  have he : abs (kalman_hw - postMean x_pred p_pred r z)
              * abs (kalman_hw - postMean x_pred p_pred r z)
            = (kalman_hw - postMean x_pred p_pred r z) * (kalman_hw - postMean x_pred p_pred r z) := by
    rw [← abs_mul]; exact abs_of_nonneg (mul_self_nonneg _)
  rw [← he]
  exact le_trans (mul_le_mul_of_nonneg_right hd (abs_nonneg _))
    (mul_le_mul_of_nonneg_left hd hε)

/-- **End-to-end**: the Q16.16 datapath's near-optimality, driven by the same hypotheses as
`kalman_update_1d_fwd_error`. Under the per-`qmul` truncation bounds + the reciprocal error `Erec`, the
fixed-point kernel `x + kd_hw`'s conditional MSE is within `ε²` of the MMSE optimum, `ε = s + |z−x|·(s +
|p|·Erec)`. One statement: *the implemented estimator is provably within `ε²` of statistically optimal.* -/
theorem kalman_update_1d_fx_near_mmse
    {x_pred p_pred z r recip_e k_hw kd_hw s Erec : Real}
    (hpr : p_pred + r ≠ 0) (hs : 0 ≤ s) (hErec : 0 ≤ Erec)
    (hrec : abs (recip_e - 1 / (p_pred + r)) ≤ Erec)
    (hk : abs (k_hw - p_pred * recip_e) ≤ s)
    (hkd : abs (kd_hw - k_hw * (z - x_pred)) ≤ s) :
    postVar p_pred r
        + ((x_pred + kd_hw) - postMean x_pred p_pred r z)
          * ((x_pred + kd_hw) - postMean x_pred p_pred r z)
      ≤ postVar p_pred r
        + (s + abs (z - x_pred) * (s + abs p_pred * Erec))
          * (s + abs (z - x_pred) * (s + abs p_pred * Erec)) := by
  have hεnn : (0 : Real) ≤ s + abs (z - x_pred) * (s + abs p_pred * Erec) :=
    add_nonneg hs (mul_nonneg (abs_nonneg _)
      (add_nonneg hs (mul_nonneg (abs_nonneg _) hErec)))
  exact (kalman_update_1d_conditional_mse_near_optimal x_pred p_pred z r (x_pred + kd_hw)
    (s + abs (z - x_pred) * (s + abs p_pred * Erec)) hεnn
    (kalman_update_1d_fwd_error hpr hrec hk hkd)).2

end Real
end MachLib
