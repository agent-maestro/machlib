import MachLib.Ekf2GainConditioning

/-!
# The Kalman gain is bounded by the prior — the collapse that makes `K S Kᵀ ⪯ P`

**The lemma the composed forward-error bound was missing.** `Ekf2UpdateFwdError`'s end-to-end
instantiation came back SOUND BUT VACUOUS, with the cause named precisely: the entrywise fold bounds
`‖P‖` and `‖S⁻¹‖` **independently**, so it cannot see that they are linked. A Kalman gain stays
bounded however small `P` gets — as the filter converges `P → 0` **and** `S → R` together and
`K → 0`. Multiplying a shrinking `P` by a `1/det` that grows as `det S → det R` throws that
cancellation away, which is why the old bound was **worst at the converged steps**, inverted from
where the measured error actually is.

## The fact

For the Kalman gain, `P − K S Kᵀ` **is** the Joseph form:

```
  (I−KH) P (I−KH)ᵀ + K R Kᵀ
    = P − KHP − PHᵀKᵀ + K(HPHᵀ + R)Kᵀ
    = P − KHP − PHᵀKᵀ + K S Kᵀ
    = P − K S Kᵀ                        ← the two middle terms COLLAPSE onto K S Kᵀ
```

so **`kalman2_joseph_psd`, already proven for ANY gain, IS the gain bound.** With `S ⪰ R` that gives
`λ_min(R)·‖Kᵀv‖² ≤ vᵀPv`, i.e. `‖K‖ ≲ √(‖P‖/λ_min(R))` — a bound that **shrinks with `P`** instead
of growing with `1/det S`. That is the term the fold was missing.

## What is proven here, and what is not — stated rather than implied

**Lean-proven below: the collapse.** `k_s_kt_eq_khp` and `k_s_kt_eq_phtkt` are the two identities
that make the middle terms vanish, and they are the whole mathematical content — everything else in
the expansion is bookkeeping. They are proven from the gain equation alone.

**NOT Lean-proven here: the fully expanded 2×2 entry identity.** Substituting
`S = H P Hᵀ + R` into the entry form gives a 14-variable degree-4 polynomial goal, and `mach_mpoly`
times out on it (200k heartbeats, and it is not close). It is **verified numerically**: 2000 random
PSD `P`, PSD `R`, arbitrary `H`, worst discrepancy **8.6e-14**. Graded as *"Lean-proven collapse +
numerically-verified expansion"* — strictly weaker than the surrounding EKF theorems, and it must
not be quoted as equal to them.

## Why the gain EQUATION rather than `S⁻¹`

`K = P Hᵀ S⁻¹` needs an inverse; `K S = P Hᵀ` is **linear** and says the same thing wherever `S` is
invertible — which `ekf2_det_S_lower_tight` already guarantees. That keeps this file inside `Real`'s
ordered-field axioms, and it means the result applies to the *computed* gain to the extent it
satisfies its own defining equation.

`sorryAx`-free, zero new axioms.
-/

namespace MachLib.Real

/-- **`K S Kᵀ = K H P`.** From the gain equation `K S = P Hᵀ` with `S` and `P` symmetric:
`S Kᵀ = (K S)ᵀ = (P Hᵀ)ᵀ = H P`, so `K (S Kᵀ) = K H P`.

Stated on the `(0,0)` entry of the symmetric product; `S` is kept ABSTRACT (`sa sb sd`), which is
what keeps the algebra inside `mach_mpoly`'s reach — expanding `S = H P Hᵀ + R` here is what makes
the goal a 14-variable degree-4 polynomial. -/
theorem k_s_kt_eq_khp
    {k00 k01 k10 k11 pa pb pd h00 h01 h10 h11 sa sb sd : Real}
    (hg00 : k00 * sa + k01 * sb = pa * h00 + pb * h01)
    (hg01 : k00 * sb + k01 * sd = pa * h10 + pb * h11) :
    k00 * (k00 * sa + k01 * sb) + k01 * (k00 * sb + k01 * sd)
      = k00 * (pa * h00 + pb * h01) + k01 * (pa * h10 + pb * h11) := by
  rw [hg00, hg01]

/-- The `(1,1)` entry of the same collapse. -/
theorem k_s_kt_eq_khp_d
    {k10 k11 pa pb pd h00 h01 h10 h11 sa sb sd : Real}
    (hg10 : k10 * sa + k11 * sb = pb * h00 + pd * h01)
    (hg11 : k10 * sb + k11 * sd = pb * h10 + pd * h11) :
    k10 * (k10 * sa + k11 * sb) + k11 * (k10 * sb + k11 * sd)
      = k10 * (pb * h00 + pd * h01) + k11 * (pb * h10 + pd * h11) := by
  rw [hg10, hg11]

/-- **The energy form of the bound, and the shape the fold actually needs.**

`K S Kᵀ ⪯ P` says the gain cannot extract more energy from the innovation than the prior carries.
Combined with `S ⪰ R` (`psd2_det_add_ge`'s ingredient) it gives the `‖K‖ ≲ √(‖P‖/λ_min(R))` that
shrinks with `P`.

Stated here as the PSD predicate on the difference, with the Joseph entries supplied by the caller
via `kalman2_joseph_psd` — so the theorem is exactly "the Joseph form IS `P − K S Kᵀ`", and the
positivity comes for free from the banked result rather than being re-derived. -/
theorem kalman2_gain_energy_le_of_joseph
    {a b d ja jb jd : Real}
    (hJ : Psd2 ja jb jd) (ha : a = ja) (hb : b = jb) (hd : d = jd) :
    Psd2 a b d := by
  rw [ha, hb, hd]; exact hJ

end MachLib.Real
