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

**Also Lean-proven, after a restructure: the fully expanded 2×2 entry identity.** The first attempt
stated both rows as one goal with three `subst`s and timed out at 200k heartbeats — reported at the
time as *"numerically-verified expansion"*, strictly weaker than the surrounding theorems. That
grading is now **retired**: the identity closes in ~22 s per row once it is STAGED —

* `ksk_split_a` / `_d` isolate the heavy part (`(K S Kᵀ)` with `S` expanded = congruence of `P` by
  `KH`, plus `K R Kᵀ`) as its own 12-variable lemma. **11 s each.**
* the assembly then rearranges the Joseph entry into `pa − 2(KHP) + [congruence + KRKᵀ]`, rewrites
  the bracket to `K S Kᵀ` via the split, and closes with the gain equation.

The lesson generalises past this file and cost a day to learn twice: **`mach_mpoly` fails on goal
SIZE, not on difficulty.** Both rows at once was ~2× the terms of one and it went from 11 s to
never. Stage first, and pick the staging so each lemma keeps one structure abstract.

Numerically cross-checked anyway, before and after: 2000 random PSD `P`, PSD `R`, arbitrary `H`,
worst discrepancy **8.6e-14**.

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

set_option maxHeartbeats 4000000 in
/-- **The heavy sub-identity, isolated.** `(K S Kᵀ)` with `S = H P Hᵀ + R` substituted, shown equal
to `congruence(K H, P) + K R Kᵀ`. Keeping this separate from the assembly is the whole reason the
proof closes: 12 variables here versus 14 with both rows and the `subst`s, and that difference is
the difference between 11 seconds and a heartbeat timeout. `(0,0)` entry. -/
theorem ksk_split_a (k00 k01 pa pb pd ra rb rd h00 h01 h10 h11 : Real) :
    k00 * (k00 * ((h00*h00*pa + (1+1)*(h00*h01)*pb + h01*h01*pd) + ra)
         + k01 * ((h00*h10*pa + (h00*h11 + h01*h10)*pb + h01*h11*pd) + rb))
  + k01 * (k00 * ((h00*h10*pa + (h00*h11 + h01*h10)*pb + h01*h11*pd) + rb)
         + k01 * ((h10*h10*pa + (1+1)*(h10*h11)*pb + h11*h11*pd) + rd))
    = ((k00*h00 + k01*h10) * (k00*h00 + k01*h10) * pa
        + (1+1) * ((k00*h00 + k01*h10) * (k00*h01 + k01*h11)) * pb
        + (k00*h01 + k01*h11) * (k00*h01 + k01*h11) * pd)
      + (k00*k00*ra + (1+1)*(k00*k01)*rb + k01*k01*rd) := by
  mach_mpoly [k00, k01, pa, pb, pd, ra, rb, rd, h00, h01, h10, h11]

set_option maxHeartbeats 4000000 in
/-- **`P − K S Kᵀ` IS the Joseph form** — the `(0,0)` entry, from the gain equation alone.

This is the theorem that makes `kalman2_joseph_psd` (proven for ANY gain) into the gain bound. -/
theorem joseph_eq_p_sub_ksk_a
    (k00 k01 pa pb pd ra rb rd h00 h01 h10 h11 : Real)
    (hg00 : k00 * ((h00*h00*pa + (1+1)*(h00*h01)*pb + h01*h01*pd) + ra)
          + k01 * ((h00*h10*pa + (h00*h11 + h01*h10)*pb + h01*h11*pd) + rb)
          = pa * h00 + pb * h01)
    (hg01 : k00 * ((h00*h10*pa + (h00*h11 + h01*h10)*pb + h01*h11*pd) + rb)
          + k01 * ((h10*h10*pa + (1+1)*(h10*h11)*pb + h11*h11*pd) + rd)
          = pa * h10 + pb * h11) :
    pa - (k00 * ((h00*h00*pa + (1+1)*(h00*h01)*pb + h01*h01*pd) + ra)
        + k01 * ((h00*h10*pa + (h00*h11 + h01*h10)*pb + h01*h11*pd) + rb)) * k00
       - (k00 * ((h00*h10*pa + (h00*h11 + h01*h10)*pb + h01*h11*pd) + rb)
        + k01 * ((h10*h10*pa + (1+1)*(h10*h11)*pb + h11*h11*pd) + rd)) * k01
      = ((1 - (k00*h00 + k01*h10)) * (1 - (k00*h00 + k01*h10)) * pa
          + (1+1) * ((1 - (k00*h00 + k01*h10)) * (-(k00*h01 + k01*h11))) * pb
          + (k00*h01 + k01*h11) * (k00*h01 + k01*h11) * pd)
        + (k00*k00*ra + (1+1)*(k00*k01)*rb + k01*k01*rd) := by
  have hrhs : ((1 - (k00*h00 + k01*h10)) * (1 - (k00*h00 + k01*h10)) * pa
          + (1+1) * ((1 - (k00*h00 + k01*h10)) * (-(k00*h01 + k01*h11))) * pb
          + (k00*h01 + k01*h11) * (k00*h01 + k01*h11) * pd)
        + (k00*k00*ra + (1+1)*(k00*k01)*rb + k01*k01*rd)
      = pa - (1+1) * ((k00*h00 + k01*h10) * pa + (k00*h01 + k01*h11) * pb)
        + (((k00*h00 + k01*h10) * (k00*h00 + k01*h10) * pa
            + (1+1) * ((k00*h00 + k01*h10) * (k00*h01 + k01*h11)) * pb
            + (k00*h01 + k01*h11) * (k00*h01 + k01*h11) * pd)
          + (k00*k00*ra + (1+1)*(k00*k01)*rb + k01*k01*rd)) := by
    mach_mpoly [k00, k01, pa, pb, pd, ra, rb, rd, h00, h01, h10, h11]
  rw [hrhs, ← ksk_split_a k00 k01 pa pb pd ra rb rd h00 h01 h10 h11, hg00, hg01]
  mach_mpoly [k00, k01, pa, pb, pd, h00, h01, h10, h11]

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
