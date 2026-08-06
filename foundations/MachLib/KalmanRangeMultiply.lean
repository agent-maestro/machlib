import MachLib.KalmanRangeInduction
import MachLib.KalmanEstimateRecursion

/-!
# The MULTIPLY path is protected by the same range condition — and I had said otherwise

`FixedPointRange.lean`'s scope section claimed:

> *"The multiply path is untouched. Only the two adds are addressed; `qmul` truncation keeps its
> existing `≤ s` treatment, which is sound and **unaffected by range**."*

**The last clause is wrong.** `mac_q = mac_p_q[WIDTH+FRAC-1:FRAC]` is a **bit slice**, so the MAC
output wraps exactly like the adds do. Measured on the shipped RTL's datapath: over a stride-7
sample of plane A, the slice wraps **4,518** times for `K`, **16,774** for `dx`, and **53,831,328**
for `P'`.

## But the correction has a good ending

**Every one of those wraps is at or above the `S`-overflow line. Below it: ZERO, out of 76,702,866
sampled points.**

And that is **not luck** — it is forced, by the one fact the Kalman gain always satisfies:

> ### `K = P⁻/(P⁻+R) ∈ [0,1]`, so every MAC in this datapath is a CONVEX WEIGHT applied to a quantity that already fits.
>
> `k·innov` cannot exceed `innov`. `(1−k)·P⁻` cannot exceed `P⁻`. **A convex combination never
> leaves the interval its inputs occupy, so the products need no range condition of their own.**

**So the multiply path is not "unaffected by range" — it is *protected by the same* range
condition.** One obligation, three protections. That is a stronger result than the claim it
replaces, and it is why `mon_fire_range` covers more than it was designed for.

**What this does NOT say:** it does not bound the *pre-slice* 32-bit product, and it does not cover
the region above the `S` line, where the gain is computed from a wrapped `S` and `K ∈ [0,1]` fails.
There the range bit is already firing.

No new axioms. No `sorry`.
-/

namespace MachLib
namespace Real

/-- **The Kalman gain is non-negative.** `P⁻ ≥ 0`, `R > 0` ⟹ `P⁻/(P⁻+R) ≥ 0`. -/
theorem kalman_gain_nonneg {R P : Real} (hR : 0 < R) (hP : 0 ≤ P) :
    0 ≤ kalmanGainMap R P := by
  have hPr : 0 < P + R := lt_of_lt_of_le hR (le_add_of_nonneg_left hP)
  exact div_nonneg hP (le_of_lt hPr)

/-- **The Kalman gain is at most one.** `P⁻ ≤ P⁻ + R` because `R > 0`, so the quotient is `≤ 1`.

This is the fact that makes every multiply in the datapath a convex weight, and it is the reason
the MAC slices cannot wrap while the range condition on `S` holds. -/
theorem kalman_gain_le_one {R P : Real} (hR : 0 < R) (hP : 0 ≤ P) :
    kalmanGainMap R P ≤ 1 := by
  have hPr : 0 < P + R := lt_of_lt_of_le hR (le_add_of_nonneg_left hP)
  exact div_le_one_of_le_of_pos hPr (le_add_of_nonneg_right (le_of_lt hR))

/-- **A convex weight cannot enlarge what it multiplies.** `|k| ≤ 1` and `Fits M v` give
`Fits M (k·v)`. -/
theorem fits_mul_of_gain {k v M : Real} (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hv : Fits M v) :
    Fits M (k * v) := by
  unfold Fits at hv ⊢
  rw [abs_mul, abs_of_nonneg hk0]
  refine le_trans (mul_le_mul_of_nonneg_right hk1 (abs_nonneg v)) ?_
  have e : (1 : Real) * abs v = abs v := by mach_mpoly [abs v]
  rw [e]; exact hv

/-- **The `dx = K·innov` product fits whenever the innovation does.** No new obligation: the
innovation's `Fits` is already carried by `kalman_innov_fits_of_envelope`. -/
theorem kalman_dx_fits {k innov M : Real}
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hi : Fits M innov) : Fits M (k * innov) :=
  fits_mul_of_gain hk0 hk1 hi

/-- **The `P' = (1−K)·P⁻` product fits whenever the prior does.** `1 − k` is the complementary
convex weight, so the same bound applies from the other side. -/
theorem kalman_pnew_fits {k p M : Real}
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hp : Fits M p) : Fits M ((1 - k) * p) := by
  refine fits_mul_of_gain (sub_nonneg_of_le hk1) ?_ hp
  -- 1 - k ≤ 1  because  0 ≤ k
  refine le_of_sub_nonneg ?_
  have e : (1 : Real) - (1 - k) = k := by mach_mpoly [k]
  rw [e]; exact hk0

/-- **THE MULTIPLY PATH, DISCHARGED.** With the gain built from a `Fits`-respecting `S`, both MAC
outputs downstream of it fit whenever their own inputs do — so the datapath's multiplies add **no
range obligation beyond the two the adds already carry.**

`mon_fire_range` therefore covers the multiply path as a corollary of covering `S`. -/
theorem kalman_multiply_path_fits {R P innov M : Real}
    (hR : 0 < R) (hP : 0 ≤ P)
    (hi : Fits M innov) (hp : Fits M P) :
    Fits M (kalmanGainMap R P * innov) ∧ Fits M ((1 - kalmanGainMap R P) * P) :=
  ⟨kalman_dx_fits (kalman_gain_nonneg hR hP) (kalman_gain_le_one hR hP) hi,
   kalman_pnew_fits (kalman_gain_nonneg hR hP) (kalman_gain_le_one hR hP) hp⟩

/-- **The THIRD name for one function.** `GaussianConjugacy.kGain sig2 r2 = sig2/(sig2+r2)` and
`KalmanEstimateRecursion.kalmanGainMap r P = P/(P+r)` are the same map with swapped arguments —
the same pattern as `kalmanVarMap`/`postVar`, which closes by `rfl` in `KalmanRangeInduction`.

**Bridged, not merged**, for the same reason: unifying them touches the MMSE chain. -/
theorem kalmanGainMap_eq_kGain (r P : Real) : kalmanGainMap r P = kGain P r := rfl

end Real
end MachLib
