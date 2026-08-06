import MachLib.KalmanVarianceRecursion
import MachLib.FixedPointRange

/-!
# When the range bit provably CANNOT fire — the steady-state design envelope

`chip2`'s `mon_fire_range` **detects** that a `WIDTH`-bit internal quantity did not fit.
`FixedPointRange.wrap_error_catastrophic` says what that **costs** — at least a full register span,
so it is not absorbable into a looser error bound. **Neither says when it can be RULED OUT.**

This file supplies the ruling-out, and the point is that it depends on the **noise parameters
alone**:

> ### `2·R + Q ≤ M`  and  `2·Zmax ≤ M`  ⟹  **neither hazard can occur at any step after the first.**

**That converts the status bit from a detector into a proof obligation the application discharges
at DESIGN time** rather than watching for at run time.

## The two hazards, and why each is bounded

`kalman_update.v` forms two `WIDTH`-bit quantities from unconstrained inputs:

| quantity | bounded by | because |
|---|---|---|
| `S = P⁻ + R = (P + Q) + R` | `2R + Q` | **the variance map lands strictly below `R`** — so after one update `P < R`, whatever `P₀` was |
| `innov = z − x` | `2·Zmax` | **the estimate stays in the convex hull of `x` and `z`** — `K ∈ [0,1)` makes the update a convex combination, so `x` never leaves the range its inputs occupy |

**The first is the interesting one.** `g(P) = P·r/(P+r) = r − r²·w` with `w = 1/(P+r) > 0`, so
`g(P) < r` **unconditionally on `P ≥ 0`** — the map forgets its argument's size in one step. That
identity is already derived inside `KalmanVarianceRecursion.kalman_var_lip_core`; this file states
it as a result rather than leaving it trapped in a `private` proof.

## ▸ THE HOLE, and it is where the hardware was measured to break

**Step 0 is NOT covered, and cannot be.** The first update consumes `P₀` directly, before any
contraction has happened, so no condition on `(Q, R)` can bound `S` at `n = 0`.

**This is exactly the measured failure.** `P₀ = 30000, R = 5000` overflows on the *first* update
(`monogate-research/chip/CHIP2_RANGE_DETERMINATION.md`), and *"initialise `P₀` large to express
ignorance"* is textbook practice. **A theorem that appeared to cover step 0 would be evidence of a
mis-statement, not a stronger result.**

**Consequence for chip 2: the range bit stays necessary for bring-up and start-up, and becomes
discharge-able for steady-state operation.** Those are different claims and the envelope separates
them.

No new axioms. No `sorry`.
-/

namespace MachLib
namespace Real

/-- `a ≤ c·b` with `b > 0` gives `a/b ≤ c`. The `≤` twin of
`WitnessResidualDeepNumeric.div_lt_of_lt_mul`, proved the same way. -/
private theorem div_le_of_le_mul {a b c : Real} (h : a ≤ c * b) (hb : 0 < b) : a / b ≤ c := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hbinv : 0 ≤ 1 / b := le_of_lt (one_div_pos_of_pos hb)
  have h2 : a * (1 / b) ≤ c * b * (1 / b) := mul_le_mul_of_nonneg_right h hbinv
  have e1 : c * b * (1 / b) = c * (b * (1 / b)) := mul_assoc c b (1 / b)
  have e2 : b * (1 / b) = 1 := mul_inv b hbne
  rw [e1, e2, mul_one_ax] at h2
  rwa [div_def a b hbne]

/-- **S1a — the variance map lands strictly below the measurement noise**, for ANY prior `P ≥ 0`.

`g(P) = P·r/(P+r) < r` reduces to `0 < r²` after clearing the (positive) denominator. **The map
forgets the size of its argument in a single step**, which is what makes the steady-state envelope
independent of `P₀`. -/
theorem kalman_var_map_lt_noise {r P : Real} (hr : 0 < r) (hP : 0 ≤ P) :
    kalmanVarMap r P < r := by
  have hPr : 0 < P + r := lt_of_lt_of_le hr (le_add_of_nonneg_left hP)
  refine div_lt_of_lt_mul ?_ hPr
  -- P·r < r·(P+r)  ⟺  0 < r²
  have hrr : 0 < r * r := mul_pos hr hr
  have e : r * (P + r) = P * r + r * r := by mach_mpoly [P, r]
  rw [e]
  have := add_lt_add_left hrr (P * r)      -- P·r + 0 < P·r + r·r
  rw [add_zero] at this
  exact this

/-- **S1b — and it does not exceed the prior either.** `g(P) ≤ P` reduces to `0 ≤ P²`. Together
with `kalman_var_map_lt_noise` this is `g(P) ≤ min(P, r)` — the posterior variance is never worse
than either thing it was built from, which is the sanity check the recursion needs. -/
theorem kalman_var_map_le_prior {r P : Real} (hr : 0 < r) (hP : 0 ≤ P) :
    kalmanVarMap r P ≤ P := by
  have hPr : 0 < P + r := lt_of_lt_of_le hr (le_add_of_nonneg_left hP)
  refine div_le_of_le_mul ?_ hPr
  -- P·r ≤ P·(P+r)  ⟺  0 ≤ P²
  have hPP : 0 ≤ P * P := mul_nonneg hP hP
  have e : P * (P + r) = P * r + P * P := by mach_mpoly [P, r]
  rw [e]
  have := add_le_add_left hPP (P * r)
  rw [add_zero] at this
  exact this

/-- **S2 — the post-update `S` is bounded by the noise parameters alone.**

One update from any prior `P ≥ 0` gives a posterior `P' = g(P⁻) < R`. The *next* step's denominator
is `S = (P' + Q) + R`, hence `S < 2R + Q` — **with no dependence on `P₀`.**

This is the numerical reachability observation of 2026-08-05 turned into a theorem: overflow in
steady operation requires a genuinely large `R`, not an unlucky prior.

**`Q` is unconstrained here on purpose.** The `Q` on each side cancels, so the bound needs no
hypothesis about the process noise at all — an earlier draft carried `0 ≤ Q` and the unused-variable
linter caught it as inert, which is the vacuity failure this arm pre-registered against. It is
removed rather than renamed `_`: a hypothesis that does no work should not appear in a signature a
reader has to satisfy. -/
theorem kalman_S_lt_envelope {R Q Pprev : Real}
    (hR : 0 < R) (hP : 0 ≤ Pprev) :
    (kalmanVarMap R Pprev + Q) + R < (R + R) + Q := by
  -- only `add_lt_add_left` exists (`c + a < c + b`), so commute rather than add a lemma
  have h1 : kalmanVarMap R Pprev < R := kalman_var_map_lt_noise hR hP
  have h2 : (Q + R) + kalmanVarMap R Pprev < (Q + R) + R := add_lt_add_left h1 (Q + R)
  have eL : (Q + R) + kalmanVarMap R Pprev = (kalmanVarMap R Pprev + Q) + R := by
    mach_mpoly [Q, R, kalmanVarMap R Pprev]
  have eR : (Q + R) + R = (R + R) + Q := by mach_mpoly [Q, R]
  rw [eL, eR] at h2
  exact h2

/-- **S4a — the `S` hazard is discharged by the envelope.** If `2R + Q ≤ M` then the post-update
denominator `Fits M`. This is the hypothesis `FixedPointRange.kalman_update_1d_fwd_error_representable`
needs for its first add, supplied from a **design-time** condition. -/
theorem kalman_S_fits_of_envelope {R Q Pprev M : Real}
    (hR : 0 < R) (hQ : 0 ≤ Q) (hP : 0 ≤ Pprev)
    (henv : (R + R) + Q ≤ M) :
    Fits M ((kalmanVarMap R Pprev + Q) + R) := by
  have hlt : (kalmanVarMap R Pprev + Q) + R < (R + R) + Q := kalman_S_lt_envelope hR hP
  have hle : (kalmanVarMap R Pprev + Q) + R ≤ M := le_trans (le_of_lt hlt) henv
  have hnn : 0 ≤ (kalmanVarMap R Pprev + Q) + R := by
    have hg : 0 ≤ kalmanVarMap R Pprev := by
      have hPr : 0 < Pprev + R := lt_of_lt_of_le hR (le_add_of_nonneg_left hP)
      exact div_nonneg (mul_nonneg hP (le_of_lt hR)) (le_of_lt hPr)
    exact add_nonneg (add_nonneg hg hQ) (le_of_lt hR)
  unfold Fits
  rw [abs_of_nonneg hnn]
  exact hle

/-- **S3 — the estimate stays in the convex hull of its inputs.**

With `k ∈ [0,1]` the update `x' = x + k·(z − x)` is `(1−k)·x + k·z`, so
`|x'| ≤ max(|x|,|z|)` — bounded here in the form actually needed: if both `|x| ≤ Zmax` and
`|z| ≤ Zmax` then `|x'| ≤ Zmax`. **The estimate never leaves the range its inputs occupy**, so the
innovation is bounded by `2·Zmax` forever. -/
theorem kalman_estimate_stays_bounded {x z k Zmax : Real}
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1)
    (hx : abs x ≤ Zmax) (hz : abs z ≤ Zmax) :
    abs (x + k * (z - x)) ≤ Zmax := by
  have e : x + k * (z - x) = (1 - k) * x + k * z := by mach_mpoly [x, z, k]
  rw [e]
  have h1k : 0 ≤ 1 - k := sub_nonneg_of_le hk1
  have hb1 : abs ((1 - k) * x) ≤ (1 - k) * Zmax := by
    rw [abs_mul, abs_of_nonneg h1k]
    exact mul_le_mul_of_nonneg_left hx h1k
  have hb2 : abs (k * z) ≤ k * Zmax := by
    rw [abs_mul, abs_of_nonneg hk0]
    exact mul_le_mul_of_nonneg_left hz hk0
  refine le_trans (abs_add _ _) ?_
  refine le_trans (add_le_add_both hb1 hb2) ?_
  exact le_of_eq (by mach_mpoly [k, Zmax])

/-- **S4b — the innovation hazard is discharged by the envelope.** `|z − x| ≤ 2·Zmax` whenever both
`|x|` and `|z|` are within `Zmax`, so `2·Zmax ≤ M` supplies `Fits M (z − x)` — the hypothesis
`kalman_update_1d_fwd_error_representable` needs for its second add. -/
theorem kalman_innov_fits_of_envelope {x z Zmax M : Real}
    (hx : abs x ≤ Zmax) (hz : abs z ≤ Zmax) (henv : Zmax + Zmax ≤ M) :
    Fits M (z - x) := by
  have h : abs (z - x) ≤ Zmax + Zmax := le_trans (abs_sub_le' z x) (add_le_add_both hz hx)
  exact le_trans h henv

/-- **S4 — THE ENVELOPE.** Both hazards discharged from conditions on the noise parameters and the
signal range alone: `2R + Q ≤ M` and `2·Zmax ≤ M`.

**Neither condition mentions `P₀`**, which is the whole point — and is also why this says nothing
about step 0, where `P₀` enters the denominator undiminished. -/
theorem kalman_range_envelope {R Q Pprev x z Zmax M : Real}
    (hR : 0 < R) (hQ : 0 ≤ Q) (hP : 0 ≤ Pprev)
    (hx : abs x ≤ Zmax) (hz : abs z ≤ Zmax)
    (henvS : (R + R) + Q ≤ M) (henvZ : Zmax + Zmax ≤ M) :
    Fits M ((kalmanVarMap R Pprev + Q) + R) ∧ Fits M (z - x) :=
  ⟨kalman_S_fits_of_envelope hR hQ hP henvS, kalman_innov_fits_of_envelope hx hz henvZ⟩

end Real
end MachLib
