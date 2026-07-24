/-
`RiemannIntegralAdditivity.lean` — interval additivity for the Riemann integral:
`∫₀ᵃf + ∫ₐᵇf = ∫₀ᵇf` for `f` continuous & nonnegative on `[0,b]`, `0 ≤ a ≤ b`.

Why: designing the √π project's disk/square sandwich needs "FTC part 1" (the integral, as a
function of its upper limit, has derivative equal to the integrand), which needs a quantitative
interval bound that `riemann_integral_mono_interval` doesn't give (it only proves order). That
bound is most naturally built on additivity.

The core new piece is `maxSub_transfer_general`: `RiemannIntervalMonotone.lean`'s `maxSub_transfer`
compares `[0,a]`'s fine partition to `[0,b]`'s coarse partition (both starting at `0`). Here the
SECOND piece `[a,b]` starts at `a`, not `0`, so the fine subinterval's alignment against the coarse
mesh needs an EXTRA "which coarse cell does `a` itself land in" correction on top of the original
"which coarse cell does this fine index land in" one — combining two independent crossing-index
constructions (`least_nq_gt`, reused unchanged) means the fine argmax can land in the target coarse
cell OR either of its two neighbors, a 3-way case split instead of the original 2-way one.
-/
import MachLib.RiemannIntervalMonotone

namespace MachLib
namespace Real

/-! ## §1 — mesh points for an arbitrary-offset interval `[p,p+w]` -/

private theorem meshWidth_offset (p w : Real) (n : Nat) : meshWidth p (p + w) n = w / natCast n := by
  show (p + w - p) / natCast n = w / natCast n
  rw [show p + w - p = w from by mach_mpoly [p, w]]

theorem meshPoint_offset (p w : Real) (n i : Nat) :
    meshPoint p (p + w) n i = p + natCast i * (w / natCast n) := by
  show p + natCast i * meshWidth p (p + w) n = p + natCast i * (w / natCast n)
  rw [meshWidth_offset p w n]

/-! ## §2 — a small inequality-rearrangement helper -/

private theorem sub_le_swap (A B q : Real) (h : A - B ≤ q) : A - q ≤ B := by
  have h1 := add_le_add_both h (le_refl B)
  rw [show A - B + B = A from by mach_mpoly [A, B], show q + B = B + q from by mach_mpoly [q, B]] at h1
  have h2 := add_le_add_both h1 (le_refl (-q))
  rw [show B + q + -q = B from by mach_mpoly [B, q]] at h2
  rwa [← sub_def A q] at h2

/-! ## §3 — the offset-generalized per-term transfer -/

/-- The coarse `[0,c]` extremum at index `mp+j` bounds the nearby fine `[p,p+w]` extremum at index
`j`, up to the uniform-continuity slack `ε'`. Generalizes `maxSub_transfer` (which is the `p=0`
case) to an arbitrary offset `p`. Unlike the `p=0` case, the fine argmax can land in the target
coarse cell OR either neighbor (three cases, not two), since the offset `p` contributes its OWN
crossing-index slack on top of the width's. -/
theorem maxSub_transfer_general (f : Real → Real) (c : Real) (hc0 : 0 ≤ c)
    (hcont : ∀ z : Real, 0 ≤ z → z ≤ c → ContinuousAt f z)
    (p w : Real) (hp0 : 0 ≤ p) (hpw : 0 ≤ w) (hpwc : p + w ≤ c)
    (hcont_p : ∀ z : Real, p ≤ z → z ≤ p + w → ContinuousAt f z)
    (m mp K : Nat) (hK : 0 < 2 ^ K) (j : Nat) (hj : j ≤ m) (hjK : mp + m + 1 ≤ 2 ^ K)
    (q : Real) (hq : meshWidth 0 c (2 ^ K) = q) (hqnn : 0 ≤ q)
    (hcross_w : natCast m * q ≤ w) (hratio_w : w ≤ natCast (m + 1) * q)
    (hcross_p : natCast mp * q ≤ p) (hratio_p : p ≤ natCast (mp + 1) * q)
    (δ ε' : Real) (hδpos : 0 < δ) (hwidth : q < δ) (hε'nn : 0 ≤ ε')
    (hδ : ∀ y z : Real, 0 ≤ y → y ≤ c → 0 ≤ z → z ≤ c → abs (y - z) < δ → abs (f y - f z) < ε') :
    maxSub f p (p + w) (le_add_of_nonneg_right hpw) hcont_p (m + 1) (by omega) j
      ≤ maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j) + ε' := by
  have hpw' : p ≤ p + w := le_add_of_nonneg_right hpw
  have hjm1 : j < m + 1 := by omega
  have hcoarse0 : mp + j < 2 ^ K := by omega
  have hmem := maxSub_mem f p (p + w) hpw' hcont_p (m + 1) (by omega) j hjm1
  let x := Classical.choose (evt_exists_max f p (p + w) hpw' hcont_p (m + 1) (by omega) j hjm1)
  have hxeq : maxSub f p (p + w) hpw' hcont_p (m + 1) (by omega) j = f x :=
    maxSub_eq f p (p + w) hpw' hcont_p (m + 1) (by omega) j hjm1
  have hx1 : p + natCast j * (w / natCast (m + 1)) ≤ x := by
    rw [← meshPoint_offset p w (m + 1) j]; exact hmem.1
  have hx2 : x ≤ p + natCast (j + 1) * (w / natCast (m + 1)) := by
    rw [← meshPoint_offset p w (m + 1) (j + 1)]; exact hmem.2
  have hwnn : (0:Real) ≤ w / natCast (m + 1) := div_nonneg hpw (le_of_lt (natCast_pos (by omega)))
  have hx0 : 0 ≤ x := by
    have h1 : (0:Real) ≤ natCast j * (w / natCast (m + 1)) := mul_nonneg (natCast_nonneg j) hwnn
    have h2 := add_le_add_both hp0 h1
    rw [zero_add (0:Real)] at h2
    exact le_trans h2 hx1
  have hxc : x ≤ c := by
    have h1 : natCast (j + 1) * (w / natCast (m + 1)) ≤ natCast (m + 1) * (w / natCast (m + 1)) :=
      mul_le_mul_of_nonneg_right (natCast_le_of_nat_le (by omega)) hwnn
    rw [mul_div_self_cancel w m] at h1
    have h2 := add_le_add_both (le_refl p) h1
    exact le_trans hx2 (le_trans h2 hpwc)
  have hceq0 : meshPoint 0 c (2 ^ K) (mp + j) = natCast (mp + j) * q := by
    show (0:Real) + natCast (mp + j) * meshWidth 0 c (2 ^ K) = natCast (mp + j) * q
    rw [hq]; mach_mpoly [natCast (mp + j), q]
  have hceq1 : meshPoint 0 c (2 ^ K) (mp + j + 1) = natCast (mp + j + 1) * q := by
    show (0:Real) + natCast (mp + j + 1) * meshWidth 0 c (2 ^ K) = natCast (mp + j + 1) * q
    rw [hq]; mach_mpoly [natCast (mp + j + 1), q]
  have hzcast : natCast (mp + j) * q ≤ natCast (mp + j + 1) * q :=
    mul_le_mul_of_nonneg_right (natCast_le_of_nat_le (by omega)) hqnn
  by_cases hleft : x < natCast (mp + j) * q
  · -- CASE LEFT: x drifted just past the coarse boundary; transfer via uniform continuity
    have hdb := drift_bound w q m j hj hcross_w hratio_w
    have hdb' : natCast j * q - q ≤ natCast j * (w / natCast (m + 1)) := sub_le_swap _ _ _ hdb
    have hstep : natCast mp * q + (natCast j * q - q) ≤ x := by
      have h1 := add_le_add_both hcross_p hdb'
      exact le_trans h1 hx1
    have heqmpj : natCast mp * q + (natCast j * q - q) = natCast (mp + j) * q - q := by
      rw [natCast_add mp j]
      mach_mpoly [natCast mp, natCast j, q]
    rw [heqmpj] at hstep
    have hdrift : natCast (mp + j) * q - x ≤ q := sub_le_swap (natCast (mp + j) * q) q x hstep
    have hposdiff : (0:Real) ≤ natCast (mp + j) * q - x := sub_nonneg_of_le (le_of_lt hleft)
    have habs1 : abs (natCast (mp + j) * q - x) < δ := by
      rw [abs_of_nonneg hposdiff]; exact lt_of_le_of_lt hdrift hwidth
    have habs2 : abs (x - natCast (mp + j) * q) < δ := by rw [abs_sub_comm]; exact habs1
    have hzb : natCast (mp + j) * q ≤ c := by
      have h1 : natCast (mp + j) * q ≤ natCast (mp + j + 1) * q := hzcast
      have h2Kb := natCast_mul_meshWidth 0 c (2 ^ K) hK
      rw [hq] at h2Kb
      have heqc : c - 0 = c := by mach_mpoly [c]
      rw [heqc] at h2Kb
      have h3 : natCast (mp + j + 1) * q ≤ natCast (2 ^ K) * q :=
        mul_le_mul_of_nonneg_right (natCast_le_of_nat_le (by omega)) hqnn
      rw [h2Kb] at h3
      exact le_trans h1 h3
    have hz0 : (0:Real) ≤ natCast (mp + j) * q := mul_nonneg (natCast_nonneg (mp + j)) hqnn
    have hftrans := hδ x (natCast (mp + j) * q) hx0 hxc hz0 hzb habs2
    have hflt := lt_add_of_abs_sub_lt (f x) (f (natCast (mp + j) * q)) ε' hε'nn hftrans
    have hzmem2 : natCast (mp + j) * q ≤ meshPoint 0 c (2 ^ K) (mp + j + 1) := by
      rw [hceq1]; exact hzcast
    have hzspec := maxSub_spec f 0 c hc0 hcont (2 ^ K) hK (mp + j) hcoarse0 (natCast (mp + j) * q)
      (by rw [hceq0]; exact le_refl _) hzmem2
    rw [hxeq]
    exact le_trans (le_of_lt hflt) (add_le_add_both hzspec (le_refl ε'))
  · by_cases hright : natCast (mp + j + 1) * q < x
    · -- CASE RIGHT: x drifted just past the NEXT coarse boundary; transfer symmetrically
      have hawq : w / natCast (m + 1) ≤ q := a_div_le_q w q m hratio_w
      have hstep1 : natCast (j + 1) * (w / natCast (m + 1)) ≤ natCast (j + 1) * q :=
        mul_le_mul_of_nonneg_left hawq (natCast_nonneg (j + 1))
      have hstep2 : p + natCast (j + 1) * (w / natCast (m + 1)) ≤ natCast (mp + 1) * q + natCast (j + 1) * q :=
        add_le_add_both hratio_p hstep1
      have heqmpj2 : natCast (mp + 1) * q + natCast (j + 1) * q = natCast (mp + j + 2) * q := by
        rw [show mp + j + 2 = (mp + 1) + (j + 1) from by omega, natCast_add (mp + 1) (j + 1)]
        mach_mpoly [natCast (mp + 1), natCast (j + 1), q]
      rw [heqmpj2] at hstep2
      have hxupper : x ≤ natCast (mp + j + 2) * q := le_trans hx2 hstep2
      have heqmpj3 : natCast (mp + j + 2) * q - natCast (mp + j + 1) * q = q := by
        rw [show mp + j + 2 = (mp + j + 1) + 1 from by omega, natCast_add (mp + j + 1) 1, natCast_one_local2]
        mach_mpoly [natCast (mp + j + 1), q]
      have hdrift : x - natCast (mp + j + 1) * q ≤ q := by
        have h1 := add_le_add_both hxupper (le_refl (-(natCast (mp + j + 1) * q)))
        rw [← sub_def x (natCast (mp + j + 1) * q)] at h1
        rw [← sub_def (natCast (mp + j + 2) * q) (natCast (mp + j + 1) * q)] at h1
        rwa [heqmpj3] at h1
      have hposdiff : (0:Real) ≤ x - natCast (mp + j + 1) * q := sub_nonneg_of_le (le_of_lt hright)
      have habs1 : abs (x - natCast (mp + j + 1) * q) < δ := by
        rw [abs_of_nonneg hposdiff]; exact lt_of_le_of_lt hdrift hwidth
      have hz1c : natCast (mp + j + 1) * q ≤ c := by
        have h2Kb := natCast_mul_meshWidth 0 c (2 ^ K) hK
        rw [hq] at h2Kb
        have heqc : c - 0 = c := by mach_mpoly [c]
        rw [heqc] at h2Kb
        have h3 : natCast (mp + j + 1) * q ≤ natCast (2 ^ K) * q :=
          mul_le_mul_of_nonneg_right (natCast_le_of_nat_le (by omega)) hqnn
        rwa [h2Kb] at h3
      have hz10 : (0:Real) ≤ natCast (mp + j + 1) * q := mul_nonneg (natCast_nonneg (mp + j + 1)) hqnn
      have hftrans := hδ x (natCast (mp + j + 1) * q) hx0 hxc hz10 hz1c habs1
      have hflt := lt_add_of_abs_sub_lt (f x) (f (natCast (mp + j + 1) * q)) ε' hε'nn hftrans
      have hzmem1 : meshPoint 0 c (2 ^ K) (mp + j) ≤ natCast (mp + j + 1) * q := by
        rw [hceq0]; exact hzcast
      have hzspec := maxSub_spec f 0 c hc0 hcont (2 ^ K) hK (mp + j) hcoarse0 (natCast (mp + j + 1) * q)
        hzmem1 (by rw [hceq1]; exact le_refl _)
      rw [hxeq]
      exact le_trans (le_of_lt hflt) (add_le_add_both hzspec (le_refl ε'))
    · -- CASE MIDDLE: x is already in cell mp+j
      have hcm1 : meshPoint 0 c (2 ^ K) (mp + j) ≤ x := by
        rw [hceq0]; exact le_of_not_lt_mono hleft
      have hcm2 : x ≤ meshPoint 0 c (2 ^ K) (mp + j + 1) := by
        rw [hceq1]; exact le_of_not_lt_mono hright
      have hspec := maxSub_spec f 0 c hc0 hcont (2 ^ K) hK (mp + j) hcoarse0 x hcm1 hcm2
      rw [hxeq]
      have h1 := add_le_add_both hspec hε'nn
      rwa [show f x + 0 = f x from by mach_mpoly [f x]] at h1

/-- Symmetric counterpart of `maxSub_transfer_general`: the coarse `[0,c]` extremum (min) at index
`mp+j` is bounded ABOVE by the fine `[p,p+w]` extremum (min) at index `j`, up to `ε'`. Needed
because additivity is an EQUALITY, so both the upper-sum and lower-sum directions are required
(unlike `riemann_integral_mono_interval`'s one-directional inequality, which only needed the max
side). -/
theorem minSub_transfer_general (f : Real → Real) (c : Real) (hc0 : 0 ≤ c)
    (hcont : ∀ z : Real, 0 ≤ z → z ≤ c → ContinuousAt f z)
    (p w : Real) (hp0 : 0 ≤ p) (hpw : 0 ≤ w) (hpwc : p + w ≤ c)
    (hcont_p : ∀ z : Real, p ≤ z → z ≤ p + w → ContinuousAt f z)
    (m mp K : Nat) (hK : 0 < 2 ^ K) (j : Nat) (hj : j ≤ m) (hjK : mp + m + 1 ≤ 2 ^ K)
    (q : Real) (hq : meshWidth 0 c (2 ^ K) = q) (hqnn : 0 ≤ q)
    (hcross_w : natCast m * q ≤ w) (hratio_w : w ≤ natCast (m + 1) * q)
    (hcross_p : natCast mp * q ≤ p) (hratio_p : p ≤ natCast (mp + 1) * q)
    (δ ε' : Real) (hδpos : 0 < δ) (hwidth : q < δ) (hε'nn : 0 ≤ ε')
    (hδ : ∀ y z : Real, 0 ≤ y → y ≤ c → 0 ≤ z → z ≤ c → abs (y - z) < δ → abs (f y - f z) < ε') :
    minSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)
      ≤ minSub f p (p + w) (le_add_of_nonneg_right hpw) hcont_p (m + 1) (by omega) j + ε' := by
  have hpw' : p ≤ p + w := le_add_of_nonneg_right hpw
  have hjm1 : j < m + 1 := by omega
  have hcoarse0 : mp + j < 2 ^ K := by omega
  have hmem := minSub_mem f p (p + w) hpw' hcont_p (m + 1) (by omega) j hjm1
  let x := Classical.choose (evt_exists_min f p (p + w) hpw' hcont_p (m + 1) (by omega) j hjm1)
  have hxeq : minSub f p (p + w) hpw' hcont_p (m + 1) (by omega) j = f x :=
    minSub_eq f p (p + w) hpw' hcont_p (m + 1) (by omega) j hjm1
  have hx1 : p + natCast j * (w / natCast (m + 1)) ≤ x := by
    rw [← meshPoint_offset p w (m + 1) j]; exact hmem.1
  have hx2 : x ≤ p + natCast (j + 1) * (w / natCast (m + 1)) := by
    rw [← meshPoint_offset p w (m + 1) (j + 1)]; exact hmem.2
  have hwnn : (0:Real) ≤ w / natCast (m + 1) := div_nonneg hpw (le_of_lt (natCast_pos (by omega)))
  have hx0 : 0 ≤ x := by
    have h1 : (0:Real) ≤ natCast j * (w / natCast (m + 1)) := mul_nonneg (natCast_nonneg j) hwnn
    have h2 := add_le_add_both hp0 h1
    rw [zero_add (0:Real)] at h2
    exact le_trans h2 hx1
  have hxc : x ≤ c := by
    have h1 : natCast (j + 1) * (w / natCast (m + 1)) ≤ natCast (m + 1) * (w / natCast (m + 1)) :=
      mul_le_mul_of_nonneg_right (natCast_le_of_nat_le (by omega)) hwnn
    rw [mul_div_self_cancel w m] at h1
    have h2 := add_le_add_both (le_refl p) h1
    exact le_trans hx2 (le_trans h2 hpwc)
  have hceq0 : meshPoint 0 c (2 ^ K) (mp + j) = natCast (mp + j) * q := by
    show (0:Real) + natCast (mp + j) * meshWidth 0 c (2 ^ K) = natCast (mp + j) * q
    rw [hq]; mach_mpoly [natCast (mp + j), q]
  have hceq1 : meshPoint 0 c (2 ^ K) (mp + j + 1) = natCast (mp + j + 1) * q := by
    show (0:Real) + natCast (mp + j + 1) * meshWidth 0 c (2 ^ K) = natCast (mp + j + 1) * q
    rw [hq]; mach_mpoly [natCast (mp + j + 1), q]
  have hzcast : natCast (mp + j) * q ≤ natCast (mp + j + 1) * q :=
    mul_le_mul_of_nonneg_right (natCast_le_of_nat_le (by omega)) hqnn
  by_cases hleft : x < natCast (mp + j) * q
  · -- CASE LEFT
    have hdb := drift_bound w q m j hj hcross_w hratio_w
    have hdb' : natCast j * q - q ≤ natCast j * (w / natCast (m + 1)) := sub_le_swap _ _ _ hdb
    have hstep : natCast mp * q + (natCast j * q - q) ≤ x := by
      have h1 := add_le_add_both hcross_p hdb'
      exact le_trans h1 hx1
    have heqmpj : natCast mp * q + (natCast j * q - q) = natCast (mp + j) * q - q := by
      rw [natCast_add mp j]
      mach_mpoly [natCast mp, natCast j, q]
    rw [heqmpj] at hstep
    have hdrift : natCast (mp + j) * q - x ≤ q := sub_le_swap (natCast (mp + j) * q) q x hstep
    have hposdiff : (0:Real) ≤ natCast (mp + j) * q - x := sub_nonneg_of_le (le_of_lt hleft)
    have habs1 : abs (natCast (mp + j) * q - x) < δ := by
      rw [abs_of_nonneg hposdiff]; exact lt_of_le_of_lt hdrift hwidth
    have hzb : natCast (mp + j) * q ≤ c := by
      have h1 : natCast (mp + j) * q ≤ natCast (mp + j + 1) * q := hzcast
      have h2Kb := natCast_mul_meshWidth 0 c (2 ^ K) hK
      rw [hq] at h2Kb
      have heqc : c - 0 = c := by mach_mpoly [c]
      rw [heqc] at h2Kb
      have h3 : natCast (mp + j + 1) * q ≤ natCast (2 ^ K) * q :=
        mul_le_mul_of_nonneg_right (natCast_le_of_nat_le (by omega)) hqnn
      rw [h2Kb] at h3
      exact le_trans h1 h3
    have hz0 : (0:Real) ≤ natCast (mp + j) * q := mul_nonneg (natCast_nonneg (mp + j)) hqnn
    have hftrans := hδ (natCast (mp + j) * q) x hz0 hzb hx0 hxc habs1
    have hflt := lt_add_of_abs_sub_lt (f (natCast (mp + j) * q)) (f x) ε' hε'nn hftrans
    have hzmem2 : natCast (mp + j) * q ≤ meshPoint 0 c (2 ^ K) (mp + j + 1) := by
      rw [hceq1]; exact hzcast
    have hzspec := minSub_spec f 0 c hc0 hcont (2 ^ K) hK (mp + j) hcoarse0 (natCast (mp + j) * q)
      (by rw [hceq0]; exact le_refl _) hzmem2
    rw [hxeq]
    exact le_trans hzspec (le_of_lt hflt)
  · by_cases hright : natCast (mp + j + 1) * q < x
    · -- CASE RIGHT
      have hawq : w / natCast (m + 1) ≤ q := a_div_le_q w q m hratio_w
      have hstep1 : natCast (j + 1) * (w / natCast (m + 1)) ≤ natCast (j + 1) * q :=
        mul_le_mul_of_nonneg_left hawq (natCast_nonneg (j + 1))
      have hstep2 : p + natCast (j + 1) * (w / natCast (m + 1)) ≤ natCast (mp + 1) * q + natCast (j + 1) * q :=
        add_le_add_both hratio_p hstep1
      have heqmpj2 : natCast (mp + 1) * q + natCast (j + 1) * q = natCast (mp + j + 2) * q := by
        rw [show mp + j + 2 = (mp + 1) + (j + 1) from by omega, natCast_add (mp + 1) (j + 1)]
        mach_mpoly [natCast (mp + 1), natCast (j + 1), q]
      rw [heqmpj2] at hstep2
      have hxupper : x ≤ natCast (mp + j + 2) * q := le_trans hx2 hstep2
      have heqmpj3 : natCast (mp + j + 2) * q - natCast (mp + j + 1) * q = q := by
        rw [show mp + j + 2 = (mp + j + 1) + 1 from by omega, natCast_add (mp + j + 1) 1, natCast_one_local2]
        mach_mpoly [natCast (mp + j + 1), q]
      have hdrift : x - natCast (mp + j + 1) * q ≤ q := by
        have h1 := add_le_add_both hxupper (le_refl (-(natCast (mp + j + 1) * q)))
        rw [← sub_def x (natCast (mp + j + 1) * q)] at h1
        rw [← sub_def (natCast (mp + j + 2) * q) (natCast (mp + j + 1) * q)] at h1
        rwa [heqmpj3] at h1
      have hposdiff : (0:Real) ≤ x - natCast (mp + j + 1) * q := sub_nonneg_of_le (le_of_lt hright)
      have habs1 : abs (x - natCast (mp + j + 1) * q) < δ := by
        rw [abs_of_nonneg hposdiff]; exact lt_of_le_of_lt hdrift hwidth
      have habs2 : abs (natCast (mp + j + 1) * q - x) < δ := by rw [abs_sub_comm]; exact habs1
      have hz1c : natCast (mp + j + 1) * q ≤ c := by
        have h2Kb := natCast_mul_meshWidth 0 c (2 ^ K) hK
        rw [hq] at h2Kb
        have heqc : c - 0 = c := by mach_mpoly [c]
        rw [heqc] at h2Kb
        have h3 : natCast (mp + j + 1) * q ≤ natCast (2 ^ K) * q :=
          mul_le_mul_of_nonneg_right (natCast_le_of_nat_le (by omega)) hqnn
        rwa [h2Kb] at h3
      have hz10 : (0:Real) ≤ natCast (mp + j + 1) * q := mul_nonneg (natCast_nonneg (mp + j + 1)) hqnn
      have hftrans := hδ (natCast (mp + j + 1) * q) x hz10 hz1c hx0 hxc habs2
      have hflt := lt_add_of_abs_sub_lt (f (natCast (mp + j + 1) * q)) (f x) ε' hε'nn hftrans
      have hzmem1 : meshPoint 0 c (2 ^ K) (mp + j) ≤ natCast (mp + j + 1) * q := by
        rw [hceq0]; exact hzcast
      have hzspec := minSub_spec f 0 c hc0 hcont (2 ^ K) hK (mp + j) hcoarse0 (natCast (mp + j + 1) * q)
        hzmem1 (by rw [hceq1]; exact le_refl _)
      rw [hxeq]
      exact le_trans hzspec (le_of_lt hflt)
    · -- CASE MIDDLE
      have hcm1 : meshPoint 0 c (2 ^ K) (mp + j) ≤ x := by
        rw [hceq0]; exact le_of_not_lt_mono hleft
      have hcm2 : x ≤ meshPoint 0 c (2 ^ K) (mp + j + 1) := by
        rw [hceq1]; exact le_of_not_lt_mono hright
      have hspec := minSub_spec f 0 c hc0 hcont (2 ^ K) hK (mp + j) hcoarse0 x hcm1 hcm2
      rw [hxeq]
      have h1 := add_le_add_both hspec hε'nn
      rwa [show minSub f 0 c hc0 hcont (2 ^ K) hK (mp + j) + 0
          = minSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)
          from by mach_mpoly [minSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)]] at h1

/-! ## §4 — summing the per-term transfer into an upper/lower-sum bound -/

/-- The "window sum" `Σ_{j<n} g(mp+j)` never exceeds the full sum `Σ_{i<N} g(i)`, for nonnegative
`g` and `mp+n≤N`: the terms before `mp` are dropped (nonneg, so dropping only shrinks the sum) and
the terms from `mp+n` to `N-1` are dropped the same way. -/
theorem partialSum_window_le {g : Nat → Real} (hg : ∀ i, 0 ≤ g i) (mp n N : Nat) (hmpnN : mp + n ≤ N) :
    partialSum (fun j => g (mp + j)) n ≤ partialSum g N := by
  have hmple : mp ≤ N := by omega
  have hsplit := partialSum_add g mp (N - mp)
  rw [show mp + (N - mp) = N from by omega] at hsplit
  have hpsmpnn : (0:Real) ≤ partialSum g mp := partialSum_nonneg hg mp
  have hwindow_le : partialSum (fun j => g (mp + j)) n ≤ partialSum (fun j => g (mp + j)) (N - mp) :=
    partialSum_mono (fun j => hg (mp + j)) (by omega)
  rw [hsplit]
  have h1 := add_le_add_both hpsmpnn hwindow_le
  rwa [zero_add] at h1

/-- Companion to `partialSum_window_le`, opposite direction: a HEAD window `[0,mp+1)` and a TAIL
window `[mp,N)` — overlapping in exactly the single cell `mp` — together cover `[0,N)`, so their
sum bounds the full sum from ABOVE (the overlap only contributes one extra nonneg term). Needed to
recombine additivity's head/tail coarse-window bounds back into a single full coarse sum. -/
theorem partialSum_two_window_cover {g : Nat → Real} (hg : ∀ i, 0 ≤ g i) (mp N : Nat)
    (hmpN : mp ≤ N) :
    partialSum g N ≤ partialSum g (mp + 1) + partialSum (fun j => g (mp + j)) (N - mp) := by
  have hsplit := partialSum_add g mp (N - mp)
  rw [show mp + (N - mp) = N from by omega] at hsplit
  have hext : partialSum g mp ≤ partialSum g (mp + 1) := partialSum_mono hg (by omega)
  rw [hsplit]
  exact add_le_add_both hext (le_refl _)

/-- The EXACT version of `partialSum_two_window_cover`: the two windows' combined sum equals the
full sum PLUS the single overlap term `g mp`, counted twice. Needed for the upper-bound direction
of additivity's assembly, where the overlap must be bounded ABOVE by a global max `M`, not just
dropped as nonneg. -/
theorem partialSum_two_window_eq (g : Nat → Real) (mp N : Nat) (hmpN : mp ≤ N) :
    partialSum g (mp + 1) + partialSum (fun j => g (mp + j)) (N - mp)
      = partialSum g N + g mp := by
  have hsplit := partialSum_add g mp (N - mp)
  rw [show mp + (N - mp) = N from by omega] at hsplit
  rw [partialSum_succ g mp, hsplit]
  mach_mpoly [partialSum g mp, g mp, partialSum (fun j => g (mp + j)) (N - mp)]

theorem upperSumCont_transfer_general (f : Real → Real) (c : Real) (hc0 : 0 ≤ c)
    (hcont : ∀ z : Real, 0 ≤ z → z ≤ c → ContinuousAt f z)
    (hnonneg : ∀ z : Real, 0 ≤ z → z ≤ c → 0 ≤ f z)
    (p w : Real) (hp0 : 0 ≤ p) (hpw : 0 ≤ w) (hpwc : p + w ≤ c)
    (hcont_p : ∀ z : Real, p ≤ z → z ≤ p + w → ContinuousAt f z)
    (m mp K : Nat) (hK : 0 < 2 ^ K) (hjK : mp + m + 1 ≤ 2 ^ K)
    (q : Real) (hq : meshWidth 0 c (2 ^ K) = q) (hqnn : 0 ≤ q)
    (hcross_w : natCast m * q ≤ w) (hratio_w : w ≤ natCast (m + 1) * q)
    (hcross_p : natCast mp * q ≤ p) (hratio_p : p ≤ natCast (mp + 1) * q)
    (δ ε' : Real) (hδpos : 0 < δ) (hwidth : q < δ) (hε'nn : 0 ≤ ε')
    (hδ : ∀ y z : Real, 0 ≤ y → y ≤ c → 0 ≤ z → z ≤ c → abs (y - z) < δ → abs (f y - f z) < ε') :
    upperSumCont f p (p + w) (le_add_of_nonneg_right hpw) hcont_p (m + 1) (by omega)
      ≤ upperSumCont f 0 c hc0 hcont (2 ^ K) hK + ε' * w := by
  show partialSum (maxSub f p (p + w) (le_add_of_nonneg_right hpw) hcont_p (m + 1) (by omega)) (m + 1)
      * meshWidth p (p + w) (m + 1)
    ≤ partialSum (maxSub f 0 c hc0 hcont (2 ^ K) hK) (2 ^ K) * meshWidth 0 c (2 ^ K) + ε' * w
  rw [hq, meshWidth_offset p w (m + 1)]
  have htermwise : ∀ j, j < m + 1 →
      maxSub f p (p + w) (le_add_of_nonneg_right hpw) hcont_p (m + 1) (by omega) j
        ≤ (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j) + ε') j := by
    intro j hj
    exact maxSub_transfer_general f c hc0 hcont p w hp0 hpw hpwc hcont_p m mp K hK j (by omega) hjK
      q hq hqnn hcross_w hratio_w hcross_p hratio_p δ ε' hδpos hwidth hε'nn hδ
  have hstep1 := partialSum_le_of_termwise_le (m + 1) htermwise
  rw [partialSum_add_const (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) ε' (m + 1)] at hstep1
  have hwnn : (0:Real) ≤ w / natCast (m + 1) := div_nonneg hpw (le_of_lt (natCast_pos (by omega)))
  have hstep2 : partialSum (maxSub f p (p + w) (le_add_of_nonneg_right hpw) hcont_p (m + 1) (by omega))
      (m + 1) * (w / natCast (m + 1))
      ≤ (partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1) + natCast (m + 1) * ε')
      * (w / natCast (m + 1)) :=
    mul_le_mul_of_nonneg_right hstep1 hwnn
  have hpartc_nonneg : ∀ i : Nat, 0 ≤ maxSub f 0 c hc0 hcont (2 ^ K) hK i :=
    fun i => maxSub_nonneg f 0 c hc0 hcont hnonneg (2 ^ K) hK i
  have hwindow : partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1)
      ≤ partialSum (maxSub f 0 c hc0 hcont (2 ^ K) hK) (2 ^ K) :=
    partialSum_window_le hpartc_nonneg mp (m + 1) (2 ^ K) hjK
  have hexpand : (partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1)
      + natCast (m + 1) * ε') * (w / natCast (m + 1))
      = partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1) * (w / natCast (m + 1))
        + ε' * w := by
    rw [show (partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1)
        + natCast (m + 1) * ε') * (w / natCast (m + 1))
        = partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1) * (w / natCast (m + 1))
          + ε' * (natCast (m + 1) * (w / natCast (m + 1)))
        from by mach_mpoly [partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1),
          w / natCast (m + 1), natCast (m + 1), ε']]
    rw [mul_div_self_cancel w m]
  rw [hexpand] at hstep2
  have hstep4 : partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1) * (w / natCast (m + 1))
      ≤ partialSum (maxSub f 0 c hc0 hcont (2 ^ K) hK) (2 ^ K) * (w / natCast (m + 1)) :=
    mul_le_mul_of_nonneg_right hwindow hwnn
  have hstep5 : partialSum (maxSub f 0 c hc0 hcont (2 ^ K) hK) (2 ^ K) * (w / natCast (m + 1))
      ≤ partialSum (maxSub f 0 c hc0 hcont (2 ^ K) hK) (2 ^ K) * q := by
    apply mul_le_mul_of_nonneg_left (a_div_le_q w q m hratio_w)
    exact partialSum_nonneg hpartc_nonneg (2 ^ K)
  have h1 := le_trans hstep2 (add_le_add_both hstep4 (le_refl (ε' * w)))
  exact le_trans h1 (add_le_add_both hstep5 (le_refl (ε' * w)))

/-- Un-loosened companion to `upperSumCont_transfer_general`: keeps the coarse bound in
WINDOWED form (`partialSum` over just the `m+1` cells `[mp,mp+m+1)`) instead of loosening it to
the full `[0,c]` coarse sum via `partialSum_window_le`. Needed for additivity's assembly, where
the head and tail windows must be recombined via `partialSum_two_window_eq` — loosening each
piece to the full sum independently (as the `_general` version does) would double-count. -/
theorem upperSumCont_transfer_windowed (f : Real → Real) (c : Real) (hc0 : 0 ≤ c)
    (hcont : ∀ z : Real, 0 ≤ z → z ≤ c → ContinuousAt f z)
    (hnonneg : ∀ z : Real, 0 ≤ z → z ≤ c → 0 ≤ f z)
    (p w : Real) (hp0 : 0 ≤ p) (hpw : 0 ≤ w) (hpwc : p + w ≤ c)
    (hcont_p : ∀ z : Real, p ≤ z → z ≤ p + w → ContinuousAt f z)
    (m mp K : Nat) (hK : 0 < 2 ^ K) (hjK : mp + m + 1 ≤ 2 ^ K)
    (q : Real) (hq : meshWidth 0 c (2 ^ K) = q) (hqnn : 0 ≤ q)
    (hcross_w : natCast m * q ≤ w) (hratio_w : w ≤ natCast (m + 1) * q)
    (hcross_p : natCast mp * q ≤ p) (hratio_p : p ≤ natCast (mp + 1) * q)
    (δ ε' : Real) (hδpos : 0 < δ) (hwidth : q < δ) (hε'nn : 0 ≤ ε')
    (hδ : ∀ y z : Real, 0 ≤ y → y ≤ c → 0 ≤ z → z ≤ c → abs (y - z) < δ → abs (f y - f z) < ε') :
    upperSumCont f p (p + w) (le_add_of_nonneg_right hpw) hcont_p (m + 1) (by omega)
      ≤ partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1) * q + ε' * w := by
  show partialSum (maxSub f p (p + w) (le_add_of_nonneg_right hpw) hcont_p (m + 1) (by omega)) (m + 1)
      * meshWidth p (p + w) (m + 1)
    ≤ partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1) * q + ε' * w
  rw [meshWidth_offset p w (m + 1)]
  have htermwise : ∀ j, j < m + 1 →
      maxSub f p (p + w) (le_add_of_nonneg_right hpw) hcont_p (m + 1) (by omega) j
        ≤ (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j) + ε') j := by
    intro j hj
    exact maxSub_transfer_general f c hc0 hcont p w hp0 hpw hpwc hcont_p m mp K hK j (by omega) hjK
      q hq hqnn hcross_w hratio_w hcross_p hratio_p δ ε' hδpos hwidth hε'nn hδ
  have hstep1 := partialSum_le_of_termwise_le (m + 1) htermwise
  rw [partialSum_add_const (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) ε' (m + 1)] at hstep1
  have hwnn : (0:Real) ≤ w / natCast (m + 1) := div_nonneg hpw (le_of_lt (natCast_pos (by omega)))
  have hstep2 : partialSum (maxSub f p (p + w) (le_add_of_nonneg_right hpw) hcont_p (m + 1) (by omega))
      (m + 1) * (w / natCast (m + 1))
      ≤ (partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1) + natCast (m + 1) * ε')
      * (w / natCast (m + 1)) :=
    mul_le_mul_of_nonneg_right hstep1 hwnn
  have hpartc_nonneg : ∀ i : Nat, 0 ≤ maxSub f 0 c hc0 hcont (2 ^ K) hK i :=
    fun i => maxSub_nonneg f 0 c hc0 hcont hnonneg (2 ^ K) hK i
  have hexpand : (partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1)
      + natCast (m + 1) * ε') * (w / natCast (m + 1))
      = partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1) * (w / natCast (m + 1))
        + ε' * w := by
    rw [show (partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1)
        + natCast (m + 1) * ε') * (w / natCast (m + 1))
        = partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1) * (w / natCast (m + 1))
          + ε' * (natCast (m + 1) * (w / natCast (m + 1)))
        from by mach_mpoly [partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1),
          w / natCast (m + 1), natCast (m + 1), ε']]
    rw [mul_div_self_cancel w m]
  rw [hexpand] at hstep2
  have hstep5w : partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1)
      * (w / natCast (m + 1))
      ≤ partialSum (fun j => maxSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1) * q := by
    apply mul_le_mul_of_nonneg_left (a_div_le_q w q m hratio_w)
    exact partialSum_nonneg (fun j => hpartc_nonneg (mp + j)) (m + 1)
  exact le_trans hstep2 (add_le_add_both hstep5w (le_refl (ε' * w)))

private theorem partialSum_const_val (M : Real) : ∀ n : Nat, partialSum (fun _ => M) n = natCast n * M
  | 0 => by show (0:Real) = natCast 0 * M; rw [natCast_zero]; mach_mpoly [M]
  | k + 1 => by
      show partialSum (fun _ => M) k + M = natCast (k + 1) * M
      rw [partialSum_const_val M k, natCast_add k 1, natCast_one_local2]
      mach_mpoly [natCast k, M]

/-- `minSub` (any base interval) never exceeds a global bound valid on a larger interval
containing it. Mirrors `minSub_nonneg`'s structure exactly, bounding above instead of below. -/
theorem minSub_le_global_bound (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (M : Real) (hMub : ∀ x : Real, a ≤ x → x ≤ b → f x ≤ M) (n : Nat) (hn : 0 < n) (i : Nat) :
    minSub f a b hab hcont n hn i ≤ M := by
  by_cases hi : i < n
  · rw [minSub_eq f a b hab hcont n hn i hi]
    have hmem := minSub_mem f a b hab hcont n hn i hi
    apply hMub
    · exact le_trans (meshPoint_mem a b n i hab hn (Nat.le_of_lt hi)).1 hmem.1
    · exact le_trans hmem.2 (meshPoint_mem a b n (i + 1) hab hn hi).2
  · unfold minSub
    rw [dif_neg hi]
    exact hMub a (le_refl a) hab

/-- `maxSub` (any base interval) never exceeds a global bound valid on a larger interval
containing it. Mirrors `minSub_le_global_bound` exactly (both `minSub`/`maxSub` equal `f` at some
point in-range via `_eq`, so a global bound on `f` transfers unchanged). Needed for additivity's
assembly: the head/tail window-overlap term `maxSub_coarse(m_a)` needs a global bound `M` too. -/
theorem maxSub_le_global_bound (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (M : Real) (hMub : ∀ x : Real, a ≤ x → x ≤ b → f x ≤ M) (n : Nat) (hn : 0 < n) (i : Nat) :
    maxSub f a b hab hcont n hn i ≤ M := by
  by_cases hi : i < n
  · rw [maxSub_eq f a b hab hcont n hn i hi]
    have hmem := maxSub_mem f a b hab hcont n hn i hi
    apply hMub
    · exact le_trans (meshPoint_mem a b n i hab hn (Nat.le_of_lt hi)).1 hmem.1
    · exact le_trans hmem.2 (meshPoint_mem a b n (i + 1) hab hn hi).2
  · unfold maxSub
    rw [dif_neg hi]
    exact hMub a (le_refl a) hab

private theorem expand1_local (X nm1 ε' q : Real) : (X + nm1 * ε') * q = X * q + nm1 * ε' * q := by
  mach_mpoly [X, nm1, ε', q]

private theorem expand2_local (X wm1 q : Real) : X * q = X * wm1 + X * (q - wm1) := by
  mach_mpoly [X, wm1, q]

private theorem assoc_add4_local (A B C D : Real) : A + B + (C + D) = A + B + C + D := by
  mach_mpoly [A, B, C, D]

/-- Symmetric counterpart of `upperSumCont_transfer_general`, but with a genuinely NEW ingredient:
the mesh-width slack `w/(m+1)≤q` that made the upper-sum bound "free" works AGAINST the lower-sum
direction (weighting the same nonneg sum by the BIGGER `q` overshoots), so an extra global-max
correction `M·q` is needed — bounded via the same `drift_bound`-style telescoping as everywhere
else in this arc, using that each term is `≤M`. -/
theorem lowerSumCont_transfer_general (f : Real → Real) (c : Real) (hc0 : 0 ≤ c)
    (hcont : ∀ z : Real, 0 ≤ z → z ≤ c → ContinuousAt f z)
    (hnonneg : ∀ z : Real, 0 ≤ z → z ≤ c → 0 ≤ f z)
    (p w : Real) (hp0 : 0 ≤ p) (hpw : 0 ≤ w) (hpwc : p + w ≤ c)
    (hcont_p : ∀ z : Real, p ≤ z → z ≤ p + w → ContinuousAt f z)
    (m mp K : Nat) (hK : 0 < 2 ^ K) (hjK : mp + m + 1 ≤ 2 ^ K)
    (q : Real) (hq : meshWidth 0 c (2 ^ K) = q) (hqnn : 0 ≤ q)
    (hcross_w : natCast m * q ≤ w) (hratio_w : w ≤ natCast (m + 1) * q)
    (hcross_p : natCast mp * q ≤ p) (hratio_p : p ≤ natCast (mp + 1) * q)
    (δ ε' : Real) (hδpos : 0 < δ) (hwidth : q < δ) (hε'nn : 0 ≤ ε')
    (hδ : ∀ y z : Real, 0 ≤ y → y ≤ c → 0 ≤ z → z ≤ c → abs (y - z) < δ → abs (f y - f z) < ε')
    (M : Real) (hMnn : 0 ≤ M) (hMub : ∀ x : Real, 0 ≤ x → x ≤ c → f x ≤ M) :
    partialSum (fun j => minSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1) * q
      ≤ lowerSumCont f p (p + w) (le_add_of_nonneg_right hpw) hcont_p (m + 1) (by omega)
        + M * q + ε' * w + ε' * q := by
  have hpw' : p ≤ p + w := le_add_of_nonneg_right hpw
  show partialSum (fun j => minSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1) * q
    ≤ partialSum (minSub f p (p + w) hpw' hcont_p (m + 1) (by omega)) (m + 1)
        * meshWidth p (p + w) (m + 1)
      + M * q + ε' * w + ε' * q
  rw [meshWidth_offset p w (m + 1)]
  have htermwise : ∀ j, j < m + 1 →
      (fun j => minSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) j
        ≤ minSub f p (p + w) hpw' hcont_p (m + 1) (by omega) j + ε' := by
    intro j hj
    exact minSub_transfer_general f c hc0 hcont p w hp0 hpw hpwc hcont_p m mp K hK j (by omega) hjK
      q hq hqnn hcross_w hratio_w hcross_p hratio_p δ ε' hδpos hwidth hε'nn hδ
  have hstep1 := partialSum_le_of_termwise_le (m + 1) htermwise
  rw [partialSum_add_const (minSub f p (p + w) hpw' hcont_p (m + 1) (by omega)) ε' (m + 1)] at hstep1
  have hstep2 : partialSum (fun j => minSub f 0 c hc0 hcont (2 ^ K) hK (mp + j)) (m + 1) * q
      ≤ (partialSum (minSub f p (p + w) hpw' hcont_p (m + 1) (by omega)) (m + 1)
        + natCast (m + 1) * ε') * q :=
    mul_le_mul_of_nonneg_right hstep1 hqnn
  have hexpand1 := expand1_local
    (partialSum (minSub f p (p + w) hpw' hcont_p (m + 1) (by omega)) (m + 1))
    (natCast (m + 1)) ε' q
  rw [hexpand1] at hstep2
  -- bound partialSum(minSub_fine)(m+1)*q ≤ lowerSumCont(fine) + M*q
  have hMub_p : ∀ x : Real, p ≤ x → x ≤ p + w → f x ≤ M := fun x hx1 hx2 =>
    hMub x (le_trans hp0 hx1) (le_trans hx2 hpwc)
  have hfine_le_M : ∀ j : Nat, minSub f p (p + w) hpw' hcont_p (m + 1) (by omega) j ≤ M :=
    fun j => minSub_le_global_bound f p (p + w) hpw' hcont_p M hMub_p (m + 1) (by omega) j
  have hfine_partial_le : partialSum (minSub f p (p + w) hpw' hcont_p (m + 1) (by omega)) (m + 1)
      ≤ natCast (m + 1) * M := by
    have h1 := partialSum_le_of_termwise_le (m + 1)
      (fun j (_ : j < m + 1) => hfine_le_M j)
    rwa [partialSum_const_val M (m + 1)] at h1
  have hwnn : (0:Real) ≤ w / natCast (m + 1) := div_nonneg hpw (le_of_lt (natCast_pos (by omega)))
  have hqwnn : (0:Real) ≤ q - w / natCast (m + 1) := sub_nonneg_of_le (a_div_le_q w q m hratio_w)
  have hexpand2 := expand2_local
    (partialSum (minSub f p (p + w) hpw' hcont_p (m + 1) (by omega)) (m + 1))
    (w / natCast (m + 1)) q
  have hexcess_le : partialSum (minSub f p (p + w) hpw' hcont_p (m + 1) (by omega)) (m + 1)
      * (q - w / natCast (m + 1)) ≤ natCast (m + 1) * M * (q - w / natCast (m + 1)) :=
    mul_le_mul_of_nonneg_right hfine_partial_le hqwnn
  have hexcess_eq : natCast (m + 1) * M * (q - w / natCast (m + 1))
      = M * (natCast (m + 1) * q - w) := by
    rw [show natCast (m + 1) * M * (q - w / natCast (m + 1))
        = M * (natCast (m + 1) * q - natCast (m + 1) * (w / natCast (m + 1)))
        from by mach_mpoly [natCast (m + 1), M, q, w / natCast (m + 1)]]
    rw [mul_div_self_cancel w m]
  have heq3 : natCast (m + 1) * q - q = natCast m * q := by
    rw [natCast_m_succ]; mach_mpoly [natCast m, q]
  have hqwq_le : natCast (m + 1) * q - w ≤ q := by
    apply sub_le_swap (natCast (m + 1) * q) q w
    rw [heq3]; exact hcross_w
  have hexcess_le2 : partialSum (minSub f p (p + w) hpw' hcont_p (m + 1) (by omega)) (m + 1)
      * (q - w / natCast (m + 1)) ≤ M * q := by
    have h1 := le_trans hexcess_le (le_of_eq hexcess_eq)
    have h2 : M * (natCast (m + 1) * q - w) ≤ M * q := mul_le_mul_of_nonneg_left hqwq_le hMnn
    exact le_trans h1 h2
  have hfine_bound : partialSum (minSub f p (p + w) hpw' hcont_p (m + 1) (by omega)) (m + 1) * q
      ≤ partialSum (minSub f p (p + w) hpw' hcont_p (m + 1) (by omega)) (m + 1)
          * (w / natCast (m + 1)) + M * q := by
    rw [hexpand2]
    exact add_le_add_both (le_refl _) hexcess_le2
  have hmq_bound : natCast (m + 1) * ε' * q ≤ ε' * w + ε' * q := by
    have h1 : natCast (m + 1) * q ≤ w + q := by
      have h2 := add_le_add_both hqwq_le (le_refl w)
      rw [show natCast (m + 1) * q - w + w = natCast (m + 1) * q from by
        rw [natCast_m_succ]; mach_mpoly [natCast m, q, w]] at h2
      rwa [show q + w = w + q from by mach_mpoly [q, w]] at h2
    have h3 : natCast (m + 1) * ε' * q = ε' * (natCast (m + 1) * q) := by
      mach_mpoly [natCast (m + 1), ε', q]
    rw [h3]
    have h4 := mul_le_mul_of_nonneg_left h1 hε'nn
    rwa [show ε' * (w + q) = ε' * w + ε' * q from by mach_mpoly [ε', w, q]] at h4
  have h5 := add_le_add_both hfine_bound hmq_bound
  have h6 : partialSum (minSub f p (p + w) hpw' hcont_p (m + 1) (by omega)) (m + 1) * q
      + natCast (m + 1) * ε' * q
      ≤ partialSum (minSub f p (p + w) hpw' hcont_p (m + 1) (by omega)) (m + 1)
          * (w / natCast (m + 1)) + M * q + (ε' * w + ε' * q) :=
    h5
  have h7 := le_trans hstep2 h6
  rwa [assoc_add4_local
    (partialSum (minSub f p (p + w) hpw' hcont_p (m + 1) (by omega)) (m + 1)
      * (w / natCast (m + 1)))
    (M * q) (ε' * w) (ε' * q)] at h7

/-! ## §6 — dyadic mesh width, generalized: shrinks below any target, monotone in the exponent -/

/-- `meshWidth 0 b (2^N)` shrinks below any positive target `T`, for some `N`. Generalizes the
inline `hwidthK1`-style derivation from `riemann_integral_mono_interval` (there specialized to
`T=δ`) so it can be reused for additivity's SECOND independent target (bounding the `M·q` overlap
slack), not just the uniform-continuity `δ`. -/
theorem meshWidth_dyadic_lt_target (b : Real) (hb0 : 0 ≤ b) (T : Real) (hT : 0 < T) :
    ∃ N : Nat, meshWidth 0 b (2 ^ N) < T := by
  obtain ⟨N, hN⟩ := archimedean (b / T)
  have hNpos : 0 < N := by
    obtain h0 | hpos := Nat.eq_zero_or_pos N
    · exfalso
      have hnn : 0 ≤ b / T := div_nonneg hb0 (le_of_lt hT)
      rw [h0, natCast_zero] at hN
      exact lt_irrefl_ax 0 (lt_of_le_of_lt hnn hN)
    · exact hpos
  have hNle2N : N ≤ 2 ^ N := nat_le_two_pow N
  have hNcast : natCast N ≤ natCast (2 ^ N) := natCast_le_of_nat_le hNle2N
  refine ⟨N, ?_⟩
  show (b - 0) / natCast (2 ^ N) < T
  rw [sub_zero_local b]
  have hstep1 : b / natCast (2 ^ N) ≤ b / natCast N :=
    div_le_div_pos hb0 (le_refl b) (natCast_pos hNpos) hNcast
  have hstep2 : b / natCast N < T := by
    have hcross : b < T * natCast N := by
      have hmul := mul_lt_mul_of_pos_right hN hT
      rw [div_mul_cancel (ne_of_gt hT)] at hmul
      rwa [mul_comm (natCast N) T] at hmul
    exact div_lt_of_lt_mul hcross (natCast_pos hNpos)
  exact lt_of_le_of_lt hstep1 hstep2

/-- `meshWidth 0 b (2^K)` only shrinks (weakly) as the exponent grows. Generalizes the inline
`hwidthK`-style derivation from `riemann_integral_mono_interval` (there specialized to a single
extra factor `N`) to an arbitrary `N ≤ K`, so it composes with several independent
`meshWidth_dyadic_lt_target` targets at once (additivity needs two: `δ` and the `M·q` bound). -/
theorem meshWidth_dyadic_le_of_ge (b : Real) (hb0 : 0 ≤ b) (N K : Nat) (hNK : N ≤ K) :
    meshWidth 0 b (2 ^ K) ≤ meshWidth 0 b (2 ^ N) := by
  have hle : natCast (2 ^ N) ≤ natCast (2 ^ K) := by
    apply natCast_le_of_nat_le
    obtain ⟨j, hj⟩ := Nat.le.dest hNK
    rw [← hj]
    calc 2 ^ N ≤ 2 ^ N * 2 ^ j := Nat.le_mul_of_pos_right (2 ^ N) (two_pow_pos j)
      _ = 2 ^ (N + j) := by rw [← Nat.pow_add]
  have hstep1 : b / natCast (2 ^ K) ≤ b / natCast (2 ^ N) :=
    div_le_div_pos hb0 (le_refl b) (natCast_pos (two_pow_pos N)) hle
  have heqK : meshWidth 0 b (2 ^ K) = b / natCast (2 ^ K) := by
    show (b - 0) / natCast (2 ^ K) = b / natCast (2 ^ K)
    rw [sub_zero_local b]
  have heqN : meshWidth 0 b (2 ^ N) = b / natCast (2 ^ N) := by
    show (b - 0) / natCast (2 ^ N) = b / natCast (2 ^ N)
    rw [sub_zero_local b]
  rw [heqK, heqN]
  exact hstep1

/-! ## §7 — a global upper bound on `f`, cheaply, via EVT at the trivial 1-cell partition -/

private theorem meshPoint_zero_one_zero (b : Real) : meshPoint 0 b 1 0 = 0 := by
  show (0:Real) + natCast 0 * meshWidth 0 b 1 = 0
  rw [natCast_zero]
  mach_mpoly [meshWidth 0 b 1]

private theorem meshPoint_zero_one_one (b : Real) : meshPoint 0 b 1 1 = b := by
  show (0:Real) + natCast 1 * meshWidth 0 b 1 = b
  have heq := natCast_mul_meshWidth 0 b 1 (by omega)
  rw [sub_zero_local b] at heq
  rw [heq]
  mach_mpoly [b]

/-- A continuous, nonnegative `f` on `[0,b]` has a global upper bound `M`, obtained cheaply via
EVT at the trivial 1-cell partition (`n=1`, so `meshPoint 0 b 1 0 = 0` and `meshPoint 0 b 1 1 = b`
cover the whole interval in a single cell) rather than a fresh construction. Needed for
additivity's assembly: the head/tail window-overlap term (`maxSub_coarse(m_a)` or
`minSub_coarse(m_a)`) needs a bound that does not depend on the coarse resolution `K`. -/
theorem exists_global_max_bound (f : Real → Real) (b : Real) (hb0 : 0 ≤ b)
    (hcont : ∀ z : Real, 0 ≤ z → z ≤ b → ContinuousAt f z)
    (hnonneg : ∀ z : Real, 0 ≤ z → z ≤ b → 0 ≤ f z) :
    ∃ M : Real, 0 ≤ M ∧ ∀ x : Real, 0 ≤ x → x ≤ b → f x ≤ M := by
  have h1 : (0:Nat) < 1 := by omega
  refine ⟨maxSub f 0 b hb0 hcont 1 h1 0, maxSub_nonneg f 0 b hb0 hcont hnonneg 1 h1 0, ?_⟩
  intro x hx1 hx2
  refine maxSub_spec f 0 b hb0 hcont 1 h1 0 (by omega) x ?_ ?_
  · rw [meshPoint_zero_one_zero b]; exact hx1
  · rw [meshPoint_zero_one_one b]; exact hx2

/-! ## §8 — epsilon-splitting arithmetic toolkit, for the final assembly's 3-way error budget -/

private theorem pos_add_one (X : Real) (hX : 0 ≤ X) : 0 < X + 1 := by
  have h1 := add_le_add_both hX (le_refl (1:Real))
  rw [show (0:Real) + 1 = 1 from by mach_mpoly [(1:Real)]] at h1
  exact lt_of_lt_of_le zero_lt_one_ax h1

private theorem le_self_add_one (X : Real) : X ≤ X + 1 :=
  le_add_of_nonneg_right (le_of_lt zero_lt_one_ax)

/-- Halving: `X/2 + X/2 = X`. Parametrized (not `let`-bound) so it composes safely with
`mach_mpoly` at every use site — the established house rule this whole arc. -/
private theorem half_sum (X : Real) : X / (1 + 1) + X / (1 + 1) = X := by
  rw [← mul_two_eq_add_self (X / (1 + 1))]
  exact div_mul_cancel (ne_of_gt two_pos)

/-- The specific 3-way split the assembly needs: a gap-budget `ε/2`, plus two independent
quarter-budgets `ε/4` (one for the uniform-continuity slack, one for the `M·q` overlap slack),
summing back to exactly `ε`. -/
private theorem eps_three_way (ε : Real) :
    ε / (1 + 1) / (1 + 1) + ε / (1 + 1) / (1 + 1) + ε / (1 + 1) = ε := by
  rw [half_sum (ε / (1 + 1)), half_sum ε]

/-- Given a fixed multiplier `X ≥ 0` and a target `> 0`, there is a nonneg `ε'` with
`ε' * X < target`. Generalizes `riemann_integral_mono_interval`'s inline `ε'`-choice
(`ε' := ε''/(a+1)`, giving `ε'*a<ε''`) into a reusable lemma. -/
private theorem eps_mul_lt (X target : Real) (hX0 : 0 ≤ X) (htarget : 0 < target) :
    ∃ ε' : Real, 0 < ε' ∧ ε' * X < target := by
  have hX1pos : 0 < X + 1 := pos_add_one X hX0
  have hε'pos : 0 < target / (X + 1) := div_pos_of_pos_pos htarget hX1pos
  refine ⟨target / (X + 1), hε'pos, ?_⟩
  have hcancel : target / (X + 1) * (X + 1) = target := div_mul_cancel (ne_of_gt hX1pos)
  have h1 : target / (X + 1) * X + target / (X + 1) = target := by
    rw [show target / (X + 1) * X + target / (X + 1) = target / (X + 1) * (X + 1)
        from by mach_mpoly [target / (X + 1), X]]
    exact hcancel
  have h2 := add_lt_add_left hε'pos (target / (X + 1) * X)
  rw [h1] at h2
  rwa [show target / (X + 1) * X + 0 = target / (X + 1) * X
      from by mach_mpoly [target / (X + 1) * X]] at h2

/-- Given `M ≥ 0`, a target `> 0`, and `q` bounded above by `target/(M+1)`, then `M*q ≤ target`.
Avoids any "divide an inequality" lemma by cross-multiplying through `(M+1)*q ≤ target` instead
(reusing only `div_mul_cancel`, already available) and then dropping from `(M+1)*q` to `M*q` via
`M ≤ M+1`. -/
private theorem M_mul_bound (M T q : Real) (hMnn : 0 ≤ M) (hT : 0 < T) (hqnn : 0 ≤ q)
    (hqle : q ≤ T / (M + 1)) :
    M * q ≤ T := by
  have hM1pos : 0 < M + 1 := pos_add_one M hMnn
  have hcancel : (M + 1) * (T / (M + 1)) = T := by
    rw [mul_comm (M + 1) (T / (M + 1))]
    exact div_mul_cancel (ne_of_gt hM1pos)
  have h1 : (M + 1) * q ≤ (M + 1) * (T / (M + 1)) :=
    mul_le_mul_of_nonneg_left hqle (le_of_lt hM1pos)
  rw [hcancel] at h1
  have h2 : M * q ≤ (M + 1) * q := mul_le_mul_of_nonneg_right (le_self_add_one M) hqnn
  exact le_trans h2 h1

/-! ## §9 — the tail's crossing index, DERIVED from the head's -/

private theorem sub_le_sub_left_anti {x y : Real} (h : x ≤ y) (c : Real) : c - y ≤ c - x := by
  have h1 := add_le_add_both (le_refl c) (neg_le_neg h)
  rwa [← sub_def c y, ← sub_def c x] at h1

private theorem natCast_succ_mul_sub (m : Nat) (q : Real) :
    natCast (m + 1) * q - q = natCast m * q := by
  rw [natCast_m_succ]
  mach_mpoly [natCast m, q]

/-- The tail's own width-crossing index (for width `b-a`) can't be found independently via
`least_nq_gt` — doing so could make the head+tail coarse windows fail to exactly cover `[0,2^K)`.
It must instead be DERIVED from the head's width-crossing index `m_a` (for width `a`) via
`m_tail := 2^K - m_a - 1`, expressed here additively as `m_a+1+m_tail=2^K` to avoid Nat
truncated-subtraction pitfalls. Worked out by hand across several follow-ups this arc; this is
the Lean transcription. -/
private theorem tail_crossing (a b q : Real) (m_a m_tail K : Nat)
    (hcross_a : natCast m_a * q ≤ a) (hratio_a : a ≤ natCast (m_a + 1) * q)
    (hsplit : m_a + 1 + m_tail = 2 ^ K) (hqb : natCast (2 ^ K) * q = b) :
    natCast m_tail * q ≤ b - a ∧ b - a ≤ natCast (m_tail + 1) * q := by
  have hsum : natCast (m_a + 1) * q + natCast m_tail * q = b := by
    rw [← hsplit, natCast_add (m_a + 1) m_tail] at hqb
    rw [← hqb]
    mach_mpoly [natCast (m_a + 1), natCast m_tail, q]
  have h1 : natCast m_tail * q = b - natCast (m_a + 1) * q := by
    rw [← hsum]
    mach_mpoly [natCast (m_a + 1) * q, natCast m_tail * q]
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact sub_le_sub_left_anti hratio_a b
  · have h2 : natCast (m_tail + 1) * q = b - natCast m_a * q := by
      rw [natCast_m_succ, show (natCast m_tail + 1) * q = natCast m_tail * q + q
          from by mach_mpoly [natCast m_tail, q]]
      rw [h1]
      rw [show b - natCast (m_a + 1) * q + q = b - (natCast (m_a + 1) * q - q)
          from by mach_mpoly [b, natCast (m_a + 1) * q, q]]
      rw [natCast_succ_mul_sub m_a q]
    rw [h2]
    exact sub_le_sub_left_anti hcross_a b

private theorem distrib_mul (X Y q : Real) : (X + Y) * q = X * q + Y * q := by
  mach_mpoly [X, Y, q]

/-- Regroups `(A+B)+(C+D)` into `(A+C)+(B+D)` — pure associativity/commutativity, but hoisted so
the MAIN proof never has to hand a `mach_mpoly` call a Real atom built from `have`/`obtain`-bound
locals (the house rule from earlier this arc: complex terms as ARGUMENTS to a pre-proven generic
lemma are safe; the same terms as ATOMS inside a fresh `mach_mpoly` call are not). -/
private theorem regroup4 (A B C D : Real) : (A + B) + (C + D) = (A + C) + (B + D) := by
  mach_mpoly [A, B, C, D]

private theorem eps_split_add (ε' a b : Real) : ε' * a + ε' * (b - a) = ε' * b := by
  mach_mpoly [ε', a, b]

/-- Right-sided companion to the axiom `add_lt_add_left` (which only adds on the left). -/
private theorem add_lt_add_right_weak {X Y : Real} (h : X < Y) (c : Real) : X + c < Y + c := by
  rw [add_comm X c, add_comm Y c]
  exact add_lt_add_left h c

/-- The exact 3-way regroup+resum the assembly's final step needs:
`I_b + ε_gap + ε_q + ε_q = I_b + ε`, where `ε_gap := ε/2`, `ε_q := ε/4` (both inline, matching
`eps_three_way`'s split up to reordering). -/
private theorem final_combine (I_b ε : Real) :
    I_b + ε / (1 + 1) + ε / (1 + 1) / (1 + 1) + ε / (1 + 1) / (1 + 1) = I_b + ε := by
  have h1 : ε / (1 + 1) + ε / (1 + 1) / (1 + 1) + ε / (1 + 1) / (1 + 1) = ε := by
    rw [show ε / (1 + 1) + ε / (1 + 1) / (1 + 1) + ε / (1 + 1) / (1 + 1)
        = ε / (1 + 1) / (1 + 1) + ε / (1 + 1) / (1 + 1) + ε / (1 + 1)
        from by mach_mpoly [ε / (1 + 1), ε / (1 + 1) / (1 + 1)]]
    exact eps_three_way ε
  rw [show I_b + ε / (1 + 1) + ε / (1 + 1) / (1 + 1) + ε / (1 + 1) / (1 + 1)
      = I_b + (ε / (1 + 1) + ε / (1 + 1) / (1 + 1) + ε / (1 + 1) / (1 + 1))
      from by mach_mpoly [I_b, ε / (1 + 1), ε / (1 + 1) / (1 + 1)]]
  rw [h1]

/-- Congruence for `upperSumCont`/`lowerSumCont` in their Nat resolution argument, local copies of
the private `upperSumCont_congr`/`lowerSumCont_congr` from `RiemannIntegralRefine.lean` (not
accessible from here). Needed because `K` is `let`-bound to `K0+N1+N2`, but `upperSumCont_dyadic_anti`
et al. produce terms indexed by `2^(K0+(N1+N2))` — propositionally, not syntactically, the same
exponent (associativity), so a raw `rw` on the exponent hits a dependent-motive failure; this
congruence lemma sidesteps that by rewriting the WHOLE `upperSumCont`/`lowerSumCont` application at
once via `N1=N2 → upperSumCont ... N1 h1 = upperSumCont ... N2 h2`. -/
private theorem upperSumCont_congr_local (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) :
    ∀ {N1 N2 : Nat}, N1 = N2 → ∀ (h1 : 0 < N1) (h2 : 0 < N2),
      upperSumCont f a b hab hcont N1 h1 = upperSumCont f a b hab hcont N2 h2
  | _, _, rfl, _, _ => rfl

private theorem lowerSumCont_congr_local (f : Real → Real) (a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z) :
    ∀ {N1 N2 : Nat}, N1 = N2 → ∀ (h1 : 0 < N1) (h2 : 0 < N2),
      lowerSumCont f a b hab hcont N1 h1 = lowerSumCont f a b hab hcont N2 h2
  | _, _, rfl, _, _ => rfl

/-- Congruence for `upperSumCont` in its Real upper-endpoint argument. Needed because
`upperSumCont_transfer_windowed`, called with `p:=0,w:=a`, produces a conclusion about
`upperSumCont f 0 (0+a) ...` — propositionally but not syntactically `upperSumCont f 0 a ...`
(`Real` addition is opaque/axiomatized, not computed) — same dependent-motive risk as above, same
fix: rewrite the whole application via a purpose-built congruence lemma instead of a raw `rw`. -/
private theorem upperSumCont_congr_val (f : Real → Real) (p : Real) :
    ∀ {b1 b2 : Real}, b1 = b2 → ∀ (hab1 : p ≤ b1) (hab2 : p ≤ b2)
      (hcont1 : ∀ z : Real, p ≤ z → z ≤ b1 → ContinuousAt f z)
      (hcont2 : ∀ z : Real, p ≤ z → z ≤ b2 → ContinuousAt f z)
      (n : Nat) (hn : 0 < n),
      upperSumCont f p b1 hab1 hcont1 n hn = upperSumCont f p b2 hab2 hcont2 n hn
  | _, _, rfl, _, _, _, _, _, _ => rfl

/-- Additive-index wrapper for `partialSum_two_window_eq`, avoiding Nat truncated subtraction in
its statement (the head/tail split is naturally additive: `m_a+1+m_tail=2^K`). -/
private theorem partialSum_two_window_eq_add (g : Nat → Real) (m_a m_tail K : Nat)
    (hsplit : m_a + 1 + m_tail = 2 ^ K) :
    partialSum g (m_a + 1) + partialSum (fun j => g (m_a + j)) (m_tail + 1)
      = partialSum g (2 ^ K) + g m_a := by
  have h := partialSum_two_window_eq g m_a (2 ^ K) (by omega)
  rwa [show 2 ^ K - m_a = m_tail + 1 from by omega] at h

/-- `upperSumCont_transfer_windowed`/`lowerSumCont_transfer_general` at `mp:=0` produce
`fun j => g (0+j)`, not `g` itself — `0+j` is only PROPOSITIONALLY, not syntactically, `j`. Bridges
this so the head's window sum can be identified with the plain `partialSum g (m_a+1)` that
`partialSum_two_window_eq_add` expects. -/
private theorem partialSum_zero_offset (g : Nat → Real) : ∀ n : Nat,
    partialSum (fun j => g (0 + j)) n = partialSum g n
  | 0 => rfl
  | k + 1 => by
      show partialSum (fun j => g (0 + j)) k + g (0 + k) = partialSum g k + g k
      rw [partialSum_zero_offset g k, Nat.zero_add]

/-! ## §10 — the headline: interval additivity for the Riemann integral, upper-bound direction -/

/-- `I_a + I_w ≤ I_b`, half of interval additivity. Takes `a < b` STRICTLY — the `a = b` case
(where `[a,b]` degenerates to a point) is handled separately by the public headline theorem, via
`riemann_integral_unique` instead of this ε-argument. -/
private theorem riemann_integral_additivity_le (f : Real → Real) (a b : Real)
    (ha0 : 0 ≤ a) (hab_lt : a < b) (hb0 : 0 ≤ b)
    (hcont : ∀ z : Real, 0 ≤ z → z ≤ b → ContinuousAt f z)
    (hcont_a : ∀ z : Real, 0 ≤ z → z ≤ a → ContinuousAt f z)
    (hcont_w : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hnonneg : ∀ z : Real, 0 ≤ z → z ≤ b → 0 ≤ f z)
    (I_a I_w I_b : Real)
    (hIa_up : ∀ k, I_a ≤ upperSumCont f 0 a ha0 hcont_a (2 ^ k) (two_pow_pos k))
    (hIa_gap : ∀ ε : Real, 0 < ε → ∃ k, upperSumCont f 0 a ha0 hcont_a (2 ^ k) (two_pow_pos k)
        - lowerSumCont f 0 a ha0 hcont_a (2 ^ k) (two_pow_pos k) < ε)
    (hIw_up : ∀ k, I_w ≤ upperSumCont f a b (le_of_lt hab_lt) hcont_w (2 ^ k) (two_pow_pos k))
    (hIw_gap : ∀ ε : Real, 0 < ε → ∃ k, upperSumCont f a b (le_of_lt hab_lt) hcont_w (2 ^ k) (two_pow_pos k)
        - lowerSumCont f a b (le_of_lt hab_lt) hcont_w (2 ^ k) (two_pow_pos k) < ε)
    (hIb_low : ∀ k, lowerSumCont f 0 b hb0 hcont (2 ^ k) (two_pow_pos k) ≤ I_b)
    (hIb_gap : ∀ ε : Real, 0 < ε → ∃ k, upperSumCont f 0 b hb0 hcont (2 ^ k) (two_pow_pos k)
        - lowerSumCont f 0 b hb0 hcont (2 ^ k) (two_pow_pos k) < ε) :
    I_a + I_w ≤ I_b := by
  have hab : a ≤ b := le_of_lt hab_lt
  apply le_of_forall_pos_lt_add
  intro ε hε
  have hε_gap_pos : 0 < ε / (1 + 1) := div_pos_of_pos_pos hε two_pos
  have hε_q_pos : 0 < ε / (1 + 1) / (1 + 1) := div_pos_of_pos_pos hε_gap_pos two_pos
  obtain ⟨M, hMnn, hMub⟩ := exists_global_max_bound f b hb0 hcont hnonneg
  obtain ⟨K0, hK0⟩ := hIb_gap (ε / (1 + 1)) hε_gap_pos
  obtain ⟨ε', hε'pos, hε'b⟩ := eps_mul_lt b (ε / (1 + 1) / (1 + 1)) hb0 hε_q_pos
  obtain ⟨δ, hδpos, hδ⟩ := heine_cantor_uniform_continuity hb0 hcont ε' hε'pos
  obtain ⟨N1, hN1⟩ := meshWidth_dyadic_lt_target b hb0 δ hδpos
  have hMq_target_pos : 0 < ε / (1 + 1) / (1 + 1) / (M + 1) :=
    div_pos_of_pos_pos hε_q_pos (pos_add_one M hMnn)
  obtain ⟨N2, hN2⟩ := meshWidth_dyadic_lt_target b hb0
    (ε / (1 + 1) / (1 + 1) / (M + 1)) hMq_target_pos
  let K := K0 + N1 + N2
  have hKeq : K = K0 + N1 + N2 := rfl
  have hK : 0 < 2 ^ K := two_pow_pos K
  have hwidthK_δ : meshWidth 0 b (2 ^ K) < δ :=
    lt_of_le_of_lt (meshWidth_dyadic_le_of_ge b hb0 N1 K (by omega)) hN1
  have hwidthK_Mq : meshWidth 0 b (2 ^ K) < ε / (1 + 1) / (1 + 1) / (M + 1) :=
    lt_of_le_of_lt (meshWidth_dyadic_le_of_ge b hb0 N2 K (by omega)) hN2
  have hgapK : upperSumCont f 0 b hb0 hcont (2 ^ K) hK
      - lowerSumCont f 0 b hb0 hcont (2 ^ K) hK < ε / (1 + 1) := by
    have hu := upperSumCont_dyadic_anti f 0 b hb0 hcont K0 (N1 + N2) (two_pow_pos K0)
    have hl := lowerSumCont_dyadic_mono f 0 b hb0 hcont K0 (N1 + N2) (two_pow_pos K0)
    have hneg : -lowerSumCont f 0 b hb0 hcont (2 ^ (K0 + (N1 + N2))) (two_pow_pos (K0 + (N1 + N2)))
        ≤ -lowerSumCont f 0 b hb0 hcont (2 ^ K0) (two_pow_pos K0) := neg_le_neg hl
    have hsum := add_le_add_both hu hneg
    rw [← sub_def (upperSumCont f 0 b hb0 hcont (2 ^ (K0 + (N1 + N2))) (two_pow_pos (K0 + (N1 + N2))))
          (lowerSumCont f 0 b hb0 hcont (2 ^ (K0 + (N1 + N2))) (two_pow_pos (K0 + (N1 + N2)))),
        ← sub_def (upperSumCont f 0 b hb0 hcont (2 ^ K0) (two_pow_pos K0))
          (lowerSumCont f 0 b hb0 hcont (2 ^ K0) (two_pow_pos K0))] at hsum
    have hpow_eq : (2:Nat) ^ K = 2 ^ (K0 + (N1 + N2)) := by rw [show K = K0 + (N1 + N2) from by omega]
    rw [upperSumCont_congr_local f 0 b hb0 hcont hpow_eq hK (two_pow_pos (K0 + (N1 + N2))),
        lowerSumCont_congr_local f 0 b hb0 hcont hpow_eq hK (two_pow_pos (K0 + (N1 + N2)))]
    exact lt_of_le_of_lt hsum hK0
  have hqnn : 0 ≤ meshWidth 0 b (2 ^ K) := meshWidth_nonneg hb0 (2 ^ K)
  have hqb : natCast (2 ^ K) * meshWidth 0 b (2 ^ K) = b := by
    have h1 := natCast_mul_meshWidth 0 b (2 ^ K) hK
    rwa [sub_zero_local b] at h1
  have haltN : a < natCast (2 ^ K) * meshWidth 0 b (2 ^ K) := by rw [hqb]; exact hab_lt
  obtain ⟨n, hnle, hn1, hn2⟩ := least_nq_gt a (meshWidth 0 b (2 ^ K)) (2 ^ K) haltN
  have hnne : n ≠ 0 := by
    intro hn0
    rw [hn0, natCast_zero, zero_mul] at hn1
    exact lt_irrefl_ax 0 (lt_of_le_of_lt ha0 hn1)
  obtain ⟨m_a, hm_a⟩ := Nat.exists_eq_succ_of_ne_zero hnne
  rw [hm_a] at hnle hn1 hn2
  have hcross_a : natCast m_a * meshWidth 0 b (2 ^ K) ≤ a := by
    obtain hz | hz := hn2
    · omega
    · rwa [show m_a + 1 - 1 = m_a from by omega] at hz
  have hratio_a : a ≤ natCast (m_a + 1) * meshWidth 0 b (2 ^ K) := le_of_lt hn1
  have hjK_a : m_a + 1 ≤ 2 ^ K := hnle
  obtain ⟨m_tail, hsplit⟩ := Nat.le.dest hjK_a
  obtain ⟨hcross_w_tail, hratio_w_tail⟩ :=
    tail_crossing a b (meshWidth 0 b (2 ^ K)) m_a m_tail K hcross_a hratio_a hsplit hqb
  -- HEAD: p=0, w=a, m=m_a, mp=0
  have hcont_p_head : ∀ z : Real, 0 ≤ z → z ≤ 0 + a → ContinuousAt f z := fun z hz1 hz2 =>
    hcont_a z hz1 (by rwa [zero_add] at hz2)
  have hp0_head : (0:Real) ≤ 0 := le_refl 0
  have hpwc_head : (0:Real) + a ≤ b := by rw [zero_add]; exact hab
  have hcross_p_head : natCast 0 * meshWidth 0 b (2 ^ K) ≤ (0:Real) := by
    rw [natCast_zero, zero_mul]; exact le_refl 0
  have hratio_p_head : (0:Real) ≤ natCast (0 + 1) * meshWidth 0 b (2 ^ K) := by
    rw [show (0 + 1 : Nat) = 1 from rfl, natCast_one_local2]
    rwa [show (1:Real) * meshWidth 0 b (2 ^ K) = meshWidth 0 b (2 ^ K)
        from by mach_mpoly [meshWidth 0 b (2 ^ K)]]
  have htransfer_head := upperSumCont_transfer_windowed f b hb0 hcont hnonneg 0 a hp0_head ha0
    hpwc_head hcont_p_head m_a 0 K hK (by omega) (meshWidth 0 b (2 ^ K)) rfl hqnn hcross_a hratio_a
    hcross_p_head hratio_p_head δ ε' hδpos hwidthK_δ (le_of_lt hε'pos) hδ
  rw [upperSumCont_congr_val f 0 (zero_add a) (le_add_of_nonneg_right ha0) ha0 hcont_p_head hcont_a
    (m_a + 1) (by omega)] at htransfer_head
  -- TAIL: p=a, w=b-a, m=m_tail, mp=m_a
  have hba : (0:Real) ≤ b - a := sub_nonneg_of_le hab
  have hab_eq : a + (b - a) = b := by mach_mpoly [a, b]
  have hpwc_tail : a + (b - a) ≤ b := by rw [hab_eq]; exact le_refl b
  have hcont_p_tail : ∀ z : Real, a ≤ z → z ≤ a + (b - a) → ContinuousAt f z := fun z hz1 hz2 =>
    hcont_w z hz1 (by rwa [hab_eq] at hz2)
  have htransfer_tail := upperSumCont_transfer_windowed f b hb0 hcont hnonneg a (b - a) ha0 hba
    hpwc_tail hcont_p_tail m_tail m_a K hK (by omega) (meshWidth 0 b (2 ^ K)) rfl hqnn
    hcross_w_tail hratio_w_tail hcross_a hratio_a δ ε' hδpos hwidthK_δ (le_of_lt hε'pos) hδ
  rw [upperSumCont_congr_val f a hab_eq (le_add_of_nonneg_right hba) hab hcont_p_tail hcont_w
    (m_tail + 1) (by omega)] at htransfer_tail
  -- I_a, I_w bound by the fine upper sums at these EXACT resolutions
  have hIa_le := le_upperSumCont_any f 0 a ha0 hcont_a I_a hIa_up hIa_gap (m_a + 1) (by omega)
  have hIw_le := le_upperSumCont_any f a b hab hcont_w I_w hIw_up hIw_gap (m_tail + 1) (by omega)
  have hIa_bound := le_trans hIa_le htransfer_head
  have hIw_bound := le_trans hIw_le htransfer_tail
  have hsum_bound := add_le_add_both hIa_bound hIw_bound
  -- bridge the head's `fun j => g(0+j)` window down to the plain `g` that partialSum_two_window_eq_add expects
  rw [show partialSum (fun j => maxSub f 0 b hb0 hcont (2 ^ K) hK (0 + j)) (m_a + 1)
      = partialSum (maxSub f 0 b hb0 hcont (2 ^ K) hK) (m_a + 1)
      from partialSum_zero_offset (maxSub f 0 b hb0 hcont (2 ^ K) hK) (m_a + 1)] at hsum_bound
  -- hsum_bound : I_a+I_w ≤ (W1q+ε'*a)+(W2q+ε'*(b-a)); regroup so eps_split_add's pattern is adjacent
  rw [regroup4
      (partialSum (maxSub f 0 b hb0 hcont (2 ^ K) hK) (m_a + 1) * meshWidth 0 b (2 ^ K)) (ε' * a)
      (partialSum (fun j => maxSub f 0 b hb0 hcont (2 ^ K) hK (m_a + j)) (m_tail + 1)
        * meshWidth 0 b (2 ^ K)) (ε' * (b - a))] at hsum_bound
  rw [eps_split_add ε' a b] at hsum_bound
  -- window-sum combination: W1*q + W2*q = FULL*q + maxSub_coarse(m_a)*q
  have hWeq := partialSum_two_window_eq_add (maxSub f 0 b hb0 hcont (2 ^ K) hK) m_a m_tail K hsplit
  have hWeq_scaled : partialSum (maxSub f 0 b hb0 hcont (2 ^ K) hK) (m_a + 1) * meshWidth 0 b (2 ^ K)
      + partialSum (fun j => maxSub f 0 b hb0 hcont (2 ^ K) hK (m_a + j)) (m_tail + 1)
        * meshWidth 0 b (2 ^ K)
      = partialSum (maxSub f 0 b hb0 hcont (2 ^ K) hK) (2 ^ K) * meshWidth 0 b (2 ^ K)
        + maxSub f 0 b hb0 hcont (2 ^ K) hK m_a * meshWidth 0 b (2 ^ K) := by
    rw [← distrib_mul (partialSum (maxSub f 0 b hb0 hcont (2 ^ K) hK) (m_a + 1))
        (partialSum (fun j => maxSub f 0 b hb0 hcont (2 ^ K) hK (m_a + j)) (m_tail + 1))
        (meshWidth 0 b (2 ^ K)), hWeq,
      distrib_mul (partialSum (maxSub f 0 b hb0 hcont (2 ^ K) hK) (2 ^ K))
        (maxSub f 0 b hb0 hcont (2 ^ K) hK m_a) (meshWidth 0 b (2 ^ K))]
  rw [hWeq_scaled] at hsum_bound
  -- hsum_bound : I_a+I_w ≤ (FULLq + g(m_a)*q) + ε'*b
  have hoverlap : maxSub f 0 b hb0 hcont (2 ^ K) hK m_a * meshWidth 0 b (2 ^ K) ≤ M * meshWidth 0 b (2 ^ K) :=
    mul_le_mul_of_nonneg_right (maxSub_le_global_bound f 0 b hb0 hcont M hMub (2 ^ K) hK m_a) hqnn
  have hMqbound : M * meshWidth 0 b (2 ^ K) ≤ ε / (1 + 1) / (1 + 1) :=
    M_mul_bound M (ε / (1 + 1) / (1 + 1)) (meshWidth 0 b (2 ^ K)) hMnn hε_q_pos hqnn
      (le_of_lt hwidthK_Mq)
  have hstep1 := le_trans hsum_bound
    (add_le_add_both
      (add_le_add_both (le_refl (partialSum (maxSub f 0 b hb0 hcont (2 ^ K) hK) (2 ^ K)
        * meshWidth 0 b (2 ^ K))) hoverlap)
      (le_refl (ε' * b)))
  have hstep2 := le_trans hstep1
    (add_le_add_both
      (add_le_add_both (le_refl (partialSum (maxSub f 0 b hb0 hcont (2 ^ K) hK) (2 ^ K)
        * meshWidth 0 b (2 ^ K))) hMqbound)
      (le_refl (ε' * b)))
  have hFULLq : partialSum (maxSub f 0 b hb0 hcont (2 ^ K) hK) (2 ^ K) * meshWidth 0 b (2 ^ K)
      = upperSumCont f 0 b hb0 hcont (2 ^ K) hK := rfl
  rw [hFULLq] at hstep2
  -- hstep2 : I_a+I_w ≤ (upperSumCont(K) + ε_q) + ε'*b
  have hgapK' : upperSumCont f 0 b hb0 hcont (2 ^ K) hK
      < lowerSumCont f 0 b hb0 hcont (2 ^ K) hK + ε / (1 + 1) := by
    have h3 := add_lt_add_left hgapK (lowerSumCont f 0 b hb0 hcont (2 ^ K) hK)
    rwa [show lowerSumCont f 0 b hb0 hcont (2 ^ K) hK
        + (upperSumCont f 0 b hb0 hcont (2 ^ K) hK - lowerSumCont f 0 b hb0 hcont (2 ^ K) hK)
        = upperSumCont f 0 b hb0 hcont (2 ^ K) hK
        from by mach_mpoly [lowerSumCont f 0 b hb0 hcont (2 ^ K) hK,
          upperSumCont f 0 b hb0 hcont (2 ^ K) hK]] at h3
  have hIbge : lowerSumCont f 0 b hb0 hcont (2 ^ K) hK ≤ I_b := hIb_low K
  have hstep3 : upperSumCont f 0 b hb0 hcont (2 ^ K) hK < I_b + ε / (1 + 1) :=
    lt_of_lt_of_le hgapK' (add_le_add_both hIbge (le_refl (ε / (1 + 1))))
  have hstep5 : upperSumCont f 0 b hb0 hcont (2 ^ K) hK + ε / (1 + 1) / (1 + 1) + ε' * b
      < upperSumCont f 0 b hb0 hcont (2 ^ K) hK + ε / (1 + 1) / (1 + 1) + ε / (1 + 1) / (1 + 1) :=
    add_lt_add_left hε'b (upperSumCont f 0 b hb0 hcont (2 ^ K) hK + ε / (1 + 1) / (1 + 1))
  have hstep6 := lt_of_le_of_lt hstep2 hstep5
  -- hstep6 : I_a+I_w < upperSumCont(K) + ε_q + ε_q
  have hstep7 : upperSumCont f 0 b hb0 hcont (2 ^ K) hK + ε / (1 + 1) / (1 + 1)
      < (I_b + ε / (1 + 1)) + ε / (1 + 1) / (1 + 1) :=
    add_lt_add_right_weak hstep3 (ε / (1 + 1) / (1 + 1))
  have hstep8 : upperSumCont f 0 b hb0 hcont (2 ^ K) hK + ε / (1 + 1) / (1 + 1) + ε / (1 + 1) / (1 + 1)
      < (I_b + ε / (1 + 1)) + ε / (1 + 1) / (1 + 1) + ε / (1 + 1) / (1 + 1) :=
    add_lt_add_right_weak hstep7 (ε / (1 + 1) / (1 + 1))
  have hstep9 := lt_trans_ax hstep6 hstep8
  rwa [final_combine I_b ε] at hstep9

end Real
end MachLib
