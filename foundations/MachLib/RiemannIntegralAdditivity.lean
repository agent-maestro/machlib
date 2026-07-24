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

end Real
end MachLib
