import MachLib.GroundedEMLInstances

/-!
# `pid_log_cosh_grounded`, instantiated on `u ≤ 2⁻⁵²`

`pid_log_cosh_grounded` (`FPGrounding.lean`) grounds the log-cosh loss `log(cosh(1.5·e + 0.4·i + 0.05·d))` through two
LOCAL primitives. Beyond what `GroundedPIDInstances.lean` discharges, it needs a range `[lo, hi]` with `0 < lo` for the
runtime `cosh`'s value read back. `real_cosh_rounds` puts that value within `4u·cosh R` of the exact `cosh x`, which is at
least `1`; on `u + u ≤ 1` the allowance can be `2·cosh R`, so no positive `lo` followed. `u_le_inv_two_pow_52`
(owner-approved, 2026-09-14) makes `4u·cosh R` below `1` for `0 ≤ R ≤ 20`, because `cosh R ≤ exp R ≤ 4²⁰ = 2⁴⁰`
(`four_u_cosh_lt_one`).

## The domain, in words

`PIDInputDomain env B δ` (`GroundedPIDInstances.lean`: the channels `e`, `i`, `d` are finite floats at most `B` in
magnitude, each `0` or at least `δ` in magnitude, `DBL_MIN ≤ 0.025·δ` and `60·B ≤ DBL_MAX`), with a range `R` such that
`60·B ≤ R ≤ 20`. The instance takes `lo = 1 − 4u·cosh R` and `hi = cosh R + 4u·cosh R`. The specimen is
`pidSpecimenEnv` (every input `floatOfR 0.004`) at `R = 0.5`.

Its conclusion is `pid_log_cosh_grounded`'s: SOME absolute bound holds (`∃ E`). That existential is the certificate's own
(`pipeline_nested_local_finite`), and this instance does not sharpen it.
-/

namespace Certcom

open MachLib MachLib.Real

/-- `cosh R ≤ exp R` for `0 ≤ R`: `exp (−R) ≤ exp R`. -/
theorem cosh_le_exp_of_nonneg {R : MachLib.Real} (hR : 0 ≤ R) : cosh R ≤ exp R := by
  have h2 : (0 : MachLib.Real) < 1 + 1 := two_pos_real
  have hne : (1 + 1 : MachLib.Real) ≠ 0 := Ne.symm (ne_of_lt h2)
  have h1 : exp (-R) ≤ exp R := exp_monotone (le_trans (neg_nonpos_of_nonneg hR) hR)
  apply le_of_mul_le_mul_right_pos _ h2
  rw [cosh_eq, div_mul_cancel hne]
  have e : exp R * (1 + 1) = exp R + exp R := by mach_ring
  rw [e]
  exact add_le_add (le_refl _) h1

/-- **`4u · cosh R < 1` for `0 ≤ R ≤ 20`**: `cosh R ≤ exp R ≤ 4²⁰`, and `u · 4²¹ < 1` (`u_mul_natCast_lt_one`). -/
theorem four_u_cosh_lt_one {R : MachLib.Real} (hR0 : 0 ≤ R) (hR : R ≤ natCast 20) :
    (u + u + u + u) * cosh R < 1 := by
  have hc : cosh R ≤ natCast (4 ^ 20) := le_trans (cosh_le_exp_of_nonneg hR0) (exp_le_natCast_pow hR)
  have h4u : (0 : MachLib.Real) ≤ u + u + u + u :=
    add_nonneg (add_nonneg (add_nonneg u_nonneg u_nonneg) u_nonneg) u_nonneg
  have h1 : (u + u + u + u) * cosh R ≤ (u + u + u + u) * natCast (4 ^ 20) := mul_le_mul_of_nonneg_left hc h4u
  have e1 : (u + u + u + u) * natCast (4 ^ 20) = u * natCast (4 * 4 ^ 20) := by
    rw [four_u_eq, natCast_mul]; mach_ring
  rw [e1] at h1
  exact lt_of_le_of_lt h1 (u_mul_natCast_lt_one (by decide))

/-- A value within `K` of `y` lies in `[y − K, y + K]`. -/
theorem mem_Icc_of_abs_sub_le {c y K : MachLib.Real} (h : abs (c - y) ≤ K) : y - K ≤ c ∧ c ≤ y + K := by
  obtain ⟨h1, h2⟩ := abs_le_iff.mp h
  refine ⟨?_, ?_⟩
  · have h3 := add_le_add_left h1 y
    have e1 : y + -K = y - K := by mach_ring
    have e2 : y + (c - y) = c := by mach_ring
    rw [e1, e2] at h3; exact h3
  · have h3 := add_le_add_left h2 y
    have e2 : y + (c - y) = c := by mach_ring
    rw [e2] at h3; exact h3

/-- **`pid_log_cosh_grounded`, instantiated** on `PIDInputDomain`, with `60·B ≤ R ≤ 20`, at `lo = 1 − 4u·cosh R` and
`hi = cosh R + 4u·cosh R`. The runtime `cosh` of the PID law is finite by `real_cosh_finite`; its read-back value is in
`[lo, hi]` by `real_cosh_rounds`, `cosh ≥ 1` and `cosh_le_of_abs_le`; and `0 < lo` is `four_u_cosh_lt_one`, which is where
`u_le_inv_two_pow_52` is used. -/
theorem pid_log_cosh_grounded_instantiated (env : Env) {B δ R : MachLib.Real} (h : PIDInputDomain env B δ)
    (hBR : 60.0 * B ≤ R) (hR : R ≤ natCast 20) :
    ∃ E, AbsEnc E
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env
        (emitC (.tr1 .ln (.tr1 .cosh pidRawEML)))).toF)
      (log (cosh (exactR realToR env pidRawEML))) := by
  obtain ⟨hs, hfl, hex⟩ := pidRawEML_domain_facts h (stdI1 leanPrims) (stdI2 leanPrims)
  have hR0 : 0 ≤ R := range_nonneg h hBR
  have hflR := le_trans hfl hBR
  have hexR := le_trans hex hBR
  obtain ⟨l1, u1⟩ := abs_le_iff.mp hflR
  obtain ⟨l2, u2⟩ := abs_le_iff.mp hexR
  have h710 : R ≤ natCast 710 := le_trans hR (natCast_le_natCast_of_nat_le (by decide))
  have hcosh : (stdI1 leanPrims .cosh (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF).isFinite
      = true :=
    real_cosh_finite _ (FloatSafe.add_isFinite hs) (le_trans hflR h710)
  have hK := four_u_cosh_lt_one hR0 hR
  have hKnn : (0 : MachLib.Real) ≤ (u + u + u + u) * cosh R :=
    mul_nonneg (add_nonneg (add_nonneg (add_nonneg u_nonneg u_nonneg) u_nonneg) u_nonneg)
      (le_of_lt (cosh_pos R))
  obtain ⟨hlo_c, hhi_c⟩ := mem_Icc_of_abs_sub_le (real_cosh_rounds R _ hcosh hflR)
  have hflx_lo2 : 1 - (u + u + u + u) * cosh R
      ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (.tr1 .cosh pidRawEML)).toF := by
    show 1 - (u + u + u + u) * cosh R
      ≤ realToR (stdI1 leanPrims .cosh (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
    exact le_trans (sub_le_sub_right (cosh_ge_one _) _) hlo_c
  have hflx_hi2 : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (.tr1 .cosh pidRawEML)).toF
      ≤ cosh R + (u + u + u + u) * cosh R := by
    show realToR (stdI1 leanPrims .cosh (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env pidRawEML).toF)
      ≤ cosh R + (u + u + u + u) * cosh R
    exact le_trans hhi_c (add_le_add (cosh_le_of_abs_le hflR) (le_refl _))
  have hxe_lo2 : 1 - (u + u + u + u) * cosh R ≤ exactRn realToR realOfLogCosh env (.tr1 .cosh pidRawEML) := by
    show 1 - (u + u + u + u) * cosh R ≤ cosh (exactRn realToR realOfLogCosh env pidRawEML)
    rw [exactRn_eq_exactR_of_arith realOfLogCosh env isArith_pidRawEML]
    exact le_trans (sub_le_self hKnn) (cosh_ge_one _)
  have hxe_hi2 : exactRn realToR realOfLogCosh env (.tr1 .cosh pidRawEML) ≤ cosh R + (u + u + u + u) * cosh R := by
    show cosh (exactRn realToR realOfLogCosh env pidRawEML) ≤ cosh R + (u + u + u + u) * cosh R
    rw [exactRn_eq_exactR_of_arith realOfLogCosh env isArith_pidRawEML]
    exact le_trans (cosh_le_of_abs_le hexR) (le_add_of_nonneg_right hKnn)
  exact pid_log_cosh_grounded env R (1 - (u + u + u + u) * cosh R) (cosh R + (u + u + u + u) * cosh R) hR0
    (sub_pos_of_lt hK) hs hcosh l1 u1 l2 u2 hflx_lo2 hflx_hi2 hxe_lo2 hxe_hi2

/-- **Specimen for `pid_log_cosh_grounded_instantiated`**, at `pidSpecimenEnv` (every input `floatOfR 0.004`) and
`R = 0.5`. -/
theorem pid_log_cosh_grounded_specimen :
    ∃ E, AbsEnc E
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) pidSpecimenEnv
        (emitC (.tr1 .ln (.tr1 .cosh pidRawEML)))).toF)
      (log (cosh (exactR realToR pidSpecimenEnv pidRawEML))) :=
  pid_log_cosh_grounded_instantiated pidSpecimenEnv pidSpecimen_domain.toPIDInputDomain pidSpecimen_range
    (point_five_le_natCast (by decide))

end Certcom
