import MachLib.AsinHardwareForwardError
import MachLib.AcosTaylorRemainder

/-!
# `eml_acos.v` hardware forward-error certificate — the fixed-point ↔ real leg

Combines `Racos0_bound` (`MachLib.AcosTaylorRemainder`) with `FixedPoint`'s
`qmul_err_loose`/`quantize_err` into a certificate against
`hardware/modules/transcendental/eml_acos.v`.

## What `eml_acos.v` actually computes (ground truth, read off the RTL)

The IDENTICAL `x2,x3,x4,x5,x7` pipeline and THREE constant multiplies as `eml_asin.v` (all reused
directly from `MachLib.AsinHardwareForwardError`), but the accumulate is `acos(x) = π/2 − asin(x)`:
`acc = HALF_PI − x1 − t3 − t5 − t7`, where `HALF_PI := (ONE·314159)/200000` is computed ONCE at
elaboration time — a RATIONAL approximation of `π/2`, not the exact value. This is a genuinely NEW
error source `asin`'s own certificate never needed: `|HALF_PI − π/2|` itself, bounded via two new
tight numeric axioms on `π` (`pi_lower_bound`/`pi_upper_bound`, `Trig.lean`).
-/

namespace MachLib.Real

/-- `eml_acos.v`'s `HALF_PI` constant, exactly as computed at RTL elaboration time. -/
noncomputable def halfPi_rtl : Real := natCast 314159 * (1 / natCast 200000)

theorem halfPi_rtl_eq : halfPi_rtl = natCast 3141590 * (1 / natCast 2000000) := by
  have h200000ne : natCast 200000 ≠ (0 : Real) := natCast_ne_zero (by decide)
  have h2000000ne : natCast 2000000 ≠ (0 : Real) := natCast_ne_zero (by decide)
  have hnd1 : natCast 10 * natCast 200000 = natCast 2000000 := by rw [← natCast_mul]
  have hfrac1 : natCast 10 * (1 / natCast 2000000) = 1 / natCast 200000 :=
    frac_reduce (natCast 10) (natCast 200000) (natCast 2000000) h200000ne h2000000ne hnd1
  unfold halfPi_rtl
  rw [show natCast 314159 * (1 / natCast 200000)
      = natCast 314159 * (natCast 10 * (1 / natCast 2000000)) from by rw [hfrac1],
    show natCast 314159 * (natCast 10 * (1 / natCast 2000000))
      = (natCast 314159 * natCast 10) * (1 / natCast 2000000) from by mach_ring,
    show natCast 314159 * natCast 10 = natCast 3141590 from by rw [← natCast_mul]]

/-- `1/natCast1000000 · 1/(1+1) = 1/natCast2000000` — the scale-matching fact both `π` bounds
need to line up against `halfPi_rtl`'s own `/2000000` representation. -/
theorem half_scale_match : (1 / natCast 1000000 : Real) * (1 / (1 + 1)) = 1 / natCast 2000000 := by
  have h1000000ne : natCast 1000000 ≠ (0 : Real) := natCast_ne_zero (by decide)
  have h2000000ne : natCast 2000000 ≠ (0 : Real) := natCast_ne_zero (by decide)
  have hnd2 : (1 + 1 : Real) * natCast 1000000 = natCast 2000000 := by rw [two_mul_natCast]
  have hfrac2 : (1 + 1 : Real) * (1 / natCast 2000000) = 1 / natCast 1000000 :=
    frac_reduce (1 + 1) (natCast 1000000) (natCast 2000000) h1000000ne h2000000ne hnd2
  rw [show (1 / natCast 1000000 : Real) = (1 + 1) * (1 / natCast 2000000) from hfrac2.symm]
  rw [show ((1 + 1 : Real) * (1 / natCast 2000000)) * (1 / (1 + 1))
      = (1 / natCast 2000000) * ((1 + 1) * (1 / (1 + 1))) from by mach_ring,
    mul_inv (1 + 1) (ne_of_gt my_two_pos)]
  mach_ring

theorem pi_half_lo : natCast 3141592 * (1 / natCast 2000000) < pi / (1 + 1) := by
  have hmul := mul_lt_mul_of_pos_right pi_lower_bound (one_div_pos_of_pos my_two_pos)
  rw [show natCast 3141592 * (1 / natCast 1000000) * (1 / (1 + 1))
      = natCast 3141592 * ((1 / natCast 1000000) * (1 / (1 + 1))) from by mach_ring,
    half_scale_match, ← div_def pi (1 + 1) (ne_of_gt my_two_pos)] at hmul
  exact hmul

theorem pi_half_hi : pi / (1 + 1) < natCast 3141593 * (1 / natCast 2000000) := by
  have hmul := mul_lt_mul_of_pos_right pi_upper_bound (one_div_pos_of_pos my_two_pos)
  rw [show natCast 3141593 * (1 / natCast 1000000) * (1 / (1 + 1))
      = natCast 3141593 * ((1 / natCast 1000000) * (1 / (1 + 1))) from by mach_ring,
    half_scale_match, ← div_def pi (1 + 1) (ne_of_gt my_two_pos)] at hmul
  exact hmul

/-- **`|HALF_PI_rtl − π/2| ≤ 3/2000000`.** `HALF_PI_rtl` is provably `< π/2` throughout (never
above), so this is really a one-sided bound, stated via `abs` for uniform composition with the
rest of the certificate. -/
theorem halfPi_rtl_error : abs (halfPi_rtl - pi / (1 + 1)) ≤ natCast 3 * (1 / natCast 2000000) := by
  have hdiff_pos : (0 : Real) < pi / (1 + 1) - halfPi_rtl := by
    rw [halfPi_rtl_eq]
    have h := pi_half_lo
    have hstep : natCast 3141590 * (1 / natCast 2000000) < pi / (1 + 1) := by
      refine lt_of_le_of_lt ?_ h
      have h2 : natCast 3141590 * (1 / natCast 2000000) ≤ natCast 3141592 * (1 / natCast 2000000) :=
        mul_le_mul_of_nonneg_right (by
          have := natCast_le_of_nat_le (show 3141590 ≤ 3141592 by decide)
          exact this) (le_of_lt (one_div_pos_of_pos (natCast_pos (n := 2000000) (by decide))))
      exact h2
    exact sub_pos_of_lt hstep
  have hdiff_bound : pi / (1 + 1) - halfPi_rtl ≤ natCast 3 * (1 / natCast 2000000) := by
    rw [halfPi_rtl_eq]
    have h := pi_half_hi
    have hsum : natCast 3141590 * (1 / natCast 2000000) + natCast 3 * (1 / natCast 2000000)
        = natCast 3141593 * (1 / natCast 2000000) := by
      rw [show natCast 3141590 * (1 / natCast 2000000) + natCast 3 * (1 / natCast 2000000)
          = (natCast 3141590 + natCast 3) * (1 / natCast 2000000) from by mach_ring,
        show natCast 3141590 + natCast 3 = natCast 3141593 from by rw [← natCast_add]]
    have hle := le_of_lt h
    rw [← hsum] at hle
    have hstep := sub_le_sub_right hle (natCast 3141590 * (1 / natCast 2000000))
    rwa [show natCast 3141590 * (1 / natCast 2000000) + natCast 3 * (1 / natCast 2000000)
        - natCast 3141590 * (1 / natCast 2000000) = natCast 3 * (1 / natCast 2000000)
        from by mach_ring] at hstep
  rw [show halfPi_rtl - pi / (1 + 1) = -(pi / (1 + 1) - halfPi_rtl) from by mach_ring, abs_neg,
    abs_of_nonneg (le_of_lt hdiff_pos)]
  exact hdiff_bound

/-- **The RTL pipeline**, definitionally: `eml_acos.v`'s `HALF_PI` constant minus `eml_asin.v`'s
own eight `qmul`s (`x2,x3,x4,x5,x7` and three constant-multiplies, all reused directly). -/
noncomputable def eml_acos_rtl (x D : Real) : Real :=
  halfPi_rtl - x - t3f_asin x D - t5f_asin x D - t7f_asin x D

/-! ## Full composition against `Racos0` -/

theorem eml_acos_fx_vs_acc_exact (x D : Real) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_acos_rtl x D -
      (halfPi_rtl - x - ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
        - (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40))
        - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336))))
      ≤ (1+1+1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D)
        + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D) := by
  unfold eml_acos_rtl
  have hsplit : (halfPi_rtl - x - t3f_asin x D - t5f_asin x D - t7f_asin x D)
      - (halfPi_rtl - x - ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
        - (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40))
        - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336)))
      = -((t3f_asin x D - ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1)))
        + (t5f_asin x D - (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40)))
        + (t7f_asin x D
            - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336)))) := by
    mach_mpoly [x, t3f_asin x D, t5f_asin x D, t7f_asin x D, halfPi_rtl,
      (((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1)) : Real),
      ((((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40)) : Real),
      ((((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336)) : Real)]
  rw [hsplit, abs_neg]
  refine le_trans (abs_add _ _) (add_le_add_both ?_ (Et7_bound_asin x D hx0 hx1 hD hD1))
  exact le_trans (abs_add _ _)
    (add_le_add_both (Et3_bound_asin x D hx0 hx1 hD hD1) (Et5_bound_asin x D hx0 hx1 hD hD1))

/-- **The full `eml_acos.v` hardware forward-error certificate.** The fixed-point RTL pipeline's
output is within `50/D` (fixed-point truncation, 8 `qmul`s, identical to `asin`'s own)
`+ 3/2000000` (`HALF_PI`'s own rational-approximation error, a NEW source `asin` never needed)
`+ NTop·h(R)^15·x^8` (Taylor truncation, `Racos0_bound`) of the true `acos x`, for `x ∈ [0, R]`
(`R = 1/2`) and any grid `D ≥ 1` — matches `eml_acos.v`'s own documented valid range exactly.
`sorryAx`-free. -/
theorem eml_acos_full_fwd_error (x D : Real) (hx0 : 0 ≤ x) (hxR : x ≤ asinR)
    (hD : 0 < D) (hD1 : 1 ≤ D) :
    abs (eml_acos_rtl x D - arccos x)
      ≤ ((1+1+1+1+1+1) * (1/D) + (1+1+1+1+1+1+1+1+1+1+1+1) * (1/D)
          + (1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) * (1/D))
        + (natCast 3 * (1 / natCast 2000000)
          + NTop * hAsinPow 15 asinR * x * x * x * x * x * x * x * x) := by
  have hx1 : x ≤ 1 := le_trans hxR (le_of_lt asinR_lt_one)
  have hstep1 := eml_acos_fx_vs_acc_exact x D hx0 hx1 hD hD1
  have hstep2 : abs
      ((halfPi_rtl - x - ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
        - (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40))
        - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336))) - arccos x)
      ≤ natCast 3 * (1 / natCast 2000000)
        + NTop * hAsinPow 15 asinR * x * x * x * x * x * x * x * x := by
    have hRacos0 := Racos0_bound x hx0 hxR
    have heq : (halfPi_rtl - x - ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
        - (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40))
        - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336))) - arccos x
        = (halfPi_rtl - pi / (1 + 1)) - Racos0 x := by
      unfold Racos0
      rw [natCast_six]
      mach_mpoly [x, arccos x, pi, halfPi_rtl, natCast 3, natCast 15,
        (1 / (1 + 1 + 1 + 1 + 1 + 1) : Real), (1 / natCast 40 : Real), (1 / natCast 336 : Real)]
    rw [heq]
    exact le_trans (abs_sub_le' _ _) (add_le_add_both halfPi_rtl_error hRacos0)
  have hsplit : eml_acos_rtl x D - arccos x
      = (eml_acos_rtl x D -
          (halfPi_rtl - x - ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
            - (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40))
            - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336))))
        + ((halfPi_rtl - x - ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
            - (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40))
            - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336))) - arccos x) := by
    mach_mpoly [eml_acos_rtl x D, arccos x,
      (halfPi_rtl - x - ((x * x) * x) * (1 / (1 + 1 + 1 + 1 + 1 + 1))
        - (((x * x) * (x * x)) * x) * (natCast 3 * (1 / natCast 40))
        - (((x * x) * (x * x)) * ((x * x) * x)) * (natCast 15 * (1 / natCast 336)) : Real)]
  rw [hsplit]
  exact le_trans (abs_add _ _) (add_le_add_both hstep1 hstep2)

end MachLib.Real
