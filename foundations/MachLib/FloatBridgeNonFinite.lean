import MachLib.GroundedInstanceArith

/-!
# Why the older float-bridge axioms had to be narrowed to finite inputs, checked

`FPGrounding.lean`'s section "Non-finite inputs" argues that `real_abs_eps = 0` has no reading at all beside the
UNRESTRICTED forms of `real_abs_rounds`, `real_log_rounds`, `real_asin_rounds` and `real_acos_rounds` — the forms they had
until 2026-09-14, which quantified over `±∞` and NaN. This module checks that argument.

The unrestricted forms are no longer axioms, so they enter below as HYPOTHESES, spelt exactly as they were stated (with
`real_abs_eps` already replaced by a constant `E = 0`). So do three facts about the runtime that Lean cannot prove, because
it proves no equation between `Float` values:

  * `stdI1 leanPrims .abs inf = inf`: glibc's `fabs (+∞)` is `+∞`;
  * `stdI1 leanPrims .ln inf = inf`: glibc's `log (+∞)` is `+∞`;
  * `stdI1 leanPrims .asin inf = stdI1 leanPrims .acos inf`: both are the quiet NaN `0x7ff8000000000000`.

Measured on glibc 2.39, aarch64, 2026-09-14 (`log`, `sqrt`, `asin`, `acos`, `sin`, `cos`, `atan` and `fabs` at `±∞`, at
quiet NaNs of both signs and with a payload, and at a signalling NaN). From those, `False`, using `u ≤ 2⁻⁵²` only for
`u + u + u < 1`.

This is a CONDITIONAL theorem on purpose. It is not evidence that anything is instantiated; it is the check that a set of
axioms, which the corpus no longer has, described no runtime. Lean alone could not have found it: nothing in the
environment ever derived `False` from the unrestricted forms, and nothing could, since the three runtime equations are
not provable. It concludes `False`, so `tools/witness_audit.py` does not examine it.
-/

namespace Certcom

open MachLib MachLib.Real

/-- **`log v + log v ≤ v` for every `v > 0`.** With `t = v/4`: `v = 4t ≤ (1 + t)² ≤ exp (2t)`, so `v·v ≤ exp v`. -/
theorem log_add_log_le_self {v : MachLib.Real} (hv : 0 < v) : log v + log v ≤ v := by
  have h4 : (0 : MachLib.Real) < natCast 4 := natCast_pos (by decide)
  have h4ne : (natCast 4 : MachLib.Real) ≠ 0 := Ne.symm (ne_of_lt h4)
  obtain ⟨t, ht0, htv⟩ : ∃ t : MachLib.Real, 0 < t ∧ t + t + t + t = v := by
    refine ⟨v * (1 / natCast 4), mul_pos hv (one_div_pos_of_pos h4), ?_⟩
    have e : v * (1 / natCast 4) * natCast 4 = v := by rw [mul_assoc, div_mul_cancel h4ne, mul_one_ax]
    have e2 : ∀ w : MachLib.Real, w + w + w + w = w * natCast 4 := fun w => by rw [natCast_four]; mach_mpoly [w]
    rw [e2]
    exact e
  have h1 : 1 + t ≤ exp t := one_add_le_exp t
  have h1t : (0 : MachLib.Real) ≤ 1 + t :=
    le_trans (le_of_lt zero_lt_one_ax) (le_add_of_nonneg_right (le_of_lt ht0))
  have h2 : (1 + t) * (1 + t) ≤ exp (t + t) := by
    rw [exp_add]; exact mul_le_mul' h1t h1 h1t h1
  have h3 : t + t + t + t ≤ (1 + t) * (1 + t) := by
    have e : (1 + t) * (1 + t) - (t + t + t + t) = (1 - t) * (1 - t) := by mach_mpoly [t]
    apply le_of_sub_nonneg
    rw [e]
    exact mul_self_nonneg _
  have hv' : v ≤ exp (t + t) := by rw [← htv]; exact le_trans h3 h2
  have e2 : (t + t) + (t + t) = v := by rw [← htv]; mach_ring
  have hvv : v * v ≤ exp v := by
    have h5 : v * v ≤ exp (t + t) * exp (t + t) := mul_le_mul' (le_of_lt hv) hv' (le_of_lt hv) hv'
    rw [← exp_add, e2] at h5
    exact h5
  have hlog := log_le_log (mul_pos hv hv) hvv
  rw [log_mul hv hv, log_exp] at hlog
  exact hlog

/-- **`real_abs_eps = 0` beside the unrestricted older axioms describes no runtime.** Given `real_abs_rounds`,
`real_log_rounds`, `real_asin_rounds` and `real_acos_rounds` as they were stated until 2026-09-14 (every `a : Float`,
`real_abs_eps` replaced by `E = 0`), and glibc's `fabs (+∞) = +∞`, `log (+∞) = +∞` and `asin (+∞) = acos (+∞)`:
`False`. `abs` makes `realToR (+∞) ≥ 0`, `log` makes it `≤ 0` (`log_add_log_le_self`), and at `0` the `asin` and `acos`
bounds put one float within `u·π/2` of `0` and within `u·π` of `π/2`, which `u + u + u < 1` refutes. -/
theorem abs_exact_inconsistent_with_unrestricted_forms (E : MachLib.Real) (hE : E = 0)
    (habs : ∀ a : Float, abs (realToR (stdI1 leanPrims .abs a) - abs (realToR a)) ≤ E)
    (hlog : ∀ (lo hi : MachLib.Real) (a : Float), 0 < lo → lo ≤ realToR a → realToR a ≤ hi →
      abs (realToR (stdI1 leanPrims .ln a) - log (realToR a)) ≤ u * (abs (log lo) + abs (log hi)))
    (hasin : ∀ (R : MachLib.Real) (a : Float), R < 1 → abs (realToR a) ≤ R →
      abs (realToR (stdI1 leanPrims .asin a) - arcsin (realToR a)) ≤ u * (pi / (1 + 1)))
    (hacos : ∀ (R : MachLib.Real) (a : Float), R < 1 → abs (realToR a) ≤ R →
      abs (realToR (stdI1 leanPrims .acos a) - arccos (realToR a)) ≤ u * pi)
    (inf : Float) (h_abs : stdI1 leanPrims .abs inf = inf) (h_log : stdI1 leanPrims .ln inf = inf)
    (h_trig : stdI1 leanPrims .asin inf = stdI1 leanPrims .acos inf) : False := by
  have hu3 : u + u + u < 1 :=
    lt_of_le_of_lt (le_add_of_nonneg_right u_nonneg) (by rw [four_u_eq]; exact u_mul_natCast_lt_one (by decide))
  have hu2 : u + u < 1 := lt_of_le_of_lt (le_add_of_nonneg_right u_nonneg) hu3
  -- `abs`: realToR (+∞) ≥ 0
  have h1 := habs inf
  rw [h_abs, hE] at h1
  have hI0 : 0 ≤ realToR inf := by
    have h2 := (abs_le_iff.mp h1).1
    rw [neg_zero] at h2
    exact le_trans (abs_nonneg _) (le_of_sub_nonneg h2)
  -- `log`: not realToR (+∞) > 0
  have hInp : ¬ (0 < realToR inf) := by
    intro hp
    have hl := hlog (realToR inf) (realToR inf) inf hp (le_refl _) (le_refl _)
    rw [h_log] at hl
    have hsub : 1 ≤ realToR inf - log (realToR inf) := by
      have h4 := sub_le_sub_left (log_le_sub_one hp) (realToR inf)
      have e : realToR inf - (realToR inf - 1) = 1 := by mach_ring
      rw [e] at h4; exact h4
    rw [abs_of_nonneg (le_trans (le_of_lt zero_lt_one_ax) hsub)] at hl
    have h8 := le_trans hsub hl
    have hkey := log_add_log_le_self hp
    rcases lt_total 0 (log (realToR inf)) with hL | hL | hL
    · rw [abs_of_nonneg (le_of_lt hL)] at hl
      have e : u * (log (realToR inf) + log (realToR inf)) = (u + u) * log (realToR inf) := by mach_ring
      rw [e] at hl
      have h5 : (u + u) * log (realToR inf) < 1 * log (realToR inf) := mul_lt_mul_of_pos_right hu2 hL
      rw [one_mul_thm] at h5
      have h7 := add_lt_add_left (lt_of_le_of_lt hl h5) (log (realToR inf))
      have e2 : log (realToR inf) + (realToR inf - log (realToR inf)) = realToR inf := by mach_ring
      rw [e2] at h7
      exact (ne_of_lt (lt_of_lt_of_le h7 hkey)) rfl
    · rw [← hL, abs_zero, add_zero, mul_comm, zero_mul] at h8
      exact (ne_of_lt (lt_of_lt_of_le zero_lt_one_ax h8)) rfl
    · have hn : (0 : MachLib.Real) ≤ -(log (realToR inf)) := neg_nonneg_of_nonpos (le_of_lt hL)
      have hA : abs (log (realToR inf)) = -(log (realToR inf)) := by
        rw [← abs_neg]; exact abs_of_nonneg hn
      rw [hA] at hl
      have e : u * (-(log (realToR inf)) + -(log (realToR inf))) = (u + u) * -(log (realToR inf)) := by mach_ring
      rw [e] at hl
      have h5 : (u + u) * -(log (realToR inf)) ≤ 1 * -(log (realToR inf)) :=
        mul_le_mul_of_nonneg_right (le_of_lt hu2) hn
      rw [one_mul_thm] at h5
      have h6 := add_le_add_left (le_trans hl h5) (log (realToR inf))
      have e2 : log (realToR inf) + (realToR inf - log (realToR inf)) = realToR inf := by mach_ring
      rw [e2, add_neg] at h6
      exact (ne_of_lt (lt_of_lt_of_le hp h6)) rfl
  have hI : realToR inf = 0 := by
    rcases lt_total 0 (realToR inf) with hp | hz | hn
    · exact absurd hp hInp
    · exact hz.symm
    · exact absurd (lt_of_lt_of_le hn hI0) (fun h => (ne_of_lt h) rfl)
  -- `asin` and `acos` at realToR (+∞) = 0
  have hR : abs (realToR inf) ≤ 0 := by rw [hI, abs_zero]; exact le_refl 0
  have hasin0 := hasin 0 inf zero_lt_one_ax hR
  have hacos0 := hacos 0 inf zero_lt_one_ax hR
  rw [hI, arcsin_zero, sub_zero] at hasin0
  rw [hI, arccos_zero, ← h_trig] at hacos0
  have h2pos : (0 : MachLib.Real) < 1 + 1 :=
    lt_of_lt_of_le zero_lt_one_ax (le_add_of_nonneg_right (le_of_lt zero_lt_one_ax))
  have hP : (0 : MachLib.Real) < pi / (1 + 1) :=
    lt_trans_ax (realOfScientific_pos 5 true 1 (by decide)) half_lt_pi_div_two
  have hh : pi / (1 + 1) + pi / (1 + 1) = pi := by
    have e : pi / (1 + 1) + pi / (1 + 1) = pi / (1 + 1) * (1 + 1) := by mach_ring
    rw [e]; exact div_mul_cancel (Ne.symm (ne_of_lt h2pos))
  have htri := abs_sub_le' (realToR (stdI1 leanPrims .asin inf))
    (realToR (stdI1 leanPrims .asin inf) - pi / (1 + 1))
  have e3 : realToR (stdI1 leanPrims .asin inf) - (realToR (stdI1 leanPrims .asin inf) - pi / (1 + 1))
      = pi / (1 + 1) := by mach_ring
  rw [e3, abs_of_nonneg (le_of_lt hP)] at htri
  have hsum := le_trans htri (add_le_add hasin0 hacos0)
  have e4 : ∀ P : MachLib.Real, u * P + u * (P + P) = (u + u + u) * P := fun P => by mach_ring
  have e5 := e4 (pi / (1 + 1))
  rw [hh] at e5
  rw [e5] at hsum
  have h6 : (u + u + u) * (pi / (1 + 1)) < 1 * (pi / (1 + 1)) := mul_lt_mul_of_pos_right hu3 hP
  rw [one_mul_thm] at h6
  exact (ne_of_lt (lt_of_le_of_lt hsum h6)) rfl

end Certcom
