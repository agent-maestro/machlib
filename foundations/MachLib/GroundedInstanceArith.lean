import MachLib.FloatSafeInstances

/-!
# Arithmetic for instantiating the grounded certificates on the literal and libm-finiteness axioms

On 2026-09-14 the owner approved three further kinds of trusted axiom, measured or witnessed before they were added:

  * `float_lit_1_5`, `float_lit_0_4`, `float_lit_0_05` (`EMLCertcomGrounded.lean`): the PID gains' `Float` literals are
    `floatOfR` of their decimals, so `real_round_bounds` and `real_round_finite` give their values and finiteness;
  * `real_exp_finite`, `real_sinh_finite`, `real_cosh_finite`, `real_log_finite` (`FPGrounding.lean`): the runtime
    primitive of a finite float in a stated range is finite;
  * `u_le_half` (`FPModel.lean`): `u + u ≤ 1`.

This module holds the real arithmetic the instances in `GroundedPIDInstances.lean` and `GroundedEMLInstances.lean` share:
halves from `u + u ≤ 1`, decimals against `DBL_MIN` and `DBL_MAX`, the three gains' bounds, and an upper bound on `exp`.

## Staying inside the trusted footprint

Two convenient routes leave it, and this module avoids both. `u_le_one` is an axiom that is neither witnessed nor in the
trusted footprint (`u_lt_one` is both), so `u ≤ 1` is taken as `le_of_lt u_lt_one`. And `mach_decimal` closes order goals
with the axioms `realOfScientific_le_of_nat` and `realOfScientific_lt_of_nat`, which are in the same position; the
`grounded_decimal` tactic below normalises the same way and closes order goals with `decimal_le_of_nat'` and
`decimal_lt_of_nat'`, proved here from the trusted `realOfScientific_clears`.

## An upper bound on `exp`, from axioms already trusted

No trusted axiom bounds `exp` from above (`exp_one_lt_three` exists, but it is neither witnessed nor in the trusted
footprint). The bound here needs none: `1 − x ≤ exp (−x)` is `one_add_le_exp` at `−x`, and `exp x · exp (−x) = 1`, so
`exp x · (1 − x) ≤ 1` for every `x`. At `x = 1/2` that is `exp (1/2) ≤ 2`, so `exp 1 ≤ 4` and `exp n ≤ 4ⁿ`. It is crude
(`e < 2.72`), and it is enough to keep a certificate's float results below `DBL_MAX` on the domains used here.
-/

namespace Certcom

open MachLib MachLib.Real

/-! ## 0. Decimal order, from `realOfScientific_clears` -/

/-- `natCast` is strictly monotone. -/
theorem natCast_lt_natCast_of_nat_lt' {a b : Nat} (h : a < b) : (natCast a : MachLib.Real) < natCast b := by
  obtain ⟨k, rfl⟩ : ∃ k, b = a + k + 1 := ⟨b - a - 1, by omega⟩
  rw [natCast_succ, natCast_add]
  have h1 : natCast a ≤ natCast a + natCast k := le_add_of_nonneg_right (Real.natCast_nonneg _)
  have h2 : natCast a + natCast k < natCast a + natCast k + 1 := by
    have h3 := add_lt_add_left zero_lt_one_ax (natCast a + natCast k)
    rw [add_zero] at h3; exact h3
  exact lt_of_le_of_lt h1 h2

/-- `(m·10⁻ᵉ)·(10ᵉ·10ᶠ) = m·10ᶠ`. -/
theorem decimal_mul_cross (m e f : Nat) :
    realOfScientific m true e * natCast (10 ^ e * 10 ^ f) = natCast (m * 10 ^ f) := by
  rw [natCast_mul, ← mul_assoc, realOfScientific_clears, ← natCast_mul]

/-- `(m·10⁻ᵉ)·(10ᶠ·10ᵉ) = m·10ᶠ`. -/
theorem decimal_mul_cross' (m e f : Nat) :
    realOfScientific m true e * natCast (10 ^ f * 10 ^ e) = natCast (m * 10 ^ f) := by
  rw [Nat.mul_comm (10 ^ f) (10 ^ e), decimal_mul_cross]

/-- **Decimal `≤` by cross-multiplication**, from `realOfScientific_clears`. The same statement as the axiom
`realOfScientific_le_of_nat`, which is not in the trusted footprint. -/
theorem decimal_le_of_nat' {m₁ e₁ m₂ e₂ : Nat} (h : m₁ * 10 ^ e₂ ≤ m₂ * 10 ^ e₁) :
    realOfScientific m₁ true e₁ ≤ realOfScientific m₂ true e₂ := by
  have hP : (0 : MachLib.Real) < natCast (10 ^ e₁ * 10 ^ e₂) :=
    natCast_pos (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)))
  refine le_of_mul_le_mul_right_pos ?_ hP
  rw [decimal_mul_cross m₁ e₁ e₂, decimal_mul_cross' m₂ e₂ e₁]
  exact natCast_le_natCast_of_nat_le h

/-- **Decimal `<` by cross-multiplication**, from `realOfScientific_clears`. The same statement as the axiom
`realOfScientific_lt_of_nat`, which is not in the trusted footprint. -/
theorem decimal_lt_of_nat' {m₁ e₁ m₂ e₂ : Nat} (h : m₁ * 10 ^ e₂ < m₂ * 10 ^ e₁) :
    realOfScientific m₁ true e₁ < realOfScientific m₂ true e₂ := by
  have hP : (0 : MachLib.Real) < natCast (10 ^ e₁ * 10 ^ e₂) :=
    natCast_pos (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)))
  have hlt : realOfScientific m₁ true e₁ * natCast (10 ^ e₁ * 10 ^ e₂)
      < realOfScientific m₂ true e₂ * natCast (10 ^ e₁ * 10 ^ e₂) := by
    rw [decimal_mul_cross m₁ e₁ e₂, decimal_mul_cross' m₂ e₂ e₁]
    exact natCast_lt_natCast_of_nat_lt' h
  rcases lt_total (realOfScientific m₁ true e₁) (realOfScientific m₂ true e₂) with hab | hab | hab
  · exact hab
  · rw [hab] at hlt; exact absurd hlt (fun hh => (ne_of_lt hh) rfl)
  · exact absurd (lt_trans_ax hlt (mul_lt_mul_of_pos_right hab hP)) (fun hh => (ne_of_lt hh) rfl)

/-- **`mach_decimal`, inside the trusted footprint.** The same normalisation of `+ − ×` over decimal literals, closing an
equality by `rfl` or cross-multiplication and an order goal with `decimal_le_of_nat'` or `decimal_lt_of_nat'`. -/
macro "grounded_decimal" : tactic => `(tactic|
  (try simp (config := { decide := true }) only
     [MachLib.Real.ofSci_eq, MachLib.Real.one_sub_decimal, MachLib.Real.decimal_add_same,
      MachLib.Real.decimal_mul, MachLib.Real.decimal_normalize]) <;>
  (first
   | rfl
   | (apply MachLib.Real.realOfScientific_eq_of_nat <;> decide)
   | (apply Certcom.decimal_le_of_nat' <;> decide)
   | (apply Certcom.decimal_lt_of_nat' <;> decide)
   | (apply le_of_lt <;> apply Certcom.decimal_lt_of_nat' <;> decide)))

/-! ## 1. Halves, from `u + u ≤ 1` -/

/-- `a + a ≤ b + b` gives `a ≤ b`. -/
theorem le_of_add_self_le_add_self {a b : MachLib.Real} (h : a + a ≤ b + b) : a ≤ b := by
  rcases lt_total a b with hab | hab | hab
  · exact le_of_lt hab
  · rw [hab]; exact le_refl b
  · have h1 : b + b < b + a := add_lt_add_left hab b
    have h2 : b + a < a + a := by
      have h3 : a + b < a + a := add_lt_add_left hab a
      rw [add_comm a b] at h3; exact h3
    exact absurd (lt_of_le_of_lt h (lt_trans_ax h1 h2)) (fun hh => (ne_of_lt hh) rfl)

/-- `a + a < b + b` gives `a < b`. -/
theorem lt_of_add_self_lt_add_self {a b : MachLib.Real} (h : a + a < b + b) : a < b := by
  rcases lt_total a b with hab | hab | hab
  · exact hab
  · rw [hab] at h; exact absurd h (fun hh => (ne_of_lt hh) rfl)
  · have h1 : b + b < b + a := add_lt_add_left hab b
    have h2 : b + a < a + a := by
      have h3 : a + b < a + a := add_lt_add_left hab a
      rw [add_comm a b] at h3; exact h3
    exact absurd (lt_trans_ax h (lt_trans_ax h1 h2)) (fun hh => (ne_of_lt hh) rfl)

/-- `u ≤ 0.5`, which is `u_le_half` with the half written as a decimal. -/
theorem u_le_point_five : u ≤ 0.5 :=
  le_of_add_self_le_add_self (by rw [show (0.5 : MachLib.Real) + 0.5 = 1 from by mach_decimal_ofnat]; exact u_le_half)

/-- A value within `u·e` of a non-negative `e` is at least `0.5·e`. This is what `u + u ≤ 1` buys over `u < 1`. -/
theorem half_le_of_close {fl e : MachLib.Real} (he : 0 ≤ e) (h : abs (fl - e) ≤ u * e) : 0.5 * e ≤ fl := by
  have h1 : -(u * e) ≤ fl - e := (abs_le_iff.mp h).1
  have h2 : u * e ≤ 0.5 * e := mul_le_mul_of_nonneg_right u_le_point_five he
  have h3 : e - u * e ≤ fl := by
    have h := add_le_add_left h1 e
    have e1 : e + -(u * e) = e - u * e := by mach_ring
    have e2 : e + (fl - e) = fl := by mach_ring
    rw [e1, e2] at h; exact h
  have h4 : e - 0.5 * e ≤ e - u * e := sub_le_sub_left h2 e
  have h5 : e - 0.5 * e = 0.5 * e := by
    have e3 : e - 0.5 * e = (1 - 0.5) * e := by mach_ring
    rw [e3, show (1 : MachLib.Real) - 0.5 = 0.5 from by grounded_decimal]
  exact le_trans (le_of_eq h5.symm) (le_trans h4 h3)

/-- A value within `u·e` of a non-negative `e` is at most `e + e`. -/
theorem le_add_self_of_close {fl e : MachLib.Real} (he : 0 ≤ e) (h : abs (fl - e) ≤ u * e) : fl ≤ e + e := by
  have h1 : fl - e ≤ u * e := (abs_le_iff.mp h).2
  have h2 : u * e ≤ e := by
    have h3 := mul_le_mul_of_nonneg_right (le_of_lt u_lt_one) he
    rw [one_mul_thm] at h3; exact h3
  have h4 := add_le_add_left (le_trans h1 h2) e
  have e2 : e + (fl - e) = fl := by mach_ring
  rw [e2] at h4; exact h4

/-- `1 + u ≤ 2.0`. -/
theorem one_add_u_le_two_point_zero : (1 : MachLib.Real) + u ≤ 2.0 :=
  le_trans one_add_u_le_two_of_lt_one (le_of_eq realOfScientific_two_dot_zero.symm)

/-! ## 2. Decimals against `DBL_MIN` and `DBL_MAX` -/

/-- A positive decimal `m·10⁻ᵉ` is at most `m`. -/
theorem decimal_le_natCast (m e : Nat) (hm : 0 < m) : realOfScientific m true e ≤ natCast m := by
  have hr : 0 ≤ realOfScientific m true e := le_of_lt (realOfScientific_pos m true e hm)
  have hN1 : (natCast 1 : MachLib.Real) ≤ natCast (10 ^ e) := natCast_le_natCast_of_nat_le (Nat.pow_pos (by decide))
  rw [natCast_one] at hN1
  have h := mul_le_mul_of_nonneg_left hN1 hr
  rw [mul_one_ax, realOfScientific_clears] at h
  exact h

set_option exponentiation.threshold 1100 in
/-- `DBL_MIN` is at most every positive decimal `m·10⁻ᵉ` with `10ᵉ ≤ 2¹⁰²²`. -/
theorem dblMin_le_decimal (m e : Nat) (hm : 0 < m) (he : 10 ^ e ≤ 2 ^ 1022) :
    dblMin ≤ realOfScientific m true e := by
  have hN : (0 : MachLib.Real) < natCast (10 ^ e) := natCast_pos (Nat.pow_pos (by decide))
  have hD : (natCast (2 ^ 1022) : MachLib.Real) ≠ 0 := Ne.symm (ne_of_lt (natCast_pos (Nat.two_pow_pos 1022)))
  have h1 : dblMin * natCast (2 ^ 1022) = 1 := div_mul_cancel hD
  have h2 : dblMin * natCast (10 ^ e) ≤ dblMin * natCast (2 ^ 1022) :=
    mul_le_mul_of_nonneg_left (natCast_le_natCast_of_nat_le he) (le_of_lt dblMin_pos)
  have h3 : (natCast 1 : MachLib.Real) ≤ natCast m := natCast_le_natCast_of_nat_le hm
  rw [natCast_one] at h3
  apply le_of_mul_le_mul_right_pos _ hN
  rw [realOfScientific_clears m e]
  rw [h1] at h2
  exact le_trans h2 h3

set_option exponentiation.threshold 1100 in
/-- **A positive decimal quantized by `floatOfR`.** For `g = m·10⁻ᵉ` with `10ᵉ ≤ 2¹⁰²²` and `m ≤ DBL_MAX`, `floatOfR g` is
finite (`real_round_finite`) and reads back between `0.5·g` and `g + g` (`real_round_bounds` and `u_le_half`). -/
theorem floatOfR_decimal_facts (m e : Nat) (hm : 0 < m) (he : 10 ^ e ≤ 2 ^ 1022) (hM : m ≤ (2 ^ 53 - 1) * 2 ^ 971) :
    (floatOfR (realOfScientific m true e)).isFinite = true ∧
    0.5 * realOfScientific m true e ≤ realToR (floatOfR (realOfScientific m true e)) ∧
    realToR (floatOfR (realOfScientific m true e)) ≤ realOfScientific m true e + realOfScientific m true e := by
  have hg0 : 0 ≤ realOfScientific m true e := le_of_lt (realOfScientific_pos m true e hm)
  have habs : abs (realOfScientific m true e) = realOfScientific m true e := abs_of_nonneg hg0
  have hmax : realOfScientific m true e ≤ dblMax :=
    le_trans (decimal_le_natCast m e hm) (natCast_le_natCast_of_nat_le hM)
  have hclose := real_round_bounds _ _ hg0 hmax (le_of_eq habs)
    (Or.inr (by rw [habs]; exact dblMin_le_decimal m e hm he))
  exact ⟨real_round_finite _ (by rw [habs]; exact hmax), half_le_of_close hg0 hclose, le_add_self_of_close hg0 hclose⟩

/-! ## 3. The PID gains -/

set_option exponentiation.threshold 1100 in
/-- The proportional gain's float `1.5`: finite, and its real value is between `0.025` and `3.0`. -/
theorem gain_1_5_facts :
    (1.5 : Float).isFinite = true ∧ (0.025 : MachLib.Real) ≤ realToR 1.5 ∧ realToR 1.5 ≤ 3.0 := by
  obtain ⟨hf, hlo, hhi⟩ := floatOfR_decimal_facts 15 1 (by decide) (by decide) (by decide)
  rw [float_lit_1_5]
  exact ⟨hf, le_trans (by grounded_decimal) hlo, le_trans hhi (by grounded_decimal)⟩

set_option exponentiation.threshold 1100 in
/-- The integral gain's float `0.4`: finite, and its real value is between `0.025` and `3.0`. -/
theorem gain_0_4_facts :
    (0.4 : Float).isFinite = true ∧ (0.025 : MachLib.Real) ≤ realToR 0.4 ∧ realToR 0.4 ≤ 3.0 := by
  obtain ⟨hf, hlo, hhi⟩ := floatOfR_decimal_facts 4 1 (by decide) (by decide) (by decide)
  rw [float_lit_0_4]
  exact ⟨hf, le_trans (by grounded_decimal) hlo, le_trans hhi (by grounded_decimal)⟩

set_option exponentiation.threshold 1100 in
/-- The derivative gain's float `0.05`: finite, and its real value is between `0.025` and `3.0`. The lower end is exactly
`0.5 · 0.05`, which is where `u + u ≤ 1` is used. -/
theorem gain_0_05_facts :
    (0.05 : Float).isFinite = true ∧ (0.025 : MachLib.Real) ≤ realToR 0.05 ∧ realToR 0.05 ≤ 3.0 := by
  obtain ⟨hf, hlo, hhi⟩ := floatOfR_decimal_facts 5 2 (by decide) (by decide) (by decide)
  rw [float_lit_0_05]
  exact ⟨hf, le_trans (by grounded_decimal) hlo, le_trans hhi (by grounded_decimal)⟩

/-! ## 4. An upper bound on `exp` -/

/-- `exp x · (1 − x) ≤ 1`, for every `x`: `1 − x ≤ exp (−x)` and `exp x · exp (−x) = 1`. -/
theorem exp_mul_one_sub_le_one (x : MachLib.Real) : exp x * (1 - x) ≤ 1 := by
  have h1 : 1 - x ≤ exp (-x) := by
    have h := one_add_le_exp (-x)
    have e : (1 : MachLib.Real) + -x = 1 - x := by mach_ring
    rw [e] at h; exact h
  have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (exp_pos x))
  rw [HyperbolicPreservation.exp_mul_exp_neg x] at h2
  exact h2

/-- `exp x ≤ 2` when `x + x ≤ 1`. -/
theorem exp_le_two_of_add_le_one {x : MachLib.Real} (hx : x + x ≤ 1) : exp x ≤ 1 + 1 := by
  have h1 : (1 : MachLib.Real) ≤ (1 - x) + (1 - x) := by
    have e : (1 - x) + (1 - x) = 1 + (1 - (x + x)) := by mach_ring
    rw [e]; exact le_add_of_nonneg_right (sub_nonneg_of_le hx)
  have h2 : exp x * 1 ≤ exp x * ((1 - x) + (1 - x)) := mul_le_mul_of_nonneg_left h1 (le_of_lt (exp_pos x))
  rw [mul_one_ax] at h2
  have e2 : exp x * ((1 - x) + (1 - x)) = exp x * (1 - x) + exp x * (1 - x) := by mach_ring
  rw [e2] at h2
  exact le_trans h2 (add_le_add (exp_mul_one_sub_le_one x) (exp_mul_one_sub_le_one x))

/-- `exp 1 ≤ 4`. -/
theorem exp_one_le_four : exp 1 ≤ natCast 4 := by
  have hh : (0.5 : MachLib.Real) + 0.5 ≤ 1 := le_of_eq (by mach_decimal_ofnat)
  have h2 := exp_le_two_of_add_le_one hh
  have e : exp 1 = exp 0.5 * exp 0.5 := by
    rw [← exp_add, show (0.5 : MachLib.Real) + 0.5 = 1 from by mach_decimal_ofnat]
  rw [e, natCast_four]
  have h3 := mul_le_mul' (le_of_lt (exp_pos _)) h2 (le_of_lt (exp_pos _)) h2
  have e4 : (1 + 1 : MachLib.Real) * (1 + 1) = 1 + 1 + 1 + 1 := by mach_ring
  rw [e4] at h3; exact h3

/-- `exp n ≤ 4ⁿ`. -/
theorem exp_natCast_le (n : Nat) : exp (natCast n) ≤ natCast (4 ^ n) := by
  induction n with
  | zero => rw [natCast_zero, exp_zero, Nat.pow_zero, natCast_one]; exact le_refl 1
  | succ k ih =>
    rw [natCast_succ, exp_add, Nat.pow_succ, natCast_mul]
    exact mul_le_mul' (le_of_lt (exp_pos _)) ih (le_of_lt (exp_pos _)) exp_one_le_four

/-- `exp x ≤ 4ⁿ` for `x ≤ n`. -/
theorem exp_le_natCast_pow {x : MachLib.Real} {n : Nat} (h : x ≤ natCast n) : exp x ≤ natCast (4 ^ n) :=
  le_trans (exp_monotone h) (exp_natCast_le n)

set_option exponentiation.threshold 1100 in
/-- `DBL_MIN ≤ exp (−R)` for `R ≤ 500`: `exp R ≤ 4⁵⁰⁰ = 2¹⁰⁰⁰ ≤ 2¹⁰²²`. -/
theorem dblMin_le_exp_neg {R : MachLib.Real} (hR : R ≤ natCast 500) : dblMin ≤ exp (-R) := by
  have hE := exp_le_natCast_pow hR
  have hpos : (0 : MachLib.Real) < natCast (4 ^ 500) := natCast_pos (Nat.pow_pos (by decide))
  have hD : (natCast (2 ^ 1022) : MachLib.Real) ≠ 0 := Ne.symm (ne_of_lt (natCast_pos (Nat.two_pow_pos 1022)))
  have h1 : dblMin * natCast (2 ^ 1022) = 1 := div_mul_cancel hD
  have h2 : dblMin * natCast (4 ^ 500) ≤ dblMin * natCast (2 ^ 1022) :=
    mul_le_mul_of_nonneg_left (natCast_le_natCast_of_nat_le (by decide)) (le_of_lt dblMin_pos)
  have h3 : exp (-R) * exp R = 1 := by rw [mul_comm]; exact HyperbolicPreservation.exp_mul_exp_neg R
  have h4 : exp (-R) * exp R ≤ exp (-R) * natCast (4 ^ 500) := mul_le_mul_of_nonneg_left hE (le_of_lt (exp_pos _))
  rw [h3] at h4
  rw [h1] at h2
  exact le_of_mul_le_mul_right_pos (le_trans h2 h4) hpos

/-- `|log x| ≤ x` for `x ≥ 1`. -/
theorem abs_log_le_self {x : MachLib.Real} (hx : 1 ≤ x) : abs (log x) ≤ x := by
  have h0 : 0 < x := lt_of_lt_of_le zero_lt_one_ax hx
  rw [abs_of_nonneg (log_nonneg hx)]
  exact le_trans (log_le_sub_one h0) (sub_le_self (le_of_lt zero_lt_one_ax))

/-! ## 4b. Numeric bounds on `u`, from `u ≤ 2⁻⁵²` -/

/-- **`u · n < 1` for every natural `n < 2⁵²`**, from `u_le_inv_two_pow_52` (owner-approved 2026-09-14). -/
theorem u_mul_natCast_lt_one {n : Nat} (h : n < 2 ^ 52) : u * natCast n < 1 := by
  have hN : (0 : MachLib.Real) < natCast (2 ^ 52) := natCast_pos (Nat.two_pow_pos 52)
  have hNe : (natCast (2 ^ 52) : MachLib.Real) ≠ 0 := Ne.symm (ne_of_lt hN)
  have h1 : u * natCast n ≤ (1 / natCast (2 ^ 52)) * natCast n :=
    mul_le_mul_of_nonneg_right u_le_inv_two_pow_52 (Real.natCast_nonneg n)
  have h2 : natCast n * (1 / natCast (2 ^ 52)) < natCast (2 ^ 52) * (1 / natCast (2 ^ 52)) :=
    mul_lt_mul_of_pos_right (natCast_lt_natCast_of_nat_lt' h) (one_div_pos_of_pos hN)
  rw [mul_comm (natCast (2 ^ 52)) (1 / natCast (2 ^ 52)), div_mul_cancel hNe,
    mul_comm (natCast n) (1 / natCast (2 ^ 52))] at h2
  exact lt_of_le_of_lt h1 h2

/-- `u + u + u + u = u · 4`. -/
theorem four_u_eq : u + u + u + u = u * natCast 4 := by
  rw [natCast_four]; mach_ring

/-! ## 5. `π/2` -/

/-- `0.5 < π/2`, from `1 < π`. -/
theorem half_lt_pi_div_two : (0.5 : MachLib.Real) < pi / (1 + 1) := by
  have h2 : (1 + 1 : MachLib.Real) ≠ 0 :=
    Ne.symm (ne_of_lt (lt_of_lt_of_le zero_lt_one_ax (le_add_of_nonneg_right (le_of_lt zero_lt_one_ax))))
  have hh : pi / (1 + 1) + pi / (1 + 1) = pi := by
    have e : pi / (1 + 1) + pi / (1 + 1) = pi / (1 + 1) * (1 + 1) := by mach_ring
    rw [e]; exact div_mul_cancel h2
  apply lt_of_add_self_lt_add_self
  rw [hh, show (0.5 : MachLib.Real) + 0.5 = 1 from by mach_decimal_ofnat]
  exact pi_gt_one

end Certcom
