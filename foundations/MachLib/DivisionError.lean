import MachLib.OperatorBasisGeneral
import MachLib.FieldLemmas

/-!
# Division: the last operator class — its inequality kit and forward-error rule

`OperatorBasisGeneral` folded every operator *except* division — the one operator that
cannot be bounded without a **denominator lower bound** (`1/y` blows up near `0`). This
file supplies that operator.

The obstacle in this Mathlib-free, weak-automation setting is reasoning over `a/b`
inequalities — there was no `abs_div`, no cross-multiply lemma. §1 builds that kit
(all *derived*, no new axioms — only the existing `one_div_pos_of_pos`): `div_mul_cancel`,
the cancellation `le_of_mul_le_mul_right_pos`, the cross-multiply `div_le_div_iff`, the
monotone `div_le_div_pos`, and `abs_div_pos`. §2 proves `aerr_div`, the division case
of the `AErr` magnitude+error certificate, for a **positive denominator bounded below**
(`0 < m ≤ vy`, `m ≤ ye` — the common case: ratios, means, normalisations). With it,
the operator basis is forward-error-bounded *in full*.

`sorryAx`-free; 0 new axioms.
-/

namespace MachLib.Real

/-! ## §1 — the division-inequality kit (derived, no new axioms) -/

/-- Two-sided product monotonicity (chained from the one-sided rules). -/
theorem mul_le_mul' {a b c d : Real} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) :
    a * c ≤ b * d :=
  le_trans (mul_le_mul_of_nonneg_right hab hc) (mul_le_mul_of_nonneg_left hcd (le_trans ha hab))

/-- `(a / b) * b = a` for `b ≠ 0`. -/
theorem div_mul_cancel {a b : Real} (hb : b ≠ 0) : a / b * b = a := by
  rw [div_def a b hb, mul_assoc, mul_comm (1 / b) b, mul_inv b hb, mul_one_ax]

/-- Cancel a positive right factor: `a * c ≤ b * c → 0 < c → a ≤ b`. -/
theorem le_of_mul_le_mul_right_pos {a b c : Real} (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b := by
  have h2 := mul_le_mul_of_nonneg_right h (le_of_lt (one_div_pos_of_pos hc))
  rw [mul_assoc, mul_inv c (ne_of_gt hc), mul_one_ax,
      mul_assoc, mul_inv c (ne_of_gt hc), mul_one_ax] at h2
  exact h2

/-- **Cross-multiply.** For positive denominators, `a/b ≤ c/d ↔ a*d ≤ c*b`. -/
theorem div_le_div_iff {a b c d : Real} (hb : 0 < b) (hd : 0 < d) :
    a / b ≤ c / d ↔ a * d ≤ c * b := by
  have hbd : (0 : Real) < b * d := mul_pos hb hd
  have e1 : a / b * (b * d) = a * d := by rw [← mul_assoc, div_mul_cancel (ne_of_gt hb)]
  have e2 : c / d * (b * d) = c * b := by
    rw [mul_comm b d, ← mul_assoc, div_mul_cancel (ne_of_gt hd)]
  constructor
  · intro h
    have h2 := mul_le_mul_of_nonneg_right h (le_of_lt hbd)
    rw [e1, e2] at h2; exact h2
  · intro h
    have key : a / b * (b * d) ≤ c / d * (b * d) := by rw [e1, e2]; exact h
    exact le_of_mul_le_mul_right_pos key hbd

/-- **Monotone division.** Larger numerator, smaller (still positive) denominator. -/
theorem div_le_div_pos {a b c d : Real} (ha : 0 ≤ a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) : a / d ≤ b / c := by
  have hd : 0 < d := lt_of_lt_of_le hc hcd
  rw [div_le_div_iff hd hc]
  exact mul_le_mul' ha hab (le_of_lt hc) hcd

/-- `|a / b| = |a| / b` for a positive denominator. -/
theorem abs_div_pos {a b : Real} (hb : 0 < b) : abs (a / b) = abs a / b := by
  have hbne : b ≠ 0 := ne_of_gt hb
  rw [div_def a b hbne, abs_mul, abs_of_nonneg (le_of_lt (one_div_pos_of_pos hb)),
      div_def (abs a) b hbne]

/-- Fresh-var right-distribution over subtraction (so `mach_mpoly` sees plain atoms,
not the opaque `/` subterms it would choke on). -/
theorem dsd_ring (X Y Z : Real) : (X - Y) * Z = X * Z - Y * Z := by mach_mpoly [X, Y, Z]

/-- `x * k = z → x = z / k` (the cross-multiply characterization of division). -/
theorem eq_div_of_mul_eq {x z k : Real} (hk : k ≠ 0) (h : x * k = z) : x = z / k := by
  rw [← h, mul_comm x k, mul_div_cancel_left' hk]

/-- **Combine two fractions** over a common product denominator. -/
theorem div_sub_div {a b c d : Real} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b - c / d = (a * d - c * b) / (b * d) := by
  apply eq_div_of_mul_eq (mul_ne_zero hb hd)
  rw [dsd_ring (a / b) (c / d) (b * d),
      show a / b * (b * d) = a * d from by rw [← mul_assoc, div_mul_cancel hb],
      show c / d * (b * d) = c * b from by rw [mul_comm b d, ← mul_assoc, div_mul_cancel hd]]

/-! ## §2 — the division forward-error rule -/

/-- **Division** (`AErr`, positive denominator bounded below `0 < m ≤ vy`, `m ≤ ye`).
The exact ratio has magnitude `≤ Mx/m`; the error is the division's own rounding plus
the propagated numerator/denominator errors, every term scaled by the reciprocal of
the lower bound `m`. The denominator bound is the side condition division alone needs
(`1/y` is unbounded near 0) — supplied per call (e.g. a guarded/clamped denominator). -/
theorem aerr_div {w Mx Ex vx xe My Ey vy ye p m : Real} (hw0 : 0 ≤ w)
    (hx : AErr Mx Ex vx xe) (hy : AErr My Ey vy ye)
    (hm : 0 < m) (hmvy : m ≤ vy) (hmye : m ≤ ye) (hp : RoundsW w p (vx / vy)) :
    AErr (Mx / m) (w * ((Mx + Ex) / m) + (Ex / m + Mx * Ey / (m * m))) p (xe / ye) := by
  have hvy : 0 < vy := lt_of_lt_of_le hm hmvy
  have hye : 0 < ye := lt_of_lt_of_le hm hmye
  have hvyye : 0 < vy * ye := mul_pos hvy hye
  have hmm : 0 < m * m := mul_pos hm hm
  have hMx0 : 0 ≤ Mx := le_trans (abs_nonneg xe) hx.1
  have hEx0 : 0 ≤ Ex := le_trans (abs_nonneg (vx - xe)) hx.2
  have hEy0 : 0 ≤ Ey := le_trans (abs_nonneg (vy - ye)) hy.2
  refine ⟨?_, ?_⟩
  · rw [abs_div_pos hye]
    exact div_le_div_pos (abs_nonneg xe) hx.1 hm hmye
  · have hT1 : abs (p - vx / vy) ≤ w * ((Mx + Ex) / m) := by
      have hb : abs (vx / vy) ≤ (Mx + Ex) / m := by
        rw [abs_div_pos hvy]; exact div_le_div_pos (abs_nonneg vx) hx.val_bound hm hmvy
      exact le_trans (roundsW_abs hp) (mul_le_mul_of_nonneg_left hb hw0)
    have hT2 : abs (vx / vy - xe / ye) ≤ Ex / m + Mx * Ey / (m * m) := by
      rw [div_sub_div (ne_of_gt hvy) (ne_of_gt hye), abs_div_pos hvyye]
      have hnum : abs (vx * ye - xe * vy) ≤ Ex * ye + Mx * Ey := by
        rw [show vx * ye - xe * vy = (vx - xe) * ye + xe * (ye - vy) from by
              mach_mpoly [vx, ye, xe, vy]]
        have hA : abs ((vx - xe) * ye) ≤ Ex * ye := by
          rw [abs_mul, abs_of_nonneg (le_of_lt hye)]
          exact mul_le_mul_of_nonneg_right hx.2 (le_of_lt hye)
        have hB : abs (xe * (ye - vy)) ≤ Mx * Ey := by
          rw [abs_mul, show ye - vy = -(vy - ye) from by mach_ring, abs_neg]
          exact mul_le_mul' (abs_nonneg xe) hx.1 (abs_nonneg (vy - ye)) hy.2
        exact le_trans (abs_add _ _) (add_le_add_both hA hB)
      have hstep : abs (vx * ye - xe * vy) / (vy * ye) ≤ (Ex * ye + Mx * Ey) / (vy * ye) :=
        div_le_div_pos (abs_nonneg _) hnum hvyye (le_refl _)
      have hP : Ex * ye / (vy * ye) ≤ Ex / m := by
        rw [div_le_div_iff hvyye hm, show Ex * (vy * ye) = Ex * ye * vy from by
              mach_mpoly [Ex, vy, ye]]
        exact mul_le_mul_of_nonneg_left hmvy (mul_nonneg hEx0 (le_of_lt hye))
      have hQ : Mx * Ey / (vy * ye) ≤ Mx * Ey / (m * m) :=
        div_le_div_pos (mul_nonneg hMx0 hEy0) (le_refl _) hmm
          (mul_le_mul' (le_of_lt hm) hmvy (le_of_lt hm) hmye)
      have hcomb : (Ex * ye + Mx * Ey) / (vy * ye) ≤ Ex / m + Mx * Ey / (m * m) := by
        rw [show (Ex * ye + Mx * Ey) / (vy * ye)
              = Ex * ye / (vy * ye) + Mx * Ey / (vy * ye) from
              (div_add_div_same (ne_of_gt hvyye)).symm]
        exact add_le_add_both hP hQ
      exact le_trans hstep hcomb
    rw [et_split3 p (vx / vy) (xe / ye)]
    exact le_trans (abs_add _ _) (add_le_add_both hT1 hT2)

/-- A guarded ratio `x / y` (`y ≥ m > 0`, exact inputs): the rule certifies magnitude
`|x|/m` and an error that is just the one division's rounding (the input-error terms
vanish), demonstrating `aerr_div` end-to-end on a concrete kernel. -/
theorem ratio_guarded_via_rule {w x y p m : Real} (hw0 : 0 ≤ w) (hm : 0 < m) (hmy : m ≤ y)
    (hp : RoundsW w p (x / y)) :
    AErr (abs x / m) (w * ((abs x + 0) / m) + (0 / m + abs x * 0 / (m * m))) p (x / y) :=
  aerr_div hw0 (aerr_leaf x) (aerr_leaf y) hm hmy hmy hp

end MachLib.Real
