import MachLib.Basic
import MachLib.Forge
import MachLib.Ring
import MachLib.MPolyRing

/-!
# Sign / order / abs-unfold lemmas — the early order layer

A small cluster of genuinely low-level order facts (`x ≤ 0 → 0 ≤ -x`, the reverse
of `≤` under negation, `abs` on a nonpositive argument, …) had drifted *downstream*
into `FPModel` / `ConditionNumber` / `IntervalArith`, even though they need only
`Basic` + `Forge` + the ring tactics. That placement blocked promoting the
`abs_mul` axiom (which is needed at `Linarith`'s level via
`abs_mul_le_of_abs_le_one`, upstream of those files) and the trig square/abs
bounds.

This module is the audit map's "early order/abs module": it owns those lemmas at
the right depth (above `Lemmas`), so the abs algebra can be proved rather than
assumed. Each lemma is relocated verbatim from its former home; the former sites
now get it via the import chain (`Lemmas` imports this).

Mathlib-free, `sorryAx`-free.
-/

namespace MachLib
namespace Real

/-- `a = b → a ≤ b` (relocated up from `FPModel`). -/
theorem le_of_eq {a b : Real} (h : a = b) : a ≤ b := h ▸ le_refl a

/-- `x ≤ 0 → 0 ≤ -x` (relocated up from `FPModel`). -/
theorem neg_nonneg_of_nonpos {x : Real} (h : x ≤ 0) : 0 ≤ -x := by
  have hc : x + (-x) ≤ 0 + (-x) := add_le_add_both h (le_refl (-x))
  have e1 : x + (-x) = 0 := add_neg x
  have e2 : (0 : Real) + (-x) = -x := zero_add (-x)
  rw [e1, e2] at hc; exact hc

/-- `a ≤ b → -b ≤ -a` (relocated up from `FPModel`). -/
theorem neg_le_neg {a b : Real} (h : a ≤ b) : -b ≤ -a := by
  have hc : a + (-a + -b) ≤ b + (-a + -b) := add_le_add_both h (le_refl (-a + -b))
  have e1 : a + (-a + -b) = -b := by rw [← add_assoc, add_neg, zero_add]
  have e2 : b + (-a + -b) = -a := by rw [add_comm (-a) (-b), ← add_assoc, add_neg, zero_add]
  rw [e1, e2] at hc; exact hc

/-- `¬ 0 ≤ x → x ≤ 0` (relocated up from `IntervalArith`). -/
theorem nonpos_of_not_nonneg {x : Real} (h : ¬ 0 ≤ x) : x ≤ 0 := by
  rcases lt_total 0 x with h0 | h0 | h0
  · exact absurd (le_of_lt h0) h
  · exact absurd (le_of_eq h0) h
  · exact le_of_lt h0

/-- `x ≤ 0 → abs x = -x` (relocated up from `ConditionNumber`). -/
theorem abs_of_nonpos {x : Real} (h : x ≤ 0) : abs x = -x := by
  unfold abs
  by_cases h0 : 0 ≤ x
  · have hx : x = 0 := le_antisymm h h0
    rw [if_pos h0, hx, neg_zero]
  · rw [if_neg h0]

/-- `0 ≤ x · x` (relocated up from `FPModel`; the squared-nonneg fact, now early
enough that `Lemmas` can use it for the trig square/abs bounds). -/
theorem mul_self_nonneg (x : Real) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact mul_nonneg h h
  · have hn : 0 ≤ -x := neg_nonneg_of_nonpos (nonpos_of_not_nonneg h)
    have hp : 0 ≤ (-x) * (-x) := mul_nonneg hn hn
    rwa [neg_mul_neg] at hp

end Real
end MachLib
