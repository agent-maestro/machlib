import MachLib.Basic
import MachLib.Forge
import MachLib.Ring
import MachLib.MPolyRing

/-!
# Field / division lemmas — the half-cancellation kit

`Basic` ships the field axioms (`div_def : b≠0 → a/b = a·(1/b)`, `mul_inv : a≠0 →
a·(1/a) = 1`, `div_zero`) but no derived division algebra, because the early files
have no ring tactic. This module sits downstream of `Ring`/`MPolyRing` and proves
the small kit the analytic-identity derivations need — chiefly the
*half-cancellation* `2·(a/2) = a` that the `sinh`/`cosh` ↔ `exp` conversions and
`tan 0 = 0` rely on.

Mathlib-free, `sorryAx`-free.
-/

namespace MachLib
namespace Real

/-- `0 < 1 + 1`. -/
theorem two_pos : (0 : Real) < 1 + 1 := by
  have h1 : (1 : Real) < 1 + 1 := by
    have h := add_lt_add_left zero_lt_one_ax 1
    rwa [add_zero] at h
  exact lt_trans_ax zero_lt_one_ax h1

/-- `(1 + 1) ≠ 0`. -/
theorem two_ne_zero : (1 + 1 : Real) ≠ 0 := fun h => lt_irrefl_ax 0 (h ▸ two_pos)

/-- `b ≠ 0 → b · (a / b) = a`. -/
theorem mul_div_cancel_left {a b : Real} (hb : b ≠ 0) : b * (a / b) = a := by
  rw [div_def a b hb, show b * (a * (1 / b)) = a * (b * (1 / b)) from by mach_ring,
      mul_inv b hb, mul_one_ax]

/-- `b ≠ 0 → (b · a) / b = a`. -/
theorem mul_div_cancel_left' {a b : Real} (hb : b ≠ 0) : (b * a) / b = a := by
  rw [div_def (b * a) b hb, show (b * a) * (1 / b) = a * (b * (1 / b)) from by mach_ring,
      mul_inv b hb, mul_one_ax]

/-- `b ≠ 0 → b / b = 1`. -/
theorem self_div {b : Real} (hb : b ≠ 0) : b / b = 1 := by
  rw [div_def b b hb, mul_inv b hb]

/-- `c ≠ 0 → a/c + b/c = (a+b)/c`. -/
theorem div_add_div_same {a b c : Real} (hc : c ≠ 0) : a / c + b / c = (a + b) / c := by
  rw [div_def a c hc, div_def b c hc, div_def (a + b) c hc]
  show a * (1 / c) + b * (1 / c) = (a + b) * (1 / c)
  mach_mpoly [a, b, 1 / c]

/-- `c ≠ 0 → a/c − b/c = (a−b)/c`. -/
theorem div_sub_div_same {a b c : Real} (hc : c ≠ 0) : a / c - b / c = (a - b) / c := by
  rw [div_def a c hc, div_def b c hc, div_def (a - b) c hc]
  show a * (1 / c) - b * (1 / c) = (a - b) * (1 / c)
  mach_mpoly [a, b, 1 / c]

/-- `c ≠ 0 → −(a/c) = (−a)/c`. -/
theorem neg_div {a c : Real} (hc : c ≠ 0) : -(a / c) = (-a) / c := by
  rw [div_def a c hc, div_def (-a) c hc, neg_mul]

/-- Left-cancellation: `c ≠ 0 → c·a = c·b → a = b` (multiply by `1/c`). -/
theorem mul_left_cancel {a b c : Real} (hc : c ≠ 0) (h : c * a = c * b) : a = b := by
  have e : (1 / c) * (c * a) = (1 / c) * (c * b) := by rw [h]
  rw [show (1 / c) * (c * a) = ((1 / c) * c) * a from by mach_ring,
      show (1 / c) * (c * b) = ((1 / c) * c) * b from by mach_ring,
      show (1 / c) * c = 1 from by rw [mul_comm]; exact mul_inv c hc,
      show (1 : Real) * a = a from by rw [mul_comm, mul_one_ax],
      show (1 : Real) * b = b from by rw [mul_comm, mul_one_ax]] at e
  exact e

/-- No zero divisors: `a ≠ 0 → b ≠ 0 → a·b ≠ 0`. -/
theorem mul_ne_zero {a b : Real} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  apply hb
  apply mul_left_cancel ha
  rw [mul_zero]; exact h

end Real
end MachLib
