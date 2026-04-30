import MachLib.Basic

/-
MachLib.Trig — sine and cosine, axiomatised.

The same delegation argument as `Exp`: agents reasoning about
trigonometric expressions need the *facts* (Pythagorean identity,
addition formulas, periodicity), not the analytic construction.
We expose the facts as axioms; a future contributor wanting to
build sin/cos from a power series or as the imaginary/real parts
of the complex exponential can do so without breaking any
downstream theorem.
-/

namespace MachLib
namespace R

axiom sin : R → R
axiom cos : R → R
axiom pi  : R

/-! ### Defining axioms -/

axiom sin_zero       : sin 0 = 0
axiom cos_zero       : cos 0 = 1
axiom sin_pi         : sin pi = 0
axiom cos_pi         : cos pi = -1
axiom pi_pos         : 0 < pi
axiom pythagorean (x : R) : sin x * sin x + cos x * cos x = 1
axiom sin_neg        (x : R) : sin (-x) = -(sin x)
axiom cos_neg        (x : R) : cos (-x) = cos x
axiom sin_add        (x y : R) :
  sin (x + y) = sin x * cos y + cos x * sin y
axiom cos_add        (x y : R) :
  cos (x + y) = cos x * cos y - sin x * sin y

/-! ### Boundedness -/

axiom sin_le_one     (x : R) : sin x ≤ 1
axiom neg_one_le_sin (x : R) : -1 ≤ sin x
axiom cos_le_one     (x : R) : cos x ≤ 1
axiom neg_one_le_cos (x : R) : -1 ≤ cos x

/-! ### Periodicity (period 2π) -/

axiom sin_periodic (x : R) : sin (x + (1 + 1) * pi) = sin x
axiom cos_periodic (x : R) : cos (x + (1 + 1) * pi) = cos x

/-! ### Derived lemmas -/

theorem sin_sq_add_cos_sq (x : R) :
    sin x * sin x + cos x * cos x = 1 :=
  pythagorean x

theorem sin_pi_zero : sin pi = 0 := sin_pi
theorem cos_pi_neg_one : cos pi = -1 := cos_pi

theorem sin_two_pi : sin ((1 + 1) * pi) = 0 := by
  have h : sin (0 + (1 + 1) * pi) = sin 0 := sin_periodic 0
  rw [zero_add] at h
  rw [h, sin_zero]

theorem cos_two_pi : cos ((1 + 1) * pi) = 1 := by
  have h : cos (0 + (1 + 1) * pi) = cos 0 := cos_periodic 0
  rw [zero_add] at h
  rw [h, cos_zero]

end R
end MachLib
