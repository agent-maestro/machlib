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
namespace Real

axiom sin : Real → Real
axiom cos : Real → Real
axiom pi  : Real

/-! ### Defining axioms -/

axiom sin_zero       : sin 0 = 0
axiom cos_zero       : cos 0 = 1
axiom sin_pi         : sin pi = 0
axiom cos_pi         : cos pi = -1
axiom pi_pos         : 0 < pi
axiom pythagorean (x : Real) : sin x * sin x + cos x * cos x = 1
axiom sin_neg        (x : Real) : sin (-x) = -(sin x)
axiom cos_neg        (x : Real) : cos (-x) = cos x
axiom sin_add        (x y : Real) :
  sin (x + y) = sin x * cos y + cos x * sin y
axiom cos_add        (x y : Real) :
  cos (x + y) = cos x * cos y - sin x * sin y

/-! ### Boundedness -/

axiom sin_le_one     (x : Real) : sin x ≤ 1
axiom neg_one_le_sin (x : Real) : -1 ≤ sin x
axiom cos_le_one     (x : Real) : cos x ≤ 1
axiom neg_one_le_cos (x : Real) : -1 ≤ cos x

/-! ### Periodicity (period 2π) -/

axiom sin_periodic (x : Real) : sin (x + (1 + 1) * pi) = sin x
axiom cos_periodic (x : Real) : cos (x + (1 + 1) * pi) = cos x

/-! ### Derived lemmas -/

theorem sin_sq_add_cos_sq (x : Real) :
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

end Real
end MachLib
