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
axiom tan : Real → Real
axiom pi  : Real

/-! ### Defining axioms -/

axiom sin_zero       : sin 0 = 0
axiom cos_zero       : cos 0 = 1
axiom tan_zero       : tan 0 = 0
axiom tan_def        (x : Real) : cos x ≠ 0 → tan x = sin x / cos x
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

/-! ### Additional analytic primitives

The forge's industry verticals reach for these names through the
emitted `Real.tanh`, `Real.sqrt`, etc. references. We axiomatise
each with the minimal property set the downstream theorems use;
contributors can add more when a specific theorem needs them. -/

axiom tanh   : Real → Real
axiom sqrt   : Real → Real
axiom atan2  : Real → Real → Real
axiom arcsin : Real → Real
axiom arccos : Real → Real

/-! ### Defining properties (minimal set) -/

-- tanh: bounded in (-1, 1), zero at zero, odd.
axiom tanh_zero     : tanh 0 = 0
axiom tanh_lt_one   (x : Real) : tanh x < 1
axiom neg_one_lt_tanh (x : Real) : -1 < tanh x
axiom tanh_neg      (x : Real) : tanh (-x) = -(tanh x)

-- sqrt: non-negative, fixed at 0 and 1, multiplicative on
-- non-negatives. We follow the GNU/IEEE convention of returning 0
-- on negative input rather than NaN.
axiom sqrt_zero       : sqrt 0 = 0
axiom sqrt_one        : sqrt 1 = 1
axiom sqrt_nonneg     (x : Real) : 0 ≤ sqrt x
axiom sqrt_sq_nonneg  (x : Real) : 0 ≤ x → sqrt x * sqrt x = x
axiom sqrt_neg_zero   (x : Real) : x < 0 → sqrt x = 0

-- arcsin / arccos: principal-value inverses, bounded.
axiom arcsin_zero  : arcsin 0 = 0
axiom arccos_zero  : arccos 0 = pi / (1 + 1)
axiom arcsin_one   : arcsin 1 = pi / (1 + 1)
axiom arccos_one   : arccos 1 = 0
axiom sin_arcsin   (x : Real) : -1 ≤ x → x ≤ 1 → sin (arcsin x) = x
axiom cos_arccos   (x : Real) : -1 ≤ x → x ≤ 1 → cos (arccos x) = x

-- atan2: the principal-value angle of the point (x, y), in (-π, π].
axiom atan2_zero_one : atan2 0 1 = 0
axiom atan2_one_zero : atan2 1 0 = pi / (1 + 1)
axiom atan2_le_pi    (y x : Real) : atan2 y x ≤ pi
axiom neg_pi_lt_atan2 (y x : Real) : -pi < atan2 y x

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
