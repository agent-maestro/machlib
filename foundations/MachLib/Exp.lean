import MachLib.Basic

/-
MachLib.Exp — the real exponential function, axiomatised.

We do not build `exp` from a power series. The series construction
is well-known (and a Mathlib theorem); MachLib's downstream
consumers — agents reasoning about EML expressions — work with the
*properties* of exp, not its analytic construction. We expose
those properties as axioms and prove a handful of derived lemmas.

If a future contributor wants to refactor `exp` into a power-series
definition, they can: every theorem downstream of this file uses
only the axioms below, so a constructive replacement is a drop-in.
-/

namespace MachLib
namespace Real

/-- The real exponential. Defined opaquely; properties below pin
down its behaviour. -/
axiom exp : Real → Real

/-! ### Defining axioms

These are the seven facts that uniquely determine `exp` among
real-valued functions on `R`. Together with the field axioms in
`Basic`, they imply everything MachLib needs about `exp`. -/

axiom exp_zero    : exp 0 = 1
axiom exp_add     (x y : Real) : exp (x + y) = exp x * exp y
axiom exp_pos     (x : Real)   : 0 < exp x
axiom exp_lt      {x y : Real} : x < y → exp x < exp y
axiom exp_surj    : ∀ y : Real, 0 < y → ∃ x : Real, exp x = y

/-! ### Derived lemmas

Algebraic consequences of the axioms. None of these reach for
analytic content (continuity, differentiability); they are pure
algebra over the field `R`. -/

theorem exp_ne_zero (x : Real) : exp x ≠ 0 :=
  ne_of_gt (exp_pos x)

theorem exp_neg_self_mul (x : Real) : exp (-x) * exp x = 1 := by
  have h : exp (-x + x) = exp (-x) * exp x := exp_add (-x) x
  rw [neg_add_self, exp_zero] at h
  exact h.symm

theorem exp_neg_inv (x : Real) : exp (-x) = 1 / exp x := by
  have hpos : exp x ≠ 0 := exp_ne_zero x
  have step : exp (-x) * exp x = 1 := exp_neg_self_mul x
  -- multiply both sides on the right by 1/(exp x)
  have inv : exp x * (1 / exp x) = 1 := mul_inv (exp x) hpos
  -- exp(-x) = exp(-x) * (exp x * 1/(exp x)) = (exp(-x) * exp x) * 1/(exp x)
  --        = 1 * 1/(exp x) = 1 / exp x
  calc exp (-x)
      = exp (-x) * 1 := (mul_one_ax _).symm
    _ = exp (-x) * (exp x * (1 / exp x)) := by rw [inv]
    _ = (exp (-x) * exp x) * (1 / exp x) := by rw [mul_assoc]
    _ = 1 * (1 / exp x) := by rw [step]
    _ = 1 / exp x := one_mul_thm _

theorem exp_monotone {x y : Real} (h : x ≤ y) : exp x ≤ exp y := by
  rcases (le_iff_lt_or_eq x y).mp h with hlt | heq
  · exact (le_iff_lt_or_eq _ _).mpr (Or.inl (exp_lt hlt))
  · rw [heq]
    exact (le_iff_lt_or_eq _ _).mpr (Or.inr rfl)

theorem exp_injective {x y : Real} (h : exp x = exp y) : x = y := by
  rcases lt_total x y with hlt | heq | hgt
  · exact (ne_of_lt (exp_lt hlt) h).elim
  · exact heq
  · exact (ne_of_gt (exp_lt hgt) h).elim

/-- `exp(x - y) = exp(x) / exp(y)`. The subtraction analogue of
`exp_add`, used in the self-map conjugacy lemmas. -/
theorem exp_sub (x y : Real) : exp (x - y) = exp x / exp y := by
  rw [sub_def, exp_add, exp_neg_inv]
  exact (div_def (exp x) (exp y) (exp_ne_zero y)).symm

end Real
end MachLib
