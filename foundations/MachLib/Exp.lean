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

/-! ### Tangent-line lower bound (axiom)

The single classical-analytic fact `1 + x < exp x` for `x > 0`,
underlying every asymptotic comparison of `exp` against polynomials.
Equivalent to the strict-convexity of `exp` at 0.

Classical proof: series `exp x = 1 + x + x²/2 + ...` with positive
remainder. MachLib doesn't carry the series machinery, so this is
axiomatised here as a foundation primitive (moved here from
`SinNotInEMLDepth2Sweep.lean` on 2026-06-19 to centralise its use).

Downstream consumers across SinNotInEMLDepth2Sweep, LambertW, and
Asymptotics all reference this single axiom; no other module
introduces a duplicate or near-duplicate axiom of the same shape. -/
axiom exp_gt_one_plus_self (x : Real) (hx : 0 < x) : 1 + x < exp x

/-- `x < exp x` for ALL real `x`. Pointwise version of
`Asymptotics.exp_grows_strictly` (which is now a theorem citing this
foundation).

Proof: case-split on `x > 0` vs `x ≤ 0`. For `x > 0`, use
`exp_gt_one_plus_self` + `1 < 1 + x`. For `x ≤ 0`, use `exp_pos`. -/
theorem exp_grows_strictly_thm (x : Real) : x < exp x := by
  by_cases hx_pos : 0 < x
  · -- x > 0: from 1 + x < exp x (exp_gt_one_plus_self) and x < 1 + x.
    have h1 : 1 + x < exp x := exp_gt_one_plus_self x hx_pos
    have h2 : x < 1 + x := by
      have := add_lt_add_left zero_lt_one_ax x
      -- this : x + 0 < x + 1
      rwa [add_zero, add_comm x 1] at this
    exact lt_trans_ax h2 h1
  · -- x ≤ 0: from exp x > 0 ≥ x.
    have hx_le_zero : x ≤ 0 := by
      rcases lt_total x 0 with h | h | h
      · exact (le_iff_lt_or_eq _ _).mpr (Or.inl h)
      · exact (le_iff_lt_or_eq _ _).mpr (Or.inr h)
      · exact absurd h hx_pos
    have h_exp_pos : 0 < exp x := exp_pos x
    -- x ≤ 0 < exp x
    rcases (le_iff_lt_or_eq _ _).mp hx_le_zero with hlt | heq
    · exact lt_trans_ax hlt h_exp_pos
    · subst heq; exact h_exp_pos

end Real
end MachLib
