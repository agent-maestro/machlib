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

The algebraic and order laws MachLib assumes of `exp`. With the field
axioms in `Basic` they give everything MachLib needs about `exp` short
of calculus. They do NOT single out base `e`: `b^x` for any `b > 1`
satisfies all four.

Each one is independent of the other three over an ordered field:
`b^x` with `0 < b < 1` breaks only `exp_lt`; `exp_surj` is the existence
law `log` is defined from (`Log.lean`).

`exp_zero` was a fifth axiom here until 2026-10-04 and is a theorem
below: it follows from `exp_add` and `exp_pos` (the owner's axiom audit:
a law the others prove is not assumed). So, since the muses' E round the
same day, is `exp_pos`: from `exp_add` and `exp_surj`. -/

axiom exp_add     (x y : Real) : exp (x + y) = exp x * exp y
axiom exp_lt      {x y : Real} : x < y → exp x < exp y
axiom exp_surj    : ∀ y : Real, 0 < y → ∃ x : Real, exp x = y

/-- `exp x ≠ 0`: were it `0`, `exp z = exp (x + (z - x)) = exp x * exp (z - x) = 0` for EVERY `z`, and
`exp_surj` gives some `z` with `exp z = 1`. -/
private theorem exp_ne_zero_b (x : Real) : exp x ≠ 0 := by
  intro h0
  obtain ⟨z, hz⟩ := exp_surj 1 zero_lt_one_ax
  have hsum : x + (z - x) = z := by
    rw [sub_def, add_comm z (-x), ← add_assoc, add_neg, zero_add]
  have he := exp_add x (z - x)
  rw [hsum, h0, zero_mul] at he
  rw [he] at hz
  exact zero_ne_one_ax hz

/-- `x/2 + x/2 = x`, with `2 = 1 + 1`. -/
private theorem half_add_half_b (x : Real) : x * (1 / (1 + 1)) + x * (1 / (1 + 1)) = x := by
  have h2 : (1 : Real) + 1 ≠ 0 := by
    have h := add_lt_add_left zero_lt_one_ax (1 : Real)
    rw [add_zero] at h
    exact ne_of_gt (lt_trans_ax zero_lt_one_ax h)
  rw [← mul_distrib]
  have hh : (1 : Real) / (1 + 1) + 1 / (1 + 1) = 1 := by
    have e : (1 : Real) / (1 + 1) * (1 + 1) = 1 / (1 + 1) + 1 / (1 + 1) := by
      rw [mul_distrib, mul_one_ax]
    rw [← e, mul_comm, mul_inv _ h2]
  rw [hh, mul_one_ax]

private theorem mul_neg_e (a b : Real) : a * -b = -(a * b) := by
  have h : a * b + a * -b = 0 := by rw [← mul_distrib, add_neg, mul_zero]
  have hc : -(a * b) + (a * b + a * -b) = -(a * b) + 0 := by rw [h]
  rw [← add_assoc, neg_add_self, zero_add, add_zero] at hc
  exact hc

private theorem neg_neg_e (a : Real) : -(-a) = a := by
  have h : -a + -(-a) = 0 := add_neg (-a)
  have hc : a + (-a + -(-a)) = a + 0 := by rw [h]
  rw [← add_assoc, add_neg, zero_add, add_zero] at hc
  exact hc

/-- A nonzero square is positive. -/
private theorem mul_self_pos_e {y : Real} (hy : y ≠ 0) : 0 < y * y := by
  rcases lt_total 0 y with hpos | hzero | hneg
  · exact mul_pos hpos hpos
  · exact absurd hzero.symm hy
  · have hny : 0 < -y := by
      have h := add_lt_add_left hneg (-y)
      rwa [neg_add_self, add_zero] at h
    have hp := mul_pos hny hny
    have e : -y * -y = y * y := by rw [mul_neg_e, mul_comm (-y) y, mul_neg_e, neg_neg_e]
    rwa [e] at hp

/-- `0 < exp x`: `exp x = exp (x/2) * exp (x/2)`, the square of a number `exp_surj` keeps from being `0`.
An axiom until 2026-10-04. -/
theorem exp_pos (x : Real) : 0 < exp x := by
  have e : exp x = exp (x * (1 / (1 + 1))) * exp (x * (1 / (1 + 1))) := by
    rw [← exp_add, half_add_half_b]
  rw [e]
  exact mul_self_pos_e (exp_ne_zero_b _)

/-- `exp 0 = 1`, from `exp_add` and `exp_pos`: `exp 0 = exp (0 + 0) = exp 0 * exp 0`,
and `exp 0` is not zero, so it is `1`. -/
theorem exp_zero : exp 0 = 1 := by
  have hne : exp 0 ≠ 0 := ne_of_gt (exp_pos 0)
  have h : exp 0 = exp 0 * exp 0 := by
    have h0 := exp_add 0 0
    rw [add_zero] at h0
    exact h0
  have hinv : exp 0 * (1 / exp 0) = 1 := mul_inv (exp 0) hne
  calc exp 0 = exp 0 * 1 := (mul_one_ax _).symm
    _ = exp 0 * (exp 0 * (1 / exp 0)) := by rw [hinv]
    _ = (exp 0 * exp 0) * (1 / exp 0) := (mul_assoc _ _ _).symm
    _ = exp 0 * (1 / exp 0) := by rw [← h]
    _ = 1 := hinv

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

/-- `exp x ≤ 1` for `x ≤ 0`. Proved (no axiom) from `exp_monotone` +
`exp_zero`. Closes the complement-of-decay floor `1 - exp(-k) ≥ 0`
(exponential fog, saturation deficits) once `-k ≤ 0`. -/
theorem exp_le_one_of_nonpos {x : Real} (hx : x ≤ 0) : exp x ≤ 1 := by
  have h := exp_monotone hx
  rwa [exp_zero] at h

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

/-- The exponential tangent line: `1 + x ≤ exp x` for ALL real `x` (equality at
`x = 0`). The non-strict, unrestricted companion to `exp_gt_one_plus_self`
(which needs `0 < x`). Closes saturating-integral nonnegativity where the
argument is `≤ 0` — e.g. sprint distance `t − τ·(1 − e^{−t/τ}) ≥ 0`, which
reduces to `1 − e^{−u} ≤ u`. Sound (the graph of exp lies above every tangent;
this is the tangent at the origin). -/
axiom one_add_le_exp (x : Real) : 1 + x ≤ exp x

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
