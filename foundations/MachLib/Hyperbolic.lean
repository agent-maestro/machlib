import MachLib.Exp
import MachLib.Trig

/-
MachLib.Hyperbolic — sinh, cosh, axiomatised. Same delegation
argument as Exp / Trig: agents reasoning about hyperbolic
expressions need the *facts* (Pythagorean, addition formulas,
ELC decomposition into exp), not the analytic construction.

`tanh` is already declared in `MachLib.Trig` (along with the other
analytic primitives the forge backends emit); this file adds the
linking axiom `tanh_eq_sinh_div_cosh` rather than redefining tanh.

A future contributor wanting to refactor sinh/cosh into
`(exp x ± exp(-x))/2` definitions can do so without breaking any
downstream theorem — every theorem here uses only the axioms below.
-/

namespace MachLib
namespace Real

/-! ### Function declarations -/

axiom sinh : Real → Real
axiom cosh : Real → Real

/-! ### Defining axioms

Mirrors `Trig`'s axiom budget: nine axioms cover sign, addition,
Pythagorean identity, and the ELC-form decomposition that ties
sinh / cosh to the exponential. -/

-- `sinh_zero`/`cosh_zero`/`sinh_neg`/`cosh_neg` PROMOTED to theorems in
-- `HyperbolicId.lean` (2026-06-27 audit; from `sinh_eq`/`cosh_eq` + FieldLemmas).
-- `cosh_pos` was an axiom here until 2026-10-04 and `cosh_ge_one` until 2026-10-05; both are theorems below
-- `cosh_eq`, which proves them.
-- `sinh_add`/`cosh_add` PROMOTED to theorems in `HyperbolicId.lean` (2026-06-27
-- audit) — derived from `sinh_eq`/`cosh_eq` + `exp_add` by clearing `1/2` factors
-- with `mul_left_cancel`. With them, and `cosh_pos`/`cosh_ge_one` proved below, sinh and cosh are ENTIRELY
-- reduced to `exp` through their defining equations.
-- `pythagorean_hyp` PROMOTED to a theorem in `HyperbolicId.lean` (2026-06-27 audit;
-- difference-of-squares from `cosh±sinh = exp(±x)` + `exp_add`/`exp_zero`).

/-! ### ELC-form decomposition

The headline ELC identity: every hyperbolic value is an arithmetic
combination of two exp-applications. This is what makes
HyperbolicPreservation work — the proof that hyperbolic functions
preserve the ELC field reduces to applying these two axioms and
then noting that exp itself preserves ELC. -/

axiom sinh_eq (x : Real) : sinh x = (exp x - exp (-x)) / (1 + 1)
axiom cosh_eq (x : Real) : cosh x = (exp x + exp (-x)) / (1 + 1)

/-- `0 < cosh x`: `(exp x + exp (-x)) / 2` with both exponentials positive. A theorem since 2026-10-04. -/
theorem cosh_pos (x : Real) : 0 < cosh x := by
  have hsum : 0 < exp x + exp (-x) := by
    have h := add_lt_add_left (exp_pos (-x)) (exp x)
    rw [add_zero] at h
    exact lt_trans_ax (exp_pos x) h
  have htwo : (0 : Real) < 1 + 1 := by
    have h := add_lt_add_left zero_lt_one_ax (1 : Real)
    rw [add_zero] at h
    exact lt_trans_ax zero_lt_one_ax h
  rw [cosh_eq, div_def _ _ (ne_of_gt htwo)]
  exact mul_pos hsum (one_div_pos_of_pos htwo)

/-! ### `cosh x ≥ 1`

An axiom until 2026-10-05, whose docstring said deriving it "needs square-monotonicity infrastructure `MachLib.Basic`
doesn't expose". It needs one fact about squares, proved here. With `a = exp x` and `b = exp (-x)`, `b * a = 1`, so
`b * (a - 1)² = b a² - 2 b a + b = a - 2 + b`: a positive number times a square is `a + b - 2`, and
`cosh x = (a + b) / 2`. The helpers are field algebra at `Basic`'s level: `Hyperbolic` sits below `Ring`, so there
is no ring tactic here, and `ac_rfl` does the rearranging. -/

private theorem neg_unique_hyp {x y : Real} (h : x + y = 0) : y = -x := by
  have hc : -x + (x + y) = -x + 0 := by rw [h]
  rw [← add_assoc, neg_add_self, zero_add, add_zero] at hc
  exact hc

private theorem mul_neg_hyp (a b : Real) : a * -b = -(a * b) := by
  have h : a * b + a * -b = 0 := by rw [← mul_distrib, add_neg, mul_zero]
  exact neg_unique_hyp h

private theorem neg_neg_hyp (a : Real) : -(-a) = a := (neg_unique_hyp (neg_add_self a)).symm

private theorem neg_add_hyp (a b : Real) : -(a + b) = -a + -b := by
  have h : (a + b) + (-a + -b) = 0 := by
    rw [show (a + b) + (-a + -b) = (a + -a) + (b + -b) by ac_rfl, add_neg, add_neg, add_zero]
  exact (neg_unique_hyp h).symm

private theorem le_of_lt_hyp {a b : Real} (h : a < b) : a ≤ b := (le_iff_lt_or_eq a b).mpr (Or.inl h)

private theorem le_refl_hyp (a : Real) : a ≤ a := (le_iff_lt_or_eq a a).mpr (Or.inr rfl)

/-- A square is not negative. -/
private theorem mul_self_nonneg_hyp (t : Real) : 0 ≤ t * t := by
  rcases lt_total 0 t with hpos | hzero | hneg
  · exact le_of_lt_hyp (mul_pos hpos hpos)
  · rw [← hzero, mul_zero]
    exact le_refl_hyp 0
  · have hny : 0 < -t := by
      have h := add_lt_add_left hneg (-t)
      rwa [neg_add_self, add_zero] at h
    have hp := mul_pos hny hny
    rw [mul_neg_hyp, mul_comm (-t) t, mul_neg_hyp, neg_neg_hyp] at hp
    exact le_of_lt_hyp hp

/-- `1 ≤ cosh x`, with equality at `x = 0`. Closes the Forge `cosh_geq_one` kernel obligation (C-245). -/
theorem cosh_ge_one (x : Real) : 1 ≤ cosh x := by
  have hab : exp (-x) * exp x = 1 := exp_neg_self_mul x
  have hb : 0 < exp (-x) := exp_pos (-x)
  have hsq : (exp x + -1) * (exp x + -1) = exp x * exp x + -exp x + (-exp x + 1) := by
    rw [mul_distrib (exp x + -1) (exp x) (-1), mul_comm (exp x + -1) (exp x),
      mul_distrib (exp x) (exp x) (-1), mul_neg_hyp, mul_one_ax, mul_neg_hyp, mul_one_ax, neg_add_hyp,
      neg_neg_hyp]
  -- the certificate: 2 + b (a - 1)² = a + b
  have hcert : 1 + 1 + exp (-x) * ((exp x + -1) * (exp x + -1)) = exp x + exp (-x) := by
    rw [hsq, mul_distrib (exp (-x)) (exp x * exp x + -exp x) (-exp x + 1),
      mul_distrib (exp (-x)) (exp x * exp x) (-exp x), mul_distrib (exp (-x)) (-exp x) 1,
      ← mul_assoc (exp (-x)) (exp x) (exp x), hab, one_mul_thm, mul_neg_hyp, hab, mul_one_ax,
      show 1 + 1 + (exp x + -1 + (-1 + exp (-x))) = exp x + exp (-x) + ((1 + -1) + (1 + -1)) by ac_rfl,
      add_neg, add_zero, add_zero]
  have hprod : 0 ≤ exp (-x) * ((exp x + -1) * (exp x + -1)) := by
    rcases (le_iff_lt_or_eq _ _).mp (mul_self_nonneg_hyp (exp x + -1)) with hlt | heq
    · exact le_of_lt_hyp (mul_pos hb hlt)
    · rw [← heq, mul_zero]
      exact le_refl_hyp 0
  have htwo : (0 : Real) < 1 + 1 := by
    have h := add_lt_add_left zero_lt_one_ax (1 : Real)
    rw [add_zero] at h
    exact lt_trans_ax zero_lt_one_ax h
  have hsum : 1 + 1 ≤ exp x + exp (-x) := by
    rw [← hcert]
    rcases (le_iff_lt_or_eq _ _).mp hprod with hlt | heq
    · have h := add_lt_add_left hlt (1 + 1)
      rw [add_zero] at h
      exact le_of_lt_hyp h
    · rw [← heq, add_zero]
      exact le_refl_hyp _
  rw [cosh_eq, div_def _ _ (ne_of_gt htwo)]
  rcases (le_iff_lt_or_eq _ _).mp hsum with hlt | heq
  · have h := mul_lt_mul_of_pos_right hlt (one_div_pos_of_pos htwo)
    rw [mul_inv _ (ne_of_gt htwo)] at h
    exact le_of_lt_hyp h
  · rw [← heq, mul_inv _ (ne_of_gt htwo)]
    exact le_refl_hyp 1

/-! ### Conversion identities between hyperbolic and exp

`cosh_add_sinh_eq_exp` / `cosh_sub_sinh_eq_exp_neg` / `two_sinh_eq_exp_sub` /
`two_cosh_eq_exp_add` PROMOTED to theorems in `HyperbolicId.lean` (2026-06-27
audit) — the "revisit as derived lemmas once MachLib gains a ring tactic" the old
comment promised. They are the half-cancellation consequences of `sinh_eq`/
`cosh_eq`, now proved with the `FieldLemmas` division kit downstream. -/

/-! ### Subtraction + double-angle identities

`sinh_sub` / `cosh_sub` / `sinh_two_mul` / `cosh_two_mul` PROMOTED to theorems in
`HyperbolicId.lean` (2026-06-27 audit) — they fall out of `sinh_add`/`cosh_add`
plus parity, and the "distribution chain wants `ring`" the old comment named is
now available downstream (`HyperbolicId` imports `Ring`/`MPolyRing`). -/

/-! ### Link to `Trig.tanh`

`tanh` is declared in `MachLib.Trig` (alongside `sqrt`, `atan2`,
etc.) with its own minimal axioms. Here we add the one identity
that ties it to sinh / cosh. -/

axiom tanh_eq_sinh_div_cosh (x : Real) :
  tanh x = sinh x / cosh x

/-! ### Derived lemmas

`cosh x ≠ 0`, used wherever a downstream proof divides by `cosh`. -/

theorem cosh_ne_zero (x : Real) : cosh x ≠ 0 :=
  ne_of_gt (cosh_pos x)

end Real
end MachLib
