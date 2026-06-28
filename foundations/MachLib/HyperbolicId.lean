import MachLib.Hyperbolic
import MachLib.Ring
import MachLib.MPolyRing
import MachLib.FieldLemmas

/-!
# Hyperbolic identities — derived consequences (2026-06-27 audit)

`Hyperbolic.lean` sits *upstream* of `Ring`/`MPolyRing` (because `Ring` imports
`Forge` imports `Hyperbolic`), so it has no ring tactic — which is why a batch of
its identities were stated as axioms even though they follow algebraically from
the addition/negation generators. This module sits downstream of both
`Hyperbolic` and the ring tactics, so it PROVES them and the upstream axioms are
removed. (Their sole consumer, `HyperbolicPreservation`, imports this.)

Each derives only from axioms that REMAIN primitive in `Hyperbolic`
(`sinh_add`/`cosh_add`/`sinh_neg`/`cosh_neg`, the `cosh±sinh = exp(±x)` forms,
`exp_add`/`exp_zero`) — no circularity.

`sorryAx`-free.
-/

namespace MachLib
namespace Real

/-! ### exp-conversions, derived from the defining `sinh_eq`/`cosh_eq` + the
half-cancellation kit (`FieldLemmas`). These were axioms in `Hyperbolic` only
because that file is upstream of the ring/field tactics. -/

/-- `sinh 0 = 0`. From `sinh_eq` + `exp_zero` + `0/2 = 0`. -/
theorem sinh_zero : sinh 0 = 0 := by
  rw [sinh_eq 0, neg_zero, exp_zero, show (1 : Real) - 1 = 0 from by mach_ring,
      zero_div_of_ne_zero two_ne_zero]

/-- `cosh 0 = 1`. From `cosh_eq` + `exp_zero` + `2/2 = 1`. -/
theorem cosh_zero : cosh 0 = 1 := by
  rw [cosh_eq 0, neg_zero, exp_zero, self_div two_ne_zero]

/-- `sinh (−x) = −sinh x` (odd). From `sinh_eq` + `neg_div`. -/
theorem sinh_neg (x : Real) : sinh (-x) = -(sinh x) := by
  rw [sinh_eq (-x), sinh_eq x, neg_div two_ne_zero, neg_neg_helper]
  show (exp (-x) - exp x) / (1 + 1) = (-(exp x - exp (-x))) / (1 + 1)
  rw [show -(exp x - exp (-x)) = exp (-x) - exp x from by mach_mpoly [exp x, exp (-x)]]

/-- `cosh (−x) = cosh x` (even). From `cosh_eq`. -/
theorem cosh_neg (x : Real) : cosh (-x) = cosh x := by
  rw [cosh_eq (-x), cosh_eq x, neg_neg_helper]
  show (exp (-x) + exp x) / (1 + 1) = (exp x + exp (-x)) / (1 + 1)
  rw [show exp (-x) + exp x = exp x + exp (-x) from by mach_mpoly [exp x, exp (-x)]]

/-- `2 · sinh x = exp x − exp(−x)`. Half-cancellation of `sinh_eq`. -/
theorem two_sinh_eq_exp_sub (x : Real) : (1 + 1) * sinh x = exp x - exp (-x) := by
  rw [sinh_eq x, mul_div_cancel_left two_ne_zero]

/-- `2 · cosh x = exp x + exp(−x)`. -/
theorem two_cosh_eq_exp_add (x : Real) : (1 + 1) * cosh x = exp x + exp (-x) := by
  rw [cosh_eq x, mul_div_cancel_left two_ne_zero]

/-- `cosh x + sinh x = exp x`. -/
theorem cosh_add_sinh_eq_exp (x : Real) : cosh x + sinh x = exp x := by
  rw [cosh_eq x, sinh_eq x, div_add_div_same two_ne_zero,
      show (exp x + exp (-x)) + (exp x - exp (-x)) = (1 + 1) * exp x from by
        mach_mpoly [exp x, exp (-x)],
      mul_div_cancel_left' two_ne_zero]

/-- `cosh x − sinh x = exp(−x)`. -/
theorem cosh_sub_sinh_eq_exp_neg (x : Real) : cosh x - sinh x = exp (-x) := by
  rw [cosh_eq x, sinh_eq x, div_sub_div_same two_ne_zero,
      show (exp x + exp (-x)) - (exp x - exp (-x)) = (1 + 1) * exp (-x) from by
        mach_mpoly [exp x, exp (-x)],
      mul_div_cancel_left' two_ne_zero]

/-! ### the addition formulas — derived from the conversions (full reduction to `exp`).
Clear the `1/2` factors by cancelling `(1+1)²` (`mul_left_cancel`), express every
`(1+1)·sinh`/`(1+1)·cosh` via the conversions, and finish with `exp_add` + ring. -/

/-- `sinh (x + y) = sinh x cosh y + cosh x sinh y`. -/
theorem sinh_add (x y : Real) : sinh (x + y) = sinh x * cosh y + cosh x * sinh y := by
  apply mul_left_cancel (mul_ne_zero two_ne_zero two_ne_zero)
  rw [show (1 + 1) * (1 + 1) * sinh (x + y) = (1 + 1) * ((1 + 1) * sinh (x + y)) from by mach_ring,
      two_sinh_eq_exp_sub (x + y),
      show exp (x + y) = exp x * exp y from exp_add x y,
      show exp (-(x + y)) = exp (-x) * exp (-y) from by rw [neg_add, exp_add],
      show (1 + 1) * (1 + 1) * (sinh x * cosh y + cosh x * sinh y)
         = ((1 + 1) * sinh x) * ((1 + 1) * cosh y)
         + ((1 + 1) * cosh x) * ((1 + 1) * sinh y) from by mach_ring,
      two_sinh_eq_exp_sub x, two_cosh_eq_exp_add y, two_cosh_eq_exp_add x, two_sinh_eq_exp_sub y]
  mach_mpoly [exp x, exp (-x), exp y, exp (-y)]

/-- `cosh (x + y) = cosh x cosh y + sinh x sinh y`. -/
theorem cosh_add (x y : Real) : cosh (x + y) = cosh x * cosh y + sinh x * sinh y := by
  apply mul_left_cancel (mul_ne_zero two_ne_zero two_ne_zero)
  rw [show (1 + 1) * (1 + 1) * cosh (x + y) = (1 + 1) * ((1 + 1) * cosh (x + y)) from by mach_ring,
      two_cosh_eq_exp_add (x + y),
      show exp (x + y) = exp x * exp y from exp_add x y,
      show exp (-(x + y)) = exp (-x) * exp (-y) from by rw [neg_add, exp_add],
      show (1 + 1) * (1 + 1) * (cosh x * cosh y + sinh x * sinh y)
         = ((1 + 1) * cosh x) * ((1 + 1) * cosh y)
         + ((1 + 1) * sinh x) * ((1 + 1) * sinh y) from by mach_ring,
      two_cosh_eq_exp_add x, two_cosh_eq_exp_add y, two_sinh_eq_exp_sub x, two_sinh_eq_exp_sub y]
  mach_mpoly [exp x, exp (-x), exp y, exp (-y)]

/-! ### identities derived from the addition formulas + the conversions above. -/

/-- `sinh (2x) = 2 · sinh x · cosh x`. From `sinh_add x x`. -/
theorem sinh_two_mul (x : Real) : sinh ((1 + 1) * x) = (1 + 1) * sinh x * cosh x := by
  have e : (1 + 1) * x = x + x := by mach_mpoly [x]
  rw [e, sinh_add]; mach_ring

/-- `cosh (2x) = cosh²x + sinh²x`. From `cosh_add x x`. -/
theorem cosh_two_mul (x : Real) : cosh ((1 + 1) * x) = cosh x * cosh x + sinh x * sinh x := by
  have e : (1 + 1) * x = x + x := by mach_mpoly [x]
  rw [e, cosh_add]

/-- `sinh (x − y) = sinh x cosh y − cosh x sinh y`. From `sinh_add x (−y)` + odd/even. -/
theorem sinh_sub (x y : Real) : sinh (x - y) = sinh x * cosh y - cosh x * sinh y := by
  rw [sub_def, sinh_add, sinh_neg, cosh_neg]
  show sinh x * cosh y + cosh x * (-(sinh y)) = sinh x * cosh y - cosh x * sinh y
  mach_mpoly [sinh x, cosh x, sinh y, cosh y]

/-- `cosh (x − y) = cosh x cosh y − sinh x sinh y`. From `cosh_add x (−y)` + odd/even. -/
theorem cosh_sub (x y : Real) : cosh (x - y) = cosh x * cosh y - sinh x * sinh y := by
  rw [sub_def, cosh_add, sinh_neg, cosh_neg]
  show cosh x * cosh y + sinh x * (-(sinh y)) = cosh x * cosh y - sinh x * sinh y
  mach_mpoly [sinh x, cosh x, sinh y, cosh y]

/-- **Hyperbolic Pythagorean** `cosh²x − sinh²x = 1`. From the difference of squares
`(cosh+sinh)(cosh−sinh) = exp x · exp(−x) = exp 0 = 1`. -/
theorem pythagorean_hyp (x : Real) : cosh x * cosh x - sinh x * sinh x = 1 := by
  have h1 := cosh_add_sinh_eq_exp x
  have h2 := cosh_sub_sinh_eq_exp_neg x
  have hprod : (cosh x + sinh x) * (cosh x - sinh x) = exp x * exp (-x) := by rw [h1, h2]
  have hexp : exp x * exp (-x) = 1 := by
    rw [← exp_add, show x + (-x) = 0 from by mach_ring, exp_zero]
  have hdiff : (cosh x + sinh x) * (cosh x - sinh x) = cosh x * cosh x - sinh x * sinh x := by
    mach_mpoly [cosh x, sinh x]
  rw [hdiff, hexp] at hprod; exact hprod

end Real
end MachLib
