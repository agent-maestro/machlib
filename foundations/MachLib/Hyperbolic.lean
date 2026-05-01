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

axiom sinh_zero  : sinh 0 = 0
axiom cosh_zero  : cosh 0 = 1
axiom sinh_neg   (x : Real) : sinh (-x) = -(sinh x)
axiom cosh_neg   (x : Real) : cosh (-x) = cosh x
axiom cosh_pos   (x : Real) : 0 < cosh x
axiom sinh_add   (x y : Real) :
  sinh (x + y) = sinh x * cosh y + cosh x * sinh y
axiom cosh_add   (x y : Real) :
  cosh (x + y) = cosh x * cosh y + sinh x * sinh y
axiom pythagorean_hyp (x : Real) :
  cosh x * cosh x - sinh x * sinh x = 1

/-! ### ELC-form decomposition

The headline ELC identity: every hyperbolic value is an arithmetic
combination of two exp-applications. This is what makes
HyperbolicPreservation work — the proof that hyperbolic functions
preserve the ELC field reduces to applying these two axioms and
then noting that exp itself preserves ELC. -/

axiom sinh_eq (x : Real) : sinh x = (exp x - exp (-x)) / (1 + 1)
axiom cosh_eq (x : Real) : cosh x = (exp x + exp (-x)) / (1 + 1)

/-! ### Conversion identities between hyperbolic and exp

These are algebraic consequences of `sinh_eq` / `cosh_eq` that
require ring-style manipulation (cancel halves, distribute over
sums) — without a `ring` tactic in MachLib those proofs become
many-line manual rewrites. We axiomatise them in the same spirit
as `sin_add` / `cos_add` in `Trig`, and revisit as derived lemmas
once MachLib gains a ring tactic. -/

axiom cosh_add_sinh_eq_exp (x : Real) :
  cosh x + sinh x = exp x
axiom cosh_sub_sinh_eq_exp_neg (x : Real) :
  cosh x - sinh x = exp (-x)
axiom two_sinh_eq_exp_sub (x : Real) :
  (1 + 1) * sinh x = exp x - exp (-x)
axiom two_cosh_eq_exp_add (x : Real) :
  (1 + 1) * cosh x = exp x + exp (-x)

/-! ### Subtraction + double-angle identities

Same ring-algebra constraint as the conversion identities — these
fall out of `sinh_add` / `cosh_add` plus parity, but the
distribution chain wants `ring` to be readable. -/

axiom sinh_sub (x y : Real) :
  sinh (x - y) = sinh x * cosh y - cosh x * sinh y
axiom cosh_sub (x y : Real) :
  cosh (x - y) = cosh x * cosh y - sinh x * sinh y
axiom sinh_two_mul (x : Real) :
  sinh ((1 + 1) * x) = (1 + 1) * sinh x * cosh x
axiom cosh_two_mul (x : Real) :
  cosh ((1 + 1) * x) = cosh x * cosh x + sinh x * sinh x

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
