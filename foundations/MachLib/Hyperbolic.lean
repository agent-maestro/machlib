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
-- `cosh_pos` was an axiom here until 2026-10-04; it is a theorem below `cosh_eq`, which proves it.
/-- `cosh x ≥ 1` for all real `x`, with equality at `x = 0`. Follows from
`pythagorean_hyp` (cosh² = 1 + sinh² ≥ 1) plus `cosh_pos`, but deriving it
needs square-monotonicity infrastructure `MachLib.Basic` doesn't expose; held
as an axiom in the same spirit as `cosh_pos`. True in any standard ordered
field. Closes the Forge `cosh_geq_one` kernel obligation. C-245. -/
axiom cosh_ge_one (x : Real) : 1 ≤ cosh x
-- `sinh_add`/`cosh_add` PROMOTED to theorems in `HyperbolicId.lean` (2026-06-27
-- audit) — derived from `sinh_eq`/`cosh_eq` + `exp_add` by clearing `1/2` factors
-- with `mul_left_cancel`. With them, sinh/cosh are now ENTIRELY reduced to `exp`
-- except positivity (`cosh_pos`/`cosh_ge_one`).
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
