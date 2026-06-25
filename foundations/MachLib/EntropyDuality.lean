import MachLib.Differentiation
import MachLib.Log
import MachLib.Linarith

/-
MachLib.EntropyDuality — the exp ↔ entropy Legendre duality, machine-checked.

Verifies the convex-analytic core of the EML information-theory frontiers
(`monogate-research` T3.D convex analysis / T1.B information theory): the
Legendre transform pairs the EML-1 exponential with the EML-2 entropy gate
`H(y) = y·log y − y`. Two facts ground the pairing:

  • `entropy_deriv`     `H'(y) = log y`   — the entropy's derivative is `log`,
    the inverse of `exp`'s derivative. THIS is what makes `(exp, entropy)` a
    Legendre-dual pair: the dual potential's gradient inverts the primal's.
  • `fenchel_young_eq`  `x·exp x = exp x + H(exp x)` — the Fenchel–Young
    inequality holds with EQUALITY at the conjugacy point `y = exp x`, the
    defining property of a Legendre dual pair (equality ⟺ tangency).

Together they ground "MaxEnt selects the exponential family because `exp` is the
convex dual of entropy" (T1.B) in a Lean proof — a second EML frontier verified
beyond the T1.A Sturm spine. Both `#print axioms`-clean: MachLib foundations
only, no `sorryAx`.

NEXT (documented, not yet proved): the global Fenchel–Young inequality
`x·y ≤ exp x + H(y)` for `y > 0`. All pieces are in MachLib — the tangent line
`one_add_le_exp : 1 + t ≤ exp t`, `mul_le_mul_of_nonneg_left`, `exp_sub`,
`exp_log`, `mul_div_cancel'`, `add_le_add_right`. Sketch: apply `one_add_le_exp`
at `t = x − log y`, multiply by `y ≥ 0`, simplify `y·exp(x−log y) = exp x` (via
`exp_sub` + `exp_log` + `mul_div_cancel'`), then add `(y·log y − y)` to both
sides. Left unproved here only because the two linear-rearrangement identities it
needs fall outside `mach_ring`'s `a+(b−a)=b` fragment and want a hand proof.
-/

namespace MachLib
namespace Real

/-- The convex conjugate of `exp`: the (negative) entropy `H(y) = y·log y − y`.
Its Legendre transform recovers `exp`, and `exp`'s recovers it (see T3.D). -/
noncomputable def entropy (y : Real) : Real := y * Real.log y - y

/-- **The entropy's derivative is `log`.** `H'(y) = log y` for `y > 0`. Since
`exp'(x) = exp x` and `log` is `exp`'s inverse, the dual potential's derivative
(`log`) inverts the primal's (`exp`) — the analytic signature of a Legendre pair. -/
theorem entropy_deriv (y : Real) (hy : 0 < y) :
    HasDerivAt entropy (Real.log y) y := by
  -- H = (fun z => z * log z) − (fun z => z); product rule then difference rule.
  have hmul : HasDerivAt (fun z => z * Real.log z)
      (1 * Real.log y + y * (1 / y)) y :=
    HasDerivAt_mul (fun z => z) Real.log 1 (1 / y) y
      (HasDerivAt_id y) (HasDerivAt_log_pos y hy)
  have hsub : HasDerivAt (fun z => z * Real.log z - z)
      ((1 * Real.log y + y * (1 / y)) - 1) y :=
    HasDerivAt_sub (fun z => z * Real.log z) (fun z => z)
      (1 * Real.log y + y * (1 / y)) 1 y hmul (HasDerivAt_id y)
  -- the derivative value collapses to `log y`:  1·log y + y·(1/y) − 1 = log y.
  have hval : (1 * Real.log y + y * (1 / y)) - 1 = Real.log y := by
    rw [one_mul_thm, mul_div_cancel' (ne_of_gt hy)]; mach_ring
  rw [hval] at hsub
  exact hsub

/-- **Fenchel–Young equality at the conjugacy point.** At `y = exp x` the
inequality `x·y ≤ exp x + H(y)` holds with EQUALITY. This pins `exp` and
`entropy` as Legendre duals (equality in Fenchel–Young ⟺ `y ∈ ∂(exp)(x)`). -/
theorem fenchel_young_eq (x : Real) :
    x * Real.exp x = Real.exp x + entropy (Real.exp x) := by
  unfold entropy
  rw [log_exp]
  -- goal: x·exp x = exp x + (exp x·x − exp x); the ±exp x cancel, then commute.
  have hRHS : Real.exp x + (Real.exp x * x - Real.exp x) = Real.exp x * x := by
    rw [sub_def, add_comm (Real.exp x * x) (-(Real.exp x)), ← add_assoc,
        add_neg, zero_add]
  rw [hRHS, mul_comm x (Real.exp x)]

end Real
end MachLib
