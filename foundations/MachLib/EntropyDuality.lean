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
  • `fenchel_young`     `x·y ≤ exp x + H(y)` (for `y > 0`) — the GLOBAL
    Fenchel–Young inequality, i.e. `−H` IS the convex conjugate of `exp`. The
    engine is the `exp` tangent line `1 + t ≤ exp t` at `t = x − log y`, scaled
    by `y > 0`. This is the inequality that makes MaxEnt work: among the
    distributions matching the moments, the exponential family is the unique
    minimiser because `exp` and `entropy` are convex duals (T1.B).

Together they ground "MaxEnt selects the exponential family because `exp` is the
convex dual of entropy" (T1.B) in a Lean proof — a second EML frontier verified
beyond the T1.A Sturm spine. All three `#print axioms`-clean: MachLib
foundations only, no `sorryAx`. (`fenchel_young`'s scaled-tangent rearrangement
`(A−B)+(B+(C−A))=C` is outside `mach_ring`'s fragment, so it is distributed by
hand and cancelled with the additive primitives — see the `helper` lemma.)
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

/-- **The Fenchel–Young inequality for the `(exp, entropy)` pair.** For `y > 0`,
`x·y ≤ exp x + H(y)` — the GLOBAL statement that `exp` and `entropy` are convex
conjugates (with equality at `y = exp x`, by `fenchel_young_eq`). The engine is
the `exp` tangent line `1 + t ≤ exp t` evaluated at `t = x − log y`, scaled by
`y > 0` and pushed through `y·exp(x − log y) = exp x`. This is the inequality
that makes MaxEnt work: `−H` is the convex conjugate of `exp`, so among the
distributions matching the moments the exponential family is the unique
minimiser (T1.B). -/
theorem fenchel_young (x y : Real) (hy : 0 < y) :
    x * y ≤ Real.exp x + entropy y := by
  unfold entropy
  -- exp tangent line at the point t = x − log y:  1 + t ≤ exp t.
  have htan : 1 + (x - Real.log y) ≤ Real.exp (x - Real.log y) :=
    one_add_le_exp (x - Real.log y)
  -- scale by y ≥ 0:
  have hmul : y * (1 + (x - Real.log y)) ≤ y * Real.exp (x - Real.log y) :=
    mul_le_mul_of_nonneg_left htan (le_of_lt hy)
  -- collapse the right side:  y · exp(x − log y) = exp x.
  have hexp : y * Real.exp (x - Real.log y) = Real.exp x := by
    rw [exp_sub, exp_log hy, mul_div_cancel' (ne_of_gt hy)]
  rw [hexp] at hmul
  -- add (y·log y − y) on the left; the scaled tangent collapses to x·y. The
  -- rearrangement is the `(A−B) + (B + (C−A)) = C` cancellation, which is
  -- outside mach_ring's fragment, so we distribute by hand then cancel.
  have helper : ∀ A B C : Real, (A + -B) + (B + (C + -A)) = C := by
    intro A B C
    rw [add_assoc, ← add_assoc (-B) B (C + -A), neg_add_self, zero_add,
        add_comm C (-A), ← add_assoc A (-A) C, add_neg, zero_add]
  have hid : (y * Real.log y - y) + y * (1 + (x - Real.log y)) = x * y := by
    rw [mul_distrib y 1 (x - Real.log y), mul_one_ax,
        sub_def x (Real.log y), mul_distrib y x (-Real.log y),
        mul_neg y (Real.log y), sub_def (y * Real.log y) y, mul_comm x y]
    exact helper (y * Real.log y) y (y * x)
  have hfin := add_le_add_left hmul (y * Real.log y - y)
  rw [hid, add_comm (y * Real.log y - y) (Real.exp x)] at hfin
  exact hfin

end Real
end MachLib
