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

And on the same tangent line, the information-theoretic floor:

  • `log_le_sub_one`   `log t ≤ t − 1` (`t > 0`) — `log` below its tangent at 1.
  • `gibbs_pointwise`  `p·log(q/p) ≤ q − p` (`p, q > 0`) — the pointwise content
    of **`KL(p‖q) ≥ 0`**: summing over `Σp = Σq = 1` gives `KL ≥ 0`, the reason
    relative entropy is bounded below. The sum is outside MachLib's scope; the
    pointwise bound (which IS the scaled `log` tangent) is the analytic heart.

All five ground "MaxEnt selects the exponential family because `exp` is the
convex dual of entropy, and relative entropy is bounded below" (T1.B) in a Lean
proof — a second EML frontier verified beyond the T1.A Sturm spine. Every one is
`#print axioms`-clean: MachLib foundations only, no `sorryAx`. (`fenchel_young`'s
scaled-tangent rearrangement `(A−B)+(B+(C−A))=C` is outside `mach_ring`'s
fragment, so it is distributed by hand and cancelled with the additive
primitives — see the `helper` lemma.)
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

/-! ### Gibbs' inequality / `KL ≥ 0`

The information-theoretic heart of T1.B: relative entropy is bounded below. It
rests on the SAME `exp` tangent line as the Fenchel–Young inequality above, in
its `log` form `log t ≤ t − 1`. -/

/-- **The log tangent line.** `log t ≤ t − 1` for `t > 0` — `log` lies below its
tangent at `1`. The dual of the `exp` tangent line `1 + s ≤ exp s`
(`one_add_le_exp`), pulled back through `exp_log`. -/
theorem log_le_sub_one {t : Real} (ht : 0 < t) : Real.log t ≤ t - 1 := by
  have h : 1 + Real.log t ≤ t := by
    have hx := one_add_le_exp (Real.log t)
    rwa [exp_log ht] at hx
  -- 1 + log t ≤ t  ⇒  log t ≤ t − 1, by adding −1 on the left and cancelling.
  have h2 := add_le_add_left h (-1)
  rw [← add_assoc, neg_add_self, zero_add, add_comm (-1) t, ← sub_def] at h2
  exact h2

/-- **Gibbs' inequality, pointwise.** For `p, q > 0`, `p·log(q/p) ≤ q − p`.
This is the per-term content of `KL(p‖q) ≥ 0`: summing over distributions with
`Σp = Σq = 1` gives `Σ p·log(q/p) ≤ 0`, i.e. `KL(p‖q) = Σ p·log(p/q) ≥ 0` — the
reason relative entropy (and hence MaxEnt) is bounded below (T1.B). The sum step
needs `Σp = Σq`, which is outside MachLib's elementary-function scope; the
pointwise bound proved here is the analytic heart (it IS the `log t ≤ t − 1`
tangent, scaled). -/
theorem gibbs_pointwise {p q : Real} (hp : 0 < p) (hq : 0 < q) :
    p * Real.log (q / p) ≤ q - p := by
  have hqp : 0 < q / p := div_pos_of_pos_pos hq hp
  have htan : Real.log (q / p) ≤ q / p - 1 := log_le_sub_one hqp
  have hmul : p * Real.log (q / p) ≤ p * (q / p - 1) :=
    mul_le_mul_of_nonneg_left htan (le_of_lt hp)
  -- p·(q/p − 1) = q − p  (distribute, cancel p·(q/p)=q).
  have hsimp : p * (q / p - 1) = q - p := by
    rw [sub_def (q / p) 1, mul_distrib, mul_neg, mul_one_ax,
        mul_div_cancel' (ne_of_gt hp), ← sub_def q p]
  rw [hsimp] at hmul
  exact hmul

end Real
end MachLib
