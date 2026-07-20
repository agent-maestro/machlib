import MachLib.WitnessResidualSimpleT1Application

/-!
# Pushing into the general case: `B` unrestricted, only `A` simple

Continuation of Option D, attempting the fully general case (`T1 = eml A B` with `B` arbitrary,
possibly compound) per direct request after `WitnessResidualSimpleT1Application.lean`'s closure.
This file records genuine further progress AND an honest, specific account of where the general
case's real wall is — not a restatement of the earlier findings, a sharper one.

**The new angle.** All earlier files that needed `B`'s positivity either required `B` itself to
be simple (`WitnessResidualSimpleRightChildren.lean`) or only got EXISTENCE of a positive point
for `B` under the extra restriction `nestedLo cs < 0`
(`WitnessResidualNestedTargetBWitness.lean`). The question here: using TODAY's whole-tree closure
(`no_tree_with_simple_right_children`) recursively — applied to `A`, not `B` — can the
`nestedLo cs < 0` restriction be dropped, for an UNRESTRICTED `B`?

**Yes.** `witness_B_not_le_zero_of_A_simple`: if `A` (not `B`!) is `RightChildrenSimplePositive`,
`B` cannot be `≤ 0` everywhere, for ANY well-formed `cs` — `B` can be arbitrarily compound,
adversarial, anything. The mechanism: assume `B ≤ 0` everywhere. Case split on `nestedLo cs`'s
sign. If `≤ 0`: the original elementary trick (evaluate at `-π/2`) still closes it directly. If
`> 0`: the collapse instead forces `A.eval x = nestedTarget (0 :: cs) x` for ALL `x` — `A` itself
realizes a target ONE layer deeper in the SAME family — and since `A` is `RightChildrenSimplePositive`,
`no_tree_with_simple_right_children` (built earlier today) refutes THAT directly. Either branch
closes; `B`'s own shape never enters the argument.

**Why this still doesn't close the general case, precisely.** This gives `∃x0, 0 < B.eval x0` —
existence, at some point, for arbitrary `B`. `EMLWitnesses T1 x0`'s third conjunct is exactly
this, so (combined with `EMLWitnesses A x0` — free, `A` is simple) the ONLY missing piece of
`EMLWitnesses T1 x0` itself is `EMLWitnesses B x0`, needed for arbitrary `B` — genuinely open,
this file does not touch it. But `EMLWitnesses T1 x0` was never actually the bottleneck for the
`RightChildrenSimplePositive` proof pattern — `EMLPfaffianValidOn` was, via `EMLNoCrossingAt`,
which needs `B.eval x ≠ 0` THROUGHOUT AN INTERVAL, not at one point. Checked directly (not
assumed) whether the SAME collapse-recursion trick could be pushed to interval-wide positivity,
using periodicity: `nestedTarget cs` is `2π`-periodic (each log-shift layer preserves whatever
period the layer inside it has, inherited ultimately from `sin`), so the "`nestedTarget cs x ≤ 0`
somewhere" and "`nestedTarget cs x > 0` somewhere" regions BOTH repeat every `2π`, forever. The
zero-counting argument needs intervals that GROW with `M` (`T1`'s own Pfaffian-chain bound,
unbounded in general) — so any interval large enough to matter re-enters BOTH regions arbitrarily
many times. The pointwise collapse trick only ever pins `B`'s sign on the `≤ 0` sub-regions; nothing
in this line of attack touches the `> 0` sub-regions, no matter how the argument is sliced. This
is not a failure of cleverness — `EMLPfaffianValidOn`'s definition is a hard, un-relaxed universal
quantifier over the whole interval (`EMLPfaffian.lean`), and nothing built so far (here or in any
prior session) supplies interval-wide sign information for a tree whose OWN VALUE (not internal
structure) is otherwise unconstrained. Closing this for real would need either genuinely new
machinery tolerant of finitely-many/measure-zero sign exceptions (a foundational change to
`EMLPfaffianValidOn`/`enc_combinedBound`'s own definitions, well beyond this session), or a
different sufficient condition on `B` altogether.
-/

namespace MachLib

open MachLib.Real

/-- **`B` unrestricted (possibly compound, possibly adversarial) still can't be `≤ 0`
everywhere, as long as `A` is `RightChildrenSimplePositive`.** Generalizes
`witness_B_not_le_zero_of_lo_neg` (which needed `nestedLo cs < 0`) to every well-formed `cs`, by
recursing into `A` via `no_tree_with_simple_right_children` on the branch the elementary trick
doesn't reach. -/
theorem witness_B_not_le_zero_of_A_simple
    {A B : EMLTree} {cs : List Real} (hwf : nestedWF cs)
    (hAsimple : RightChildrenSimplePositive A)
    (hT1eq : ∀ x, (EMLTree.eml A B).eval x = nestedTarget cs x) :
    ∃ x0, 0 < B.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, B.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (B.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  rcases lt_total (nestedLo cs) 0 with hlt | heq | hgt
  · have hle : nestedLo cs ≤ 0 := le_of_lt hlt
    let x0 : Real := -(pi / (1 + 1))
    have hlog0 : Real.log (B.eval x0) = 0 := Real.log_nonpos (hallle x0)
    have h1 : Real.exp (A.eval x0) - Real.log (B.eval x0) = nestedTarget cs x0 := hT1eq x0
    rw [hlog0, sub_zero, nestedTarget_at_neg_pi_div_two cs hwf] at h1
    rw [← h1] at hle
    exact lt_irrefl_ax 0 (lt_of_lt_of_le (Real.exp_pos _) hle)
  · have hle : nestedLo cs ≤ 0 := le_of_eq heq
    let x0 : Real := -(pi / (1 + 1))
    have hlog0 : Real.log (B.eval x0) = 0 := Real.log_nonpos (hallle x0)
    have h1 : Real.exp (A.eval x0) - Real.log (B.eval x0) = nestedTarget cs x0 := hT1eq x0
    rw [hlog0, sub_zero, nestedTarget_at_neg_pi_div_two cs hwf] at h1
    rw [← h1] at hle
    exact lt_irrefl_ax 0 (lt_of_lt_of_le (Real.exp_pos _) hle)
  · have hAeq : ∀ x, A.eval x = nestedTarget (0 :: cs) x := by
      intro x
      have hlog0 : Real.log (B.eval x) = 0 := Real.log_nonpos (hallle x)
      have h1 : Real.exp (A.eval x) - Real.log (B.eval x) = nestedTarget cs x := hT1eq x
      rw [hlog0, sub_zero] at h1
      rw [nestedTarget_cons]
      have e0 : (0 : Real) + nestedTarget cs x = nestedTarget cs x := by mach_ring
      rw [e0]
      calc A.eval x = Real.log (Real.exp (A.eval x)) := (Real.log_exp _).symm
        _ = Real.log (nestedTarget cs x) := by rw [h1]
    have hwf' : nestedWF (0 :: cs) := by
      refine ⟨?_, hwf⟩
      have e0 : (0 : Real) + nestedLo cs = nestedLo cs := by mach_ring
      rw [e0]; exact hgt
    exact no_tree_with_simple_right_children hwf' hAsimple hAeq

end MachLib
