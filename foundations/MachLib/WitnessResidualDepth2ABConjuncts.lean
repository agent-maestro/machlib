import MachLib.WitnessResidualDepth2Elementary
import MachLib.EMLSmoothness

/-!
# `EMLWitnesses A x0` / `EMLWitnesses B x0` for `T1 = eml A B` — scoping, not closing

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`).
`WitnessResidualDepth2Elementary.lean` closed the THIRD conjunct of `EMLWitnesses T1 x0`
(`0 < B.eval x0`) for `1 < c2 < 2`. This file attacks the other two conjuncts
(`EMLWitnesses A x0`, `EMLWitnesses B x0`) and reports what was actually found: a genuine
narrowing, not a closure, plus a load-bearing negative result that RESCOPES the remaining
problem (full argument in the decision doc — this header states only the mechanized content).

Two things are proved here:

1. `eml_witnesses_leaf_const` / `eml_witnesses_leaf_var` — `EMLWitnesses` is trivially `True` at
   any point for a LEAF (`const`/`var`). Cheap, but worth naming: whenever `B` (or `A`) turns
   out to be a leaf, one of the two open conjuncts is free, and the recursion concentrates
   entirely on the other child.
2. `depth2_no_T1_with_const_B_small` — if `B` is specifically a CONSTANT `b`, `T1 = eml A B`
   can satisfy `T1.eval x = log(c2+sin x)` (any `c2 > 1` — the upper bound `c2 < 2` used
   elsewhere in this family turns out NOT to be needed here) only if `b*(c2-1) > 1`. This
   generalizes `depth2_witness_B_of_c2_between_one_two`'s "`B ≤ 0` everywhere is impossible" to
   a WIDER band of constant `B` — not just non-positive constants, small POSITIVE constants are
   excluded too. Verified numerically first (5 values of `b` straddling the `1/(c2-1)` threshold
   at `c2=1.4`, all matching the predicted sign) before formalizing.

**What this does NOT do, honestly**: close `EMLWitnesses A x0` or `EMLWitnesses B x0` in
general. Pushed on paper (see decision doc), the escape route from (2) — `B` a LARGE enough
constant to survive the `x=-π/2` check — forces `A` to satisfy `exp(A.eval x) = log(c2+sin x) +
log b` globally, which at the `kπ` points (`sin(kπ)=0`) collapses to a fixed level
`log(c2) + log b` for every integer `k`, i.e. `A` itself must equal a nested target of exactly
the `log(log(c2+sin x))` shape already flagged as the open `c2 ≥ 2` case's difficulty — reached
here even though the outer `c2` is in `(1,2)`. So `EMLWitnesses A x0 / B x0` and the `c2 ≥ 2`
nested-target case are the SAME underlying difficulty, not two independently choosable pieces of
work. Not sketched further in Lean this pass — this file formalizes only what's cleanly
closeable; the decision doc records the paper-level finding in full.
-/

namespace MachLib
namespace Real

/-- `EMLWitnesses` is trivially satisfied by a `const` leaf, at any point. Direct unfold of the
recursive definition's base case. -/
theorem eml_witnesses_leaf_const (c x0 : Real) : EMLWitnesses (.const c) x0 := trivial

/-- `EMLWitnesses` is trivially satisfied by the `var` leaf, at any point. Direct unfold of the
recursive definition's base case. -/
theorem eml_witnesses_leaf_var (x0 : Real) : EMLWitnesses .var x0 := trivial

/-- **A wider band of constant `B` is excluded.** If `T1 = eml A B` with `B` the constant `b > 0`
satisfies `T1.eval x = log(c2+sin x)` globally for `c2 > 1`, then `b*(c2-1) > 1` — the
`x = -π/2` evaluation (same point as `depth2_witness_B_of_c2_between_one_two`) forces
`exp(A.eval(-π/2)) = log(c2-1) + log b = log((c2-1)*b)` (via `log_mul`), which must be positive
since `exp > 0`; `b*(c2-1) ≤ 1` would make that `≤ 0`, contradiction. Strictly generalizes the
`B ≤ 0` exclusion (the `b*(c2-1) ≤ 0` sub-case, always true once `B` clamps) to a whole open
band of small positive constants too. Unlike `depth2_witness_B_of_c2_between_one_two`, this does
NOT need `c2 < 2` — the `-π/2` point only ever produces the value `log(c2-1)`, never `log(c2+1)`
or anything else that would need the upper bound, so the proof carries to every `c2 > 1`
unchanged (checked by removing the hypothesis and confirming the proof still closes, not assumed
from the start). -/
theorem depth2_no_T1_with_const_B_small
    {A : EMLTree} {b c2 : Real}
    (hb : 0 < b) (hc2lo : 1 < c2)
    (hbc2 : b * (c2 - 1) ≤ 1)
    (hT1eq : ∀ x, (EMLTree.eml A (EMLTree.const b)).eval x = Real.log (c2 + Real.sin x)) :
    False := by
  let x0 : Real := -(pi / (1 + 1))
  have hsinx0 : Real.sin x0 = -1 := by
    show Real.sin (-(pi / (1 + 1))) = -1
    rw [Real.sin_neg, Real.sin_pi_div_two]
  have h1 : Real.exp (A.eval x0) - Real.log ((EMLTree.const b).eval x0)
      = Real.log (c2 + Real.sin x0) := hT1eq x0
  have hBeval : (EMLTree.const b).eval x0 = b := rfl
  rw [hBeval, hsinx0] at h1
  have hrw : c2 + (-1 : Real) = c2 - 1 := by mach_ring
  rw [hrw] at h1
  -- h1 : exp(A.eval x0) - log b = log(c2 - 1)
  have hc2m1_pos : (0 : Real) < c2 - 1 := by
    have h01 : (0 : Real) + 1 = 1 := by mach_ring
    exact lt_sub_of_add_lt (by rw [h01]; exact hc2lo)
  have h2 : (Real.exp (A.eval x0) - Real.log b) + Real.log b
      = Real.log (c2 - 1) + Real.log b := by rw [h1]
  have hlhs : (Real.exp (A.eval x0) - Real.log b) + Real.log b = Real.exp (A.eval x0) := by
    mach_ring
  rw [hlhs] at h2
  -- h2 : exp(A.eval x0) = log(c2-1) + log b
  have hmullog : Real.log ((c2 - 1) * b) = Real.log (c2 - 1) + Real.log b :=
    log_mul hc2m1_pos hb
  rw [← hmullog] at h2
  -- h2 : exp(A.eval x0) = log((c2-1)*b)
  have hcommute : b * (c2 - 1) = (c2 - 1) * b := mul_comm b (c2 - 1)
  have hle1 : (c2 - 1) * b ≤ 1 := by rw [← hcommute]; exact hbc2
  have hprod_pos : (0 : Real) < (c2 - 1) * b := mul_pos hc2m1_pos hb
  have hlogle : Real.log ((c2 - 1) * b) ≤ 0 := by
    rcases (le_iff_lt_or_eq ((c2 - 1) * b) 1).mp hle1 with hlt | heq
    · exact le_of_lt (log_neg_of_lt_one hprod_pos hlt)
    · rw [heq]; exact le_of_eq log_one
  rw [← h2] at hlogle
  -- hlogle : exp(A.eval x0) ≤ 0, contradicting exp positivity
  exact lt_irrefl_ax 0 (lt_of_lt_of_le (Real.exp_pos _) hlogle)

end Real
end MachLib
