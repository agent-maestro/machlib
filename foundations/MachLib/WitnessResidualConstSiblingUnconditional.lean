import MachLib.WitnessResidualSimpleT1Application
import MachLib.WitnessResidualNestedTargetTailSign
import MachLib.WitnessResidualNestedTargetFullyUnconditional

/-!
# Wiring the unconditional `TailSign` closure back to the original `t.eval = sin` residual

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Cont. 63 deliberately
stopped short of connecting cont. 58-62's unconditional results back to the ORIGINAL, pre-existing
residual (`t = eml T1 (eml (const c2) S3)`, `t.eval = sin`) — the question this whole multi-week
arc started from, before the `TailSign` detour. This file does it, carefully.

**The connection.** `eml_T1eq_of_const_sibling_le_zero` (`WitnessResidualSimpleT1Application.lean`)
is a PURE ALGEBRA derivation, no hypothesis on `T1` at all: given `S3 ≤ 0` everywhere and
`t.eval = sin`, it derives `T1.eval x = log(c2+\sin x)` for every `x`. This is EXACTLY the shape
`no_tree_eq_log_c2_plus_sin_unconditional` (cont. 60) refutes, unconditionally, for `1 < c2 ≤ 2`.
Chaining them: assuming `S3 ≤ 0` everywhere is IMPOSSIBLE whenever `1 < c2 ≤ 2`, for ANY `T1`
whatsoever — no `RightChildrenSimplePositive T1` restriction needed at all.

**Payoff.** `eml_depth2_witness_of_const_gt_one_sibling_unconditional` — removes the
`RightChildrenSimplePositive T1` restriction from
`eml_depth2_witness_of_const_gt_one_sibling_simple_T1` (the THIRD member of the
`eml_depth2_witness_of_const_*_sibling` family, built 2026-07-20) entirely, for `1 < c2 ≤ 2`. This
is a genuine closure of a piece of the ORIGINAL residual that predates the `TailSign` detour by
several days of this arc's own timeline — not a restatement of an already-proven fact in new
notation.

**Honest scope.** Covers `1 < c2 ≤ 2` only (cont. 60's sharp boundary — `c2 > 2` is provably
unreachable by this method, confirmed there). `T1` is now fully unrestricted, but `S3` still needs
to be a "sibling" in the ORIGINAL depth-2 shape (`t = eml T1 (eml (const c2) S3)`) — this does not
address `EMLWitnesses A x0`/`EMLWitnesses B x0` (the two OTHER open conjuncts named since the
2026-07-20 rescoping entry), only the third.
-/

namespace MachLib

open MachLib.Real

/-- **The `RightChildrenSimplePositive T1` restriction removed entirely, for `1 < c2 ≤ 2`.**
`T1` can be ANY EML tree — the unconditional `TailSign` closure (cont. 58-60) supplies what the
restriction used to be needed for. -/
theorem eml_depth2_witness_of_const_gt_one_sibling_unconditional
    {T1 S3 : EMLTree} {c2 : Real} (hc2 : 1 < c2) (hc2le : c2 ≤ 1 + 1)
    (hsin : ∀ x, (EMLTree.eml T1 (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, S3.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (S3.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hT1eq : ∀ x, T1.eval x = Real.log (c2 + Real.sin x) :=
    eml_T1eq_of_const_sibling_le_zero hc2 hallle hsin
  exact no_tree_eq_log_c2_plus_sin_unconditional c2 hc2 hc2le T1 hT1eq

/-- **The FULL closure: no restriction on `c2` (beyond `c2 > 1`) OR `T1`, at all.** Supersedes
`eml_depth2_witness_of_const_gt_one_sibling_unconditional` above entirely — that theorem's own
`c2 ≤ 1 + 1` restriction is gone, via `no_tree_eq_log_c2_plus_sin_fully_unconditional`
(`WitnessResidualNestedTargetFullyUnconditional.lean`), which runs the SAME zero-counting argument
entirely on a tail (`eml_eventually_valid_repr`) rather than needing validity from `0` — so it
never needed the straddle condition `c2 ≤ 2` was standing in for. This closes the THIRD
`EMLWitnesses` conjunct completely, for the WHOLE original depth-2 family, no restriction left on
either side. -/
theorem eml_depth2_witness_of_const_sibling_fully_unconditional
    {T1 S3 : EMLTree} {c2 : Real} (hc2 : 1 < c2)
    (hsin : ∀ x, (EMLTree.eml T1 (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, S3.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (S3.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hT1eq : ∀ x, T1.eval x = Real.log (c2 + Real.sin x) :=
    eml_T1eq_of_const_sibling_le_zero hc2 hallle hsin
  exact no_tree_eq_log_c2_plus_sin_fully_unconditional c2 hc2 T1 hT1eq

end MachLib
