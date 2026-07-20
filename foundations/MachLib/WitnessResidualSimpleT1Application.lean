import MachLib.WitnessResidualSimpleRightChildren

/-!
# Closing the loop: a direct witness for `S3`, in the original problem's own vocabulary

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Every file so far in
today's session worked in terms of `nestedTarget cs` — useful for building general machinery,
but one step removed from the actual question this whole arc exists to answer:
`eml_depth2_witness_of_const_le_one_sibling` and `eml_depth2_witness_of_const_sibling_unbounded_T1`
(`EMLSmoothness.lean`) both conclude `∃x0, 0 < S3.eval x0` directly from
`t = eml T1 (eml (const c2) S3)` agreeing with `sin` — the "`c2 > 1`, `T1` bounded" case between
them is EXACTLY the residual this whole investigation has been chasing since 2026-07-15. This
file adds the third member of that family, closing it for `T1` with `RightChildrenSimplePositive`.

**Step 1** (`no_tree_with_simple_right_children`): the previous file's closure
(`no_T1_with_simple_right_children`) required its tree to be literally `eml A B` at the top —
an artifact of how it was built, not a real requirement (every piece it used — `EMLWitnesses`/
`EMLNoCrossingAt` freeness, the derivative, the final `no_tree_eq_nested_target_given_validon`
call — works for ANY `EMLTree`). Restated for arbitrary `T1`, dropping the unnecessary `eml A B`
decomposition.

**Step 2**: the `S3 ≤ 0` collapse itself, derived directly (mirroring
`eml_depth2_witness_of_const_le_one_sibling`'s own derivation line-for-line, but concluding
`T1.eval x = log(c2+sin x)` instead of an immediate contradiction, since `c2 > 1` doesn't refute
at a single point the way `c2 ≤ 1` does).

**Step 3** (`eml_depth2_witness_of_const_gt_one_sibling_simple_T1`): combining both closes
`∃x0, 0 < S3.eval x0` directly from `t.eval = sin`, `c2 > 1`, and `RightChildrenSimplePositive
T1` — no `nestedTarget`/`cs` visible anywhere in the final statement, matching the vocabulary of
the two existing family members exactly.
-/

namespace MachLib

open MachLib.Real

/-- **`no_T1_with_simple_right_children`, generalized to any tree shape.** The `eml A B`
requirement in the previous file was incidental — every piece of that proof (`EMLWitnesses`/
`EMLNoCrossingAt` freeness, the derivative construction, the final zero-counting call) already
works for an arbitrary `T1`. Stated once, generally, here. -/
theorem no_tree_with_simple_right_children
    {T1 : EMLTree} {cs : List Real} (hwf : nestedWF cs)
    (hT1simple : RightChildrenSimplePositive T1)
    (hT1eq : ∀ x, T1.eval x = nestedTarget cs x) :
    False := by
  have hppos : (0 : Real) < pi + pi / (1 + 1) := pi_plus_pi_div_two_pos
  have hwitT1 : EMLWitnesses T1 (pi + pi / (1 + 1)) :=
    eml_witnesses_of_right_children_simple_positive T1 hT1simple _ hppos
  have hDdAll : ∀ x, HasDerivAt T1.eval (nestedTargetDeriv cs x) x := fun x =>
    HasDerivAt_of_eq (nestedTarget cs) T1.eval (nestedTargetDeriv cs x) x
      (fun y => (hT1eq y).symm) (nestedTarget_hasDerivAt cs hwf x)
  have hncAll : ∀ x, 0 < x → EMLNoCrossingAt T1 x := fun x hx =>
    eml_no_crossing_of_right_children_simple_positive T1 hT1simple x hx
  have hvalidon_any_b : ∀ b : Real, 0 < b → EMLPfaffianValidOn T1 0 b := by
    intro b hb
    rcases lt_total b (pi + pi / (1 + 1)) with hbp | hbp | hbp
    · exact EMLPfaffianValidOn_mono_b (le_of_lt hbp)
        (eml_pfaffian_validon_of_witnesses_backward T1 0 (pi + pi / (1 + 1)) hppos
          (nestedTargetDeriv cs) (fun x _ _ => hDdAll x) (fun x hx1 _ => hncAll x hx1) hwitT1)
    · rw [hbp]
      exact eml_pfaffian_validon_of_witnesses_backward T1 0 (pi + pi / (1 + 1)) hppos
        (nestedTargetDeriv cs) (fun x _ _ => hDdAll x) (fun x hx1 _ => hncAll x hx1) hwitT1
    · exact eml_pfaffian_validon_of_witnesses_twosided T1 0 b (pi + pi / (1 + 1)) hppos hbp
        (nestedTargetDeriv cs) (fun x _ _ => hDdAll x) (fun x hx1 _ => hncAll x hx1) hwitT1
  exact no_tree_eq_nested_target_given_validon cs hwf T1 hT1eq hvalidon_any_b

/-- **The `S3 ≤ 0` collapse, derived directly.** Mirrors
`eml_depth2_witness_of_const_le_one_sibling`'s own derivation exactly, up through
`exp(T1.eval x) = c2 + sin x`; the difference is what comes after — for `c2 ≤ 1` that identity
is immediately contradictory (that theorem's own conclusion), but for `c2 > 1` it's a genuine
equation `T1` must satisfy, so this stops at `T1.eval x = log(c2+sin x)` rather than deriving
`False` outright. -/
theorem eml_T1eq_of_const_sibling_le_zero
    {T1 S3 : EMLTree} {c2 : Real} (hc2 : 1 < c2)
    (hS3le : ∀ x, S3.eval x ≤ 0)
    (hsin : ∀ x, (EMLTree.eml T1 (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∀ x, T1.eval x = Real.log (c2 + Real.sin x) := by
  intro x
  have hlog0 : Real.log (S3.eval x) = 0 := Real.log_nonpos (hS3le x)
  have h1 : Real.exp (T1.eval x) -
      Real.log ((EMLTree.eml (EMLTree.const c2) S3).eval x) = Real.sin x := hsin x
  have hNeval : (EMLTree.eml (EMLTree.const c2) S3).eval x = Real.exp c2 := by
    show Real.exp c2 - Real.log (S3.eval x) = Real.exp c2
    rw [hlog0, sub_zero]
  rw [hNeval, Real.log_exp] at h1
  -- h1 : exp(T1.eval x) - c2 = sin x
  have h2 : Real.exp (T1.eval x) - c2 + c2 = Real.sin x + c2 := by rw [h1]
  have hlhs : Real.exp (T1.eval x) - c2 + c2 = Real.exp (T1.eval x) := by mach_ring
  rw [hlhs] at h2
  -- h2 : exp(T1.eval x) = sin x + c2
  have hc2pos : (0 : Real) < c2 := lt_trans_ax zero_lt_one_ax hc2
  have hsin_ge : (-1 : Real) ≤ Real.sin x := neg_one_le_sin x
  have hpos : (0 : Real) < c2 + Real.sin x := by
    rcases (le_iff_lt_or_eq _ _).mp hsin_ge with h | h
    · have hstep := add_lt_add hc2 h
      have e : (1 : Real) + (-1) = 0 := by mach_ring
      rwa [e] at hstep
    · rw [← h]
      have e : c2 + (-1 : Real) = c2 - 1 := by mach_ring
      rw [e]
      have h01 : (0 : Real) + 1 = 1 := by mach_ring
      exact lt_sub_of_add_lt (by rw [h01]; exact hc2)
  have h3 : Real.exp (T1.eval x) = c2 + Real.sin x := by
    have e : Real.sin x + c2 = c2 + Real.sin x := add_comm _ _
    rw [e] at h2; exact h2
  calc T1.eval x = Real.log (Real.exp (T1.eval x)) := (Real.log_exp _).symm
    _ = Real.log (c2 + Real.sin x) := by rw [h3]

/-- **The third member of the family.** `eml_depth2_witness_of_const_le_one_sibling` closes
`c2 ≤ 1`; `eml_depth2_witness_of_const_sibling_unbounded_T1` closes `T1` unbounded, any `c2`.
This closes `c2 > 1` when `T1` has `RightChildrenSimplePositive` — a real (if syntactically
restricted) slice of the remaining `c2 > 1`, `T1` bounded gap, stated with no `nestedTarget`
visible: purely in terms of the original `t = eml T1 (eml (const c2) S3)` agreeing with `sin`. -/
theorem eml_depth2_witness_of_const_gt_one_sibling_simple_T1
    {T1 S3 : EMLTree} {c2 : Real} (hc2 : 1 < c2) (hT1simple : RightChildrenSimplePositive T1)
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
  have hwf : nestedWF [c2] := by
    refine ⟨?_, trivial⟩
    show (0 : Real) < c2 + (-1)
    have e : c2 + (-1 : Real) = c2 - 1 := by mach_ring
    rw [e]
    have h01 : (0 : Real) + 1 = 1 := by mach_ring
    exact lt_sub_of_add_lt (by rw [h01]; exact hc2)
  have hT1eq' : ∀ x, T1.eval x = nestedTarget [c2] x := by
    intro x
    rw [nestedTarget_cons, nestedTarget_nil]
    exact hT1eq x
  exact no_tree_with_simple_right_children hwf hT1simple hT1eq'

end MachLib
