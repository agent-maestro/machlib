import MachLib.WitnessResidualExpWrappedNonMonotonic
import MachLib.WitnessResidualSimpleT1Application

/-! # `expWrappedNonMonotonicWitness` closes too — via the pre-existing heavy machinery

Last round found `expWrappedNonMonotonicWitness`: a concrete tree escaping every "free" closure
built this session (bounded both directions, non-constant, non-`RightChildrenSimplePositive`,
non-monotonic). That was explicitly framed as a TEST CASE, not a disproof — the open question
left behind was whether the heavier, pre-existing zero-counting/Pfaffian-chain machinery (built
before this session, e.g. `no_tree_eq_nested_target_given_validon`,
`eml_pfaffian_validon_of_witnesses_backward`/`_twosided`) could still close it.

**This file answers that: yes.** `no_tree_with_simple_right_children`
(`WitnessResidualSimpleT1Application.lean`) closes trees via that heavy machinery by supplying
two structural facts — `EMLWitnesses T1 x0` (a positivity anchor threaded through every node)
and `∀x>0, EMLNoCrossingAt T1 x` (no internal log-argument hits exactly `0`, for `x>0`) — using
`RightChildrenSimplePositive`'s freeness to get both automatically. `RightChildrenSimplePositive`
fails for `expWrappedNonMonotonicWitness` (that's WHY it escaped every free closure), so that
shortcut doesn't apply — but both facts turn out to be independently provable BY HAND for this
specific tree, using facts already established about `nonMonotonicWitness`:

- **The key structural observation**: `nonMonotonicWitness`'s own problematic zero-crossing
  (where its right-child chain `D := eml var (const 2)` crosses zero) sits at `x0 = log(log 2) ≈
  -0.37` — a NEGATIVE point. The machinery above only ever needs `EMLNoCrossingAt` for `x > 0`.
  The crossing that caused all the trouble (unbounded-below divergence, non-monotonicity) simply
  isn't IN that region — `nonMonotonicWitness_Dpos`/`nonMonotonicWitness_Bpos` (both already
  proven, for `x > nonMonotonicWitness_x0`) directly supply strict positivity for every node's
  log-argument throughout `x > 0`, with zero new case-analysis.
- The witness anchor uses the SAME established point `π + π/2` the existing family members use,
  for the SAME reason (a specific point safely past the tree's own local structure).

**What this settles.** `expWrappedNonMonotonicWitness` — despite being a genuine, hard-won
member of the residual's open classification — poses NO actual threat to the witness-finding
argument: `eml_depth2_witness_of_const_gt_one_sibling_expwrapped_T1` closes it completely, `c2 >
1`, no restriction. The classification being non-empty (last round) and the residual failing to
close for a SPECIFIC member of it (this round, refuted) are different questions — this round
answers the second one, for this one tree, in the reassuring direction. It does NOT prove the
classification is closable in GENERAL (this proof is specific to `expWrappedNonMonotonicWitness`'s
own structure, particularly the negative-crossing observation, which won't hold for every tree
in the class) — but it is a second, independent confirmation (after `nonMonotonicWitness`'s own
resolution two rounds ago) that finding a member of the open class does not, by itself, threaten
the underlying theorem. -/

namespace MachLib
namespace Real

open EMLTree

/-- `nonMonotonicWitness`'s own crossing sits at a NEGATIVE `x` — the key fact making this whole
closure possible, since the heavy machinery below only ever needs positivity for `x > 0`. -/
theorem nonMonotonicWitness_x0_neg : nonMonotonicWitness_x0 < 0 := by
  show Real.log (Real.log (1 + 1)) < 0
  have hlog2pos := nonMonotonicWitness_log2_pos
  have he : (1 + 1 : Real) < Real.exp 1 := exp_gt_one_plus_self 1 zero_lt_one_ax
  have h2 := log_lt_log zero_lt_one_add_one he
  rw [log_exp] at h2
  exact log_neg_of_lt_one hlog2pos h2

/-- `nonMonotonicWitness`'s inner `B` subtree, unfolded (`log 1 = 0` simplifies away the
would-be `- log 1` term, matching `nonMonotonicWitness_Bpos`'s own stated form exactly). -/
theorem nonMonotonicWitnessB_eval (x : Real) :
    (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
      (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1)))).eval x
    = Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log (1 + 1)) := by
  show Real.exp ((EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x)
      - Real.log ((EMLTree.eml EMLTree.var (EMLTree.const (1 + 1))).eval x) = _
  have hC : (EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x = Real.exp x - Real.log 1 := rfl
  have hD : (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1))).eval x
      = Real.exp x - Real.log (1 + 1) := rfl
  rw [hC, hD, log_one, sub_zero]

theorem nonMonotonicWitnessD_eval (x : Real) :
    (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1))).eval x = Real.exp x - Real.log (1 + 1) := rfl

/-- **`EMLWitnesses` holds at `π + π/2`.** Every leaf-level obligation is trivial; the two real
positivity requirements (`B`'s and `D`'s) reduce directly to `nonMonotonicWitness_Bpos`/`_Dpos`,
applicable since `π + π/2 > 0 > nonMonotonicWitness_x0`. -/
theorem expWrappedNonMonotonicWitness_witnesses :
    EMLWitnesses expWrappedNonMonotonicWitness (Real.pi + Real.pi / (1 + 1)) := by
  have hppos : (0 : Real) < Real.pi + Real.pi / (1 + 1) := pi_plus_pi_div_two_pos
  have hx0lt : nonMonotonicWitness_x0 < Real.pi + Real.pi / (1 + 1) :=
    lt_trans_ax nonMonotonicWitness_x0_neg hppos
  have hDpos := nonMonotonicWitness_Dpos hx0lt
  have hBpos := nonMonotonicWitness_Bpos hx0lt
  show EMLWitnesses nonMonotonicWitness (Real.pi + Real.pi / (1 + 1))
      ∧ EMLWitnesses (EMLTree.const 1) (Real.pi + Real.pi / (1 + 1))
      ∧ 0 < (EMLTree.const 1 : EMLTree).eval (Real.pi + Real.pi / (1 + 1))
  refine ⟨?_, trivial, zero_lt_one_ax⟩
  show EMLWitnesses EMLTree.var (Real.pi + Real.pi / (1 + 1))
      ∧ EMLWitnesses (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
          (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1)))) (Real.pi + Real.pi / (1 + 1))
      ∧ 0 < (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
          (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1)))).eval (Real.pi + Real.pi / (1 + 1))
  refine ⟨trivial, ?_, by rw [nonMonotonicWitnessB_eval]; exact hBpos⟩
  show EMLWitnesses (EMLTree.eml EMLTree.var (EMLTree.const 1)) (Real.pi + Real.pi / (1 + 1))
      ∧ EMLWitnesses (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1))) (Real.pi + Real.pi / (1 + 1))
      ∧ 0 < (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1))).eval (Real.pi + Real.pi / (1 + 1))
  refine ⟨⟨trivial, trivial, zero_lt_one_ax⟩, ⟨trivial, trivial, zero_lt_one_add_one⟩, ?_⟩
  rw [nonMonotonicWitnessD_eval]
  exact hDpos

/-- **`EMLNoCrossingAt` holds for all `x > 0`.** Same structural facts as above, feeding into
the pointwise (`≠ 0`) rather than anchored (`0 < _`) requirement. -/
theorem expWrappedNonMonotonicWitness_no_crossing :
    ∀ x : Real, 0 < x → EMLNoCrossingAt expWrappedNonMonotonicWitness x := by
  intro x hx
  have hx0lt : nonMonotonicWitness_x0 < x := lt_trans_ax nonMonotonicWitness_x0_neg hx
  have hDpos := nonMonotonicWitness_Dpos hx0lt
  have hBpos := nonMonotonicWitness_Bpos hx0lt
  show EMLNoCrossingAt nonMonotonicWitness x ∧ EMLNoCrossingAt (EMLTree.const 1) x
      ∧ (EMLTree.const 1 : EMLTree).eval x ≠ 0
  refine ⟨?_, trivial, ne_of_gt zero_lt_one_ax⟩
  show EMLNoCrossingAt EMLTree.var x
      ∧ EMLNoCrossingAt (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
          (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1)))) x
      ∧ (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
          (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1)))).eval x ≠ 0
  refine ⟨trivial, ?_, by rw [nonMonotonicWitnessB_eval]; exact ne_of_gt hBpos⟩
  show EMLNoCrossingAt (EMLTree.eml EMLTree.var (EMLTree.const 1)) x
      ∧ EMLNoCrossingAt (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1))) x
      ∧ (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1))).eval x ≠ 0
  refine ⟨⟨trivial, trivial, ne_of_gt zero_lt_one_ax⟩,
    ⟨trivial, trivial, ne_of_gt zero_lt_one_add_one⟩, ?_⟩
  rw [nonMonotonicWitnessD_eval]
  exact ne_of_gt hDpos

/-- **`no_tree_with_expwrapped_nonmonotonic_T1`**: mirrors `no_tree_with_simple_right_children`
exactly, but for the SPECIFIC (non-simple!) tree `expWrappedNonMonotonicWitness`, using the
hand-built witness/no-crossing facts above in place of `RightChildrenSimplePositive`'s freeness
machinery. -/
theorem no_tree_with_expwrapped_nonmonotonic_T1
    {cs : List Real} (hwf : nestedWF cs)
    (hT1eq : ∀ x, expWrappedNonMonotonicWitness.eval x = nestedTarget cs x) :
    False := by
  have hppos : (0 : Real) < Real.pi + Real.pi / (1 + 1) := pi_plus_pi_div_two_pos
  have hwitT1 := expWrappedNonMonotonicWitness_witnesses
  have hDdAll : ∀ x, HasDerivAt expWrappedNonMonotonicWitness.eval (nestedTargetDeriv cs x) x :=
    fun x => HasDerivAt_of_eq (nestedTarget cs) expWrappedNonMonotonicWitness.eval
      (nestedTargetDeriv cs x) x (fun y => (hT1eq y).symm) (nestedTarget_hasDerivAt cs hwf x)
  have hncAll := expWrappedNonMonotonicWitness_no_crossing
  have hvalidon_any_b :
      ∀ b : Real, 0 < b → EMLPfaffianValidOn expWrappedNonMonotonicWitness 0 b := by
    intro b hb
    rcases lt_total b (Real.pi + Real.pi / (1 + 1)) with hbp | hbp | hbp
    · exact EMLPfaffianValidOn_mono_b (le_of_lt hbp)
        (eml_pfaffian_validon_of_witnesses_backward expWrappedNonMonotonicWitness 0
          (Real.pi + Real.pi / (1 + 1)) hppos (nestedTargetDeriv cs) (fun x _ _ => hDdAll x)
          (fun x hx1 _ => hncAll x hx1) hwitT1)
    · rw [hbp]
      exact eml_pfaffian_validon_of_witnesses_backward expWrappedNonMonotonicWitness 0
        (Real.pi + Real.pi / (1 + 1)) hppos (nestedTargetDeriv cs) (fun x _ _ => hDdAll x)
        (fun x hx1 _ => hncAll x hx1) hwitT1
    · exact eml_pfaffian_validon_of_witnesses_twosided expWrappedNonMonotonicWitness 0 b
        (Real.pi + Real.pi / (1 + 1)) hppos hbp (nestedTargetDeriv cs) (fun x _ _ => hDdAll x)
        (fun x hx1 _ => hncAll x hx1) hwitT1
  exact no_tree_eq_nested_target_given_validon cs hwf expWrappedNonMonotonicWitness hT1eq
    hvalidon_any_b

/-- **The finale: `expWrappedNonMonotonicWitness` poses no threat to witness-finding, for any
`c2 > 1`.** Despite escaping every free closure built this session, it closes completely via the
pre-existing heavy machinery. -/
theorem eml_depth2_witness_of_const_gt_one_sibling_expwrapped_T1
    {S3 : EMLTree} {c2 : Real} (hc2 : 1 < c2)
    (hsin : ∀ x, (EMLTree.eml expWrappedNonMonotonicWitness
      (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, S3.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (S3.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hT1eq : ∀ x, expWrappedNonMonotonicWitness.eval x = Real.log (c2 + Real.sin x) :=
    eml_T1eq_of_const_sibling_le_zero hc2 hallle hsin
  have hwf : nestedWF [c2] := by
    refine ⟨?_, trivial⟩
    show (0 : Real) < c2 + (-1)
    have e : c2 + (-1 : Real) = c2 - 1 := by mach_ring
    rw [e]
    have h01 : (0 : Real) + 1 = 1 := by mach_ring
    exact lt_sub_of_add_lt (by rw [h01]; exact hc2)
  have hT1eq' : ∀ x, expWrappedNonMonotonicWitness.eval x = nestedTarget [c2] x := by
    intro x
    rw [nestedTarget_cons, nestedTarget_nil]
    exact hT1eq x
  exact no_tree_with_expwrapped_nonmonotonic_T1 hwf hT1eq'

end Real
end MachLib
