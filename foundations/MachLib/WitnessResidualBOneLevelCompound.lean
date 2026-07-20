import MachLib.WitnessResidualBWitnessGeneralB

/-!
# A genuinely different mechanism: `B` allowed ONE level of compoundness

Continuation of the general-case attempt. Every closure so far needed `T1`'s own right child
`B` to be a bare leaf (`var` or a positive constant) — the ONLY way found, until now, to get
`B.eval x` positive THROUGHOUT an interval. This file finds a second, genuinely different
mechanism for that same fact, one that does not require `B` to be a leaf at all.

**The mechanism.** `log`'s domain-clamp cuts both ways: if a node's log-argument is `≤ 1` (not
just `≤ 0`), its `log` is `≤ 0` (`log 1 = 0`, `log` increasing), so SUBTRACTING it can only
INCREASE the node's value. Concretely: `(eml P (const c)).eval x = exp(P.eval x) - log c`, and
if `0 < c ≤ 1`, `log c ≤ 0`, so this is `≥ exp(P.eval x) > 0` — for ANY `P` at all, with no
restriction whatsoever. This is a completely different route to "compound node, provably
positive throughout an interval" than `RightChildrenSimplePositive` uses (which needs the node
to BE simple); here the node is compound (`eml P _`) and provably positive precisely BECAUSE of
that structure, not despite it.

**What this buys.** `T1 = eml A B` where `B = eml P (const c)` (`0 < c ≤ 1`) — ONE level of
compoundness in `T1`'s own right child, previously excluded entirely — closes the same way
`RightChildrenSimplePositive T1` did, PROVIDED `A` and `P` are themselves
`RightChildrenSimplePositive` (their own right-children still need to be well-behaved for
`EMLWitnesses`/`EMLNoCrossingAt` to reach them — this mechanism supplies `B`'s OWN value, not
`B`'s internal structure). Genuinely widens the closed class; does not remove the general wall
(`P` and `A` are still restricted, and `B`'s shape is still a specific, narrow pattern, not
"anything"), but it's concrete evidence the wall isn't monolithic — different mechanisms chip
away at different parts of it.
-/

namespace MachLib

open MachLib.Real

/-- **A compound node is provably positive, for ANY left child, when its right child is a
constant `≤ 1`.** `log c ≤ 0` for `0 < c ≤ 1` (equality only at `c=1`), so subtracting it from
`exp(P.eval x) > 0` can only increase the result. -/
theorem eml_pos_of_right_const_le_one {P : EMLTree} {c : Real} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (x : Real) : 0 < (EMLTree.eml P (EMLTree.const c)).eval x := by
  show 0 < Real.exp (P.eval x) - Real.log c
  rcases (le_iff_lt_or_eq c 1).mp hc1 with hlt | heq
  · have hlogneg : Real.log c < 0 := log_neg_of_lt_one hc0 hlt
    have hnegpos : (0 : Real) < -Real.log c := neg_pos_of_neg hlogneg
    have hsum : (0 : Real) < Real.exp (P.eval x) + (-Real.log c) := add_pos (Real.exp_pos _) hnegpos
    have e : Real.exp (P.eval x) - Real.log c = Real.exp (P.eval x) + (-Real.log c) := sub_def _ _
    rw [e]; exact hsum
  · rw [heq, Real.log_one, sub_zero]; exact Real.exp_pos _

/-- **The closure, with `B` allowed one level of compoundness.** `T1 = eml A (eml P (const
c))`, `A` and `P` both `RightChildrenSimplePositive`, `0 < c ≤ 1`: no such `T1` can equal any
well-formed nested target — unconditionally, same shape of result as
`no_T1_with_simple_right_children`, for a strictly WIDER class of `T1`. -/
theorem no_T1_with_B_one_level_compound
    {A P : EMLTree} {c : Real} {cs : List Real} (hwf : nestedWF cs)
    (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hA : RightChildrenSimplePositive A) (hP : RightChildrenSimplePositive P)
    (hT1eq : ∀ x, (EMLTree.eml A (EMLTree.eml P (EMLTree.const c))).eval x = nestedTarget cs x) :
    False := by
  have hppos : (0 : Real) < pi + pi / (1 + 1) := pi_plus_pi_div_two_pos
  have hwitA : EMLWitnesses A (pi + pi / (1 + 1)) :=
    eml_witnesses_of_right_children_simple_positive A hA _ hppos
  have hwitP : EMLWitnesses P (pi + pi / (1 + 1)) :=
    eml_witnesses_of_right_children_simple_positive P hP _ hppos
  have hBpos : ∀ x, 0 < (EMLTree.eml P (EMLTree.const c)).eval x :=
    fun x => eml_pos_of_right_const_le_one hc0 hc1 x
  have hwitB : EMLWitnesses (EMLTree.eml P (EMLTree.const c)) (pi + pi / (1 + 1)) :=
    ⟨hwitP, trivial, hc0⟩
  have hwitT1 : EMLWitnesses (EMLTree.eml A (EMLTree.eml P (EMLTree.const c)))
      (pi + pi / (1 + 1)) := ⟨hwitA, hwitB, hBpos _⟩
  have hncA : ∀ x, 0 < x → EMLNoCrossingAt A x :=
    fun x hx => eml_no_crossing_of_right_children_simple_positive A hA x hx
  have hncP : ∀ x, 0 < x → EMLNoCrossingAt P x :=
    fun x hx => eml_no_crossing_of_right_children_simple_positive P hP x hx
  have hncB : ∀ x, 0 < x → EMLNoCrossingAt (EMLTree.eml P (EMLTree.const c)) x :=
    fun x hx => ⟨hncP x hx, trivial, ne_of_gt hc0⟩
  have hncAll : ∀ x, 0 < x →
      EMLNoCrossingAt (EMLTree.eml A (EMLTree.eml P (EMLTree.const c))) x :=
    fun x hx => ⟨hncA x hx, hncB x hx, ne_of_gt (hBpos x)⟩
  have hDdAll : ∀ x, HasDerivAt (EMLTree.eml A (EMLTree.eml P (EMLTree.const c))).eval
      (nestedTargetDeriv cs x) x := fun x =>
    HasDerivAt_of_eq (nestedTarget cs) (EMLTree.eml A (EMLTree.eml P (EMLTree.const c))).eval
      (nestedTargetDeriv cs x) x (fun y => (hT1eq y).symm) (nestedTarget_hasDerivAt cs hwf x)
  have hvalidon_any_b : ∀ b : Real, 0 < b →
      EMLPfaffianValidOn (EMLTree.eml A (EMLTree.eml P (EMLTree.const c))) 0 b := by
    intro b hb
    rcases lt_total b (pi + pi / (1 + 1)) with hbp | hbp | hbp
    · exact EMLPfaffianValidOn_mono_b (le_of_lt hbp)
        (eml_pfaffian_validon_of_witnesses_backward
          (EMLTree.eml A (EMLTree.eml P (EMLTree.const c))) 0 (pi + pi / (1 + 1)) hppos
          (nestedTargetDeriv cs) (fun x _ _ => hDdAll x) (fun x hx1 _ => hncAll x hx1) hwitT1)
    · rw [hbp]
      exact eml_pfaffian_validon_of_witnesses_backward
        (EMLTree.eml A (EMLTree.eml P (EMLTree.const c))) 0 (pi + pi / (1 + 1)) hppos
        (nestedTargetDeriv cs) (fun x _ _ => hDdAll x) (fun x hx1 _ => hncAll x hx1) hwitT1
    · exact eml_pfaffian_validon_of_witnesses_twosided
        (EMLTree.eml A (EMLTree.eml P (EMLTree.const c))) 0 b (pi + pi / (1 + 1)) hppos hbp
        (nestedTargetDeriv cs) (fun x _ _ => hDdAll x) (fun x hx1 _ => hncAll x hx1) hwitT1
  exact no_tree_eq_nested_target_given_validon cs hwf
    (EMLTree.eml A (EMLTree.eml P (EMLTree.const c))) hT1eq hvalidon_any_b

end MachLib
