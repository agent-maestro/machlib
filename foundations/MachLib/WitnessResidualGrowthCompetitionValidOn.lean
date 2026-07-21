import MachLib.WitnessResidualGrowthCompetitionAssembly
import MachLib.WitnessResidualChainSkeleton
import MachLib.WitnessResidualSimpleT1Application

/-! # THE FULL CLOSURE: `growthCompetitionWitness` can never be a witness-finding counterexample

Last round closed `growthCompetitionWitness`'s non-monotonicity — establishing it as a genuine,
verified member of the residual's open classification (bounded, non-constant, non-simple,
non-monotonic). The natural next question, flagged but not attempted then: does this witness (or
one built from it) actually BREAK the `t.eval = sin` equation, or does the witness-finding theorem
still hold for it? This file answers: **the theorem still holds** — `growthCompetitionWitness`
can never be part of a genuine counterexample, for ANY valid parameters.

**The route that worked, found by re-examining `EMLPfaffianValidOn`'s OWN definition instead of
reaching for the elaborate numerical machinery (two-equal-points via IVT) planned initially.**
`EMLPfaffianValidOn` is a simple structural recursion: `True` at every leaf, and at an `eml t1 t2`
node, `EMLPfaffianValidOn t1 ∧ EMLPfaffianValidOn t2 ∧ (t2 positive throughout the interval)`. The
ENTIRE reason this predicate has been the arc's central open difficulty for weeks is that GENERAL
compound trees mix `log`-clamped and unclamped regions, needing a not-yet-built branch-switching
Pfaffian chain type (see the `2026-07-20` "grounded WHY path (1) is hard" entry in the decision
doc). But `growthCompetitionWitness` was built from `boundedNonConstantWitness`, whose defining
feature is that it NEVER clamps — `boundedNonConstantWitness_Bpos` already gives `0 <
exp(exp x) - log c` UNCONDITIONALLY, for every `x`, no case split. Once every log-argument
positivity condition in the tree is available UNCONDITIONALLY like this, `EMLPfaffianValidOn`
falls out by direct structural recursion — no induction on tree depth needed, no branch-switching
chain type needed, just walking the (fixed, finite) tree shape once.

**The two building blocks.** `boundedNonConstantWitness_EMLPfaffianValidOn`: `EMLPfaffianValidOn
(boundedNonConstantWitness c) a b` for ANY `a, b` — the recursion bottoms out in three trivial
facts (`0<1`, `0<c` from `1<c`) plus one already-proven one (`boundedNonConstantWitness_Bpos`,
after simplifying `log 1 = 0` the same way `boundedNonConstantWitness_eval` does).
`growthCompetitionWitness_EMLPfaffianValidOn`: reuses the above TWICE (once per inner constant,
`c1` and `c2`) plus one trivial `exp(...) - log 1 = exp(...) > 0` fact for the outer structure.
Both fully unconditional in `a, b` — no interval restriction, no case split anywhere.

**The closure itself.** `eml_T1eq_of_const_sibling_le_zero` (already in
`WitnessResidualSimpleT1Application.lean`, general, no `RightChildrenSimplePositive` needed)
derives `T1.eval x = log(c2+sin x)` from the `S3 ≤ 0` assumption. Feeding
`growthCompetitionWitness`'s now-unconditional `EMLPfaffianValidOn` into
`T1_not_eq_log_c2_plus_sin_given_validon` (`WitnessResidualChainSkeleton.lean`, the generic
zero-counting contradiction, previously only ever exercised with `hvalidon_any_b` as an
UNDISCHARGED hypothesis) gives `False` directly — so the `S3≤0` assumption is impossible, meaning
the witness `∃x0, 0<S3.eval x0` holds. `#print axioms` confirms `eml_pfaffian_validon_from_sin_
equality` does NOT appear in the dependency chain — this is a genuine, non-circular result.

**Why this matters beyond the one tree.** This is the FIRST time in the whole 40+-file arc that
`hvalidon_any_b` has been discharged for a genuinely COMPOUND, non-trivial tree WITHOUT either (a)
restricting to `RightChildrenSimplePositive` (needing every right child literally `var`/positive
constant) or (b) building the not-yet-existing branch-switching chain machinery. The mechanism —
"if every log-argument positivity fact in the tree is available unconditionally, `EMLPfaffianValidOn`
is free" — is not specific to `growthCompetitionWitness`'s exact shape; it should apply to ANY tree
built entirely from non-clamping pieces. Whether it extends to a broader class of trees is a real
follow-up question, genuinely open — not claimed or attempted here. -/

namespace MachLib
namespace Real

open EMLTree

/-- `EMLPfaffianValidOn (boundedNonConstantWitness c) a b`, for ANY `a, b` — no interval
restriction. The recursion bottoms out in `boundedNonConstantWitness_Bpos` (already unconditional
in `x`) plus trivial constant-positivity facts. -/
theorem boundedNonConstantWitness_EMLPfaffianValidOn {c a b : Real} (hc : 1 < c)
    (hc1 : Real.log c < 1) :
    EMLPfaffianValidOn (boundedNonConstantWitness c) a b := by
  unfold boundedNonConstantWitness
  refine ⟨trivial, ⟨⟨trivial, trivial, fun x _ _ => zero_lt_one_ax⟩,
    trivial, fun x _ _ => lt_trans_ax zero_lt_one_ax hc⟩, fun x _ _ => ?_⟩
  have h1 : (EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x = Real.exp x - Real.log 1 := rfl
  show (0:Real) < Real.exp ((EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x) - Real.log c
  rw [h1, log_one]
  have h2 : Real.exp x - 0 = Real.exp x := sub_zero _
  rw [h2]
  exact boundedNonConstantWitness_Bpos hc1 x

/-- `EMLPfaffianValidOn (growthCompetitionWitness c1 c2) a b`, for ANY `a, b`. Reuses the above
twice (once per inner constant) plus one trivial `exp(...) > 0` fact for the outer `log 1 = 0`
collapse. -/
theorem growthCompetitionWitness_EMLPfaffianValidOn {c1 c2 a b : Real}
    (hc1 : 1 < c1) (hc1' : Real.log c1 < 1) (hc2 : 1 < c2) (hc2' : Real.log c2 < 1) :
    EMLPfaffianValidOn (growthCompetitionWitness c1 c2) a b := by
  unfold growthCompetitionWitness
  refine ⟨boundedNonConstantWitness_EMLPfaffianValidOn hc1 hc1',
    ⟨boundedNonConstantWitness_EMLPfaffianValidOn hc2 hc2', trivial, fun x _ _ => zero_lt_one_ax⟩,
    fun x _ _ => ?_⟩
  show (0:Real) < Real.exp ((boundedNonConstantWitness c2).eval x) - Real.log 1
  rw [log_one]
  have h : Real.exp ((boundedNonConstantWitness c2).eval x) - 0
      = Real.exp ((boundedNonConstantWitness c2).eval x) := sub_zero _
  rw [h]
  exact Real.exp_pos _

/-- **THE FULL CLOSURE.** `growthCompetitionWitness c1' c2'` can never be part of a genuine
counterexample to the witness-finding theorem — for ANY valid `c1', c2'` (not just the concrete
`2.2, 2.7` instance whose non-monotonicity was proven last round) and ANY outer `c2 > 1`. This is
a member of the SAME three-theorem family as `eml_depth2_witness_of_const_le_one_sibling`
(`c2≤1`), `eml_depth2_witness_of_const_sibling_unbounded_T1` (`T1` unbounded), and
`eml_depth2_witness_of_const_gt_one_sibling_simple_T1` (`RightChildrenSimplePositive`) — a fourth
family member, covering a T1 shape that is bounded, non-simple, AND non-monotonic all at once,
the exact combination none of the other three reach. -/
theorem eml_depth2_witness_of_const_gt_one_sibling_growthCompetition
    {c1' c2' : Real} (hc1 : 1 < c1') (hc1' : Real.log c1' < 1)
    (hc2' : 1 < c2') (hc2'' : Real.log c2' < 1)
    {S3 : EMLTree} {c2 : Real} (hc2 : 1 < c2)
    (hsin : ∀ x, (EMLTree.eml (growthCompetitionWitness c1' c2')
      (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, S3.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (S3.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hT1eq := eml_T1eq_of_const_sibling_le_zero hc2 hallle hsin
  have hvalidon_any_b : ∀ b : Real, 0 < b → EMLPfaffianValidOn (growthCompetitionWitness c1' c2') 0 b :=
    fun b _ => growthCompetitionWitness_EMLPfaffianValidOn hc1 hc1' hc2' hc2''
  exact T1_not_eq_log_c2_plus_sin_given_validon c2 hc2 (growthCompetitionWitness c1' c2') hT1eq
    hvalidon_any_b

end Real
end MachLib
