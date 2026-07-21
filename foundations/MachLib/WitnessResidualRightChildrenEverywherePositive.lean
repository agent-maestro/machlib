import MachLib.WitnessResidualGrowthCompetitionValidOn
import MachLib.WitnessResidualChainSkeleton
import MachLib.WitnessResidualSimpleT1Application

/-! # Generalizing the `growthCompetitionWitness` closure route: no-clamp-anywhere ⟹ free validity

`WitnessResidualGrowthCompetitionValidOn.lean` found that `EMLPfaffianValidOn` falls out of
`growthCompetitionWitness`'s SPECIFIC structure by direct recursion, because every log-argument
positivity condition needed was ALREADY available unconditionally in `x` (no interval, no case
split — `boundedNonConstantWitness_Bpos`). That file flagged, but didn't pursue, whether the
underlying mechanism is general: "if every log-argument positivity fact in the tree is available
UNCONDITIONALLY, `EMLPfaffianValidOn` is free, by direct structural recursion... not tied to
`growthCompetitionWitness`'s specific shape at all."

**This file confirms it.** `RightChildrenEverywherePositive` is the general predicate:
`True` at every leaf; at `eml t1 t2`, both children satisfy it recursively AND `t2` is positive
for EVERY `x` (not `∀x ∈ (a,b)` — no interval at all). `EMLPfaffianValidOn_of_right_children_
everywhere_positive` converts this into `EMLPfaffianValidOn T a b` for ANY `a, b`, by one
structural induction mirroring `EMLPfaffianValidOn`'s own recursive shape exactly — the induction
step is a single line (`⟨ih1 h1, ih2 h2, fun x _ _ => h3 x⟩`), since the ONLY thing changing is
weakening `∀x` to `∀x ∈ (a,b)`.

**Relationship to `RightChildrenSimplePositive`** (`WitnessResidualSimpleRightChildren.lean`,
the FIRST unconditional closure in the whole arc) — CORRECTED from an earlier draft of this note:
these are INCOMPARABLE, complementary conditions, NEITHER subsuming the other. `RightChildren
SimplePositive` explicitly allows a right child to be `var` (`t2 = EMLTree.var`, see its
definition) — and `var.eval x = x` is positive only for `x > 0`, NOT unconditionally. That
predicate's own closure mechanism (`eml_witnesses_of_right_children_simple_positive`) only ever
needs a SINGLE-POINT witness (`EMLWitnesses A x0` at some `x0 > 0`), not uniform positivity — a
genuinely different technique. So a `RightChildrenSimplePositive` tree with a bare `var` right
child does NOT satisfy `RightChildrenEverywherePositive`. Conversely `RightChildrenEverywhere
Positive` allows arbitrarily COMPOUND right children (not just leaves) as long as their positivity
holds for every `x` — `growthCompetitionWitness` is the witness that this is a real, non-empty
extension in ITS direction. The two predicates cover genuinely different, overlapping-but-neither-
contained-in-the-other slices of the "right child is positive enough" space.

**Relationship to the OTHER existing route to `EMLPfaffianValidOn`**
(`eml_pfaffian_validon_of_witnesses_backward`/`_twosided`, `EMLSmoothness.lean`): that mechanism
derives validity from a SINGLE-POINT witness (`EMLWitnesses t x0`) plus no-crossing plus
differentiability — genuinely more powerful in principle (works even where positivity ISN'T
uniform, as long as there's no sign change), but correspondingly harder to discharge in practice
(needs the crossing-analysis machinery this whole arc has spent weeks building out one shape at a
time). `RightChildrenEverywherePositive` is a much BLUNTER instrument — it only ever applies to
trees that never clamp at all — but for exactly that (real, useful) class, it is closable in a
single pass with no case analysis whatsoever.

**Confirmed via a sanity-check corollary**: `growthCompetitionWitness_EMLPfaffianValidOn_via_
general` re-derives `WitnessResidualGrowthCompetitionValidOn.lean`'s hand-built result EXACTLY
through this general machinery — the generalization captures the same content, not merely a
similar-looking one.

**The closure itself is generalized too, not just the validity derivation.** `eml_depth2_witness_
of_const_gt_one_sibling_growthCompetition` (`WitnessResidualGrowthCompetitionValidOn.lean`) never
actually used anything specific to `growthCompetitionWitness` beyond feeding its `EMLPfaffianValidOn`
into the SAME generic pieces (`eml_T1eq_of_const_sibling_le_zero`,
`T1_not_eq_log_c2_plus_sin_given_validon`) that were ALREADY tree-agnostic. Restating it to take
`RightChildrenEverywherePositive T1` directly, for an ARBITRARY `T1`, turns a two-tree result
into an infinite-family one: `eml_depth2_witness_of_const_gt_one_sibling_right_children_
everywhere_positive` — ANY tree satisfying the predicate, not just `growthCompetitionWitness`,
can never be part of a counterexample. Confirmed via a second sanity-check corollary that this
reproduces the specific `growthCompetitionWitness` closure exactly.

**Open, honestly**: which OTHER trees in this arc (or future ones) actually satisfy
`RightChildrenEverywherePositive` is not surveyed here. Every other "compound tree" investigation
in this whole arc (`EMLZeroCrossingDomainSplit*.lean` and its many variants) deliberately explores
trees whose right children DO cross zero — the interesting, hard case this predicate structurally
excludes by design. Whether a genuinely NEW, non-constant tree exists that's both compound AND
covered by this predicate (beyond `growthCompetitionWitness` itself) is unexplored — but now that
the CLOSURE itself is general, any future such discovery gets the witness-finding result for free,
no bespoke proof needed. -/

namespace MachLib
namespace Real

open EMLTree

/-- A tree where every right child, throughout the WHOLE structure, is provably positive for
EVERY `x` — not `∀x` restricted to some interval, genuinely unconditional. INCOMPARABLE to
`RightChildrenSimplePositive` (see the module docstring) — allows compound right children that
predicate excludes, but is strictly stronger about the leaf case `var` (which that predicate
allows despite `var.eval x = x` not being everywhere positive). -/
def RightChildrenEverywherePositive : EMLTree → Prop
  | EMLTree.const _ => True
  | EMLTree.var => True
  | EMLTree.eml t1 t2 =>
      RightChildrenEverywherePositive t1 ∧ RightChildrenEverywherePositive t2
        ∧ (∀ x, 0 < t2.eval x)

/-- **The general closure.** `RightChildrenEverywherePositive T` gives `EMLPfaffianValidOn T a b`
for ANY `a, b` — one structural induction, mirroring `EMLPfaffianValidOn`'s own shape exactly. -/
theorem EMLPfaffianValidOn_of_right_children_everywhere_positive {T : EMLTree}
    (h : RightChildrenEverywherePositive T) (a b : Real) :
    EMLPfaffianValidOn T a b := by
  induction T with
  | const c => trivial
  | var => trivial
  | eml t1 t2 ih1 ih2 =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨ih1 h1, ih2 h2, fun x _ _ => h3 x⟩

theorem boundedNonConstantWitness_RightChildrenEverywherePositive {c : Real} (hc : 1 < c)
    (hc1 : Real.log c < 1) :
    RightChildrenEverywherePositive (boundedNonConstantWitness c) := by
  refine ⟨trivial, ⟨⟨trivial, trivial, fun _ => zero_lt_one_ax⟩, trivial,
    fun _ => lt_trans_ax zero_lt_one_ax hc⟩, fun x => ?_⟩
  have h1 : (EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x = Real.exp x - Real.log 1 := rfl
  show (0:Real) < Real.exp ((EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x) - Real.log c
  rw [h1, log_one]
  have h2 : Real.exp x - 0 = Real.exp x := sub_zero _
  rw [h2]
  exact boundedNonConstantWitness_Bpos hc1 x

theorem growthCompetitionWitness_RightChildrenEverywherePositive {c1 c2 : Real}
    (hc1 : 1 < c1) (hc1' : Real.log c1 < 1) (hc2 : 1 < c2) (hc2' : Real.log c2 < 1) :
    RightChildrenEverywherePositive (growthCompetitionWitness c1 c2) := by
  refine ⟨boundedNonConstantWitness_RightChildrenEverywherePositive hc1 hc1',
    ⟨boundedNonConstantWitness_RightChildrenEverywherePositive hc2 hc2', trivial,
      fun _ => zero_lt_one_ax⟩, fun x => ?_⟩
  show (0:Real) < Real.exp ((boundedNonConstantWitness c2).eval x) - Real.log 1
  rw [log_one]
  have h : Real.exp ((boundedNonConstantWitness c2).eval x) - 0
      = Real.exp ((boundedNonConstantWitness c2).eval x) := sub_zero _
  rw [h]
  exact Real.exp_pos _

/-- Sanity check: the general machinery reproduces `WitnessResidualGrowthCompetitionValidOn.lean`'s
hand-built `growthCompetitionWitness_EMLPfaffianValidOn` exactly. -/
theorem growthCompetitionWitness_EMLPfaffianValidOn_via_general {c1 c2 a b : Real}
    (hc1 : 1 < c1) (hc1' : Real.log c1 < 1) (hc2 : 1 < c2) (hc2' : Real.log c2 < 1) :
    EMLPfaffianValidOn (growthCompetitionWitness c1 c2) a b :=
  EMLPfaffianValidOn_of_right_children_everywhere_positive
    (growthCompetitionWitness_RightChildrenEverywherePositive hc1 hc1' hc2 hc2') a b

/-- **THE FULLY GENERAL CLOSURE.** ANY `T1` satisfying `RightChildrenEverywherePositive` can
never be part of a genuine witness-finding counterexample — not just `growthCompetitionWitness`,
any tree at all whose every log-argument positivity fact is unconditional. Supersedes
`eml_depth2_witness_of_const_gt_one_sibling_growthCompetition`
(`WitnessResidualGrowthCompetitionValidOn.lean`), which is kept as-is (not refactored to call
this) since it's already shipped and its specific statement is still useful on its own. -/
theorem eml_depth2_witness_of_const_gt_one_sibling_right_children_everywhere_positive
    {T1 S3 : EMLTree} {c2 : Real} (hc2 : 1 < c2) (hT1valid : RightChildrenEverywherePositive T1)
    (hsin : ∀ x, (EMLTree.eml T1 (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, S3.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (S3.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hT1eq := eml_T1eq_of_const_sibling_le_zero hc2 hallle hsin
  have hvalidon_any_b : ∀ b : Real, 0 < b → EMLPfaffianValidOn T1 0 b :=
    fun b _ => EMLPfaffianValidOn_of_right_children_everywhere_positive hT1valid 0 b
  exact T1_not_eq_log_c2_plus_sin_given_validon c2 hc2 T1 hT1eq hvalidon_any_b

/-- Sanity check: the general closure reproduces the `growthCompetitionWitness`-specific one. -/
theorem eml_depth2_witness_of_const_gt_one_sibling_growthCompetition_via_general
    {c1' c2' : Real} (hc1 : 1 < c1') (hc1' : Real.log c1' < 1)
    (hc2' : 1 < c2') (hc2'' : Real.log c2' < 1)
    {S3 : EMLTree} {c2 : Real} (hc2 : 1 < c2)
    (hsin : ∀ x, (EMLTree.eml (growthCompetitionWitness c1' c2')
      (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 :=
  eml_depth2_witness_of_const_gt_one_sibling_right_children_everywhere_positive hc2
    (growthCompetitionWitness_RightChildrenEverywherePositive hc1 hc1' hc2' hc2'') hsin

end Real
end MachLib
