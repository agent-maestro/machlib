import MachLib.WitnessResidualGrowthCompetitionValidOn

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
the FIRST unconditional closure in the whole arc): that predicate requires every right child to
be a LEAF (`var` or a positive constant) — positivity is then trivial by construction, but the
tree shape itself is heavily restricted. `RightChildrenEverywherePositive` drops the "leaf" part
entirely — right children can be arbitrarily COMPOUND, as long as their positivity can be proven
unconditionally by OTHER means (a derivative argument, an algebraic identity, whatever). Strictly
more general: any `RightChildrenSimplePositive` tree trivially satisfies
`RightChildrenEverywherePositive` too (a leaf's positivity, if it holds at all, holds
unconditionally by definition), but the converse fails — `growthCompetitionWitness` itself is the
witness, since its right children are genuinely compound (not leaves) yet still provably positive
everywhere.

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

**Open, honestly**: which OTHER trees in this arc (or future ones) actually satisfy
`RightChildrenEverywherePositive` is not surveyed here. Every other "compound tree" investigation
in this whole arc (`EMLZeroCrossingDomainSplit*.lean` and its many variants) deliberately explores
trees whose right children DO cross zero — the interesting, hard case this predicate structurally
excludes by design. Whether a genuinely NEW, non-constant tree exists that's both compound AND
covered by this predicate (beyond `growthCompetitionWitness` itself) is unexplored. -/

namespace MachLib
namespace Real

open EMLTree

/-- A tree where every right child, throughout the WHOLE structure, is provably positive for
EVERY `x` — not `∀x` restricted to some interval, genuinely unconditional. Strictly more general
than `RightChildrenSimplePositive` (drops the "must be a leaf" requirement entirely). -/
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

end Real
end MachLib
