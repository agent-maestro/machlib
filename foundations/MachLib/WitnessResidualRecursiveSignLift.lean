import MachLib.WitnessResidualQuantitativeBound
import MachLib.WitnessResidualBoundedNonConstant

/-! # The full recursive lift: `AllRightChildrenSignDefinite`, proven by structural induction

Lifts `WitnessResidualSignNecessity.lean`'s ONE-LEVEL necessary condition (`eml A B` bounded
above ⟹ `B` sign-definite) to a genuine, fully recursive statement about an ENTIRE compound
tree's structure — the piece explicitly flagged as not yet attempted at the end of that file.

**The obstacle, found and worked through rather than assumed away.** The natural first attempt —
"if `T` is bounded, its immediate right child is sign-definite; recurse into `T`'s left and right
children using the SAME top-level bound" — does NOT work. Checked directly: `boundedNonConstantWitness`
itself is a counterexample to naive propagation. `T := eml var B` (`B` compound) is bounded
overall via a delicate CANCELLATION between `exp(x)` and `log(B(x))` as `x→±∞` — but `x ↦ x`
(the bare `var` playing `T`'s own left child) is individually UNBOUNDED, and `B` itself need not be
bounded ABOVE either (only bounded away from `0` below, per `WitnessResidualQuantitativeBound.lean`).
Boundedness of a compound tree does NOT require boundedness of its parts; parts can individually
diverge and still cancel. So the recursive theorem cannot take "T is bounded" as its only
hypothesis and derive everything by propagation — it needs an EXPLICIT per-node hypothesis
package, supplied by the caller (exactly how `EMLPfaffianValidOn` and `RightChildrenEverywherePositive`
themselves are already structured, incidentally — this arc's own prior definitions had already
made the right design choice for reasons that are now explicit).

**A second obstacle, found while testing the hypothesis against `boundedNonConstantWitness`
directly.** The natural per-node hypothesis ("every `eml` node's own eval is bounded above")
is too strong — `boundedNonConstantWitness`'s own inner node `eml var (const 1)` (`= exp(x)`,
literally unbounded above) fails it, even though its right child (`const 1`) is trivially
sign-definite and needs no boundedness argument at all: a literal constant's sign is decidable
directly (`lt_total 0 c`), with no derivative or IVT machinery required. `SupportsSignAnalysis`
special-cases this: nodes whose right child is a literal `const` skip the boundedness requirement
entirely, only demanding it where the one-level theorem is actually needed (right child `var` or
compound).

**`AllRightChildrenSignDefinite`**: the recursive CONCLUSION, mirroring `RightChildrenEverywherePositive`'s
own shape exactly but weaker — allows either positive-everywhere OR non-positive-everywhere at
each right child (matching the sign-necessity dichotomy, not just the positive half).

**`supportsSignAnalysis_sign_definite_and_diff`**: the main theorem, proven by structural
induction on the tree, concluding BOTH `AllRightChildrenSignDefinite` throughout AND
differentiability everywhere (needed together — the differentiability half is what lets the
induction invoke the one-level theorem again one level up). `eml_node_sign_and_diff` factors out
the shared "given a differentiable right child and this node's own bound, get sign + this node's
own differentiability" step, reused for both the `var` and compound-right-child cases.

**Confirmed against a real construction, not left as an abstract exercise.**
`boundedNonConstantWitness_supportsSignAnalysis` verifies `boundedNonConstantWitness` — the safe
building block this entire arc has relied on since its first appearance — genuinely satisfies
`SupportsSignAnalysis` (using its own already-established upper bound,
`boundedNonConstantWitness_upper_bound`, at the top level, with every inner node's bound
requirement vanishing via the `const`-right-child special case). `boundedNonConstantWitness_
allRightChildrenSignDefinite` then applies the main theorem, concluding
`AllRightChildrenSignDefinite (boundedNonConstantWitness c)` — proven via the GENERAL machinery
here, not by re-deriving positivity by hand the way every earlier file in this arc did for this
exact tree.

`sorryAx`-free, verified via a genuinely fresh rebuild: same axiom footprint as the one-level
results this builds on (foundational axioms plus `hasDerivAt_continuousAt` and `sup_exists`) — no
dependence on `EMLPfaffianValidOn` or `eml_pfaffian_validon_from_sin_equality`. -/

namespace MachLib
namespace Real

/-- Recursive predicate mirroring `RightChildrenEverywherePositive`'s shape, but weaker: allows
EITHER positive-everywhere OR non-positive-everywhere at each right child (not just positive). -/
def AllRightChildrenSignDefinite : EMLTree → Prop
  | EMLTree.const _ => True
  | EMLTree.var => True
  | EMLTree.eml t1 t2 =>
      AllRightChildrenSignDefinite t1 ∧ AllRightChildrenSignDefinite t2 ∧
        ((∀ x : Real, 0 < t2.eval x) ∨ (∀ x : Real, t2.eval x ≤ 0))

/-- The per-node hypothesis the recursion needs: at every internal `eml`-node whose right child
is NOT a literal constant (const's own sign is decidable directly, no boundedness argument
needed), THAT NODE'S OWN sub-evaluation must be bounded above. -/
def SupportsSignAnalysis : EMLTree → Prop
  | EMLTree.const _ => True
  | EMLTree.var => True
  | EMLTree.eml t1 (EMLTree.const _) => SupportsSignAnalysis t1
  | EMLTree.eml t1 t2 =>
      SupportsSignAnalysis t1 ∧ SupportsSignAnalysis t2 ∧
        (∃ M : Real, ∀ x : Real, (EMLTree.eml t1 t2).eval x ≤ M)

/-- Shared step: given `t2` differentiable, `t1`'s own recursive facts, and THIS node's own
boundedness, conclude sign-definiteness of the whole `eml t1 t2` node plus its own
differentiability. -/
theorem eml_node_sign_and_diff (t1 t2 : EMLTree)
    (hdiff1 : ∀ z : Real, ∃ t1d : Real, HasDerivAt t1.eval t1d z)
    (hdiff2 : ∀ z : Real, ∃ t2d : Real, HasDerivAt t2.eval t2d z)
    (M : Real) (hM : ∀ x : Real, (EMLTree.eml t1 t2).eval x ≤ M) :
    ((∀ x : Real, 0 < t2.eval x) ∨ (∀ x : Real, t2.eval x ≤ 0)) ∧
    (∀ z : Real, ∃ Td : Real, HasDerivAt (EMLTree.eml t1 t2).eval Td z) := by
  have hsign := eml_A_B_bounded_above_sign_definite t1 t2 hdiff2 M hM
  refine ⟨hsign, ?_⟩
  intro z
  rcases hsign with hpos | hnonpos
  · obtain ⟨t1d, ht1d⟩ := hdiff1 z
    obtain ⟨t2d, ht2d⟩ := hdiff2 z
    have hexpcomp := HasDerivAt_comp Real.exp t1.eval t1d (Real.exp (t1.eval z)) z ht1d
      (HasDerivAt_exp _)
    have hlogcomp := HasDerivAt_comp Real.log t2.eval t2d (1 / t2.eval z) z ht2d
      (HasDerivAt_log_pos _ (hpos z))
    exact ⟨_, HasDerivAt_sub (fun w => Real.exp (t1.eval w)) (fun w => Real.log (t2.eval w))
      (Real.exp (t1.eval z) * t1d) (1 / t2.eval z * t2d) z hexpcomp hlogcomp⟩
  · obtain ⟨t1d, ht1d⟩ := hdiff1 z
    have hexpcomp := HasDerivAt_comp Real.exp t1.eval t1d (Real.exp (t1.eval z)) z ht1d
      (HasDerivAt_exp _)
    have heq : ∀ y : Real, Real.exp (t1.eval y) = (EMLTree.eml t1 t2).eval y :=
      fun y => (eml_A_B_eq_exp_A_of_nonpos t1 t2 hnonpos y).symm
    exact ⟨_, HasDerivAt_of_eq (fun w => Real.exp (t1.eval w)) (EMLTree.eml t1 t2).eval
      (Real.exp (t1.eval z) * t1d) z heq hexpcomp⟩

/-- **The full recursive lift.** Given per-node boundedness throughout (skipping literal
constant right children, whose sign never needs a boundedness argument), EVERY right child in
the WHOLE tree is sign-definite, AND the tree's own eval is differentiable everywhere. -/
theorem supportsSignAnalysis_sign_definite_and_diff (T : EMLTree) (hT : SupportsSignAnalysis T) :
    AllRightChildrenSignDefinite T ∧ (∀ z : Real, ∃ Td : Real, HasDerivAt T.eval Td z) := by
  induction T with
  | const c => exact ⟨trivial, fun z => ⟨0, HasDerivAt_const c z⟩⟩
  | var => exact ⟨trivial, fun z => ⟨1, HasDerivAt_id z⟩⟩
  | eml t1 t2 ih1 ih2 =>
    cases t2 with
    | const c2 =>
      obtain ⟨hrcsd1, hdiff1⟩ := ih1 hT
      have hsign : (∀ x : Real, 0 < (EMLTree.const c2).eval x) ∨
          (∀ x : Real, (EMLTree.const c2).eval x ≤ 0) := by
        show (∀ x : Real, (0 : Real) < c2) ∨ (∀ x : Real, c2 ≤ (0 : Real))
        rcases lt_total (0 : Real) c2 with h | h | h
        · exact Or.inl (fun _ => h)
        · exact Or.inr (fun _ => le_of_eq h.symm)
        · exact Or.inr (fun _ => le_of_lt h)
      refine ⟨⟨hrcsd1, trivial, hsign⟩, ?_⟩
      intro z
      rcases hsign with hpos | hnonpos
      · obtain ⟨t1d, ht1d⟩ := hdiff1 z
        have hexpcomp := HasDerivAt_comp Real.exp t1.eval t1d (Real.exp (t1.eval z)) z ht1d
          (HasDerivAt_exp _)
        have hlogcomp : HasDerivAt (fun w => Real.log ((EMLTree.const c2).eval w)) 0 z :=
          HasDerivAt_const (Real.log c2) z
        exact ⟨_, HasDerivAt_sub (fun w => Real.exp (t1.eval w))
          (fun w => Real.log ((EMLTree.const c2).eval w)) (Real.exp (t1.eval z) * t1d) 0 z
          hexpcomp hlogcomp⟩
      · obtain ⟨t1d, ht1d⟩ := hdiff1 z
        have hexpcomp := HasDerivAt_comp Real.exp t1.eval t1d (Real.exp (t1.eval z)) z ht1d
          (HasDerivAt_exp _)
        have heq : ∀ y : Real, Real.exp (t1.eval y) = (EMLTree.eml t1 (EMLTree.const c2)).eval y :=
          fun y => (eml_A_B_eq_exp_A_of_nonpos t1 (EMLTree.const c2) hnonpos y).symm
        exact ⟨_, HasDerivAt_of_eq (fun w => Real.exp (t1.eval w))
          (EMLTree.eml t1 (EMLTree.const c2)).eval (Real.exp (t1.eval z) * t1d) z heq hexpcomp⟩
    | var =>
      obtain ⟨hs1, _, hbdd⟩ := hT
      obtain ⟨hrcsd1, hdiff1⟩ := ih1 hs1
      obtain ⟨M, hM⟩ := hbdd
      have hdiff2 : ∀ z : Real, ∃ Bd : Real, HasDerivAt (EMLTree.var).eval Bd z :=
        fun z => ⟨1, HasDerivAt_id z⟩
      obtain ⟨hsign, hdiffT⟩ := eml_node_sign_and_diff t1 EMLTree.var hdiff1 hdiff2 M hM
      exact ⟨⟨hrcsd1, trivial, hsign⟩, hdiffT⟩
    | eml t2a t2b =>
      obtain ⟨hs1, hs2, hbdd⟩ := hT
      obtain ⟨hrcsd1, hdiff1⟩ := ih1 hs1
      obtain ⟨hrcsd2, hdiff2⟩ := ih2 hs2
      obtain ⟨M, hM⟩ := hbdd
      obtain ⟨hsign, hdiffT⟩ :=
        eml_node_sign_and_diff t1 (EMLTree.eml t2a t2b) hdiff1 hdiff2 M hM
      exact ⟨⟨hrcsd1, hrcsd2, hsign⟩, hdiffT⟩

/-- Sanity check: `boundedNonConstantWitness` — the safe building block this WHOLE arc has relied
on — genuinely satisfies `SupportsSignAnalysis`, confirming the recursive lift isn't a vacuous
abstraction. -/
theorem boundedNonConstantWitness_supportsSignAnalysis {c : Real} (hc : 1 < c)
    (hc1 : Real.log c < 1) : SupportsSignAnalysis (boundedNonConstantWitness c) := by
  refine ⟨trivial, trivial, -Real.log (1 - Real.log c), ?_⟩
  intro x
  exact le_of_lt (boundedNonConstantWitness_upper_bound hc hc1 x)

/-- The recursive lift, applied: `boundedNonConstantWitness`'s right children, EVERYWHERE in its
structure, are genuinely sign-definite — confirmed via the general machinery, not by re-deriving
it by hand as every prior file in this arc did. -/
theorem boundedNonConstantWitness_allRightChildrenSignDefinite {c : Real} (hc : 1 < c)
    (hc1 : Real.log c < 1) : AllRightChildrenSignDefinite (boundedNonConstantWitness c) :=
  (supportsSignAnalysis_sign_definite_and_diff (boundedNonConstantWitness c)
    (boundedNonConstantWitness_supportsSignAnalysis hc hc1)).1

end Real
end MachLib
