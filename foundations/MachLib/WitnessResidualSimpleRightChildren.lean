import MachLib.WitnessResidualNestedTargetBWitness
import MachLib.WitnessResidualDepth2ABConjuncts
import MachLib.Differentiation

/-!
# A complete end-to-end closure, for trees with simple right children

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Every prior file in
this arc left `EMLPfaffianValidOn T1` (equivalently, `EMLWitnesses T1 x0` for some `x0`) as an
explicit, undischarged hypothesis — the "recursive wall" confirmed from two independent angles
in the previous file. This file asks a narrower, answerable question: is there a natural,
CHECKABLE class of trees for which the wall doesn't bite at all?

**Yes: trees whose right children, at every `eml` node throughout the WHOLE tree (recursively),
are either the bare variable or a POSITIVE constant** — never a compound subtree, never a
non-positive constant. Call this `RightChildrenSimplePositive`. Left children are completely
UNRESTRICTED — can be arbitrarily deep and compound — only right children are constrained, and
only in shape, not depth.

**Why this class evades the wall, and a real subtlety found while assembling the proof (not
anticipated going in).** `EMLWitnesses`'s recursive definition needs `0 < (right child).eval x0`
at ONE point — trivial to satisfy uniformly for simple right children (any `x0>0` for `var`; no
constraint at all for a positive constant). But `EMLPfaffianValidOn`'s underlying machinery ALSO
needs `EMLNoCrossingAt` — `(right child).eval x ≠ 0` throughout a whole INTERVAL, not one point —
and for the OUTER tree `T1 = eml A B`, that third conjunct is about `B`'s own overall VALUE, not
about `B`'s internal right-children. One positive point (which is all
`witness_B_pos_at_point_of_lo_neg` from the previous file supplies) genuinely cannot establish
"nonzero throughout an interval" for a compound `B`. The fix that actually works: require `B`
ITSELF — not just its descendants — to be `var` or a positive constant. Concretely, that means
applying `RightChildrenSimplePositive` to the WHOLE tree `T1 = eml A B` at once (which, unfolded,
is exactly `RightChildrenSimplePositive A ∧ (B = var ∨ ∃c, B = const c ∧ 0<c)`) rather than to
`A` and `B` as two separate hypotheses. Once `B` is simple at the top level, its positivity and
non-vanishing hold EVERYWHERE for free, and — a genuine surprise — `nestedLo cs < 0` (needed for
the elementary trick that would have supplied a compound `B`'s positivity) turns out not to be
needed at all: this closure holds for literally any well-formed `cs`.

**What this closes.** `no_T1_with_simple_right_children`: no finite tree `T1 = eml A B` with
`RightChildrenSimplePositive T1`, can satisfy `T1.eval = nestedTarget cs` globally, for ANY
well-formed `cs` — a COMPLETE, unconditional closure (no undischarged hypotheses) for this
class. This is the first result in the whole Option D arc that doesn't leave
`EMLPfaffianValidOn`/`EMLWitnesses` as a hypothesis for someone else to discharge.

**What this doesn't close, honestly.** `RightChildrenSimplePositive` is a real restriction —
`WitnessResidualCancellation.lean`'s counterexample tree has a compound right child at its top
node and falls outside this class. The fully general case (arbitrary `A`, `B`) is exactly as
open as the previous file left it. This result narrows WHERE the wall matters, it doesn't remove
the wall. `witness_B_pos_at_point_of_lo_neg` (below) is kept as a standalone result — genuinely
useful for the `EMLWitnesses` third conjunct on its own terms — even though the final closure
theorem doesn't end up needing it, precisely because of the point-vs-interval gap explained
above; that gap is itself a real, worth-recording finding about why the third conjunct alone
was never going to be enough.
-/

namespace MachLib

open MachLib.Real

/-! ## `RightChildrenSimplePositive`: the restricted class -/

/-- Every right child, at every `eml` node throughout the tree (recursively — left children are
unrestricted, but THEIR right children are constrained too), is either `var` or a positive
constant. -/
def RightChildrenSimplePositive : EMLTree → Prop
  | .const _ => True
  | .var => True
  | .eml t1 t2 => RightChildrenSimplePositive t1 ∧
      (t2 = EMLTree.var ∨ ∃ c : Real, t2 = EMLTree.const c ∧ 0 < c)

/-- **`EMLWitnesses` is free for this class, at any `x0 > 0`.** No target equation needed —
purely structural, by induction on the tree. -/
theorem eml_witnesses_of_right_children_simple_positive
    (A : EMLTree) (hA : RightChildrenSimplePositive A) (x0 : Real) (hx0 : 0 < x0) :
    EMLWitnesses A x0 := by
  induction A with
  | const c => trivial
  | var => trivial
  | eml t1 t2 ih1 _ih2 =>
    obtain ⟨hwf1, hwf2⟩ := hA
    refine ⟨ih1 hwf1, ?_, ?_⟩
    · rcases hwf2 with hvar | ⟨c, hc, _⟩
      · rw [hvar]; exact eml_witnesses_leaf_var x0
      · rw [hc]; exact eml_witnesses_leaf_const c x0
    · rcases hwf2 with hvar | ⟨c, hc, hcpos⟩
      · rw [hvar]; exact hx0
      · rw [hc]; exact hcpos

/-- **`EMLNoCrossingAt` is free for this class too, at any `x0 > 0`.** Same reason: a `var`
right child never evaluates to `0` when `x0 > 0`, and a positive constant never evaluates to `0`
at all. -/
theorem eml_no_crossing_of_right_children_simple_positive
    (A : EMLTree) (hA : RightChildrenSimplePositive A) (x0 : Real) (hx0 : 0 < x0) :
    EMLNoCrossingAt A x0 := by
  induction A with
  | const c => trivial
  | var => trivial
  | eml t1 t2 ih1 _ih2 =>
    obtain ⟨hwf1, hwf2⟩ := hA
    refine ⟨ih1 hwf1, ?_, ?_⟩
    · rcases hwf2 with hvar | ⟨c, hc, _⟩
      · rw [hvar]; trivial
      · rw [hc]; trivial
    · rcases hwf2 with hvar | ⟨c, hc, hcpos⟩
      · rw [hvar]; exact ne_of_gt hx0
      · rw [hc]; exact ne_of_gt hcpos

/-! ## A positive point where the nested target still hits its minimum -/

/-- Generalizes `nestedTarget_at_neg_pi_div_two` (`WitnessResidualNestedTargetBWitness.lean`)
from the specific point `-π/2` to ANY point `p` where `sin p = -1` — the `cons`-case induction
step never used anything about `-π/2` beyond `sin`'s value there. -/
theorem nestedTarget_at_sin_neg_one (cs : List Real) (hwf : nestedWF cs) (p : Real)
    (hp : Real.sin p = -1) :
    nestedTarget cs p = nestedLo cs := by
  induction cs with
  | nil => show Real.sin p = -1; exact hp
  | cons c cs' ih =>
    obtain ⟨hwf_c, hwf_cs'⟩ := hwf
    rw [nestedTarget_cons, nestedLo_cons, ih hwf_cs']

/-- `sin(π + π/2) = -1` — a POSITIVE point (unlike `-π/2`) where `sin` still hits its minimum,
via `sin(π+θ) = -sin θ` (`sin_add` + `sin_pi = 0` + `cos_pi = -1`) at `θ = π/2`. -/
theorem sin_pi_plus_pi_div_two : Real.sin (pi + pi / (1 + 1)) = -1 := by
  rw [Real.sin_add, Real.sin_pi, Real.cos_pi, Real.sin_pi_div_two]
  mach_ring

/-- `π + π/2 > 0`. -/
theorem pi_plus_pi_div_two_pos : (0 : Real) < pi + pi / (1 + 1) :=
  add_pos pi_pos (div_pos_of_pos_pos pi_pos (add_pos zero_lt_one_ax zero_lt_one_ax))

/-- **`0 < B.eval` at a CONCRETE, positive point** — not just `∃x0`, and specifically at the SAME
point `RightChildrenSimplePositive`'s witness lemmas above use (`π+π/2 > 0`). This is what makes
the final assembly possible: all three `EMLWitnesses T1 x0` conjuncts land on ONE common `x0`. -/
theorem witness_B_pos_at_point_of_lo_neg
    {A B : EMLTree} {cs : List Real} (hwf : nestedWF cs) (hlo : nestedLo cs < 0)
    (hT1eq : ∀ x, (EMLTree.eml A B).eval x = nestedTarget cs x) :
    0 < B.eval (pi + pi / (1 + 1)) := by
  have hble_or : B.eval (pi + pi / (1 + 1)) ≤ 0 ∨ 0 < B.eval (pi + pi / (1 + 1)) := by
    rcases lt_total 0 (B.eval (pi + pi / (1 + 1))) with h | h | h
    · exact Or.inr h
    · exact Or.inl (le_of_eq h.symm)
    · exact Or.inl (le_of_lt h)
  rcases hble_or with hble | hpos
  · exfalso
    have hlog0 : Real.log (B.eval (pi + pi / (1 + 1))) = 0 := Real.log_nonpos hble
    have h1 : Real.exp (A.eval (pi + pi / (1 + 1))) - Real.log (B.eval (pi + pi / (1 + 1)))
        = nestedTarget cs (pi + pi / (1 + 1)) := hT1eq (pi + pi / (1 + 1))
    rw [hlog0, sub_zero, nestedTarget_at_sin_neg_one cs hwf _ sin_pi_plus_pi_div_two] at h1
    rw [← h1] at hlo
    exact lt_irrefl_ax 0 (lt_trans_ax (Real.exp_pos _) hlo)
  · exact hpos

/-! ## `nestedTarget`'s derivative -/

/-- The derivative formula for `nestedTarget`, mirroring its own recursive shape: `sin`'s
derivative is `cos`; each further `log(c + ·)` layer contributes a `1/(c+·)` factor via the
chain rule, exactly the positivity `nestedWF` already guarantees never divides by zero or a
clamped argument. -/
noncomputable def nestedTargetDeriv : List Real → Real → Real
  | [], x => Real.cos x
  | c :: cs, x => (1 / (c + nestedTarget cs x)) * nestedTargetDeriv cs x

theorem nestedTargetDeriv_cons (c : Real) (cs : List Real) (x : Real) :
    nestedTargetDeriv (c :: cs) x = (1 / (c + nestedTarget cs x)) * nestedTargetDeriv cs x := rfl

/-- **`nestedTarget cs` is differentiable everywhere, with the formula above, given `nestedWF
cs`.** By induction on `cs`: the base case is `HasDerivAt_sin` transported across
`nestedTarget_nil` via `HasDerivAt_of_eq`; the step composes `HasDerivAt_log_pos` (positivity
from `nestedWF`'s own condition, combined with `nestedTarget_facts`'s range bound — no new
positivity argument needed) with the inductive hypothesis via `HasDerivAt_comp`, then transports
across `nestedTarget_cons` the same way. -/
theorem nestedTarget_hasDerivAt (cs : List Real) (hwf : nestedWF cs) (x : Real) :
    HasDerivAt (nestedTarget cs) (nestedTargetDeriv cs x) x := by
  induction cs generalizing x with
  | nil =>
    exact HasDerivAt_of_eq Real.sin (nestedTarget []) (Real.cos x) x
      (fun y => (nestedTarget_nil y).symm) (HasDerivAt_sin x)
  | cons c cs' ih =>
    obtain ⟨hwf_c, hwf_cs'⟩ := hwf
    have hihx : HasDerivAt (nestedTarget cs') (nestedTargetDeriv cs' x) x := ih hwf_cs' x
    have hinner : HasDerivAt (fun y => c + nestedTarget cs' y)
        (0 + nestedTargetDeriv cs' x) x :=
      HasDerivAt_add (fun _ => c) (nestedTarget cs') 0 (nestedTargetDeriv cs' x) x
        (HasDerivAt_const c x) hihx
    have hpos : (0 : Real) < c + nestedTarget cs' x := by
      have hr := (nestedTarget_facts cs' hwf_cs').1 x
      exact lt_of_lt_of_le hwf_c (add_le_add_left hr.1 c)
    have hlogcomp : HasDerivAt (fun y => Real.log (c + nestedTarget cs' y))
        ((1 / (c + nestedTarget cs' x)) * (0 + nestedTargetDeriv cs' x)) x :=
      HasDerivAt_comp Real.log (fun y => c + nestedTarget cs' y)
        (0 + nestedTargetDeriv cs' x) (1 / (c + nestedTarget cs' x)) x
        hinner (HasDerivAt_log_pos (c + nestedTarget cs' x) hpos)
    have hval : (1 / (c + nestedTarget cs' x)) * (0 + nestedTargetDeriv cs' x)
        = (1 / (c + nestedTarget cs' x)) * nestedTargetDeriv cs' x := by mach_ring
    rw [hval] at hlogcomp
    rw [nestedTargetDeriv_cons]
    exact HasDerivAt_of_eq (fun y => Real.log (c + nestedTarget cs' y)) (nestedTarget (c :: cs'))
      ((1 / (c + nestedTarget cs' x)) * nestedTargetDeriv cs' x) x
      (fun y => (nestedTarget_cons c cs' y).symm) hlogcomp

/-! ## The complete closure -/

/-- **No finite tree, with `RightChildrenSimplePositive` applied to the WHOLE tree `T1 = eml A
B` (not `A` and `B` separately), can equal any well-formed nested target — unconditionally, no
undischarged hypotheses.** Unfolded, the hypothesis says: `A` satisfies the recursive condition
(arbitrarily deep on its own left spine), AND `B` ITSELF is directly `var` or a positive
constant — not just `B`'s descendants. That stronger requirement on `B` specifically is what
makes this proof go through where `witness_B_pos_at_point_of_lo_neg` alone couldn't: `EMLWitnesses`'s
third conjunct only ever needs positivity at ONE point, but `EMLNoCrossingAt` (needed for
differentiability throughout the WHOLE interval, not just at the witness point) needs `B.eval x
≠ 0` EVERYWHERE in that interval — a fact one positive point can't supply for a compound `B`,
but which is immediate when `B` is itself a leaf. Discovered while assembling this proof, not
anticipated in advance: `nestedLo cs < 0` (needed for the elementary `B`-positivity trick when
`B` is compound) turns out NOT to be needed at all once `B` is required to be simple directly —
this closure holds for literally any well-formed `cs`. -/
theorem no_T1_with_simple_right_children
    {A B : EMLTree} {cs : List Real} (hwf : nestedWF cs)
    (hT1simple : RightChildrenSimplePositive (EMLTree.eml A B))
    (hT1eq : ∀ x, (EMLTree.eml A B).eval x = nestedTarget cs x) :
    False := by
  have hppos : (0 : Real) < pi + pi / (1 + 1) := pi_plus_pi_div_two_pos
  have hwitT1 : EMLWitnesses (EMLTree.eml A B) (pi + pi / (1 + 1)) :=
    eml_witnesses_of_right_children_simple_positive (EMLTree.eml A B) hT1simple _ hppos
  have hDdAll : ∀ x, HasDerivAt (EMLTree.eml A B).eval (nestedTargetDeriv cs x) x := fun x =>
    HasDerivAt_of_eq (nestedTarget cs) (EMLTree.eml A B).eval (nestedTargetDeriv cs x) x
      (fun y => (hT1eq y).symm) (nestedTarget_hasDerivAt cs hwf x)
  have hncAll : ∀ x, 0 < x → EMLNoCrossingAt (EMLTree.eml A B) x := fun x hx =>
    eml_no_crossing_of_right_children_simple_positive (EMLTree.eml A B) hT1simple x hx
  have hvalidon_any_b : ∀ b : Real, 0 < b → EMLPfaffianValidOn (EMLTree.eml A B) 0 b := by
    intro b hb
    rcases lt_total b (pi + pi / (1 + 1)) with hbp | hbp | hbp
    · exact EMLPfaffianValidOn_mono_b (le_of_lt hbp)
        (eml_pfaffian_validon_of_witnesses_backward (EMLTree.eml A B) 0 (pi + pi / (1 + 1)) hppos
          (nestedTargetDeriv cs) (fun x _ _ => hDdAll x) (fun x hx1 _ => hncAll x hx1) hwitT1)
    · rw [hbp]
      exact eml_pfaffian_validon_of_witnesses_backward (EMLTree.eml A B) 0 (pi + pi / (1 + 1))
        hppos (nestedTargetDeriv cs) (fun x _ _ => hDdAll x) (fun x hx1 _ => hncAll x hx1) hwitT1
    · exact eml_pfaffian_validon_of_witnesses_twosided (EMLTree.eml A B) 0 b (pi + pi / (1 + 1))
        hppos hbp (nestedTargetDeriv cs) (fun x _ _ => hDdAll x) (fun x hx1 _ => hncAll x hx1)
        hwitT1
  exact no_tree_eq_nested_target_given_validon cs hwf (EMLTree.eml A B) hT1eq hvalidon_any_b

end MachLib
