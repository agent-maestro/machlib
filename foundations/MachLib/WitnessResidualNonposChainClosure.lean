import MachLib.WitnessResidualClosureAttempt
import MachLib.WitnessResidualNestedTargetBWitness

/-! # The residual, fully closed for the "non-positive left-spine" special case

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). `WitnessResidualClosureAttempt.lean`
built two reusable techniques (differentiability transport, pointwise algebraic determination of
`B`) but did not close the residual — it left an "ambiguous set" (points where `exp(A(x))` hits
the target exactly) whose emptiness needed information about `A` not obviously available. This
file closes off a genuinely disjoint case where that ambiguity CANNOT arise at all: **`B ≤ 0`
everywhere, at every level of the tree's own left spine.**

**Why this case is special.** When `B ≤ 0` everywhere, `eml_A_B_eq_exp_A_of_nonpos`
(`WitnessResidualSignNecessity.lean`) already reduces `T1.eval x` to `exp(A.eval x)` exactly — no
ambiguity, no case split, no algebra needed to determine anything. The only question left is
whether `exp(A.eval x) = nestedTarget cs x` for all `x` is itself possible. That splits cleanly on
`nestedLo cs`: if `nestedLo cs ≤ 0`, evaluating at `x = -π/2` (`nestedTarget`'s own attained
minimum, via the pre-existing `nestedTarget_at_neg_pi_div_two`) forces `exp(A(-π/2)) ≤ 0`,
contradicting `exp > 0` immediately. If `nestedLo cs > 0`, the exponential can be undone by `log`
(`log_exp`), giving `A.eval x = nestedTarget (0 :: cs) x` for ALL `x` — i.e. `A` itself equals
one level DEEPER in the same nested-target family. Since `A` is a genuine subterm of `T1`, this is
a real structural recursion: `no_tree_eq_nested_target_of_BChainNonpos` inducts on the tree,
re-applying the same argument to `A` against `cs` with one more `0` prepended, terminating at the
`const`/`var` base cases (two small new lemmas: a constant can't match `nestedTarget cs` because
the family takes two different values, at `kπ` and at `π+1`, already established by
`nestedTarget_facts`; `var` can't match because `nestedTarget cs` is bounded by `nestedHi cs` but
`id` is not).

**Scope, stated honestly.** `BChainNonpos` requires `B ≤ 0` everywhere at EVERY `eml` node down
the tree's own left spine, not just at the top. This is the "opposite extreme" from
`RightChildrenEverywherePositive` (which requires every right child positive) — together the two
results now fully cover both endpoints of the sign spectrum. What remains open is the same
"mixed" case flagged in `WitnessResidualClosureAttempt.lean`: some right child that is positive
somewhere and non-positive elsewhere. That case is NOT addressed here. (Promising unexplored
connection for whoever continues: a right child that takes both signs is by definition a
CROSSING in the sense of `WitnessResidualCrossingUnboundedGeneral.lean`, and `nestedTarget cs` is
BOUNDED — so if the crossing machinery's differentiability hypothesis could be established for an
arbitrary compound `B`, the "mixed" case might force unboundedness, contradicting boundedness,
and close as well. That connection is unexplored, not merely unproven — it has not been checked
even informally beyond this one paragraph.)

`sorryAx`-free, verified via a genuinely fresh rebuild. Depends on nothing beyond this codebase's
base ordered-field/trig/exp axioms — no `EMLPfaffianValidOn`, no
`eml_pfaffian_validon_from_sin_equality`, no differentiability axioms at all (this case needed
none). -/

namespace MachLib
namespace Real

/-- A tree built by nesting `eml` purely down its left spine, where every right child along
that spine is non-positive everywhere. `const`/`var` are the base cases (trivially `True`, since
the predicate only constrains `eml` nodes). -/
def BChainNonpos : EMLTree → Prop
  | EMLTree.const _ => True
  | EMLTree.var => True
  | EMLTree.eml A B => (∀ x : Real, B.eval x ≤ 0) ∧ BChainNonpos A

/-- A constant tree can never equal any member of the nested-target family: the family takes two
different values (`nestedLevel cs` at every `kπ`, something else at `π + 1`, per
`nestedTarget_facts`), which a constant function cannot. -/
theorem const_ne_nestedTarget (c : Real) (cs : List Real) (hwf : nestedWF cs)
    (hT1eq : ∀ x : Real, (EMLTree.const c).eval x = nestedTarget cs x) : False := by
  obtain ⟨_, hkpi, hpi1⟩ := nestedTarget_facts cs hwf
  have h1 := hT1eq (natCast 1 * pi)
  have h2 := hT1eq (pi + 1)
  have hceval1 : (EMLTree.const c).eval (natCast 1 * pi) = c := rfl
  have hceval2 : (EMLTree.const c).eval (pi + 1) = c := rfl
  rw [hceval1] at h1
  rw [hceval2] at h2
  rw [hkpi 1 (Nat.le_refl 1)] at h1
  have heq : nestedTarget cs (pi + 1) = nestedLevel cs := by rw [← h2]; exact h1
  exact hpi1 heq

/-- The identity tree (`var`) can never equal any member of the nested-target family: the family
is bounded above by `nestedHi cs` (`nestedTarget_facts`), but `id` is unbounded. -/
theorem var_ne_nestedTarget (cs : List Real) (hwf : nestedWF cs)
    (hT1eq : ∀ x : Real, EMLTree.var.eval x = nestedTarget cs x) : False := by
  obtain ⟨hrange, _, _⟩ := nestedTarget_facts cs hwf
  have hx := hT1eq (nestedHi cs + 1)
  have hxeval : EMLTree.var.eval (nestedHi cs + 1) = nestedHi cs + 1 := rfl
  rw [hxeval] at hx
  have hle := (hrange (nestedHi cs + 1)).2
  rw [← hx] at hle
  have hlt : nestedHi cs < nestedHi cs + 1 := by
    have h := add_lt_add_left one_pos (nestedHi cs); rwa [add_zero] at h
  exact lt_irrefl_ax (nestedHi cs) (lt_of_lt_of_le hlt hle)

/-- **The main closure.** No tree whose left spine is entirely non-positive-right-child can equal
any member of the nested-target family — unconditionally, no `EMLPfaffianValidOn` hypothesis
anywhere. Proven by structural induction on the tree: `const`/`var` are immediate (the two lemmas
above), and the `eml A B` case reduces to `A` matching one level deeper into the same family
(`0 :: cs`), recursing on the strictly smaller subterm `A`. -/
theorem no_tree_eq_nested_target_of_BChainNonpos :
    ∀ (T : EMLTree), BChainNonpos T →
      ∀ (cs : List Real), nestedWF cs → (∀ x : Real, T.eval x = nestedTarget cs x) → False := by
  intro T
  induction T with
  | const c => intro _ cs hwf hT1eq; exact const_ne_nestedTarget c cs hwf hT1eq
  | var => intro _ cs hwf hT1eq; exact var_ne_nestedTarget cs hwf hT1eq
  | eml A B ihA _ihB =>
    intro hchain cs hwf hT1eq
    obtain ⟨hBnonpos, hAchain⟩ := hchain
    have hexpA : ∀ x : Real, Real.exp (A.eval x) = nestedTarget cs x := by
      intro x
      have hred := eml_A_B_eq_exp_A_of_nonpos A B hBnonpos x
      rw [← hred]; exact hT1eq x
    have hcontra_of_le : nestedLo cs ≤ 0 → False := by
      intro hle
      have hx0 := hexpA (-(pi / (1 + 1)))
      rw [nestedTarget_at_neg_pi_div_two cs hwf] at hx0
      have hpos := Real.exp_pos (A.eval (-(pi / (1 + 1))))
      rw [hx0] at hpos
      exact lt_irrefl_ax 0 (lt_of_lt_of_le hpos hle)
    rcases lt_total (nestedLo cs) 0 with hlo | hlo | hlo
    · exact hcontra_of_le (le_of_lt hlo)
    · exact hcontra_of_le (le_of_eq hlo)
    · have hwf0 : nestedWF (0 :: cs) := by
        refine ⟨?_, hwf⟩
        rw [zero_add]; exact hlo
      have hAeq : ∀ x : Real, A.eval x = nestedTarget (0 :: cs) x := by
        intro x
        rw [nestedTarget_cons, zero_add, ← hexpA x, log_exp]
      exact ihA hAchain (0 :: cs) hwf0 hAeq

end Real
end MachLib
