import MachLib.EMLPfaffian
import MachLib.Log
import MachLib.Exp

/-! # A fundamental, structural limit of `EMLPfaffianValidOn`: it cannot survive a positive crossing

`WitnessResidualExpWrappedNonMonotonicClosed.lean` closed `expWrappedNonMonotonicWitness` via the
pre-existing heavy machinery, but that resolution leaned on one specific structural fact: its
inner crossing (`nonMonotonicWitness`'s own `D := eml var (const 2)` hitting zero) sits at a
NEGATIVE `x` (`x0 = log(log 2) ≈ -0.37`), safely outside the `x > 0` region that machinery's
`no_tree_eq_nested_target_given_validon` route ever needs. That round's honest scope note
flagged the natural question: what if the crossing sat at POSITIVE `x` instead — same tree
shape, bigger crossing constant?

**This file confirms, rigorously, that the answer is not "the same technique still works
somehow" — it structurally CANNOT.** `EMLPfaffianValidOn`'s own definition demands strict
positivity of every log-argument throughout the WHOLE open interval; if some internal node's
right child hits exactly `0` anywhere inside `(a,b)`, `EMLPfaffianValidOn _ a b` is FALSE by a
single unfolding step — no induction, no case analysis, an almost immediate consequence of the
definition. Combined with the fact that failure at any sub-node propagates upward through
arbitrarily many further wrappings (a compound `eml v t2`'s own validity NEEDS both children
valid, unconditionally), a tree shaped like `expWrappedNonMonotonicWitness` but with its
crossing constant increased past `e` (so the crossing point `x0(c) = log(log c)` becomes
positive) has `EMLPfaffianValidOn _ 0 b` PROVABLY FALSE for every `b` past that crossing.

**What this does and does NOT establish.** This is a NEGATIVE, structural result about the
`EMLPfaffianValidOn`-based closure route specifically — it does NOT construct a new counterexample
to the witness-finding residual (that would additionally need proving
`expWrappedNonMonotonicWitnessC c` is bounded both directions and non-monotonic for such `c`,
which was only checked NUMERICALLY here, not formalized — see the concluding remark). What it
DOES establish, rigorously: the specific resolution technique from the previous round is not a
general-purpose tool that happens to work for every tree in the residual's open classification —
it structurally cannot reach ANY tree with a positive-x crossing, confirming (now via a concrete,
verified example, not just abstract reasoning) something this whole multi-week arc suspected much
earlier (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`'s "why path (1) is hard, precisely" entry):
positivity-based validity has no notion of a relation that switches sign, and genuinely cannot
describe a tree across a sign change without a branch-switching chain construction this codebase
does not yet have. -/

namespace MachLib
namespace Real

open EMLTree

/-- **The core fact, one unfolding step from the definition.** If a right child's value hits
`0` anywhere inside the open interval, validity fails there — `EMLPfaffianValidOn`'s own
positivity requirement is violated exactly at that point. -/
theorem eml_pfaffian_validon_false_of_crossing {s1 t2 : EMLTree} {a b x0 : Real}
    (hx0a : a < x0) (hx0b : x0 < b) (hcross : t2.eval x0 = 0) :
    ¬ EMLPfaffianValidOn (EMLTree.eml s1 t2) a b := by
  intro hvalid
  have h3 := hvalid.2.2 x0 hx0a hx0b
  rw [hcross] at h3
  exact lt_irrefl_ax _ h3

/-- Failure at a right child propagates up through further wrapping — `EMLPfaffianValidOn` of a
compound tree unconditionally needs its right child valid too. -/
theorem eml_pfaffian_validon_false_propagates_right {v t2 : EMLTree} {a b : Real}
    (hfail : ¬ EMLPfaffianValidOn t2 a b) :
    ¬ EMLPfaffianValidOn (EMLTree.eml v t2) a b :=
  fun h => absurd h.2.1 hfail

/-- Same, for the left child. -/
theorem eml_pfaffian_validon_false_propagates_left {t1 v : EMLTree} {a b : Real}
    (hfail : ¬ EMLPfaffianValidOn t1 a b) :
    ¬ EMLPfaffianValidOn (EMLTree.eml t1 v) a b :=
  fun h => absurd h.1 hfail

/-- Same shape as `nonMonotonicWitness`/`expWrappedNonMonotonicWitness`
(`WitnessResidualNonMonotonic.lean`), but with the crossing constant `c` left free instead of
hardcoded to `1+1` — so its own crossing point `x0(c) := log(log c)` can be pushed positive by
choosing `c` large enough (`c > e`, i.e. `log c > 1`). -/
noncomputable def nonMonotonicWitnessC (c : Real) : EMLTree :=
  EMLTree.eml EMLTree.var
    (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
      (EMLTree.eml EMLTree.var (EMLTree.const c)))

noncomputable def expWrappedNonMonotonicWitnessC (c : Real) : EMLTree :=
  EMLTree.eml (nonMonotonicWitnessC c) (EMLTree.const 1)

theorem crossing_at_log_log_c {c : Real} (hc : 1 < c) :
    (EMLTree.eml EMLTree.var (EMLTree.const c)).eval (Real.log (Real.log c)) = 0 := by
  show Real.exp (Real.log (Real.log c)) - Real.log c = 0
  have hlogcpos : 0 < Real.log c := by
    have h := log_lt_log zero_lt_one_ax hc
    rwa [log_one] at h
  rw [Real.exp_log hlogcpos]
  have e : Real.log c - Real.log c = 0 := by mach_ring
  exact e

/-- **The main negative result.** For `c > 1` with a positive crossing point (`0 < log(log
c)`), `EMLPfaffianValidOn (expWrappedNonMonotonicWitnessC c) 0 b` is FALSE for every `b` past
that crossing — the exact route that resolved the negative-crossing case
(`no_tree_eq_nested_target_given_validon`, needing validity on `(0,b)` for ALL `b > 0`)
structurally cannot supply its own hypothesis here, for any `b` beyond `log(log c)`. -/
theorem expWrappedNonMonotonicWitnessC_validon_false {c b : Real} (hc : 1 < c)
    (hx0pos : 0 < Real.log (Real.log c)) (hx0b : Real.log (Real.log c) < b) :
    ¬ EMLPfaffianValidOn (expWrappedNonMonotonicWitnessC c) 0 b := by
  have hBfail : ¬ EMLPfaffianValidOn
      (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
        (EMLTree.eml EMLTree.var (EMLTree.const c))) 0 b :=
    eml_pfaffian_validon_false_of_crossing hx0pos hx0b (crossing_at_log_log_c hc)
  have hTfail : ¬ EMLPfaffianValidOn (nonMonotonicWitnessC c) 0 b :=
    eml_pfaffian_validon_false_propagates_right hBfail
  exact eml_pfaffian_validon_false_propagates_left hTfail

/-- **Concrete existence witness**, not just an abstract conditional: `c := exp(exp 1)` gives an
EXACT crossing point `x0(c) = 1` (two applications of `log_exp`), no numerical estimation of `e`
needed at all. -/
noncomputable def concreteC : Real := Real.exp (Real.exp 1)

theorem concreteC_gt_one : 1 < concreteC := by
  show 1 < Real.exp (Real.exp 1)
  have h := Real.exp_lt (Real.exp_pos 1)
  rwa [Real.exp_zero] at h

theorem concreteC_x0_eq_one : Real.log (Real.log concreteC) = 1 := by
  show Real.log (Real.log (Real.exp (Real.exp 1))) = 1
  rw [log_exp, log_exp]

/-- **The instantiated obstruction**: a fully concrete tree, `EMLPfaffianValidOn`-invalid on
`(0, 2)`, exhibiting the phenomenon with no free parameters or numerical approximation left. -/
theorem concreteC_validon_false :
    ¬ EMLPfaffianValidOn (expWrappedNonMonotonicWitnessC concreteC) 0 (1 + 1) := by
  have hone_lt_two : (1 : Real) < 1 + 1 := by
    have h := add_lt_add_left zero_lt_one_ax (1 : Real)
    rwa [add_zero] at h
  apply expWrappedNonMonotonicWitnessC_validon_false concreteC_gt_one
  · rw [concreteC_x0_eq_one]; exact zero_lt_one_ax
  · rw [concreteC_x0_eq_one]; exact hone_lt_two

end Real
end MachLib
