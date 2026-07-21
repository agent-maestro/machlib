import MachLib.WitnessResidualRightChildrenEverywherePositive

/-! # A SECOND concrete tree satisfying `RightChildrenEverywherePositive`

Answers the open question flagged at the end of `WitnessResidualRightChildrenEverywherePositive.lean`:
no other tree in this arc had yet been confirmed to satisfy the predicate besides
`growthCompetitionWitness`. This file exhibits a structurally DIFFERENT one, found by asking what
OTHER combinations of the same two safe building blocks (`boundedNonConstantWitness`, and
`E(c) := eml (boundedNonConstantWitness c) (const 1)`, evaluating to `exp((BNCW c).eval x)`,
itself bounded and always positive) are available.

**The construction, found by search, verified numerically first (mpmath, not float64 — see the
gotcha below).** `growthCompetitionWitness` pits `exp(BNCW c1)` (ONE exp wrap) against `BNCW c2`
DIRECTLY (zero wraps) — an asymmetry of exactly one exponential level. Checking the OTHER natural
"one-level-asymmetric" combination — `exp(exp(BNCW c1))` (TWO wraps) against `exp(BNCW c2)` (ONE
wrap) — gives `growthCompetitionWitnessDeep c1 c2 := eml (E c1) (eml (E c2) (const 1))`,
evaluating to `exp(exp((BNCW c1).eval x)) - exp((BNCW c2).eval x)`. Numerically confirmed
non-monotonic for `c1 = 1.5, c2 = 2.0` (and other pairs): a SINGLE local maximum near `x ≈ -2.2`
(value `≈ 2.171`), increasing before it from a left asymptote `exp(exp(U(c1))) - exp(U(c2)) ≈
2.117`, decreasing after it toward the right asymptote `e - 1 ≈ 1.718` — a genuinely different
SHAPE from `growthCompetitionWitness`'s own local-max-then-local-min wiggle (this one has only a
single hump, not two turning points).

**A real numeric gotcha, worth recording.** An initial float64 (`math`) scan across many `(c1,c2)`
pairs of the SYMMETRIC alternative (`exp(BNCW c1) - exp(BNCW c2)`, not the tree built here)
reported "non-monotonic" for almost every pair — a false positive from floating-point noise near
the flat asymptotic tail (differences on the order of `1e-10`, indistinguishable from rounding
error at float64 precision). Re-checked with `mpmath` at 30 decimal digits: that symmetric
alternative is actually ALWAYS monotonic — confirmed analytically too (its derivative reduces to
`E·[f(log c2, E) - f(log c1, E)]` for `f(q,E) := q/(E-q)²`, and `∂f/∂q = (E+q)/(E-q)³ > 0`, so `f`
is strictly increasing in `q`, meaning the bracket never changes sign). The asymmetric
double-exp-vs-single-exp construction built here is qualitatively different and DOES show a real
sign change, confirmed at the same high precision.

**What this file establishes**: the tree's structure, its clean closed-form `eval`,
`RightChildrenEverywherePositive` (trivial, reusing the same building blocks as
`growthCompetitionWitness`), a crude additive boundedness bound (same technique — bound each
factor's range via `boundedNonConstantWitness`'s own established bounds, chain via
`sub_lt_sub_left_local`/`sub_lt_sub_right_of_lt`), and non-`RightChildrenSimplePositive` (same
`EMLTree.noConfusion` argument, one level deeper).

**What's NOT established here, honestly**: non-monotonicity itself. Unlike
`growthCompetitionWitness`'s derivative (which collapsed to a PURE ALGEBRA quadratic after
clearing denominators), this tree's derivative retains a genuine transcendental term —
`d/dx[exp(exp(A(x)))] = exp(exp(A(x)))·exp(A(x))·A'(x)`, and `exp(A(x)) = E/(E-p)` doesn't let
`exp(exp(A(x))) = exp(E/(E-p))` simplify further; it stays a real exponential of a rational
function of `E`, not reducible to algebra the way `quadratic_neg_between`'s target was. Closing
non-monotonicity for this tree would need either new numeric bounds on `exp` at moving arguments
(more machinery than the log-bound axioms `growthCompetitionWitness` needed) or a different
analytic route — a genuinely open, harder follow-up, not attempted this round. Also not
established: non-constancy (though not needed for `RightChildrenEverywherePositive`-based closure,
which doesn't require it) — the crude bound alone doesn't distinguish two specific points without
extra numeric work. -/

namespace MachLib
namespace Real

open EMLTree

/-- `E(c) := eml (BNCW c) (const 1)`, evaluating to `exp((BNCW c).eval x)` — a bounded, always-
positive building block (the same one `growthCompetitionWitness` uses for its right subtree). -/
noncomputable def E_BNCW (c : Real) : EMLTree :=
  EMLTree.eml (boundedNonConstantWitness c) (EMLTree.const 1)

theorem E_BNCW_eval (c x : Real) :
    (E_BNCW c).eval x = Real.exp ((boundedNonConstantWitness c).eval x) := by
  show Real.exp ((boundedNonConstantWitness c).eval x) - Real.log 1 = _
  rw [log_one, sub_zero]

/-- Double-exp(c1) vs single-exp(c2): `eml (E c1) (eml (E c2) (const 1))`. -/
noncomputable def growthCompetitionWitnessDeep (c1 c2 : Real) : EMLTree :=
  EMLTree.eml (E_BNCW c1) (EMLTree.eml (E_BNCW c2) (EMLTree.const 1))

theorem growthCompetitionWitnessDeep_eval (c1 c2 x : Real) :
    (growthCompetitionWitnessDeep c1 c2).eval x
      = Real.exp (Real.exp ((boundedNonConstantWitness c1).eval x))
        - Real.exp ((boundedNonConstantWitness c2).eval x) := by
  show Real.exp ((E_BNCW c1).eval x) - Real.log ((EMLTree.eml (E_BNCW c2) (EMLTree.const 1)).eval x) = _
  rw [E_BNCW_eval]
  have h2 : (EMLTree.eml (E_BNCW c2) (EMLTree.const 1)).eval x = Real.exp ((E_BNCW c2).eval x) := by
    show Real.exp ((E_BNCW c2).eval x) - Real.log 1 = _
    rw [log_one, sub_zero]
  rw [h2, E_BNCW_eval, Real.log_exp]

theorem E_BNCW_RightChildrenEverywherePositive {c : Real} (hc : 1 < c) (hc1 : Real.log c < 1) :
    RightChildrenEverywherePositive (E_BNCW c) :=
  ⟨boundedNonConstantWitness_RightChildrenEverywherePositive hc hc1, trivial,
    fun _ => zero_lt_one_ax⟩

theorem growthCompetitionWitnessDeep_RightChildrenEverywherePositive {c1 c2 : Real}
    (hc1 : 1 < c1) (hc1' : Real.log c1 < 1) (hc2 : 1 < c2) (hc2' : Real.log c2 < 1) :
    RightChildrenEverywherePositive (growthCompetitionWitnessDeep c1 c2) :=
  ⟨E_BNCW_RightChildrenEverywherePositive hc1 hc1',
    ⟨E_BNCW_RightChildrenEverywherePositive hc2 hc2', trivial, fun _ => zero_lt_one_ax⟩,
    fun x => by
      show (0:Real) < Real.exp ((E_BNCW c2).eval x) - Real.log 1
      rw [log_one, sub_zero]
      exact Real.exp_pos _⟩

/-- **Lower bound, any `x`.** `exp(exp(A)) > exp(1)` (from `A > 0`) and `exp(B) < exp(U2)`
(`boundedNonConstantWitness_upper_bound`), chained the same way `growthCompetitionWitness`'s own
bound was. -/
theorem growthCompetitionWitnessDeep_lower_bound {c1 c2 : Real}
    (hc1 : 1 < c1) (hc1' : Real.log c1 < 1) (hc2 : 1 < c2) (hc2' : Real.log c2 < 1) (x : Real) :
    Real.exp 1 - Real.exp (-Real.log (1 - Real.log c2)) < (growthCompetitionWitnessDeep c1 c2).eval x := by
  rw [growthCompetitionWitnessDeep_eval]
  have hApos : 0 < (boundedNonConstantWitness c1).eval x := boundedNonConstantWitness_pos hc1 hc1' x
  have hexpA1 : (1:Real) < Real.exp ((boundedNonConstantWitness c1).eval x) := by
    have h := Real.exp_lt hApos
    rwa [Real.exp_zero] at h
  have hexpexpA1 : Real.exp 1 < Real.exp (Real.exp ((boundedNonConstantWitness c1).eval x)) :=
    Real.exp_lt hexpA1
  have hBub : (boundedNonConstantWitness c2).eval x < -Real.log (1 - Real.log c2) :=
    boundedNonConstantWitness_upper_bound hc2 hc2' x
  have hexpBub : Real.exp ((boundedNonConstantWitness c2).eval x) < Real.exp (-Real.log (1 - Real.log c2)) :=
    Real.exp_lt hBub
  have step1 : Real.exp (Real.exp ((boundedNonConstantWitness c1).eval x))
      - Real.exp (-Real.log (1 - Real.log c2))
      < Real.exp (Real.exp ((boundedNonConstantWitness c1).eval x))
        - Real.exp ((boundedNonConstantWitness c2).eval x) :=
    sub_lt_sub_left_local _ hexpBub
  have step2 : Real.exp 1 - Real.exp (-Real.log (1 - Real.log c2))
      < Real.exp (Real.exp ((boundedNonConstantWitness c1).eval x)) - Real.exp (-Real.log (1 - Real.log c2)) :=
    sub_lt_sub_right_of_lt (r := Real.exp (-Real.log (1 - Real.log c2))) hexpexpA1
  exact lt_trans_ax step2 step1

/-- **Upper bound, any `x`.** `exp(exp(A)) < exp(exp(U1))` and `exp(B) > 1`, chained the same
way. -/
theorem growthCompetitionWitnessDeep_upper_bound {c1 c2 : Real}
    (hc1 : 1 < c1) (hc1' : Real.log c1 < 1) (hc2 : 1 < c2) (hc2' : Real.log c2 < 1) (x : Real) :
    (growthCompetitionWitnessDeep c1 c2).eval x
      < Real.exp (Real.exp (-Real.log (1 - Real.log c1))) - 1 := by
  rw [growthCompetitionWitnessDeep_eval]
  have hAub : (boundedNonConstantWitness c1).eval x < -Real.log (1 - Real.log c1) :=
    boundedNonConstantWitness_upper_bound hc1 hc1' x
  have hexpAub : Real.exp ((boundedNonConstantWitness c1).eval x) < Real.exp (-Real.log (1 - Real.log c1)) :=
    Real.exp_lt hAub
  have hexpexpAub : Real.exp (Real.exp ((boundedNonConstantWitness c1).eval x))
      < Real.exp (Real.exp (-Real.log (1 - Real.log c1))) := Real.exp_lt hexpAub
  have hBpos : 0 < (boundedNonConstantWitness c2).eval x := boundedNonConstantWitness_pos hc2 hc2' x
  have hexpB1 : (1:Real) < Real.exp ((boundedNonConstantWitness c2).eval x) := by
    have h := Real.exp_lt hBpos
    rwa [Real.exp_zero] at h
  have step1 : Real.exp (Real.exp ((boundedNonConstantWitness c1).eval x))
      - Real.exp ((boundedNonConstantWitness c2).eval x)
      < Real.exp (Real.exp ((boundedNonConstantWitness c1).eval x)) - 1 :=
    sub_lt_sub_left_local _ hexpB1
  have step2 : Real.exp (Real.exp ((boundedNonConstantWitness c1).eval x)) - 1
      < Real.exp (Real.exp (-Real.log (1 - Real.log c1))) - 1 :=
    sub_lt_sub_right_of_lt (r := (1:Real)) hexpexpAub
  exact lt_trans_ax step1 step2

/-- **Not `RightChildrenSimplePositive`**: inherits the failure from the left child's left
child, `boundedNonConstantWitness c1`, whose own right child is compound — same
`EMLTree.noConfusion` argument used throughout this arc. -/
theorem growthCompetitionWitnessDeep_not_RightChildrenSimplePositive (c1 c2 : Real) :
    ¬ RightChildrenSimplePositive (growthCompetitionWitnessDeep c1 c2) := by
  intro hsimple
  have h1 := hsimple.1
  have h1' := h1.1
  have h2 : boundedNonConstantWitness c1 = EMLTree.eml EMLTree.var
      (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1)) (EMLTree.const c1)) := rfl
  rw [h2] at h1'
  have h3 := h1'.2
  rcases h3 with h | ⟨c, hc, _⟩
  · exact EMLTree.noConfusion h
  · exact EMLTree.noConfusion hc

/-- **The (partial) witness, packaged.** Bounded both directions, non-`RightChildrenSimplePositive`,
and satisfies `RightChildrenEverywherePositive` (hence closes the witness-finding theorem
unconditionally, via `eml_depth2_witness_of_const_gt_one_sibling_right_children_everywhere_positive`)
— for ANY valid `c1, c2`. Non-monotonicity is NOT included here; see the module docstring for
exactly why it's harder than `growthCompetitionWitness`'s case and left open. -/
theorem growthCompetitionWitnessDeep_partial_exists {c1 c2 : Real}
    (hc1 : 1 < c1) (hc1' : Real.log c1 < 1) (hc2 : 1 < c2) (hc2' : Real.log c2 < 1) :
    (∀ x, Real.exp 1 - Real.exp (-Real.log (1 - Real.log c2))
        < (growthCompetitionWitnessDeep c1 c2).eval x) ∧
    (∀ x, (growthCompetitionWitnessDeep c1 c2).eval x
        < Real.exp (Real.exp (-Real.log (1 - Real.log c1))) - 1) ∧
    ¬ RightChildrenSimplePositive (growthCompetitionWitnessDeep c1 c2) ∧
    RightChildrenEverywherePositive (growthCompetitionWitnessDeep c1 c2) :=
  ⟨fun x => growthCompetitionWitnessDeep_lower_bound hc1 hc1' hc2 hc2' x,
   fun x => growthCompetitionWitnessDeep_upper_bound hc1 hc1' hc2 hc2' x,
   growthCompetitionWitnessDeep_not_RightChildrenSimplePositive c1 c2,
   growthCompetitionWitnessDeep_RightChildrenEverywherePositive hc1 hc1' hc2 hc2'⟩

end Real
end MachLib
