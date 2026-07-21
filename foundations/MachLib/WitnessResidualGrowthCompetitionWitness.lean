import MachLib.WitnessResidualBoundedNonConstant
import MachLib.WitnessResidualNonMonotonic
import MachLib.WitnessResidualSimpleRightChildren

/-! # A structurally NEW candidate: bounded via growth-rate competition, no clamp anywhere

Every non-monotonic tree explored in this whole arc (`nonMonotonicWitness` and its whole
crossing-family, now fully closed by `WitnessResidualEntireCrossingFamilyClosed.lean`) got its
non-monotonicity from a `log`-clamp transition — a genuine zero-crossing somewhere inside the
tree. This file explores a DIFFERENT mechanism, found earlier in the session but not followed up
on until now: pure GROWTH-RATE competition between two smooth, never-clamping sub-expressions
(`exp(exp x) - x` was the original example, but that one is unbounded). The question this file
answers (checked numerically first, per house style): can the SAME growth-competition mechanism
produce a tree that stays BOUNDED in both directions, unlike that simple example?

**The construction.** `growthCompetitionWitness c1 c2 := eml (boundedNonConstantWitness c1) (eml
(boundedNonConstantWitness c2) (const 1))`. Since `eml t1 (eml t2 (const 1)) = exp(t1) -
log(exp(t2)) = exp(t1) - t2` (via `log ∘ exp = id`), this evaluates to `exp(BNCW(x,c1)) -
BNCW(x,c2)` — `BNCW` decreasing pushes the first (exponentiated) term down and the second term's
negation up, exactly the "decreasing + increasing" shape that produced a genuine valley in the
`exp(exp x) - x` prototype, but built from TWO already-bounded pieces instead of `exp(exp x)`
and `x` (both unbounded).

**Numerically confirmed** (not yet formalized — see below): at `c1 = 2`, `c2 = 5/2`, the tree is
bounded in roughly `[0.7785, 1.0]`, approaches `1` as `x → +∞`, approaches `≈0.7785` as `x →
-∞`, and has a genuine local max then local min around `x ≈ -0.69` (confirmed via a fine grid,
not a numerical artifact) — a real, non-monotonic wiggle, entirely without any `log`-clamp
triggering anywhere (`inner := exp(exp x) - log c` stays strictly positive throughout, for both
`c1` and `c2`, checked over a wide range).

**What THIS file formalizes.** Boundedness in BOTH directions, for ANY valid `c1, c2` (not just
the numerically-found pair) — the additive-bound argument is fully general and needed no new
machinery, just combining `boundedNonConstantWitness`'s ALREADY-established bounds. And
non-`RightChildrenSimplePositive` (inherits the failure from the left child, same
`EMLTree.noConfusion` argument used throughout this arc).

**What remains OPEN, stated plainly.** Non-monotonicity (and hence non-constancy, which would
follow from it) is NOT formalized here. The mechanism is numerically overwhelming (a clean local
extremum, confirmed on a fine grid) but proving it in Lean needs either (a) a derivative-based
sign-crossing argument (`T'(x) = exp(A(x))·A'(x) - B'(x)`, both `A'`, `B'` already known
negative-valued formulas from `boundedNonConstantWitness_deriv_neg`, but their RATIO crossing 1
needs a genuinely new comparison not reducible to existing lemmas), or (b) careful numerical
interval bounds at specific points (tedious, no shortcut identified). Both are real, sizable
undertakings — correctly scoped as the next concrete step for whoever continues, not attempted
in this round. -/

namespace MachLib
namespace Real

open EMLTree

/-- `eml (BNCW c1) (eml (BNCW c2) (const 1))` — growth-rate competition between two ALREADY-
bounded pieces, instead of the unbounded `exp(exp x)` vs. `x` in the original prototype. -/
noncomputable def growthCompetitionWitness (c1 c2 : Real) : EMLTree :=
  EMLTree.eml (boundedNonConstantWitness c1)
    (EMLTree.eml (boundedNonConstantWitness c2) (EMLTree.const 1))

/-- `log ∘ exp = id` collapses the right subtree cleanly: `eval x = exp(BNCW(x,c1)) -
BNCW(x,c2)`, not merely close to it. -/
theorem growthCompetitionWitness_eval (c1 c2 x : Real) :
    (growthCompetitionWitness c1 c2).eval x
      = Real.exp ((boundedNonConstantWitness c1).eval x) - (boundedNonConstantWitness c2).eval x := by
  show Real.exp ((boundedNonConstantWitness c1).eval x)
      - Real.log ((EMLTree.eml (boundedNonConstantWitness c2) (EMLTree.const 1)).eval x) = _
  have hB : (EMLTree.eml (boundedNonConstantWitness c2) (EMLTree.const 1)).eval x
      = Real.exp ((boundedNonConstantWitness c2).eval x) := by
    show Real.exp ((boundedNonConstantWitness c2).eval x) - Real.log 1 = _
    rw [log_one, sub_zero]
  rw [hB, log_exp]

/-- **Lower bound, any `x`.** `exp(A) > 1` (from `A > 0`) and `B < U2 := -log(1-log c2)`
(`boundedNonConstantWitness_upper_bound`) chain, via two `sub_lt_sub_*` steps, to `1 - U2 <
exp(A) - B`. -/
theorem growthCompetitionWitness_lower_bound {c1 c2 : Real} (hc1 : 1 < c1) (hc1' : Real.log c1 < 1)
    (hc2 : 1 < c2) (hc2' : Real.log c2 < 1) (x : Real) :
    1 - (-Real.log (1 - Real.log c2)) < (growthCompetitionWitness c1 c2).eval x := by
  rw [growthCompetitionWitness_eval]
  have hApos : 0 < (boundedNonConstantWitness c1).eval x := boundedNonConstantWitness_pos hc1 hc1' x
  have hexpA : 1 < Real.exp ((boundedNonConstantWitness c1).eval x) := by
    have h := Real.exp_lt hApos
    rwa [Real.exp_zero] at h
  have hBub : (boundedNonConstantWitness c2).eval x < -Real.log (1 - Real.log c2) :=
    boundedNonConstantWitness_upper_bound hc2 hc2' x
  have step1 : Real.exp ((boundedNonConstantWitness c1).eval x) - (-Real.log (1 - Real.log c2))
      < Real.exp ((boundedNonConstantWitness c1).eval x) - (boundedNonConstantWitness c2).eval x :=
    sub_lt_sub_left_local _ hBub
  have step2 : 1 - (-Real.log (1 - Real.log c2))
      < Real.exp ((boundedNonConstantWitness c1).eval x) - (-Real.log (1 - Real.log c2)) :=
    sub_lt_sub_right_of_lt (r := -Real.log (1 - Real.log c2)) hexpA
  exact lt_trans_ax step2 step1

/-- **Upper bound, any `x`.** `A < U1 := -log(1-log c1)` gives `exp(A) < exp(U1)`; `B > 0` chain,
via the same two-step pattern, to `exp(A) - B < exp(U1)`. -/
theorem growthCompetitionWitness_upper_bound {c1 c2 : Real} (hc1 : 1 < c1) (hc1' : Real.log c1 < 1)
    (hc2 : 1 < c2) (hc2' : Real.log c2 < 1) (x : Real) :
    (growthCompetitionWitness c1 c2).eval x < Real.exp (-Real.log (1 - Real.log c1)) := by
  rw [growthCompetitionWitness_eval]
  have hAub : (boundedNonConstantWitness c1).eval x < -Real.log (1 - Real.log c1) :=
    boundedNonConstantWitness_upper_bound hc1 hc1' x
  have hexpAub : Real.exp ((boundedNonConstantWitness c1).eval x)
      < Real.exp (-Real.log (1 - Real.log c1)) := Real.exp_lt hAub
  have hBpos : 0 < (boundedNonConstantWitness c2).eval x := boundedNonConstantWitness_pos hc2 hc2' x
  have step1 : Real.exp ((boundedNonConstantWitness c1).eval x) - (boundedNonConstantWitness c2).eval x
      < Real.exp ((boundedNonConstantWitness c1).eval x) - 0 :=
    sub_lt_sub_left_local _ hBpos
  have step2 : Real.exp ((boundedNonConstantWitness c1).eval x) - 0
      < Real.exp (-Real.log (1 - Real.log c1)) - 0 :=
    sub_lt_sub_right_of_lt (r := (0 : Real)) hexpAub
  have e : Real.exp (-Real.log (1 - Real.log c1)) - 0 = Real.exp (-Real.log (1 - Real.log c1)) :=
    sub_zero _
  rw [e] at step2
  exact lt_trans_ax step1 step2

/-- **Not `RightChildrenSimplePositive`**: inherits the failure from the left child
`boundedNonConstantWitness c1`, whose own right child (`eml (eml var (const 1)) (const c1)`) is
compound — the same `EMLTree.noConfusion` argument used throughout this whole arc. -/
theorem growthCompetitionWitness_not_RightChildrenSimplePositive (c1 c2 : Real) :
    ¬ RightChildrenSimplePositive (growthCompetitionWitness c1 c2) := by
  intro hsimple
  have h1 := hsimple.1
  have h2 : boundedNonConstantWitness c1 = EMLTree.eml EMLTree.var
      (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1)) (EMLTree.const c1)) := rfl
  rw [h2] at h1
  have h3 := h1.2
  rcases h3 with h | ⟨c, hc, _⟩
  · exact EMLTree.noConfusion h
  · exact EMLTree.noConfusion hc

end Real
end MachLib
