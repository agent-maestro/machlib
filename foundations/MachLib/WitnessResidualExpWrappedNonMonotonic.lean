import MachLib.WitnessResidualNonMonotonic
import MachLib.WitnessResidualSimpleRightChildren

/-! # MILESTONE: the open classification is NOT vacuous — a concrete member found

Every round since `nonMonotonicWitness` was built has narrowed the witness-finding residual's
surviving open territory down to exactly: `T1` bounded in BOTH directions, non-constant, non-
`RightChildrenSimplePositive`, and NOT strictly monotonic in either direction. Every attempt to
CLOSE that territory (three fully general free closures, two parametrized family closures) came
up empty for `nonMonotonicWitness` itself, because it turned out to only be bounded in ONE
direction. The open question hanging over the whole arc has been: is that four-property class
actually EMPTY (in which case a strong enough induction would eventually close the whole
residual), or does it contain a genuine member?

**This file answers it: the class is NOT empty.** `nonMonotonicWitness` is bounded above but
diverges to `-∞` — the fix is to apply `exp` to it. `exp` is strictly increasing (order- and
strict-inequality-preserving) and always strictly positive, so:

- it preserves EVERY relative comparison `nonMonotonicWitness` satisfies at any two points —
  in particular its PROVEN non-monotonicity (the flat→down→up valley) survives intact;
- it turns the `-∞` divergence into an approach to `0` from above — `exp(-∞) → 0`, NOT `-∞` —
  taming the one direction that was previously unbounded, while the already-proven upper bound
  (`< log 2`) becomes, after `exp`, an upper bound of `2`.

The result, `expWrappedNonMonotonicWitness := eml nonMonotonicWitness (const 1)` (the `const 1`
right child makes this exactly `exp(nonMonotonicWitness.eval x)`, since `log 1 = 0`), is bounded
in BOTH directions (`0 < eval < 2`, both facts elementary), non-constant, non-
`RightChildrenSimplePositive` (inherits the failure from its own left child), and non-monotonic
— EVERY property transported almost for free from already-proven facts about
`nonMonotonicWitness`, via `exp`'s strict monotonicity. No new hard mathematics — the insight was
recognizing that `nonMonotonicWitness`'s own "flaw" (unbounded below) could be repaired by
wrapping it in the one EML operation guaranteed to turn `-∞` into a finite floor.

**What this settles, and what it does NOT settle.** This is a genuine, concrete tree that no
closure built so far can rule out as a `T1` candidate — the classification's open territory is
real, not an artifact of insufficiently general closures. It does NOT mean the axiom
(`eml_pfaffian_validon_from_sin_equality`) is false, nor does it mean this specific tree
actually breaks the witness-finding argument — it only means the "free" shortcuts built this
whole session are now known to be INSUFFICIENT to handle this tree; whether the FULL residual
still closes for `T1 = expWrappedNonMonotonicWitness` (via the heavier zero-counting/Pfaffian-
chain machinery this arc built earlier) remains completely open, unattempted here. -/

namespace MachLib
namespace Real

open EMLTree

/-- **The tree**: `exp` applied to `nonMonotonicWitness`, via `eml nonMonotonicWitness (const
1)` (`log 1 = 0` makes this exactly `exp ∘ nonMonotonicWitness`, not merely close to it). -/
noncomputable def expWrappedNonMonotonicWitness : EMLTree :=
  EMLTree.eml nonMonotonicWitness (EMLTree.const 1)

theorem expWrappedNonMonotonicWitness_eval (x : Real) :
    expWrappedNonMonotonicWitness.eval x = Real.exp (nonMonotonicWitness.eval x) := by
  show Real.exp (nonMonotonicWitness.eval x) - Real.log 1 = Real.exp (nonMonotonicWitness.eval x)
  rw [log_one, sub_zero]

/-- **Bounded below**, trivially: `exp` is always strictly positive, regardless of what
`nonMonotonicWitness` does. -/
theorem expWrappedNonMonotonicWitness_pos (x : Real) :
    0 < expWrappedNonMonotonicWitness.eval x := by
  rw [expWrappedNonMonotonicWitness_eval]
  exact Real.exp_pos _

/-- **Bounded above**: transported directly from `nonMonotonicWitness`'s own proven upper bound
(`< log(1+1)`) through `exp`'s strict monotonicity plus `exp_log`. -/
theorem expWrappedNonMonotonicWitness_upper_bound (x : Real) :
    expWrappedNonMonotonicWitness.eval x < 1 + 1 := by
  rw [expWrappedNonMonotonicWitness_eval]
  have h := bounded_nonmonotonic_eml_tree_exists.1 x
  have h2 := Real.exp_lt h
  rwa [Real.exp_log zero_lt_one_add_one] at h2

/-- **Not `RightChildrenSimplePositive`**: inherits the failure from its own left child.
`nonMonotonicWitness`'s right child is a compound `eml` node, which can never equal `var` or
`const c` (different constructors of the same inductive type) — so
`RightChildrenSimplePositive nonMonotonicWitness` is false, and the top-level conjunction fails
with it. -/
theorem expWrappedNonMonotonicWitness_not_RightChildrenSimplePositive :
    ¬ RightChildrenSimplePositive expWrappedNonMonotonicWitness := by
  intro hsimple
  have h1 := hsimple.1
  have h2 : nonMonotonicWitness = EMLTree.eml EMLTree.var
      (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
        (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1)))) := rfl
  rw [h2] at h1
  have h3 := h1.2
  rcases h3 with h | ⟨c, hc, _⟩
  · exact EMLTree.noConfusion h
  · exact EMLTree.noConfusion hc

/-- **Non-constant**: `exp` is injective (via `exp_lt` + trichotomy), so the two points
`nonMonotonicWitness_x0` (`T = 0`) and `nonMonotonicWitness_xb` (`T < 0`) — already known to
give different `nonMonotonicWitness` values — give different `expWrappedNonMonotonicWitness`
values too. -/
theorem expWrappedNonMonotonicWitness_not_constant :
    ∃ x y, expWrappedNonMonotonicWitness.eval x ≠ expWrappedNonMonotonicWitness.eval y := by
  refine ⟨nonMonotonicWitness_x0, nonMonotonicWitness_xb, ?_⟩
  rw [expWrappedNonMonotonicWitness_eval, expWrappedNonMonotonicWitness_eval]
  intro heq
  have hTa : nonMonotonicWitness.eval nonMonotonicWitness_x0 = 0 :=
    nonMonotonicWitness_eval_clamped (le_refl _)
  have hTb : nonMonotonicWitness.eval nonMonotonicWitness_xb < 0 :=
    nonMonotonicWitness_neg_of_lt_one nonMonotonicWitness_x0_lt_xb
      (by rw [nonMonotonicWitness_D_xb]; exact nonMonotonicWitness_half_pos)
      (by rw [nonMonotonicWitness_D_xb]; exact nonMonotonicWitness_half_lt_one)
  have hlt : nonMonotonicWitness.eval nonMonotonicWitness_xb
      < nonMonotonicWitness.eval nonMonotonicWitness_x0 := by rw [hTa]; exact hTb
  have hexplt := Real.exp_lt hlt
  rw [heq] at hexplt
  exact lt_irrefl_ax _ hexplt

/-- **Not monotonic in either direction**: the SAME three witness points
`nonMonotonicWitness_not_monotone` used (`x_a < x_b < x_c`, `T(x_a) > T(x_b)` and `T(x_b) <
T(x_c)`), transported through `exp`'s strict monotonicity — since `exp` preserves every strict
inequality, `U(x_a) > U(x_b)` and `U(x_b) < U(x_c)` follow immediately, refuting monotone
increasing and monotone decreasing exactly as before. -/
theorem expWrappedNonMonotonicWitness_not_monotone :
    ¬ (∀ x y : Real, x < y → expWrappedNonMonotonicWitness.eval x
        ≤ expWrappedNonMonotonicWitness.eval y) ∧
    ¬ (∀ x y : Real, x < y → expWrappedNonMonotonicWitness.eval y
        ≤ expWrappedNonMonotonicWitness.eval x) := by
  have hTa : nonMonotonicWitness.eval nonMonotonicWitness_x0 = 0 :=
    nonMonotonicWitness_eval_clamped (le_refl _)
  have hTb : nonMonotonicWitness.eval nonMonotonicWitness_xb < 0 :=
    nonMonotonicWitness_neg_of_lt_one nonMonotonicWitness_x0_lt_xb
      (by rw [nonMonotonicWitness_D_xb]; exact nonMonotonicWitness_half_pos)
      (by rw [nonMonotonicWitness_D_xb]; exact nonMonotonicWitness_half_lt_one)
  have hxc_gt_x0 : nonMonotonicWitness_x0 < nonMonotonicWitness_xc :=
    lt_trans_ax nonMonotonicWitness_x0_lt_xb nonMonotonicWitness_xb_lt_xc
  have hTc : 0 < nonMonotonicWitness.eval nonMonotonicWitness_xc :=
    nonMonotonicWitness_pos_of_gt_one hxc_gt_x0
      (by rw [nonMonotonicWitness_D_xc]; exact one_lt_one_add_one)
  have hUa : expWrappedNonMonotonicWitness.eval nonMonotonicWitness_x0 = Real.exp 0 := by
    rw [expWrappedNonMonotonicWitness_eval, hTa]
  have hUb_lt_Ua : expWrappedNonMonotonicWitness.eval nonMonotonicWitness_xb
      < expWrappedNonMonotonicWitness.eval nonMonotonicWitness_x0 := by
    rw [expWrappedNonMonotonicWitness_eval, hUa]
    exact Real.exp_lt hTb
  have hUb_lt_Uc : expWrappedNonMonotonicWitness.eval nonMonotonicWitness_xb
      < expWrappedNonMonotonicWitness.eval nonMonotonicWitness_xc := by
    rw [expWrappedNonMonotonicWitness_eval, expWrappedNonMonotonicWitness_eval]
    exact Real.exp_lt (lt_trans_ax hTb hTc)
  constructor
  · intro hmono
    have h := hmono nonMonotonicWitness_x0 nonMonotonicWitness_xb nonMonotonicWitness_x0_lt_xb
    exact lt_irrefl_ax _ (lt_of_lt_of_le hUb_lt_Ua h)
  · intro hanti
    have h := hanti nonMonotonicWitness_xb nonMonotonicWitness_xc nonMonotonicWitness_xb_lt_xc
    exact lt_irrefl_ax _ (lt_of_lt_of_le hUb_lt_Uc h)

/-- **The packaged milestone**: a concrete EML tree, bounded in BOTH directions, non-constant,
non-`RightChildrenSimplePositive`, and non-monotonic — a genuine member of the witness-finding
residual's precisely-characterized open class. Settles (in the negative) the standing question
of whether that class is empty. -/
theorem expWrappedNonMonotonicWitness_exists :
    (∀ x, 0 < expWrappedNonMonotonicWitness.eval x) ∧
    (∀ x, expWrappedNonMonotonicWitness.eval x < 1 + 1) ∧
    (∃ x y, expWrappedNonMonotonicWitness.eval x ≠ expWrappedNonMonotonicWitness.eval y) ∧
    ¬ RightChildrenSimplePositive expWrappedNonMonotonicWitness ∧
    ¬ (∀ x y : Real, x < y → expWrappedNonMonotonicWitness.eval x
        ≤ expWrappedNonMonotonicWitness.eval y) ∧
    ¬ (∀ x y : Real, x < y → expWrappedNonMonotonicWitness.eval y
        ≤ expWrappedNonMonotonicWitness.eval x) :=
  ⟨expWrappedNonMonotonicWitness_pos, expWrappedNonMonotonicWitness_upper_bound,
   expWrappedNonMonotonicWitness_not_constant,
   expWrappedNonMonotonicWitness_not_RightChildrenSimplePositive,
   expWrappedNonMonotonicWitness_not_monotone.1, expWrappedNonMonotonicWitness_not_monotone.2⟩

end Real
end MachLib
