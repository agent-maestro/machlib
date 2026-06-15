import MachLib.Asymptotics
import MachLib.SinNotInEML
import MachLib.InvXNotInEML
import MachLib.Forge

/-!
# EML Asymptotic Classification Framework — Phase 1

This file ships the foundation for the structural-induction route
to closing the open conjecture

> `1/x ∉ EML at any finite depth`

(the load-bearing sub-lemma the addition-closure, differentiation-
closure, and 1/x stories all converge on — see
`exploration/eml_hardy_field_bridge_crack_2026_06_15/FINDINGS.md`
for the framing).

## The structural idea

Partition `Real → Real` functions into asymptotic classes. Show:

  1. Every EMLTree.eval lands in some class via structural
     induction over the EMLTree constructor.
  2. `inv_x` lands in a specific class (`EventuallyKOverX 1`).
  3. The classes are disjoint, OR for EMLTree.eval to be in
     `EventuallyKOverX K`, K is structurally bounded away from 1.

This is Phase 1 of that program. We ship the predicates, the
basic disjointness/uniqueness lemmas, and the inv_x
classification. The structural induction over EMLTree (Phase 2)
remains the next session.

## What this file ships

### Predicates

  `EventuallyConstant f` — `∃ c N, ∀ x ≥ N, f x = c`.
  `EventuallyKOverX K f` — `∃ N, ∀ x ≥ N, f x = K / x`.

### Basic facts

  `inv_x_eventually_K_over_x_one` — `inv_x` is exactly K = 1.
  `not_eventually_constant_inv_x` — `inv_x` is non-constant on
                                    any tail.
  `EventuallyConstant.not_eventually_K_over_x` — disjointness
                                                 when K ≠ 0.

## What this DOES NOT do

  - The structural induction `∀ t : EMLTree, ¬ EventuallyKOverX 1
    t.eval` — that's the Phase 2 deliverable. It requires
    case analysis on the eml constructor with sub-induction
    hypotheses, and amounts to formalizing the K-coefficient
    barrier identified in the Hardy-field bridge FINDINGS.

  - The full asymptotic-class partition (constant vs. K/x vs.
    K·exp x vs. iter_exp k vs. -log vs. ...). Only the two
    predicates needed for `inv_x` are defined here.

## No new axioms

All proofs use existing MachLib primitives.
-/

namespace MachLib

open Real

/-! ## The asymptotic-class predicates -/

/-- `f` is eventually constant: there exists a threshold `N` and a
constant `c` such that `f x = c` for all `x ≥ N`. -/
def EventuallyConstant (f : Real → Real) : Prop :=
  ∃ c N : Real, ∀ x : Real, N ≤ x → f x = c

/-- `f` is eventually `K / x`: there exists a threshold `N` such that
`f x = K / x` for all `x ≥ N`. -/
def EventuallyKOverX (K : Real) (f : Real → Real) : Prop :=
  ∃ N : Real, ∀ x : Real, N ≤ x → f x = K / x

/-! ## `inv_x` classification -/

/-- `inv_x` is `EventuallyKOverX 1`. Trivially — `inv_x x = 1/x`
by definition. -/
theorem inv_x_eventually_K_over_x_one : EventuallyKOverX 1 inv_x := by
  refine ⟨0, ?_⟩
  intro x _
  rfl

/-! ## Arithmetic helpers -/

/-- `(a / b) * b = a` when `b ≠ 0`. -/
private theorem div_mul_cancel {a b : Real} (hb : b ≠ 0) : (a / b) * b = a := by
  rw [Real.div_def a b hb]
  rw [Real.mul_assoc]
  rw [Real.mul_comm (1/b) b]
  rw [Real.mul_inv b hb]
  rw [Real.mul_one_ax]

/-- For `x > 0`, `1/x ≠ 1/(x+1)`. The proof multiplies both sides
by `x` then by `x+1`, simplifies via `mul_inv`, gets `x+1 = x`,
hence `1 = 0`. -/
private theorem one_div_x_ne_one_div_x_plus_one (x : Real) (hx_pos : 0 < x) :
    (1 : Real) / x ≠ 1 / (x + 1) := by
  intro h_eq
  have hx_ne : x ≠ 0 := Real.ne_of_gt hx_pos
  have hxp1_pos : 0 < x + 1 := Real.add_pos hx_pos Real.zero_lt_one_ax
  have hxp1_ne : x + 1 ≠ 0 := Real.ne_of_gt hxp1_pos
  -- Step 1: multiply h_eq by x.
  have step1 : (1 / x) * x = (1 / (x + 1)) * x :=
    congrArg (fun y => y * x) h_eq
  rw [Real.mul_comm (1/x) x, Real.mul_inv x hx_ne] at step1
  -- step1 : 1 = (1/(x+1)) * x
  -- Step 2: multiply step1 by (x+1). Cannot use `rw [step1]` because
  -- step1's LHS is `1`, which appears all over the goal and would
  -- cascade. Use congrArg instead.
  have step2 : 1 * (x + 1) = ((1/(x+1)) * x) * (x + 1) :=
    congrArg (fun y => y * (x + 1)) step1
  -- Simplify RHS: ((1/(x+1)) * x) * (x+1)
  --             = (x * (1/(x+1))) * (x+1)        [mul_comm inner]
  --             = x * ((1/(x+1)) * (x+1))        [mul_assoc]
  --             = x * ((x+1) * (1/(x+1)))        [mul_comm inner]
  --             = x * 1                          [mul_inv]
  --             = x                              [mul_one]
  rw [Real.mul_comm (1/(x+1)) x] at step2
  rw [Real.mul_assoc x (1/(x+1)) (x+1)] at step2
  rw [Real.mul_comm (1/(x+1)) (x+1)] at step2
  rw [Real.mul_inv (x+1) hxp1_ne] at step2
  rw [Real.mul_one_ax] at step2
  -- LHS: 1 * (x+1) = x+1.
  rw [Real.one_mul_thm] at step2
  -- step2 : x + 1 = x
  have step3 : -x + (x + 1) = -x + x := by rw [step2]
  rw [← Real.add_assoc, Real.neg_add_self, Real.zero_add] at step3
  -- step3 : 1 = 0  (the all-occurrences `Real.neg_add_self` collapsed
  -- both -x+x copies in one pass.)
  exact Real.one_ne_zero step3

/-- `inv_x` is NOT eventually constant. -/
theorem not_eventually_constant_inv_x : ¬ EventuallyConstant inv_x := by
  intro ⟨c, N, hN⟩
  -- Sample at x_0 = max N 1 (≥ N and ≥ 1, hence > 0) and x_0 + 1
  -- (≥ N too). Both give c = inv_x x_i = 1/x_i, so 1/x_0 = 1/(x_0+1).
  -- Refuted by one_div_x_ne_one_div_x_plus_one.
  have hN_le : N ≤ max N 1 := le_max_left N 1
  have h_one_le : (1 : Real) ≤ max N 1 := le_max_right N 1
  have h_pos : (0 : Real) < max N 1 :=
    Real.lt_of_lt_of_le Real.zero_lt_one_ax h_one_le
  have h_step : max N 1 + 0 < max N 1 + 1 :=
    Real.add_lt_add_left Real.zero_lt_one_ax (max N 1)
  rw [Real.add_zero] at h_step
  have hN_le_xp1 : N ≤ max N 1 + 1 := Real.le_trans hN_le (Real.le_of_lt h_step)
  have h0 : inv_x (max N 1) = c := hN (max N 1) hN_le
  have h1 : inv_x (max N 1 + 1) = c := hN (max N 1 + 1) hN_le_xp1
  have heq : inv_x (max N 1) = inv_x (max N 1 + 1) := h0.trans h1.symm
  simp only [inv_x] at heq
  exact one_div_x_ne_one_div_x_plus_one (max N 1) h_pos heq

/-! ## Disjointness of the two classes (when K ≠ 0)

A function can't simultaneously be eventually constant AND
eventually `K/x` for `K ≠ 0`.

The proof: pick `x_0` large enough that both hypotheses apply.
Then `c = K/x_0` and `c = K/(x_0+1)`. Multiply each by the
appropriate denominator (using `div_mul_cancel`) to get
`c * x_0 = K` and `c * (x_0+1) = K`. So `c * x_0 = c * (x_0+1)`,
distributing gives `c * x_0 = c * x_0 + c`, hence `c = 0`, hence
`K = c * x_0 = 0`. Contradiction with `K ≠ 0`. -/

/-- A function can't be both eventually constant and `EventuallyKOverX K`
for nonzero `K`. -/
theorem EventuallyConstant.not_eventually_K_over_x {K : Real} (hK : K ≠ 0)
    {f : Real → Real} (hconst : EventuallyConstant f) :
    ¬ EventuallyKOverX K f := by
  obtain ⟨c, N1, hN1⟩ := hconst
  intro ⟨N2, hN2⟩
  -- Sample at max (max N1 N2) 1 and (that) + 1.
  have hN1_le : N1 ≤ max (max N1 N2) 1 :=
    Real.le_trans (le_max_left N1 N2) (le_max_left (max N1 N2) 1)
  have hN2_le : N2 ≤ max (max N1 N2) 1 :=
    Real.le_trans (le_max_right N1 N2) (le_max_left (max N1 N2) 1)
  have h_one_le : (1 : Real) ≤ max (max N1 N2) 1 :=
    le_max_right (max N1 N2) 1
  have h_pos : (0 : Real) < max (max N1 N2) 1 :=
    Real.lt_of_lt_of_le Real.zero_lt_one_ax h_one_le
  have h_ne : max (max N1 N2) 1 ≠ 0 := Real.ne_of_gt h_pos
  have h_xp1_pos : (0 : Real) < max (max N1 N2) 1 + 1 :=
    Real.add_pos h_pos Real.zero_lt_one_ax
  have h_xp1_ne : max (max N1 N2) 1 + 1 ≠ 0 := Real.ne_of_gt h_xp1_pos
  have h_step : max (max N1 N2) 1 + 0 < max (max N1 N2) 1 + 1 :=
    Real.add_lt_add_left Real.zero_lt_one_ax (max (max N1 N2) 1)
  rw [Real.add_zero] at h_step
  have hN1_le_xp1 : N1 ≤ max (max N1 N2) 1 + 1 :=
    Real.le_trans hN1_le (Real.le_of_lt h_step)
  have hN2_le_xp1 : N2 ≤ max (max N1 N2) 1 + 1 :=
    Real.le_trans hN2_le (Real.le_of_lt h_step)
  -- Both hypotheses apply at x_0 and x_0+1.
  have hc_x_0 : c = K / max (max N1 N2) 1 :=
    (hN1 (max (max N1 N2) 1) hN1_le).symm.trans (hN2 (max (max N1 N2) 1) hN2_le)
  have hc_x_0_p1 : c = K / (max (max N1 N2) 1 + 1) :=
    (hN1 (max (max N1 N2) 1 + 1) hN1_le_xp1).symm.trans
      (hN2 (max (max N1 N2) 1 + 1) hN2_le_xp1)
  -- Multiply hc_x_0 by x_0 to get c * x_0 = K.
  have h_c_x_0 : c * max (max N1 N2) 1 = K := by
    rw [hc_x_0]
    exact div_mul_cancel h_ne
  -- Multiply hc_x_0_p1 by x_0 + 1 to get c * (x_0+1) = K.
  have h_c_x_0_p1 : c * (max (max N1 N2) 1 + 1) = K := by
    rw [hc_x_0_p1]
    exact div_mul_cancel h_xp1_ne
  -- Equate: c * x_0 = c * (x_0+1).
  have h_eq_K : c * max (max N1 N2) 1 = c * (max (max N1 N2) 1 + 1) :=
    h_c_x_0.trans h_c_x_0_p1.symm
  -- Distribute RHS: c * (x_0+1) = c * x_0 + c * 1 = c * x_0 + c.
  rw [Real.mul_distrib c (max (max N1 N2) 1) 1, Real.mul_one_ax] at h_eq_K
  -- h_eq_K : c * x_0 = c * x_0 + c
  -- Hence c = 0. (Subtract c * x_0 from both sides.)
  have h_c_zero : c = 0 := by
    -- Don't use `rw [h_eq_K]` here — h_eq_K's RHS contains the LHS
    -- pattern (`c * x_0` is in `c * x_0 + c`) and Lean's all-
    -- occurrences rewriter would cascade. Use congrArg instead.
    have step : -(c * max (max N1 N2) 1) + (c * max (max N1 N2) 1) =
                -(c * max (max N1 N2) 1) + (c * max (max N1 N2) 1 + c) :=
      congrArg (fun y => -(c * max (max N1 N2) 1) + y) h_eq_K
    rw [Real.neg_add_self] at step
    -- step : 0 = -(c * x_0) + (c * x_0 + c)
    rw [← Real.add_assoc, Real.neg_add_self, Real.zero_add] at step
    -- step : 0 = c
    exact step.symm
  -- K = c * x_0 = 0 * x_0 = 0. Contradicts hK.
  have h_K_zero : K = 0 := by
    rw [← h_c_x_0, h_c_zero, Real.zero_mul]
  exact hK h_K_zero

/-! ## Phase 2: structural induction over EMLTree — base cases

The Phase-2 deliverable to close `1/x ∉ EML at any depth`:

  `∀ t : EMLTree, ¬ EventuallyKOverX 1 (fun x => t.eval x)`

This file ships the depth-0 base cases (const c, var) plus the
depth-1 `eml(const, const)` case via the existing
`EventuallyConstant.not_eventually_K_over_x` machinery. The
remaining depth-1 cases (eml(const, var), eml(var, const),
eml(var, var)) and the full inductive case for depth ≥ 2 are
documented but not shipped — they require additional asymptotic
classification predicates (e.g., `EventuallyExpX`,
`EventuallyMinusLog`) beyond Phase 1's two.

This is honest partial progress on the structural induction. -/

/-- Base case 1 (depth-0 const): the constant function `fun _ => c`
is NOT `EventuallyKOverX 1`. Same shape as
`not_eventually_constant_inv_x` but specialized to a different
target asymptotic. -/
theorem not_eventually_K_over_x_one_const (c : Real) :
    ¬ EventuallyKOverX 1 (fun _ : Real => c) := by
  intro ⟨N, hN⟩
  -- For x ≥ max(N,1), c = 1/x. Two samples give 1/x_0 = 1/(x_0+1).
  have hN_le : N ≤ max N 1 := le_max_left N 1
  have h_one_le : (1 : Real) ≤ max N 1 := le_max_right N 1
  have h_pos : (0 : Real) < max N 1 :=
    Real.lt_of_lt_of_le Real.zero_lt_one_ax h_one_le
  have h_step : max N 1 + 0 < max N 1 + 1 :=
    Real.add_lt_add_left Real.zero_lt_one_ax (max N 1)
  rw [Real.add_zero] at h_step
  have hN_le_xp1 : N ≤ max N 1 + 1 := Real.le_trans hN_le (Real.le_of_lt h_step)
  have h0 : c = 1 / max N 1 := hN (max N 1) hN_le
  have h1 : c = 1 / (max N 1 + 1) := hN (max N 1 + 1) hN_le_xp1
  have heq : (1 : Real) / max N 1 = 1 / (max N 1 + 1) := h0.symm.trans h1
  exact one_div_x_ne_one_div_x_plus_one (max N 1) h_pos heq

/-- Base case 2 (depth-0 var): the identity function `fun x => x`
is NOT `EventuallyKOverX 1`. Sample at x_0 = max N (1+1), then
x_0 ≥ 2 > 1 and x_0 = 1/x_0. Multiplying by x_0: x_0² = 1. But
x_0 > 1 implies x_0² > x_0 > 1, contradicting x_0² = 1. -/
theorem not_eventually_K_over_x_one_var :
    ¬ EventuallyKOverX 1 (fun x : Real => x) := by
  intro ⟨N, hN⟩
  -- Sample at x_0 = max N (1+1). Then x_0 ≥ N and x_0 ≥ 1+1 > 1.
  have hN_le : N ≤ max N (1+1) := le_max_left N (1+1)
  have h_two_le : (1+1 : Real) ≤ max N (1+1) := le_max_right N (1+1)
  have h_one_lt_two : (1 : Real) < 1 + 1 := one_lt_one_plus_one
  have h_one_lt : (1 : Real) < max N (1+1) :=
    Real.lt_of_lt_of_le h_one_lt_two h_two_le
  have h_pos : (0 : Real) < max N (1+1) :=
    Real.lt_trans_ax Real.zero_lt_one_ax h_one_lt
  have h_ne : max N (1+1) ≠ 0 := Real.ne_of_gt h_pos
  -- (fun x => x)(max N (1+1)) = 1 / max N (1+1)
  have h_eq : max N (1+1) = 1 / max N (1+1) := hN (max N (1+1)) hN_le
  -- Multiply both sides by max N (1+1):
  --   (max N (1+1))² = (1/max N (1+1)) * (max N (1+1)) = 1.
  have h_step : max N (1+1) * max N (1+1) =
                (1 / max N (1+1)) * max N (1+1) :=
    congrArg (fun y => y * max N (1+1)) h_eq
  rw [Real.mul_comm (1 / max N (1+1)) (max N (1+1))] at h_step
  rw [Real.mul_inv (max N (1+1)) h_ne] at h_step
  -- h_step : max N (1+1) * max N (1+1) = 1
  -- But max N (1+1) > 1 ⟹ max N (1+1) * max N (1+1) > 1 * max N (1+1)
  --                     = max N (1+1) > 1.
  have h_strict : 1 * max N (1+1) < max N (1+1) * max N (1+1) :=
    Real.mul_lt_mul_of_pos_right h_one_lt h_pos
  rw [Real.one_mul_thm] at h_strict
  rw [h_step] at h_strict
  -- h_strict : max N (1+1) < 1
  exact Real.lt_irrefl_ax _ (Real.lt_trans_ax h_one_lt h_strict)

/-- **Phase-2 partial theorem: depth-0 EMLTrees don't satisfy
`EventuallyKOverX 1`.** Combines the two base cases. -/
theorem not_eventually_K_over_x_one_eml_depth_zero
    (t : EMLTree) (ht : t.depth = 0) :
    ¬ EventuallyKOverX 1 (fun x => t.eval x) := by
  cases t with
  | const c =>
    -- (const c).eval x = c definitionally; goal reduces.
    exact not_eventually_K_over_x_one_const c
  | var =>
    -- var.eval x = x definitionally.
    exact not_eventually_K_over_x_one_var
  | eml _ _ =>
    -- (eml _ _).depth ≥ 1, contradicting ht : depth = 0.
    simp [EMLTree.depth] at ht

/-- **Phase-2 partial theorem: the `eml(const a, const b)` depth-1
case.** Eval is constant; closed via the existing
`EventuallyConstant.not_eventually_K_over_x` disjointness from
Phase 1. Demonstrates the framework's reusability. -/
theorem not_eventually_K_over_x_one_eml_const_const (a b : Real) :
    ¬ EventuallyKOverX 1 (fun x => (EMLTree.eml (.const a) (.const b)).eval x) := by
  apply EventuallyConstant.not_eventually_K_over_x Real.one_ne_zero
  -- Show: EventuallyConstant (fun x => exp(a) - log(b)).
  refine ⟨Real.exp a - Real.log b, 0, ?_⟩
  intro x _
  rfl

/-- **Phase-2 partial: the `eml(var, const b)` depth-1 case.**
Eval x = `exp x - log b`. As x → ∞, exp x grows super-exp while
log b + 1/x stays bounded. So eventually `exp x - log b > 1 > 1/x`.

Sample at `x_0 = max N (max (1+1) (log b + 1))`. Three properties:
  - `x_0 ≥ N` (so the eventually-K/x hypothesis applies).
  - `x_0 > 1` (so 1/x_0 < 1 by `div_lt_one_of_pos_lt`).
  - `x_0 ≥ log b + 1` (so `exp x_0 > x_0 ≥ log b + 1`, hence
    `eval x_0 = exp x_0 - log b > 1`).

Combined: `1 < eval x_0 = 1/x_0 < 1`, contradicting `lt_irrefl`. -/
theorem not_eventually_K_over_x_one_eml_var_const (b : Real) :
    ¬ EventuallyKOverX 1
      (fun x => (EMLTree.eml .var (.const b)).eval x) := by
  intro ⟨N, hN⟩
  have hN_le : N ≤ max N (max (1+1) (Real.log b + 1)) := le_max_left _ _
  have h_inner_le :
      max (1+1) (Real.log b + 1) ≤ max N (max (1+1) (Real.log b + 1)) :=
    le_max_right _ _
  have h_two_le_inner : (1+1 : Real) ≤ max (1+1) (Real.log b + 1) :=
    le_max_left _ _
  have h_logb_le_inner :
      Real.log b + 1 ≤ max (1+1) (Real.log b + 1) := le_max_right _ _
  have h_two_le : (1+1 : Real) ≤ max N (max (1+1) (Real.log b + 1)) :=
    Real.le_trans h_two_le_inner h_inner_le
  have h_logb_le :
      Real.log b + 1 ≤ max N (max (1+1) (Real.log b + 1)) :=
    Real.le_trans h_logb_le_inner h_inner_le
  have h_one_lt_two : (1 : Real) < 1 + 1 := one_lt_one_plus_one
  have h_one_lt : (1 : Real) < max N (max (1+1) (Real.log b + 1)) :=
    Real.lt_of_lt_of_le h_one_lt_two h_two_le
  have h_pos : (0 : Real) < max N (max (1+1) (Real.log b + 1)) :=
    Real.lt_trans_ax Real.zero_lt_one_ax h_one_lt
  -- Apply hN at x_0:
  have h_eval :
      (EMLTree.eml .var (.const b)).eval (max N (max (1+1) (Real.log b + 1)))
      = 1 / max N (max (1+1) (Real.log b + 1)) :=
    hN (max N (max (1+1) (Real.log b + 1))) hN_le
  simp only [EMLTree.eval] at h_eval
  -- h_eval : exp(x_0) - log b = 1 / x_0
  -- Show: 1 < exp(x_0) - log b.
  have h_exp_gt :
      max N (max (1+1) (Real.log b + 1)) <
        Real.exp (max N (max (1+1) (Real.log b + 1))) :=
    exp_grows_strictly _
  have h_log_lt_exp :
      Real.log b + 1 < Real.exp (max N (max (1+1) (Real.log b + 1))) :=
    Real.lt_of_le_of_lt h_logb_le h_exp_gt
  have h_eval_gt_one :
      1 < Real.exp (max N (max (1+1) (Real.log b + 1))) - Real.log b := by
    have step :
        -(Real.log b) + (Real.log b + 1) <
        -(Real.log b) + Real.exp (max N (max (1+1) (Real.log b + 1))) :=
      Real.add_lt_add_left h_log_lt_exp (-(Real.log b))
    rw [← Real.add_assoc, Real.neg_add_self, Real.zero_add] at step
    -- step : 1 < -(log b) + exp(x_0)
    rw [Real.add_comm (-(Real.log b))
        (Real.exp (max N (max (1+1) (Real.log b + 1))))] at step
    rw [← Real.sub_def] at step
    exact step
  -- Combine with h_eval (eval = 1/x_0):
  rw [h_eval] at h_eval_gt_one
  -- h_eval_gt_one : 1 < 1 / x_0
  -- But 1/x_0 < 1 (since x_0 > 1, by div_lt_one_of_pos_lt).
  have h_div_lt_one :
      (1 : Real) / max N (max (1+1) (Real.log b + 1)) < 1 :=
    Real.div_lt_one_of_pos_lt h_pos h_one_lt
  exact Real.lt_irrefl_ax _ (Real.lt_trans_ax h_eval_gt_one h_div_lt_one)

/- PHASE 2 — REMAINING WORK

Phase 2 shipped here:
  - Depth-0 base cases: const c, var.
  - Depth-1 case 1: eml(const, const) via the EventuallyConstant
    framework.
  - Depth-1 case 2: eml(var, const b) via exp dominance (exp x
    eventually exceeds any constant log b + 1, so eval > 1 > 1/x).

Phase 2 remaining (the other two depth-1 cases):

  - `eml(const a, var)`: eval x = exp a - log x. As x → ∞, log x
    grows past any constant, so eval → -∞. At
    `x_0 = max N (exp(exp a + 1) + 1)`: log x_0 > exp a + 1, so
    eval x_0 < -1 < 0 < 1/x_0. Mechanically requires the
    `(exp a + -log x_0) + 1 < 0` rearrangement chain (4-5 rw
    steps) which is tractable but exceeds this session's budget.
    Documented + designed; ~50 lines of careful chain.

  - `eml(var, var)`: eval x = exp x - log x. Harder than
    eml(var, const b) because log x is now non-constant. The
    `exp x > log x + 1/x` inequality holds asymptotically but
    proving it at a specific large x requires either a tighter
    exp_grows_strictly variant (e.g., `exp x > x + 1` for x ≥ 0)
    or sampling at a specific x like exp 1 with the threshold
    case-split (sample at max N (exp 1)). Open.

Phase 2 for depth ≥ 2:

  Structural induction with IH on sub-trees. The IH must be
  stronger than just `¬ EventuallyKOverX 1`: it must classify
  each sub-tree's eval into a finite set of asymptotic classes
  (EventuallyConstant, EventuallyExpGrowth, EventuallyMinusLog,
  EventuallyKOverX_K with K specifically `exp(exp(...))`-valued,
  etc.). Each new asymptotic class needs its own predicate +
  disjointness lemmas from `EventuallyKOverX 1`.

  Estimated 3-5 sessions for full coverage, or an axiomatic
  shortcut (lift the K-coefficient barrier as a structural axiom
  on EMLTree.eval forms).

This file's Phase-2 contribution: 4 of the 6 depth-≤-1 shapes
closed (const, var, eml(const, const), eml(var, const)). The
other 2 (eml(const, var), eml(var, var)) are the natural next
deliverables. Phase 2 at full coverage closes
`1/x ∉ EML at depth ≤ 1` via the framework — a clean
reformulation of `inv_x_not_in_eml_1` from InvXNotInEML.lean
that doesn't depend on the global-equation hypothesis.
-/

end MachLib
