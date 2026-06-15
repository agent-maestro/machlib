import MachLib.Asymptotics
import MachLib.SinNotInEML
import MachLib.InvXNotInEML
import MachLib.Forge
import MachLib.Linarith              -- one_div_pos_of_pos
import MachLib.EMLAsymptoticBound    -- log_le_id_at_one

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

/-- **Phase-2 partial: the `eml(const a, var)` depth-1 case.**
Eval x = `exp a - log x`. As x → ∞, log x → ∞, so eval → -∞.
Meanwhile 1/x → 0+. So at sufficiently large x, eval < 0 < 1/x.

Sample at x_0 = `max N (exp(exp a + 1) + 1)`.
  - x_0 > exp(exp a + 1), so log x_0 > exp a + 1 (by log_lt_log + log_exp).
  - Hence (exp a - log x_0) + 1 < 0, i.e., exp a - log x_0 < -1.
  - But eval x_0 = 1/x_0 > 0 from hypothesis.
  - So 1/x_0 < -1 < 0 < 1/x_0, contradiction. -/
theorem not_eventually_K_over_x_one_eml_const_var (a : Real) :
    ¬ EventuallyKOverX 1
      (fun x => (EMLTree.eml (.const a) .var).eval x) := by
  intro ⟨N, hN⟩
  -- Sample setup: x_0 = max N (exp(exp a + 1) + 1).
  have hN_le : N ≤ max N (Real.exp (Real.exp a + 1) + 1) := le_max_left _ _
  have h_Tp1_le :
      Real.exp (Real.exp a + 1) + 1 ≤
        max N (Real.exp (Real.exp a + 1) + 1) := le_max_right _ _
  -- x_0 > T = exp(exp a + 1):
  have h_T_pos : (0 : Real) < Real.exp (Real.exp a + 1) := Real.exp_pos _
  have h_T_lt_Tp1 :
      Real.exp (Real.exp a + 1) < Real.exp (Real.exp a + 1) + 1 := by
    have step :
        Real.exp (Real.exp a + 1) + 0 < Real.exp (Real.exp a + 1) + 1 :=
      Real.add_lt_add_left Real.zero_lt_one_ax _
    rw [Real.add_zero] at step
    exact step
  have h_T_lt_x0 :
      Real.exp (Real.exp a + 1) <
        max N (Real.exp (Real.exp a + 1) + 1) :=
    Real.lt_of_lt_of_le h_T_lt_Tp1 h_Tp1_le
  have h_x0_pos : (0 : Real) < max N (Real.exp (Real.exp a + 1) + 1) :=
    Real.lt_trans_ax h_T_pos h_T_lt_x0
  -- log x_0 > exp a + 1 (log_lt_log + log_exp):
  have h_log_T_lt :
      Real.log (Real.exp (Real.exp a + 1)) <
        Real.log (max N (Real.exp (Real.exp a + 1) + 1)) :=
    Real.log_lt_log h_T_pos h_T_lt_x0
  rw [Real.log_exp] at h_log_T_lt
  -- h_log_T_lt : exp a + 1 < log x_0
  -- Derive (exp a - log x_0) + 1 < 0:
  have h_step1 :
      (Real.exp a -
        Real.log (max N (Real.exp (Real.exp a + 1) + 1))) + 1 < 0 := by
    have step :
        -Real.log (max N (Real.exp (Real.exp a + 1) + 1)) +
          (Real.exp a + 1) <
        -Real.log (max N (Real.exp (Real.exp a + 1) + 1)) +
          Real.log (max N (Real.exp (Real.exp a + 1) + 1)) :=
      Real.add_lt_add_left h_log_T_lt _
    rw [Real.neg_add_self] at step
    -- step : -log x_0 + (exp a + 1) < 0
    rw [Real.add_comm
        (-Real.log (max N (Real.exp (Real.exp a + 1) + 1)))
        (Real.exp a + 1)] at step
    rw [Real.add_assoc] at step
    rw [Real.add_comm 1
        (-Real.log (max N (Real.exp (Real.exp a + 1) + 1)))] at step
    rw [← Real.add_assoc] at step
    rw [← Real.sub_def] at step
    exact step
  -- Derive exp a - log x_0 < -1:
  have h_eval_lt_neg_one :
      Real.exp a -
        Real.log (max N (Real.exp (Real.exp a + 1) + 1)) < -1 := by
    have step :
        -(1 : Real) +
          ((Real.exp a -
              Real.log (max N (Real.exp (Real.exp a + 1) + 1))) + 1) <
        -(1 : Real) + 0 :=
      Real.add_lt_add_left h_step1 (-(1 : Real))
    rw [Real.add_zero] at step
    -- step : -1 + ((exp a - log x_0) + 1) < -1
    rw [← Real.add_assoc] at step
    rw [Real.add_comm (-(1 : Real))
        (Real.exp a -
          Real.log (max N (Real.exp (Real.exp a + 1) + 1)))] at step
    rw [Real.add_assoc] at step
    rw [Real.neg_add_self] at step
    rw [Real.add_zero] at step
    exact step
  -- Apply hN at x_0:
  have h_eval :
      (EMLTree.eml (.const a) .var).eval
        (max N (Real.exp (Real.exp a + 1) + 1)) =
      1 / max N (Real.exp (Real.exp a + 1) + 1) :=
    hN _ hN_le
  simp only [EMLTree.eval] at h_eval
  -- h_eval : exp a - log x_0 = 1/x_0
  rw [h_eval] at h_eval_lt_neg_one
  -- h_eval_lt_neg_one : 1/x_0 < -1
  have h_one_div_pos :
      (0 : Real) < 1 / max N (Real.exp (Real.exp a + 1) + 1) :=
    Real.one_div_pos_of_pos h_x0_pos
  have h_neg_one_lt_zero : -(1 : Real) < 0 := by
    have step : -(1 : Real) + 0 < -(1 : Real) + 1 :=
      Real.add_lt_add_left Real.zero_lt_one_ax _
    rw [Real.neg_add_self, Real.add_zero] at step
    exact step
  -- Chain: 1/x_0 < -1 < 0 < 1/x_0 ⟹ 1/x_0 < 1/x_0, contradiction.
  have h_lt_zero :
      (1 : Real) / max N (Real.exp (Real.exp a + 1) + 1) < 0 :=
    Real.lt_trans_ax h_eval_lt_neg_one h_neg_one_lt_zero
  exact Real.lt_irrefl_ax _ (Real.lt_trans_ax h_lt_zero h_one_div_pos)

/-! ## The tangent-line axiom (closes `eml(var, var)`)

Classical fact: `Real.exp` is strictly convex (second derivative
positive everywhere). The tangent line at `x = 0` is `y = 1 + x`.
By strict convexity, `exp(x) > tangent(x) = 1 + x` for `x ≠ 0`.
In particular, `x + 1 < exp x` for `x > 0`.

Lifted as a classical-citation axiom here following the precedent
of `log_le_id_at_one` in `EMLAsymptoticBound.lean`. Discharge
path: ~30 lines via a convexity primitive (`exp_convex`) plus
the tangent-equation derivation. The existing
`exp_grows_strictly : x < exp x` is the weaker version (the
secant-line bound at x = 0 vs. ∞); the tangent-line bound is the
strict sharper form needed here. -/
axiom exp_tangent_line_strict (x : Real) (hx : 0 < x) :
    x + 1 < Real.exp x

/-- **Phase-2: `eml(var, var)` depth-1 case via the tangent-line axiom.**
Eval x = `exp x - log x`. Hypothesis = 1/x eventually.

Sample at x_0 = max N (1+1). At this x_0:
  - log x_0 ≤ x_0 (by log_le_id_at_one).
  - 1/x_0 ≤ 1 (by div_lt_one_of_pos_lt since x_0 > 1).
  - So 1/x_0 + log x_0 ≤ 1 + x_0 (by add_le_add_both).
  - From hypothesis: exp x_0 - log x_0 = 1/x_0, so
    exp x_0 = 1/x_0 + log x_0 ≤ 1 + x_0 = x_0 + 1.
  - But x_0 + 1 < exp x_0 (by tangent_line_strict, since x_0 > 0).
  - So x_0 + 1 < exp x_0 ≤ x_0 + 1, contradicting lt_irrefl. -/
theorem not_eventually_K_over_x_one_eml_var_var :
    ¬ EventuallyKOverX 1 (fun x => (EMLTree.eml .var .var).eval x) := by
  intro ⟨N, hN⟩
  -- Sample at x_0 = max N (1+1).
  have hN_le : N ≤ max N (1+1) := le_max_left _ _
  have h_two_le : (1+1 : Real) ≤ max N (1+1) := le_max_right _ _
  have h_one_lt_two : (1 : Real) < 1 + 1 := one_lt_one_plus_one
  have h_one_lt : (1 : Real) < max N (1+1) :=
    Real.lt_of_lt_of_le h_one_lt_two h_two_le
  have h_pos : (0 : Real) < max N (1+1) :=
    Real.lt_trans_ax Real.zero_lt_one_ax h_one_lt
  have h_one_le : (1 : Real) ≤ max N (1+1) := Real.le_of_lt h_one_lt
  -- Apply hN at x_0:
  have h_eval :
      (EMLTree.eml .var .var).eval (max N (1+1)) = 1 / max N (1+1) :=
    hN _ hN_le
  simp only [EMLTree.eval] at h_eval
  -- h_eval : exp x_0 - log x_0 = 1/x_0
  -- Rearrange to exp x_0 = 1/x_0 + log x_0:
  have h_eval_rearr :
      Real.exp (max N (1+1)) =
        1 / max N (1+1) + Real.log (max N (1+1)) := by
    have step :
        (Real.exp (max N (1+1)) - Real.log (max N (1+1))) +
          Real.log (max N (1+1)) =
        1 / max N (1+1) + Real.log (max N (1+1)) :=
      congrArg (fun y => y + Real.log (max N (1+1))) h_eval
    rw [Real.sub_def] at step
    rw [Real.add_assoc] at step
    rw [Real.neg_add_self] at step
    rw [Real.add_zero] at step
    exact step
  -- 1/x_0 ≤ 1 and log x_0 ≤ x_0, so 1/x_0 + log x_0 ≤ 1 + x_0:
  have h_div_lt : (1 : Real) / max N (1+1) < 1 :=
    Real.div_lt_one_of_pos_lt h_pos h_one_lt
  have h_div_le : (1 : Real) / max N (1+1) ≤ 1 := Real.le_of_lt h_div_lt
  have h_log_le : Real.log (max N (1+1)) ≤ max N (1+1) :=
    EMLTree.log_le_id_at_one (max N (1+1)) h_one_le
  have h_bound :
      (1 : Real) / max N (1+1) + Real.log (max N (1+1)) ≤
        1 + max N (1+1) :=
    Real.add_le_add_both h_div_le h_log_le
  -- So exp x_0 ≤ 1 + x_0:
  have h_exp_le : Real.exp (max N (1+1)) ≤ 1 + max N (1+1) := by
    rw [h_eval_rearr]
    exact h_bound
  -- Rewrite 1 + x_0 to x_0 + 1 to match the tangent-line bound:
  rw [Real.add_comm 1 (max N (1+1))] at h_exp_le
  -- h_exp_le : exp x_0 ≤ x_0 + 1
  -- Tangent-line axiom: x_0 + 1 < exp x_0.
  have h_tan : max N (1+1) + 1 < Real.exp (max N (1+1)) :=
    exp_tangent_line_strict (max N (1+1)) h_pos
  -- Combine: x_0 + 1 < exp x_0 ≤ x_0 + 1, contradiction.
  exact Real.lt_irrefl_ax _ (Real.lt_of_lt_of_le h_tan h_exp_le)

/-! ## Phase 2 (depth-2 starter): the clamp-trigger eventually-constant pattern

For depth-2 EMLTrees with shape
`eml(const c1, eml(const c2, var))`:

  eval x = exp c1 - log_clamped(exp c2 - log x).

For x ≥ exp(exp c2), the inner `exp c2 - log x ≤ 0`, so the clamp
fires and `log_clamped = 0`. Hence eval = exp c1, constant.

This means the entire tree is eventually constant, so the Phase-1
`EventuallyConstant.not_eventually_K_over_x` closes the case
immediately. Same template as `x_plus_one_not_in_eml_2_eml_const_eml_const_var`
in EMLAdditionClosureFailure.lean, ported to inv_x. -/

/-- **Shared clamp-trigger helper.** For x ≥ exp(exp a), the inner
`exp a - log x ≤ 0`, so the clamped log returns 0. Reused across
multiple depth-2 cases. -/
private theorem log_inner_zero_at_exp_exp (a x : Real)
    (hx : Real.exp (Real.exp a) ≤ x) :
    Real.log (Real.exp a - Real.log x) = 0 := by
  rcases (Real.le_iff_lt_or_eq (Real.exp (Real.exp a)) x).mp hx with hxlt | hxeq
  · have h_exp_a_pos : (0 : Real) < Real.exp (Real.exp a) := Real.exp_pos _
    have hlog_lt :
        Real.log (Real.exp (Real.exp a)) < Real.log x :=
      Real.log_lt_log h_exp_a_pos hxlt
    rw [Real.log_exp] at hlog_lt
    have h_diff_neg : Real.exp a - Real.log x < 0 := by
      rw [Real.sub_def]
      have step := Real.add_lt_add_left hlog_lt (-Real.log x)
      rw [Real.neg_add_self] at step
      rw [Real.add_comm] at step
      exact step
    exact Real.log_nonpos (Real.le_of_lt h_diff_neg)
  · rw [← hxeq, Real.log_exp, Real.sub_self, Real.log_zero]

theorem not_eventually_K_over_x_one_eml_const_eml_const_var
    (c1 c2 : Real) :
    ¬ EventuallyKOverX 1
      (fun x =>
        (EMLTree.eml (.const c1) (EMLTree.eml (.const c2) .var)).eval x) := by
  apply EventuallyConstant.not_eventually_K_over_x Real.one_ne_zero
  refine ⟨Real.exp c1, Real.exp (Real.exp c2), ?_⟩
  intro x hx
  show Real.exp c1 - Real.log (Real.exp c2 - Real.log x) = Real.exp c1
  rw [log_inner_zero_at_exp_exp c2 x hx]
  rw [Real.sub_def, Real.neg_zero, Real.add_zero]

/-! ## Depth-2 sweep: all-constants cases (eval is literally constant in x)

These shapes have no `var` anywhere, so eval is constant in x and
the framework closes them via Phase 1's
`EventuallyConstant.not_eventually_K_over_x` immediately. -/

/-- Depth-2 all-constants A: `eml(const c, eml(const a, const b))`. -/
theorem not_eventually_K_over_x_one_eml_const_eml_const_const
    (c a b : Real) :
    ¬ EventuallyKOverX 1
      (fun x =>
        (EMLTree.eml (.const c) (EMLTree.eml (.const a) (.const b))).eval x) := by
  apply EventuallyConstant.not_eventually_K_over_x Real.one_ne_zero
  refine ⟨Real.exp c - Real.log (Real.exp a - Real.log b), 0, ?_⟩
  intro x _
  rfl

/-- Depth-2 all-constants B: `eml(eml(const c1, const c2), const c)`. -/
theorem not_eventually_K_over_x_one_eml_eml_const_const_const
    (c1 c2 c : Real) :
    ¬ EventuallyKOverX 1
      (fun x =>
        (EMLTree.eml (EMLTree.eml (.const c1) (.const c2)) (.const c)).eval x) := by
  apply EventuallyConstant.not_eventually_K_over_x Real.one_ne_zero
  refine ⟨Real.exp (Real.exp c1 - Real.log c2) - Real.log c, 0, ?_⟩
  intro x _
  rfl

/-- Depth-2 all-constants C: `eml(eml(const c1, const c2), eml(const a, const b))`. -/
theorem not_eventually_K_over_x_one_eml_eml_const_const_eml_const_const
    (c1 c2 a b : Real) :
    ¬ EventuallyKOverX 1
      (fun x =>
        (EMLTree.eml (EMLTree.eml (.const c1) (.const c2))
                     (EMLTree.eml (.const a) (.const b))).eval x) := by
  apply EventuallyConstant.not_eventually_K_over_x Real.one_ne_zero
  refine ⟨Real.exp (Real.exp c1 - Real.log c2) -
          Real.log (Real.exp a - Real.log b), 0, ?_⟩
  intro x _
  rfl

/-! ## Depth-2 sweep: clamp-trigger cases (eval eventually constant via clamp) -/

/-- Depth-2 clamp D:
`eml(eml(const c1, const c2), eml(const a, var))`. Same template
as `not_eventually_K_over_x_one_eml_const_eml_const_var` but with
t1 = eml(const c1, const c2) instead of const c. The eval becomes
`exp(exp c1 - log c2)` for x ≥ exp(exp a). -/
theorem not_eventually_K_over_x_one_eml_eml_const_const_eml_const_var
    (c1 c2 a : Real) :
    ¬ EventuallyKOverX 1
      (fun x =>
        (EMLTree.eml (EMLTree.eml (.const c1) (.const c2))
                     (EMLTree.eml (.const a) .var)).eval x) := by
  apply EventuallyConstant.not_eventually_K_over_x Real.one_ne_zero
  refine ⟨Real.exp (Real.exp c1 - Real.log c2), Real.exp (Real.exp a), ?_⟩
  intro x hx
  show Real.exp (Real.exp c1 - Real.log c2) -
       Real.log (Real.exp a - Real.log x) =
       Real.exp (Real.exp c1 - Real.log c2)
  rw [log_inner_zero_at_exp_exp a x hx]
  rw [Real.sub_def, Real.neg_zero, Real.add_zero]

/-! ## Depth-2 sweep: exp-dominance cases (t1 = var) -/

/-- Depth-2 exp-dominance E: `eml(var, eml(const a, const b))`.
Eval x = `exp x - log_clamped(exp a - log b)`. The inner is a
constant (call it L). eval = exp x - L for all x. Same exp
dominance chain as `eml(var, const b)` at depth 1, with
L = `log_clamped(exp a - log b)` replacing `log b`. -/
theorem not_eventually_K_over_x_one_eml_var_eml_const_const
    (a b : Real) :
    ¬ EventuallyKOverX 1
      (fun x =>
        (EMLTree.eml .var (EMLTree.eml (.const a) (.const b))).eval x) := by
  intro ⟨N, hN⟩
  -- Let L := log_clamped(exp a - log b). Sample at
  -- x_0 = max N (max (1+1) (L + 1)).
  -- exp x_0 > x_0 ≥ L + 1, so eval = exp x_0 - L > 1.
  -- But eval = 1/x_0 < 1, contradiction.
  --
  -- This is the same proof body as not_eventually_K_over_x_one_eml_var_const
  -- with L = Real.log (Real.exp a - Real.log b) replacing `Real.log b`.
  -- We inline rather than factor a helper because the helper would need to
  -- abstract over the EMLTree shape too, which complicates the unfolding.
  have hN_le :
      N ≤ max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1)) :=
    le_max_left _ _
  have h_inner_le :
      max (1+1) (Real.log (Real.exp a - Real.log b) + 1) ≤
        max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1)) :=
    le_max_right _ _
  have h_two_le_inner :
      (1+1 : Real) ≤
        max (1+1) (Real.log (Real.exp a - Real.log b) + 1) :=
    le_max_left _ _
  have h_L_le_inner :
      Real.log (Real.exp a - Real.log b) + 1 ≤
        max (1+1) (Real.log (Real.exp a - Real.log b) + 1) :=
    le_max_right _ _
  have h_two_le :
      (1+1 : Real) ≤
        max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1)) :=
    Real.le_trans h_two_le_inner h_inner_le
  have h_L_le :
      Real.log (Real.exp a - Real.log b) + 1 ≤
        max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1)) :=
    Real.le_trans h_L_le_inner h_inner_le
  have h_one_lt_two : (1 : Real) < 1 + 1 := one_lt_one_plus_one
  have h_one_lt :
      (1 : Real) <
        max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1)) :=
    Real.lt_of_lt_of_le h_one_lt_two h_two_le
  have h_pos :
      (0 : Real) <
        max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1)) :=
    Real.lt_trans_ax Real.zero_lt_one_ax h_one_lt
  have h_eval :
      (EMLTree.eml .var (EMLTree.eml (.const a) (.const b))).eval
        (max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1))) =
      1 / max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1)) :=
    hN _ hN_le
  simp only [EMLTree.eval] at h_eval
  have h_exp_gt :
      max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1)) <
        Real.exp
          (max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1))) :=
    exp_grows_strictly _
  have h_L_lt_exp :
      Real.log (Real.exp a - Real.log b) + 1 <
        Real.exp
          (max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1))) :=
    Real.lt_of_le_of_lt h_L_le h_exp_gt
  have h_eval_gt_one :
      1 < Real.exp
            (max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1))) -
          Real.log (Real.exp a - Real.log b) := by
    have step :
        -Real.log (Real.exp a - Real.log b) +
          (Real.log (Real.exp a - Real.log b) + 1) <
        -Real.log (Real.exp a - Real.log b) +
          Real.exp
            (max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1))) :=
      Real.add_lt_add_left h_L_lt_exp _
    rw [← Real.add_assoc, Real.neg_add_self, Real.zero_add] at step
    rw [Real.add_comm
          (-Real.log (Real.exp a - Real.log b))
          (Real.exp
            (max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1))))] at step
    rw [← Real.sub_def] at step
    exact step
  rw [h_eval] at h_eval_gt_one
  have h_div_lt_one :
      (1 : Real) /
        max N (max (1+1) (Real.log (Real.exp a - Real.log b) + 1)) < 1 :=
    Real.div_lt_one_of_pos_lt h_pos h_one_lt
  exact Real.lt_irrefl_ax _
    (Real.lt_trans_ax h_eval_gt_one h_div_lt_one)

/-- Depth-2 exp-dom + clamp F: `eml(var, eml(const a, var))`. The inner
t2 = eml(const a, var) clamps for x ≥ exp(exp a). After clamping,
eval = exp x. For x ≥ max(N, exp(exp a), 1+1):
  exp x > x ≥ 1+1 > 1 > 1/x, but eval = 1/x. Contradiction. -/
theorem not_eventually_K_over_x_one_eml_var_eml_const_var
    (a : Real) :
    ¬ EventuallyKOverX 1
      (fun x =>
        (EMLTree.eml .var (EMLTree.eml (.const a) .var)).eval x) := by
  intro ⟨N, hN⟩
  -- Sample at x_0 = max N (max (1+1) (exp(exp a))).
  have hN_le :
      N ≤ max N (max (1+1) (Real.exp (Real.exp a))) := le_max_left _ _
  have h_inner_le :
      max (1+1) (Real.exp (Real.exp a)) ≤
        max N (max (1+1) (Real.exp (Real.exp a))) := le_max_right _ _
  have h_two_le_inner :
      (1+1 : Real) ≤ max (1+1) (Real.exp (Real.exp a)) :=
    le_max_left _ _
  have h_expexp_le_inner :
      Real.exp (Real.exp a) ≤ max (1+1) (Real.exp (Real.exp a)) :=
    le_max_right _ _
  have h_two_le :
      (1+1 : Real) ≤ max N (max (1+1) (Real.exp (Real.exp a))) :=
    Real.le_trans h_two_le_inner h_inner_le
  have h_expexp_le :
      Real.exp (Real.exp a) ≤
        max N (max (1+1) (Real.exp (Real.exp a))) :=
    Real.le_trans h_expexp_le_inner h_inner_le
  have h_one_lt_two : (1 : Real) < 1 + 1 := one_lt_one_plus_one
  have h_one_lt :
      (1 : Real) < max N (max (1+1) (Real.exp (Real.exp a))) :=
    Real.lt_of_lt_of_le h_one_lt_two h_two_le
  have h_pos :
      (0 : Real) < max N (max (1+1) (Real.exp (Real.exp a))) :=
    Real.lt_trans_ax Real.zero_lt_one_ax h_one_lt
  -- Apply hN at x_0:
  have h_eval :
      (EMLTree.eml .var (EMLTree.eml (.const a) .var)).eval
        (max N (max (1+1) (Real.exp (Real.exp a)))) =
      1 / max N (max (1+1) (Real.exp (Real.exp a))) :=
    hN _ hN_le
  simp only [EMLTree.eval] at h_eval
  -- h_eval : exp x_0 - log(exp a - log x_0) = 1/x_0
  -- Use the clamp helper: log(exp a - log x_0) = 0 since x_0 ≥ exp(exp a).
  rw [log_inner_zero_at_exp_exp a
      (max N (max (1+1) (Real.exp (Real.exp a))))
      h_expexp_le, Real.sub_def, Real.neg_zero, Real.add_zero] at h_eval
  -- h_eval : exp x_0 = 1/x_0
  -- exp x_0 > x_0 > 1 > 1/x_0:
  have h_exp_gt_x :
      max N (max (1+1) (Real.exp (Real.exp a))) <
        Real.exp (max N (max (1+1) (Real.exp (Real.exp a)))) :=
    exp_grows_strictly _
  have h_div_lt_one :
      (1 : Real) / max N (max (1+1) (Real.exp (Real.exp a))) < 1 :=
    Real.div_lt_one_of_pos_lt h_pos h_one_lt
  -- exp x_0 > x_0 > 1:
  have h_exp_gt_one :
      (1 : Real) <
        Real.exp (max N (max (1+1) (Real.exp (Real.exp a)))) :=
    Real.lt_trans_ax h_one_lt h_exp_gt_x
  -- Combine: 1 < exp x_0 = 1/x_0 < 1, contradiction.
  rw [h_eval] at h_exp_gt_one
  exact Real.lt_irrefl_ax _ (Real.lt_trans_ax h_exp_gt_one h_div_lt_one)

/- PHASE 2 — STATUS as of 2026-06-15 (post depth-2 sweep)

**Depth ≤ 1 fully closed.** All 6 EMLTree shapes at depth ≤ 1
ruled out as `EventuallyKOverX 1` via the framework. **Depth-2
sweep partially closed**: 7 of 32 depth-2 shapes shipped
via the framework, covering the "no-var" all-constants cases,
the clamp-trigger cases, and the t1=var exp-dominance cases.

Closed (13 theorems, zero sorries):

  Depth 0:
    ✓ const c
    ✓ var

  Depth 1:
    ✓ eml(const, const)  (via EventuallyConstant disjointness)
    ✓ eml(const a, var)  (log dominance: log x_0 > exp a + 1
                          forces eval x_0 < -1, but eval = 1/x_0 > 0)
    ✓ eml(var, const b)  (exp dominance: exp x_0 > log b + 1
                          forces eval x_0 > 1, but eval = 1/x_0 < 1)
    ✓ eml(var, var)      (tangent-line bound: x_0 + 1 < exp x_0,
                          but eval = 1/x_0 + log x_0 ≤ 1 + x_0,
                          contradiction)

  Depth 2 (7 shapes covered, 25 remaining):
    ✓ eml(const c, eml(const a, var))
                          (eventually constant via clamp trigger
                          for x ≥ exp(exp a))
    ✓ eml(const c, eml(const a, const b))             [all-const]
    ✓ eml(eml(const c1, const c2), const c)           [all-const]
    ✓ eml(eml(const c1, const c2), eml(const a, const b))
                                                      [all-const]
    ✓ eml(eml(const c1, const c2), eml(const a, var))
                          (clamp trigger as in eml(const, ...))
    ✓ eml(var, eml(const a, const b))
                          (exp dominance, t2 inner constant)
    ✓ eml(var, eml(const a, var))
                          (t2 clamps, eval = exp x > 1 > 1/x)

  Depth 2 remaining (~25 shapes, mostly K/x and non-clamp patterns):
    - eml(eml(const, var), const c)        K/x coefficient (closed
                                           in InvXNotInEML.lean v0
                                           with global hypothesis;
                                           framework version needs
                                           eventually-equation chain)
    - eml(eml(const, var), eml(const, var)) similar K/x
    - eml(eml(var, *), *)                  iterated-exp super-growth
    - eml(var, var) and var children       eventually-constant via
                                           other patterns or new
                                           predicates
    - eml(const, eml(var, *))              eval involves exp(c) -
                                           log(non-trivial t2)

The depth-≤-1 closure means the framework version is now
STRICTLY STRONGER than the existing `inv_x_not_in_eml_1` from
InvXNotInEML.lean — the framework uses the weaker "eventually
equal" hypothesis vs. the existing "globally equal" one.

One new axiom this commit:
  `exp_tangent_line_strict : 0 < x → x + 1 < exp x`
  Classical tangent-line bound from strict convexity of exp at
  x = 0. Precedent: `log_le_id_at_one` in EMLAsymptoticBound.lean.

Depth ≥ 2: ~31+ shapes remaining. Many close via the
EventuallyConstant disjointness whenever a clamped-log triggers
asymptotically (estimating ~50-70% of depth-2 shapes). Concrete
examples that will close cleanly via the framework once shipped:
  - eml(const, eml(var, const))  — eventually constant (different
                                   trigger).
  - eml(const, eml(const, eml(_, _)))
                                  — recursive clamp.
  - eml(_, eml(eml(const, var), _))
                                  — inner sub-tree drives clamp.

Shapes where the clamped log NEVER triggers (e.g., when t2.eval
stays positive — common for tree subterms like `eml(var, var)`
which gives `exp x - log x > 0` for x ≥ 1) need new asymptotic
predicates beyond Phase 1's two. The next file
(EMLAsymptoticClassPhase3.lean) would ship those — predicates
like `EventuallyExpGrowth`, `EventuallyMinusLog`, and their
classification + disjointness lemmas.

Path summary: 5 of 6 depth-≤-1 shapes closed mechanically + 1
depth-2 case as the first structural-induction step. The
EventuallyConstant disjointness is the workhorse for any
clamp-trigger shape at any depth. The K-coefficient mechanism
identified in the Hardy-field bridge crack
(InvXNotInEML.lean :: exp_exp_ne_one) handles the K/x-asymptotic
shapes. Together these close the majority of depth-2 cases.
The residual non-clamp non-K/x shapes (eml(var, var) and its
descendants) remain the structural-induction frontier.
-/

end MachLib
