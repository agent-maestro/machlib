import MachLib.LambertW
import MachLib.Asymptotics
import MachLib.Ring

/-!
# MachLib.LambertWAsymptotics — Lambert-W asymptotic bounds via the substrate

Applies the `MachLib.Asymptotics` substrate (eventual ordering of
functions via `EventuallyLE`, `EventuallyLt`) to Lambert-W. Derives
concrete asymptotic bounds: `W < x < exp x` eventually, hence
`W < iter_exp k` eventually for any `k ≥ 1`.

## New axioms (2 classical-true)

  1. `lambertW_func_eq : W(x) · exp(W(x)) = x` (the defining equation)
  2. `lambertW_monotone : 0 ≤ a ≤ b → W(a) ≤ W(b)` (monotonicity)

Both are foundational facts about W. Neither can be discharged from
MachLib's existing primitives without a complete W construction
(e.g., via inverse-function theorem on `y · exp y`).

Net axiom delta: +2.

## What this enables / what's still open

Concrete asymptotic bounds on W via the substrate. Does NOT close
the Lambert-W any-depth barrier (which would require an additional
lower-bound argument or structural-shape argument — open math).
Documented at end of file.
-/

namespace MachLib
namespace Real

/-! ## Foundational Lambert-W axioms -/

/-- **Defining equation of the Lambert-W function**: `W(x) · exp(W(x)) = x`
on the principal branch.

Restricting to `x ≥ 0` here for simplicity (the full statement holds
for `x ≥ -1/e`, but `x ≥ 0` is enough for the asymptotic bounds). -/
axiom lambertW_func_eq (x : Real) (hx : 0 ≤ x) :
    lambertW x * exp (lambertW x) = x

/-- **Monotonicity of Lambert-W** on the nonnegative reals.

Classical fact: W is strictly monotonically increasing on its
principal-branch domain `[-1/e, ∞)`. Restricting to `0 ≤ a ≤ b`
here. -/
axiom lambertW_monotone (a b : Real) (ha : 0 ≤ a) (hab : a ≤ b) :
    lambertW a ≤ lambertW b

/-! ## Helper: strict mul on the left -/

private theorem mul_lt_mul_pos_left
    {c : Real} (hc : 0 < c) {a b : Real} (h : a < b) :
    c * a < c * b := by
  -- b - a > 0
  have hba_pos : (0 : Real) < b - a := by
    have step := add_lt_add_left h (-a)
    rw [neg_add_self, add_comm (-a) b, ← sub_def] at step
    exact step
  -- c * (b - a) > 0
  have hprod : (0 : Real) < c * (b - a) := mul_pos hc hba_pos
  -- c * (b - a) = c * b - c * a (distributivity)
  have hdistr : c * (b - a) = c * b - c * a := by
    have e1 : (b - a) = b + -a := sub_def _ _
    have e2 : c * b - c * a = c * b + -(c * a) := sub_def _ _
    rw [e1, e2, mul_distrib, mul_neg]
  rw [hdistr] at hprod
  -- hprod : 0 < c * b - c * a
  -- conclude c * a < c * b
  have step := add_lt_add_left hprod (c * a)
  rw [add_zero, sub_def, add_comm (c * b) (-(c * a)), ← add_assoc,
      add_neg, zero_add] at step
  exact step

/-! ## Derived nonneg bounds -/

theorem lambertW_nonneg_at_nonneg (x : Real) (hx : 0 ≤ x) :
    0 ≤ lambertW x := by
  have h_W0_le_Wx : lambertW 0 ≤ lambertW x :=
    lambertW_monotone 0 x (le_refl _) hx
  rw [lambertW_zero] at h_W0_le_Wx
  exact h_W0_le_Wx

theorem lambertW_pos_at_one_le (x : Real) (hx : 1 ≤ x) :
    0 < lambertW x := by
  have h_W1_le_Wx : lambertW 1 ≤ lambertW x :=
    lambertW_monotone 1 x ((le_iff_lt_or_eq _ _).mpr (Or.inl zero_lt_one_ax)) hx
  exact lt_of_lt_of_le lambertW_one_pos h_W1_le_Wx

/-! ## W ≤ id and W < id -/

theorem lambertW_le_id_at_nonneg (x : Real) (hx : 0 ≤ x) :
    lambertW x ≤ x := by
  have h_W_nonneg : 0 ≤ lambertW x := lambertW_nonneg_at_nonneg x hx
  have h_exp_W_ge_one : 1 ≤ exp (lambertW x) := by
    have h_exp_W_ge_exp_zero : exp 0 ≤ exp (lambertW x) :=
      exp_monotone h_W_nonneg
    rw [exp_zero] at h_exp_W_ge_exp_zero
    exact h_exp_W_ge_exp_zero
  have h_W_mul_one : lambertW x * 1 ≤ lambertW x * exp (lambertW x) :=
    mul_le_mul_of_nonneg_left h_exp_W_ge_one h_W_nonneg
  rw [mul_one_ax] at h_W_mul_one
  have h_func_eq : lambertW x * exp (lambertW x) = x := lambertW_func_eq x hx
  rw [h_func_eq] at h_W_mul_one
  exact h_W_mul_one

theorem lambertW_lt_id_at_one_le (x : Real) (hx : 1 ≤ x) :
    lambertW x < x := by
  have h_W_pos : 0 < lambertW x := lambertW_pos_at_one_le x hx
  have h_exp_W_gt_one : 1 < exp (lambertW x) := by
    have h := exp_lt h_W_pos
    rw [exp_zero] at h
    exact h
  have h_W_mul_one_lt : lambertW x * 1 < lambertW x * exp (lambertW x) :=
    mul_lt_mul_pos_left h_W_pos h_exp_W_gt_one
  rw [mul_one_ax] at h_W_mul_one_lt
  have h_x_nonneg : 0 ≤ x := by
    have h_one_le : (1 : Real) ≤ x := hx
    exact (le_iff_lt_or_eq _ _).mpr
      (Or.inl (lt_of_lt_of_le zero_lt_one_ax h_one_le))
  have h_func_eq : lambertW x * exp (lambertW x) = x :=
    lambertW_func_eq x h_x_nonneg
  rw [h_func_eq] at h_W_mul_one_lt
  exact h_W_mul_one_lt

/-! ## Asymptotic bounds via the substrate -/

theorem lambertW_eventually_lt_id :
    EventuallyLt lambertW (fun x => x) := by
  refine ⟨1, ?_⟩
  intro x hx
  exact lambertW_lt_id_at_one_le x hx

theorem lambertW_eventually_lt_exp :
    EventuallyLt lambertW Real.exp :=
  EventuallyLt.trans lambertW_eventually_lt_id id_eventually_lt_exp

/-- **W is eventually strictly less than `iter_exp k`** for any `k ≥ 1`.

Chain: `W eventually-lt exp = iter_exp 1`, then `iter_exp 1` ≤
`iter_exp k` for `k ≥ 1`.
-/
theorem lambertW_eventually_lt_iter_exp (k : Nat) (hk : 0 < k) :
    EventuallyLt lambertW (iter_exp k) := by
  have h_exp_eq_iter1 : Real.exp = iter_exp 1 := by
    funext x
    show Real.exp x = Real.exp (iter_exp 0 x)
    rfl
  by_cases hk_eq_one : k = 1
  · -- k = 1: directly use lambertW_eventually_lt_exp
    subst hk_eq_one
    rw [← h_exp_eq_iter1]
    exact lambertW_eventually_lt_exp
  · -- k > 1: chain via iter_exp_eventually_lt
    have hk_gt_one : 1 < k := by omega
    have h_W_lt_iter1 : EventuallyLt lambertW (iter_exp 1) := by
      rw [← h_exp_eq_iter1]
      exact lambertW_eventually_lt_exp
    have h_iter1_lt_iterk : EventuallyLt (iter_exp 1) (iter_exp k) :=
      iter_exp_eventually_lt hk_gt_one
    exact EventuallyLt.trans h_W_lt_iter1 h_iter1_lt_iterk

/-! ## Closing notes — what this enables, what's still open

This file establishes that **W is asymptotically dominated by every
iter_exp k for k ≥ 1**, using the substrate constructively.

**Does NOT close** the Lambert-W any-depth barrier (W ∉ EML_k for
any k). The EML asymptotic bound (`tame_eval_eventually_le` in
`EMLAsymptoticBound.lean`) gives an UPPER bound on EML_k's growth
(eventually ≤ iter_exp (k+1)). Both W and EML can be below this
bound — no contradiction.

A complete any-depth closure needs EITHER:

(a) A LOWER bound on EML_k's eventual growth incompatible with W's
    upper bound. Requires characterising EML's slowest growth
    classes — open math.

(b) A STRUCTURAL property of W's asymptotic expansion (e.g., the
    `log log x / log x` correction term) provably absent from EML's
    possible asymptotic shapes. Requires full asymptotic-expansion
    infrastructure — multi-week.

(c) A FUNCTIONAL-EQUATION-based argument: derive a contradiction
    from `W(x) · exp(W(x)) = x` combined with EML_k structural
    constraints. Path B in the scoping doc; combinatorially complex.

This file's contribution: the substrate IS now WORKING on Lambert-W.
Any of the three paths above can build on it.
-/

end Real
end MachLib
