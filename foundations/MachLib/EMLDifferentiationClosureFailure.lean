import MachLib.SinNotInEML
import MachLib.EMLHierarchy
import MachLib.EMLAdditionClosureFailure   -- piggybacks LambertW imports for two_lt_exp_one
import MachLib.LambertW                    -- two_lt_exp_one
import MachLib.Forge                       -- one_lt_one_plus_one, div_lt_one_of_pos_lt, etc.

/-!
# EML Differentiation-Closure Failure (depth ≤ 1)

This file ships the load-bearing Lean artifact for the
2026-06-15 EML differentiation-closure attempt
(`exploration/eml_differentiation_closure_attempt_2026_06_15/`).

## What we prove

`eml(var, var)` is an EML-tree of depth 1. Its evaluation is
`x ↦ Real.exp x - Real.log x` (on `x > 0`). Classically,

  d/dx [exp x - log x] = exp x - 1/x.

The question for Lambert-W candidate 1 was whether EML is closed
under differentiation with bounded depth cost. We prove here:

> The function `f(x) = exp(x) - 1/x` is NOT representable as
> `s.eval` for any EMLTree `s` with `s.depth ≤ 1`.

So differentiation does not preserve depth — at the cheapest
bound (output depth ≤ input depth), closure already fails. This
weakens the Lambert-W candidate 1 strategy substantially.

## What this DOES NOT prove

- The general-depth statement (`f ∉ EML` at any finite depth) is
  not in Lean yet. The FINDINGS doc reduces it to an addition-
  closure / constant-subtraction sub-lemma that converges with the
  open problem from `eml_addition_closure_depth2_scoping_2026_06_13`.
  Future research should attack that sub-lemma directly.
- Whether some weaker form of "differentiation closure" (allowing
  unbounded depth growth) holds is not addressed.

## Proof shape

Two sample points do all the work: `x = 1` and `x = exp 1`. The
`exp 1` sample is the trick — it lets us avoid `1/2` literal
arithmetic (which MachLib's Basic + Forge can't directly chain)
by trading it for `exp_neg_inv : exp(-x) = 1/exp x`, which gives
`1/(exp 1) = exp(-1)`. `exp_lt` + `exp_zero` then bound
`exp(-1) < 1` cleanly.

The load-bearing inequality chain (used by const c, eml(const,
const), and eml(const, var)) is:

  exp 1 < exp(exp 1)              -- from exp_lt + one_lt_exp_one
  exp 1 + (something < 0) < exp 1 -- from add_lt_add_left
  ⟹ exp(exp 1) < exp 1, contradicting exp 1 < exp(exp 1).

The `var`, `eml(var, var)`, and `eml(var, const b)` subcases use
a single `x = 1` sample (or one extra `exp 1` sample for the last)
and refute via `two_lt_exp_one`, `one_ne_zero`, or `exp(-1) < 1`
respectively. No sign case-split on `c2` is needed for the
`eml(var, const c)` case because two samples on the same `log c2`
value pin both `log c2 = 1` AND `log c2 = exp(-1)`, giving the
contradiction directly.
-/

namespace MachLib

open Real

/-! ## Target function

`deriv_xx x := exp x - 1/x` is the classical derivative of
`exp x - log x` on `x > 0`. We use this name throughout. -/

noncomputable def deriv_xx (x : Real) : Real := Real.exp x - 1 / x

/-! ## Arithmetic helpers used by multiple cases

These wrap the basic axioms into the exact inequality shapes the
case analysis needs. -/

/-- `1/1 = 1`. -/
private theorem one_div_one_eq_one : (1 : Real) / 1 = 1 := by
  have := Real.mul_inv 1 Real.one_ne_zero
  rw [Real.one_mul_thm] at this
  exact this

/-- `1/(exp 1) = exp(-1)`. -/
private theorem one_div_exp_one_eq_exp_neg_one :
    (1 : Real) / Real.exp 1 = Real.exp (-1) :=
  (Real.exp_neg_inv 1).symm

/-- `−1 < 0`. Stated with explicit `-(1 : Real)` so the pattern in
`neg_add_self` matches (the literal `(-1 : Real)` does not reduce
to `Neg.neg 1` for `rw` purposes). -/
private theorem neg_one_lt_zero : -(1 : Real) < 0 := by
  have step : -(1 : Real) + 0 < -(1 : Real) + 1 :=
    Real.add_lt_add_left Real.zero_lt_one_ax (-(1 : Real))
  rw [Real.neg_add_self] at step
  rw [Real.add_zero] at step
  exact step

/-- `exp(-1) < 1`. -/
private theorem exp_neg_one_lt_one : Real.exp (-1) < 1 := by
  have step : Real.exp (-(1 : Real)) < Real.exp 0 := Real.exp_lt neg_one_lt_zero
  rw [Real.exp_zero] at step
  exact step

/-- `exp 1 < exp(exp 1)`. -/
private theorem exp_one_lt_exp_exp_one : Real.exp 1 < Real.exp (Real.exp 1) :=
  Real.exp_lt one_lt_exp_one

/-! ## Non-constancy of `deriv_xx`

Sampling at `x = 1` and `x = exp 1`:

  deriv_xx 1     = exp 1 - 1/1   = exp 1 - 1
  deriv_xx (e)   = exp e - 1/e   = exp e - exp(-1)   (via exp_neg_inv)

If those were equal, `exp 1 - 1 = exp(exp 1) - exp(-1)`, which
rearranges to `exp(exp 1) = exp 1 + (-1 + exp(-1))`. But the RHS
is `< exp 1` (because `-1 + exp(-1) < -1 + 1 = 0`), while the LHS
is `> exp 1` (from `exp_lt + one_lt_exp_one`). Contradiction. -/
theorem deriv_xx_1_ne_exp_1 :
    deriv_xx 1 ≠ deriv_xx (Real.exp 1) := by
  intro h_eq
  simp only [deriv_xx] at h_eq
  rw [one_div_one_eq_one] at h_eq
  rw [one_div_exp_one_eq_exp_neg_one] at h_eq
  -- h_eq : exp 1 - 1 = exp(exp 1) - exp(-1)
  rw [Real.sub_def, Real.sub_def] at h_eq
  -- h_eq : exp 1 + -1 = exp(exp 1) + -exp(-1)
  have rearr : Real.exp (Real.exp 1) = Real.exp 1 + (-1 + Real.exp (-1)) := by
    have step : (Real.exp 1 + -1) + Real.exp (-1) =
                (Real.exp (Real.exp 1) + -Real.exp (-1)) + Real.exp (-1) := by
      rw [h_eq]
    rw [Real.add_assoc] at step
    rw [Real.add_assoc (Real.exp (Real.exp 1))] at step
    rw [Real.neg_add_self] at step
    rw [Real.add_zero] at step
    exact step.symm
  -- exp 1 + (-1 + exp(-1)) < exp 1 via add_lt_add_left.
  have h_inner : -1 + Real.exp (-1) < 0 := by
    have step : -1 + Real.exp (-1) < -1 + 1 :=
      Real.add_lt_add_left exp_neg_one_lt_one (-1)
    rw [Real.neg_add_self] at step
    exact step
  have h_lt : Real.exp 1 + (-1 + Real.exp (-1)) < Real.exp 1 := by
    have step : Real.exp 1 + (-1 + Real.exp (-1)) < Real.exp 1 + 0 :=
      Real.add_lt_add_left h_inner (Real.exp 1)
    rw [Real.add_zero] at step
    exact step
  have h_gt : Real.exp 1 < Real.exp (Real.exp 1) := exp_one_lt_exp_exp_one
  rw [rearr] at h_gt
  exact Real.lt_irrefl_ax _ (Real.lt_trans_ax h_gt h_lt)

/-! ## Depth-0 proof

`exp x - 1/x` at `x = 1` is `exp 1 - 1` and at `x = exp 1` is
`exp(exp 1) - exp(-1)`. Both samples refute each depth-0 shape. -/

/-- `exp x - 1/x` is not expressible by any depth-0 EMLTree. -/
theorem eml_xx_deriv_not_in_eml_0 (t : EMLTree) (ht : t.depth ≤ 0) :
    ¬ (∀ x : Real, t.eval x = deriv_xx x) := by
  intro heq
  cases t with
  | const c =>
    -- t.eval x = c. Both samples give c on the LHS, so deriv_xx 1
    -- = deriv_xx (exp 1). Use deriv_xx_1_ne_exp_1.
    have h1 := heq 1
    have h_e := heq (Real.exp 1)
    simp only [EMLTree.eval] at h1 h_e
    have heq1e : deriv_xx 1 = deriv_xx (Real.exp 1) := h1.symm.trans h_e
    exact deriv_xx_1_ne_exp_1 heq1e
  | var =>
    -- t.eval x = x. At x = 1: 1 = exp 1 - 1, so exp 1 = 1 + 1.
    -- Contradicts two_lt_exp_one.
    have h1 := heq 1
    simp only [EMLTree.eval, deriv_xx] at h1
    rw [one_div_one_eq_one] at h1
    -- h1 : 1 = exp 1 - 1
    have h_exp1 : Real.exp 1 = 1 + 1 := by
      have step : Real.exp 1 = (Real.exp 1 - 1) + 1 := by
        rw [Real.sub_def]
        rw [Real.add_assoc, Real.neg_add_self, Real.add_zero]
      rw [step, ← h1]
    have h_strict : ((1 + 1 : Real)) < Real.exp 1 := two_lt_exp_one
    rw [h_exp1] at h_strict
    exact Real.lt_irrefl_ax _ h_strict
  | eml _ _ =>
    simp [EMLTree.depth] at ht

/-! ## Depth-1 proof: case analysis on the 4 eml subcases

For depth-1 we have the new shapes `eml(t1, t2)` where each of
`t1, t2` is `const c` or `var`. So 4 combinations.

The `eml(const, var)` case is the most arithmetically demanding;
its sub-proof samples at `x = 1` AND `x = exp 1` and chains
through `log_one`, `log_exp`, `exp_neg_inv`, `exp_lt`,
`one_lt_exp_one` to get a clean monotonicity contradiction. The
others fall out faster. -/

theorem eml_xx_deriv_not_in_eml_1 (t : EMLTree) (ht : t.depth ≤ 1) :
    ¬ (∀ x : Real, t.eval x = deriv_xx x) := by
  intro heq
  cases t with
  | const c =>
    exact eml_xx_deriv_not_in_eml_0 (.const c)
      (by simp [EMLTree.depth]) heq
  | var =>
    exact eml_xx_deriv_not_in_eml_0 .var
      (by simp [EMLTree.depth]) heq
  | eml t1 t2 =>
    have htd : t1.depth = 0 ∧ t2.depth = 0 := by
      simp [EMLTree.depth] at ht
      have hmax : max t1.depth t2.depth ≤ 0 := by omega
      refine ⟨?_, ?_⟩
      · exact Nat.le_zero.mp (Nat.le_trans (Nat.le_max_left _ _) hmax)
      · exact Nat.le_zero.mp (Nat.le_trans (Nat.le_max_right _ _) hmax)
    cases t1 with
    | const c1 =>
      cases t2 with
      | const c2 =>
        -- eml(const c1, const c2): eval x = exp c1 - log c2, constant.
        -- Same as the const c case via deriv_xx_1_ne_exp_1.
        have h1 := heq 1
        have h_e := heq (Real.exp 1)
        simp only [EMLTree.eval] at h1 h_e
        have heq1e : deriv_xx 1 = deriv_xx (Real.exp 1) := h1.symm.trans h_e
        exact deriv_xx_1_ne_exp_1 heq1e
      | var =>
        -- eml(const c, var): eval x = exp c - log x.
        -- At x = 1:    exp c - 0   = exp 1 - 1        ⟹ exp c = exp 1 - 1
        -- At x = exp 1: exp c - 1  = exp(exp 1) - exp(-1)
        -- Substitute:   (exp 1 - 1) - 1 = exp(exp 1) - exp(-1)
        --   ⟹ exp(exp 1) = (exp 1 + -1) + -1 + exp(-1)
        -- Then exp(-1) < 1 ⟹ (exp 1 + -1 + -1) + exp(-1) < exp 1 + -1 + -1 + 1
        --                                                 = exp 1 + -1
        --                                                 < exp 1.
        -- Combined with exp 1 < exp(exp 1), contradiction.
        have h1 := heq 1
        have h_e := heq (Real.exp 1)
        simp only [EMLTree.eval, Real.log_one, Real.log_exp, Real.sub_zero,
                   deriv_xx] at h1 h_e
        rw [one_div_one_eq_one] at h1
        rw [one_div_exp_one_eq_exp_neg_one] at h_e
        -- h1  : exp c1 = exp 1 - 1
        -- h_e : exp c1 - 1 = exp(exp 1) - exp(-1)
        rw [h1] at h_e
        -- h_e : (exp 1 - 1) - 1 = exp(exp 1) - exp(-1)
        rw [Real.sub_def, Real.sub_def, Real.sub_def] at h_e
        -- h_e : ((exp 1 + -1) + -1) = exp(exp 1) + -exp(-1)
        have rearr : Real.exp (Real.exp 1) =
                     ((Real.exp 1 + -1) + -1) + Real.exp (-1) := by
          have step : ((Real.exp 1 + -1) + -1) + Real.exp (-1) =
                      (Real.exp (Real.exp 1) + -Real.exp (-1)) + Real.exp (-1) := by
            rw [h_e]
          rw [Real.add_assoc (Real.exp (Real.exp 1))] at step
          rw [Real.neg_add_self] at step
          rw [Real.add_zero] at step
          exact step.symm
        -- ((exp 1 + -1) + -1) + exp(-1) < ((exp 1 + -1) + -1) + 1
        have h_step1 : ((Real.exp 1 + -1) + -1) + Real.exp (-1) <
                       ((Real.exp 1 + -1) + -1) + 1 :=
          Real.add_lt_add_left exp_neg_one_lt_one ((Real.exp 1 + -1) + -1)
        -- ((exp 1 + -1) + -1) + 1 = exp 1 + -1
        have h_simp : ((Real.exp 1 + -1) + -1) + 1 = Real.exp 1 + -1 := by
          rw [Real.add_assoc (Real.exp 1 + -1)]
          rw [Real.neg_add_self]
          rw [Real.add_zero]
        rw [h_simp] at h_step1
        -- exp 1 + -1 < exp 1
        have h_step2 : Real.exp 1 + -1 < Real.exp 1 := by
          have step : Real.exp 1 + -1 < Real.exp 1 + 0 :=
            Real.add_lt_add_left neg_one_lt_zero (Real.exp 1)
          rw [Real.add_zero] at step
          exact step
        have h_lt : ((Real.exp 1 + -1) + -1) + Real.exp (-1) < Real.exp 1 :=
          Real.lt_trans_ax h_step1 h_step2
        have h_gt : Real.exp 1 < Real.exp (Real.exp 1) := exp_one_lt_exp_exp_one
        rw [rearr] at h_gt
        exact Real.lt_irrefl_ax _ (Real.lt_trans_ax h_gt h_lt)
      | eml a b =>
        have : (1 : Nat) ≤ 0 := by
          have hd : (EMLTree.eml a b).depth ≤ 0 := Nat.le_of_eq htd.2
          simp [EMLTree.depth] at hd
        omega
    | var =>
      cases t2 with
      | const c2 =>
        -- eml(var, const c): eval x = exp x - log c.
        -- At x = 1:     exp 1 - log c   = exp 1 - 1
        -- At x = exp 1: exp(exp 1) - log c = exp(exp 1) - exp(-1)
        -- The two equations both pin -log c: from first, -log c = -1,
        -- from second, -log c = -exp(-1). Hence -1 = -exp(-1), so
        -- 1 = exp(-1), contradicting exp(-1) < 1.
        --
        -- Note: no sign case-split on c is needed. The clamped log
        -- value (whatever it is) gets pinned to both 1 and exp(-1).
        have h1 := heq 1
        have h_e := heq (Real.exp 1)
        simp only [EMLTree.eval, deriv_xx] at h1 h_e
        rw [one_div_one_eq_one] at h1
        rw [one_div_exp_one_eq_exp_neg_one] at h_e
        -- h1  : exp 1 - log c2 = exp 1 - 1
        -- h_e : exp(exp 1) - log c2 = exp(exp 1) - exp(-1)
        rw [Real.sub_def, Real.sub_def] at h1
        rw [Real.sub_def, Real.sub_def] at h_e
        -- Cancel exp 1 on both sides of h1 ⟹ -log c2 = -1
        have h_neg_log_eq_neg_one : -Real.log c2 = (-1 : Real) := by
          have step : (-Real.exp 1) + (Real.exp 1 + -Real.log c2) =
                      (-Real.exp 1) + (Real.exp 1 + -1) := by rw [h1]
          rw [← Real.add_assoc, Real.neg_add_self, Real.zero_add] at step
          rw [← Real.add_assoc, Real.neg_add_self, Real.zero_add] at step
          exact step
        -- Substitute -log c2 = -1 into h_e (via the LHS):
        rw [h_neg_log_eq_neg_one] at h_e
        -- h_e : exp(exp 1) + -1 = exp(exp 1) + -exp(-1)
        --
        -- The straightforward approach (cancel exp(exp 1), then negate
        -- both sides to get 1 = exp(-1)) hits a `rw` cascade: `-1 →
        -- -exp(-1)` rewrites the `-1` inside the new `exp(-1)` too.
        -- Instead, derive `-1 < -exp(-1)` from `exp(-1) < 1` (a clean
        -- `add_lt_add_left` chain), apply that to add `exp(exp 1)`
        -- to both sides, and rewrite via h_e to get `α < α`.
        have h_neg_strict : -(1 : Real) < -Real.exp (-1) := by
          have step : (-(1 : Real) + -Real.exp (-1)) + Real.exp (-1) <
                      (-(1 : Real) + -Real.exp (-1)) + 1 :=
            Real.add_lt_add_left exp_neg_one_lt_one
              (-(1 : Real) + -Real.exp (-1))
          rw [Real.add_assoc] at step
          rw [Real.neg_add_self] at step
          rw [Real.add_zero] at step
          rw [Real.add_comm (-(1 : Real)) (-Real.exp (-1))] at step
          rw [Real.add_assoc] at step
          rw [Real.neg_add_self] at step
          rw [Real.add_zero] at step
          exact step
        have h_strict : Real.exp (Real.exp 1) + -1 <
                        Real.exp (Real.exp 1) + -Real.exp (-1) :=
          Real.add_lt_add_left h_neg_strict (Real.exp (Real.exp 1))
        rw [h_e] at h_strict
        exact Real.lt_irrefl_ax _ h_strict
      | var =>
        -- eml(var, var): eval x = exp x - log x.
        -- At x = 1: exp 1 - log 1 = exp 1 - 0 = exp 1.
        -- Target: deriv_xx 1 = exp 1 - 1.
        -- So exp 1 = exp 1 - 1 ⟹ 0 = -1 ⟹ 1 = 0, contradicts one_ne_zero.
        have h1 := heq 1
        simp only [EMLTree.eval, deriv_xx, Real.log_one] at h1
        rw [Real.sub_zero, one_div_one_eq_one] at h1
        -- h1 : exp 1 = exp 1 - 1
        rw [Real.sub_def] at h1
        -- h1 : exp 1 = exp 1 + -1
        have step : (-Real.exp 1) + (Real.exp 1 + -1) =
                    (-Real.exp 1) + Real.exp 1 := by
          rw [← h1]
        rw [← Real.add_assoc, Real.neg_add_self, Real.zero_add] at step
        -- step : -1 = 0  (rw rewrites all occurrences of `-?a + ?a` in
        -- one pass, so a single `Real.neg_add_self` collapses both
        -- copies of `(-exp 1) + exp 1` simultaneously.)
        have h_one_eq_zero : (1 : Real) = 0 := by
          have hn : -((-1 : Real)) = -(0 : Real) := by rw [step]
          rw [Real.neg_zero] at hn
          have hnn : -((-1 : Real)) = 1 := Real.neg_neg_helper 1
          rw [hnn] at hn
          exact hn
        exact Real.one_ne_zero h_one_eq_zero
      | eml a b =>
        have : (1 : Nat) ≤ 0 := by
          have hd : (EMLTree.eml a b).depth ≤ 0 := Nat.le_of_eq htd.2
          simp [EMLTree.depth] at hd
        omega
    | eml a b =>
      have : (1 : Nat) ≤ 0 := by
        have hd : (EMLTree.eml a b).depth ≤ 0 := Nat.le_of_eq htd.1
        simp [EMLTree.depth] at hd
      omega

end MachLib
