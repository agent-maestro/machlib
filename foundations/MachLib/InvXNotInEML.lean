import MachLib.SinNotInEML
import MachLib.EMLHierarchy
import MachLib.EMLAdditionClosureFailure          -- pulls LambertW etc.
import MachLib.LambertW                           -- two_lt_exp_one, one_lt_exp_one
import MachLib.Forge                              -- one_lt_one_plus_one
import MachLib.EMLDifferentiationClosureFailure   -- deriv_xx_1_ne_exp_1

/-!
# `inv_x ∉ EML` at depth ≤ 1 (load-bearing sub-lemma base case)

Both the addition-closure attempt
(`eml_addition_closure_depth2_scoping_2026_06_13/FINDINGS.md`) and
the differentiation-closure attempt
(`eml_differentiation_closure_attempt_2026_06_15/FINDINGS.md`)
converge on a single open structural sub-problem:

> **`1/x` is not in EML at any finite depth.**

This file ships the **mechanical base case** for that conjecture:
`1/x` is not representable as `s.eval` for any EMLTree `s` of
depth ≤ 1.

## Why this is the right partial result to ship

The diff-closure FINDINGS reduces the general
"differentiation closure fails" claim to "`1/x ∉ EML at any depth"
via an asymptotic dominance argument. And the addition-closure
FINDINGS arrives at the same convergent question via the
"EML cannot subtract a constant from a non-constant subtree-eval"
framing. So the depth-≤-1 mechanical proof here is the *founda-
tional* artifact for BOTH stories — the depth-1 base case of the
shared open conjecture.

## Proof technique

Same x = 1 and x = exp 1 sampling that worked for the diff-closure
proof. The two samples give

  inv_x 1     = 1/1   = 1
  inv_x (e)   = 1/e   = exp(-1)   (via exp_neg_inv)

For each of the 6 depth-≤-1 EMLTree shapes, the two-sample
constraints force either:

  - `1 = exp(-1)`               (constant-eval shapes; refuted by exp(-1) < 1)
  - `exp 1 = exp(-1)`           (var shape; refuted by exp_lt with -1 < 1)
  - `0 = exp(-1)`               (eml(const, var); refuted by exp_pos)
  - `exp 1 = 1`                 (eml(var, var); refuted by one_lt_exp_one)
  - `deriv_xx 1 = deriv_xx(e)` (eml(var, const); reuses
                                `deriv_xx_1_ne_exp_1` from the
                                diff-closure file).

Each subcase closes mechanically without sorry.

## What this DOES NOT prove

- The general-depth claim (`inv_x ∉ EML` at any finite depth). For
  depth ≥ 2 the case analysis explodes; a structural argument is
  needed. The diff-closure FINDINGS sketches an asymptotic-
  dominance route (`exp(s1) - log(s2) ~ exp(x)` at infinity vs.
  `1/x → 0`), but that needs Hardy-field / iterated-exp-log
  asymptotic machinery not yet in MachLib.

- Whether `inv_x ∈ EML at depth 2` directly. The full 36 depth-2
  cases mirror the addition-closure depth-2 scoping (~1500-3000
  Lean lines). Deferred. We do include a one-line proof for the
  all-constants depth-2 case as a demonstration the depth-1
  result composes cleanly.

## No new axioms

All proofs use existing MachLib primitives plus
`deriv_xx_1_ne_exp_1` from EMLDifferentiationClosureFailure.
-/

namespace MachLib

open Real

/-! ## Target function -/

noncomputable def inv_x (x : Real) : Real := 1 / x

/-! ## Arithmetic helpers (duplicated from EMLDifferentiationClosureFailure
because those were declared `private`; small enough to reproduce locally
rather than rip them out and re-share — keeps each file self-contained
for future agents reading just this file). -/

private theorem one_div_one_eq_one : (1 : Real) / 1 = 1 := by
  have := Real.mul_inv 1 Real.one_ne_zero
  rw [Real.one_mul_thm] at this
  exact this

private theorem one_div_exp_one_eq_exp_neg_one :
    (1 : Real) / Real.exp 1 = Real.exp (-1) :=
  (Real.exp_neg_inv 1).symm

private theorem neg_one_lt_zero : -(1 : Real) < 0 := by
  have step : -(1 : Real) + 0 < -(1 : Real) + 1 :=
    Real.add_lt_add_left Real.zero_lt_one_ax (-(1 : Real))
  rw [Real.neg_add_self] at step
  rw [Real.add_zero] at step
  exact step

private theorem neg_one_lt_one : -(1 : Real) < 1 :=
  Real.lt_trans_ax neg_one_lt_zero Real.zero_lt_one_ax

private theorem exp_neg_one_lt_one : Real.exp (-1) < 1 := by
  have step : Real.exp (-(1 : Real)) < Real.exp 0 := Real.exp_lt neg_one_lt_zero
  rw [Real.exp_zero] at step
  exact step

/-! ## Non-constancy: `inv_x 1 ≠ inv_x (exp 1)`

inv_x 1     = 1/1   = 1.
inv_x (e)   = 1/e   = exp(-1).

If those were equal: 1 = exp(-1), but `exp(-1) < 1` so `1 ≠ exp(-1)`. -/

theorem inv_x_1_ne_exp_1 : inv_x 1 ≠ inv_x (Real.exp 1) := by
  intro h_eq
  simp only [inv_x] at h_eq
  rw [one_div_one_eq_one] at h_eq
  rw [one_div_exp_one_eq_exp_neg_one] at h_eq
  -- h_eq : 1 = exp(-1)
  exact Real.ne_of_gt exp_neg_one_lt_one h_eq

/-! ## Depth-0 -/

theorem inv_x_not_in_eml_0 (t : EMLTree) (ht : t.depth ≤ 0) :
    ¬ (∀ x : Real, t.eval x = inv_x x) := by
  intro heq
  cases t with
  | const c =>
    -- eval x = c. So c = inv_x 1 AND c = inv_x (exp 1).
    -- Hence inv_x 1 = inv_x (exp 1). Use inv_x_1_ne_exp_1.
    have h1 := heq 1
    have h_e := heq (Real.exp 1)
    simp only [EMLTree.eval] at h1 h_e
    exact inv_x_1_ne_exp_1 (h1.symm.trans h_e)
  | var =>
    -- eval x = x. At x = exp 1: exp 1 = 1/(exp 1) = exp(-1).
    -- So exp 1 = exp(-1). But -1 < 1 ⟹ exp(-1) < exp 1 (strict).
    have h_e := heq (Real.exp 1)
    simp only [EMLTree.eval, inv_x] at h_e
    rw [one_div_exp_one_eq_exp_neg_one] at h_e
    -- h_e : exp 1 = exp(-1)
    have h_lt : Real.exp (-1) < Real.exp 1 := Real.exp_lt neg_one_lt_one
    rw [← h_e] at h_lt
    -- h_lt : exp 1 < exp 1
    exact Real.lt_irrefl_ax _ h_lt
  | eml _ _ =>
    simp [EMLTree.depth] at ht

/-! ## Depth-1: 4 new subcases via `eml(t1, t2)` with `t1, t2` depth-0 -/

theorem inv_x_not_in_eml_1 (t : EMLTree) (ht : t.depth ≤ 1) :
    ¬ (∀ x : Real, t.eval x = inv_x x) := by
  intro heq
  cases t with
  | const c =>
    exact inv_x_not_in_eml_0 (.const c) (by simp [EMLTree.depth]) heq
  | var =>
    exact inv_x_not_in_eml_0 .var (by simp [EMLTree.depth]) heq
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
        -- eml(const, const): constant eval. Reduce to inv_x_1_ne_exp_1.
        have h1 := heq 1
        have h_e := heq (Real.exp 1)
        simp only [EMLTree.eval] at h1 h_e
        exact inv_x_1_ne_exp_1 (h1.symm.trans h_e)
      | var =>
        -- eml(const c1, var): eval x = exp c1 - log x.
        -- At x = 1: exp c1 - 0 = exp c1 = 1, so exp c1 = 1.
        -- At x = exp 1: exp c1 - 1 = 1 - 1 = 0. Target: exp(-1).
        -- So 0 = exp(-1). But 0 < exp(-1) by exp_pos. Contradiction.
        have h1 := heq 1
        have h_e := heq (Real.exp 1)
        simp only [EMLTree.eval, Real.log_one, Real.log_exp, Real.sub_zero,
                   inv_x] at h1 h_e
        rw [one_div_one_eq_one] at h1
        rw [one_div_exp_one_eq_exp_neg_one] at h_e
        -- h1 : exp c1 = 1
        -- h_e : exp c1 - 1 = exp(-1)
        rw [h1] at h_e
        -- h_e : 1 - 1 = exp(-1)
        rw [Real.sub_def, Real.add_neg] at h_e
        -- h_e : 0 = exp(-1)
        have h_pos : (0 : Real) < Real.exp (-1) := Real.exp_pos _
        rw [← h_e] at h_pos
        exact Real.lt_irrefl_ax _ h_pos
      | eml a b =>
        have : (1 : Nat) ≤ 0 := by
          have hd : (EMLTree.eml a b).depth ≤ 0 := Nat.le_of_eq htd.2
          simp [EMLTree.depth] at hd
        omega
    | var =>
      cases t2 with
      | const c2 =>
        -- eml(var, const c): eval x = exp x - log c2.
        -- At x = 1:    exp 1 - log c2     = 1
        -- At x = exp 1: exp(exp 1) - log c2 = exp(-1)
        -- Cancelling log c2 between them gives
        --   exp 1 - 1 = exp(exp 1) - exp(-1),
        -- which is exactly `deriv_xx 1 = deriv_xx (exp 1)` after
        -- unfolding deriv_xx. We then invoke `deriv_xx_1_ne_exp_1`
        -- from EMLDifferentiationClosureFailure for the contradiction.
        have h1 := heq 1
        have h_e := heq (Real.exp 1)
        simp only [EMLTree.eval, inv_x] at h1 h_e
        rw [one_div_one_eq_one] at h1
        rw [one_div_exp_one_eq_exp_neg_one] at h_e
        rw [Real.sub_def] at h1
        rw [Real.sub_def] at h_e
        -- h1  : exp 1 + -log c2 = 1
        -- h_e : exp(exp 1) + -log c2 = exp(-1)
        -- Derive log c2 = exp 1 + -1 (i.e., log c2 = exp 1 - 1):
        have h_log_c2_eq_1 : Real.log c2 = Real.exp 1 + -1 := by
          have step1 : Real.exp 1 = 1 + Real.log c2 := by
            have h : (Real.exp 1 + -Real.log c2) + Real.log c2 =
                     1 + Real.log c2 := by rw [h1]
            rw [Real.add_assoc, Real.neg_add_self, Real.add_zero] at h
            exact h
          have step2 : -(1 : Real) + (1 + Real.log c2) = -1 + Real.exp 1 := by
            rw [step1]
          rw [← Real.add_assoc, Real.neg_add_self, Real.zero_add] at step2
          rw [Real.add_comm (-(1 : Real)) (Real.exp 1)] at step2
          exact step2
        -- Derive log c2 = exp(exp 1) + -exp(-1):
        have h_log_c2_eq_e : Real.log c2 = Real.exp (Real.exp 1) +
                                           -Real.exp (-1) := by
          have step1 : Real.exp (Real.exp 1) = Real.exp (-1) + Real.log c2 := by
            have h : (Real.exp (Real.exp 1) + -Real.log c2) + Real.log c2 =
                     Real.exp (-1) + Real.log c2 := by rw [h_e]
            rw [Real.add_assoc, Real.neg_add_self, Real.add_zero] at h
            exact h
          have step2 : -Real.exp (-1) + (Real.exp (-1) + Real.log c2) =
                       -Real.exp (-1) + Real.exp (Real.exp 1) := by rw [step1]
          rw [← Real.add_assoc, Real.neg_add_self, Real.zero_add] at step2
          rw [Real.add_comm (-Real.exp (-1)) (Real.exp (Real.exp 1))] at step2
          exact step2
        -- Combine: exp 1 + -1 = exp(exp 1) + -exp(-1).
        have h_derived : Real.exp 1 + -1 =
                         Real.exp (Real.exp 1) + -Real.exp (-1) :=
          h_log_c2_eq_1.symm.trans h_log_c2_eq_e
        -- Lift to deriv_xx form: deriv_xx 1 = deriv_xx (exp 1).
        have h_deriv_eq : deriv_xx 1 = deriv_xx (Real.exp 1) := by
          show Real.exp 1 - 1/1 = Real.exp (Real.exp 1) - 1/Real.exp 1
          rw [one_div_one_eq_one, one_div_exp_one_eq_exp_neg_one]
          rw [Real.sub_def, Real.sub_def]
          exact h_derived
        exact deriv_xx_1_ne_exp_1 h_deriv_eq
      | var =>
        -- eml(var, var): eval x = exp x - log x.
        -- At x = 1: exp 1 - 0 = exp 1 = 1/1 = 1.
        -- But one_lt_exp_one says 1 < exp 1. Contradiction.
        have h1 := heq 1
        simp only [EMLTree.eval, Real.log_one, Real.sub_zero, inv_x] at h1
        rw [one_div_one_eq_one] at h1
        -- h1 : exp 1 = 1
        have h_strict : (1 : Real) < Real.exp 1 := one_lt_exp_one
        rw [h1] at h_strict
        exact Real.lt_irrefl_ax _ h_strict
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

/-! ## Depth-2 partial: the all-constants case

`t = eml(eml(const a, const b), eml(const a', const b'))` evaluates
to a constant in x. The same `inv_x_1_ne_exp_1` non-constancy
witness closes the case immediately.

This is the analog of `x_plus_one_not_in_eml_2_all_constants` in
`EMLAdditionClosureFailure.lean`. The full depth-2 case analysis (36
subcases) is multi-session work, paralleling the addition-closure
depth-2 scoping. -/

theorem inv_x_not_in_eml_2_all_constants
    (a b a' b' : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (EMLTree.eml (.const a) (.const b))
                     (EMLTree.eml (.const a') (.const b'))).eval x = inv_x x) := by
  intro hsum
  -- eval is constant in x (no `var` appears). So eval 1 = eval (exp 1)
  -- = inv_x 1 = inv_x (exp 1). Contradicts inv_x_1_ne_exp_1.
  have h1 := hsum 1
  have h_e := hsum (Real.exp 1)
  simp only [EMLTree.eval] at h1 h_e
  exact inv_x_1_ne_exp_1 (h1.symm.trans h_e)

/-! ## The K-coefficient structural lemma

This is the load-bearing structural mechanism for ruling out `inv_x`
in K/x-asymptotic shapes at every depth.

**Claim.** Any depth-2 EMLTree shape that produces `eval x = K/x +
log_term` for constant K, when evaluated at appropriate x, forces
`K = 1`. But in every such shape, K has the form `exp(exp(...))`
where the inner `exp(...)` is strictly positive (by `exp_pos`), so
`K = exp(strictly-positive) > exp(0) = 1` (by `exp_lt`). Hence
`K ≠ 1` and the shape cannot represent `inv_x`.

The helper `exp_exp_ne_one` packages this: `exp(exp a) ≠ 1` for any
`a : Real`. Used by depth-2 K/x cases below. -/

/-- For any real `a`, `exp(exp a) > 1`. Strict, because `exp a > 0`
(by `exp_pos`) and `exp` is strictly monotone with `exp 0 = 1`. -/
private theorem one_lt_exp_exp (a : Real) : 1 < Real.exp (Real.exp a) := by
  have h_exp_a_pos : (0 : Real) < Real.exp a := Real.exp_pos a
  have h_strict : Real.exp 0 < Real.exp (Real.exp a) := Real.exp_lt h_exp_a_pos
  rw [Real.exp_zero] at h_strict
  exact h_strict

/-- `exp(exp a) ≠ 1` for any `a : Real`. The closure key for K/x-shaped
depth-2 EMLTrees. -/
private theorem exp_exp_ne_one (a : Real) : Real.exp (Real.exp a) ≠ 1 :=
  Real.ne_of_gt (one_lt_exp_exp a)

/-! ## Depth-2 case: `eml(eml(const a, var), const 1)` — exact K/x

This shape evaluates to `exp(exp(a) - log(x)) - log(1) = exp(exp(a) -
log(x)) - 0 = exp(exp(a))/x` for all `x > 0` (using
`exp_neg_inv`-style identity `exp(c - log x) = exp(c)/x`).

For this to equal `1/x` everywhere, we'd need `exp(exp(a)) = 1`,
which `exp_exp_ne_one` rules out.

Sample at x = 1: log 1 = 0, so eval 1 = exp(exp(a)). Target inv_x 1 = 1.
So exp(exp(a)) = 1, refuted by `exp_exp_ne_one`. -/
theorem inv_x_not_in_eml_2_eml_const_var_const_one (a : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (EMLTree.eml (.const a) .var) (.const 1)).eval x = inv_x x) := by
  intro hsum
  have h1 := hsum 1
  simp only [EMLTree.eval, Real.log_one, Real.sub_zero, inv_x] at h1
  rw [one_div_one_eq_one] at h1
  -- h1 : exp(exp a) = 1
  exact exp_exp_ne_one a h1

/-! ## Depth-2 case: `eml(eml(const a, var), eml(const a', var))` — K/x via inner clamp

Evaluates to `exp(exp(a) - log x) - log_clamped(exp(a') - log x)`.
For x ≥ exp(exp a'), the inner `exp(a') - log x ≤ 0` so the clamped
log gives 0. Then eval = `exp(exp(a))/x` for x large.

Sample at x = exp(exp a'): get exp(a') - exp(a') = 0 inside the clamped
log, which is `log 0 = 0`. Then eval = `exp(exp(a) - exp(a'))`. Target
inv_x (exp(exp a')) = 1/(exp(exp a')) = exp(-exp(a')) via exp_neg_inv.
So `exp(exp(a) - exp(a')) = exp(-exp(a'))`. By exp injectivity (via
`exp_injective` or strict-monotonicity), `exp(a) - exp(a') = -exp(a')`,
hence `exp(a) = 0`. Contradicts `exp_pos`. -/
theorem inv_x_not_in_eml_2_eml_const_var_eml_const_var (a a' : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (EMLTree.eml (.const a) .var)
                     (EMLTree.eml (.const a') .var)).eval x = inv_x x) := by
  intro hsum
  -- Sample at x = exp(exp a').
  have h := hsum (Real.exp (Real.exp a'))
  simp only [EMLTree.eval, Real.log_exp, inv_x] at h
  -- h : exp (exp a - exp a') - log (exp a' - exp a') = 1 / exp (exp a')
  rw [Real.sub_self, Real.log_zero, Real.sub_zero] at h
  -- h : exp (exp a - exp a') = 1 / exp (exp a')
  -- Rewrite RHS using exp_neg_inv: 1/exp y = exp(-y).
  rw [← Real.exp_neg_inv (Real.exp a')] at h
  -- h : exp (exp a - exp a') = exp (-exp a')
  -- Now exp injectivity: exp a - exp a' = -exp a', so exp a = 0.
  -- We derive this directly via the exp_lt + lt_total tactic instead
  -- of relying on a packaged exp_injective.
  have h_arg_eq : Real.exp a - Real.exp a' = -Real.exp a' := by
    -- Use exp's strict monotonicity: if exp(u) = exp(v) then u = v.
    rcases Real.lt_total (Real.exp a - Real.exp a') (-Real.exp a') with hlt | heq | hgt
    · -- u < v ⟹ exp u < exp v, contradicts h.
      have hexp_lt : Real.exp (Real.exp a - Real.exp a') < Real.exp (-Real.exp a') :=
        Real.exp_lt hlt
      rw [h] at hexp_lt
      exact absurd hexp_lt (Real.lt_irrefl_ax _)
    · exact heq
    · -- v < u ⟹ exp v < exp u, contradicts h (the other direction).
      have hexp_lt : Real.exp (-Real.exp a') < Real.exp (Real.exp a - Real.exp a') :=
        Real.exp_lt hgt
      rw [h] at hexp_lt
      exact absurd hexp_lt (Real.lt_irrefl_ax _)
  -- exp a - exp a' = -exp a' ⟹ exp a = 0. Contradicts exp_pos.
  have h_exp_a_eq_zero : Real.exp a = 0 := by
    -- h_arg_eq : exp a + -exp a' = -exp a'  (after sub_def).
    -- Add exp a' to both: exp a + (-exp a' + exp a') = -exp a' + exp a'.
    -- ⟹ exp a + 0 = 0.
    -- ⟹ exp a = 0.
    rw [Real.sub_def] at h_arg_eq
    have step : (Real.exp a + -Real.exp a') + Real.exp a' =
                -Real.exp a' + Real.exp a' := by rw [h_arg_eq]
    rw [Real.add_assoc, Real.neg_add_self, Real.add_zero] at step
    -- step : exp a = 0  (the all-occurrences rewrite of `neg_add_self`
    -- collapsed both `-exp a' + exp a'` instances simultaneously,
    -- leaving the bare `exp a` on the LHS).
    exact step
  have h_exp_a_pos : (0 : Real) < Real.exp a := Real.exp_pos a
  rw [h_exp_a_eq_zero] at h_exp_a_pos
  exact Real.lt_irrefl_ax _ h_exp_a_pos

/-! ## Depth-2 case: `eml(const c, eml(const a, var))` — eventually constant

Evaluates to `exp(c) - log_clamped(exp(a) - log(x))`. For x ≥ exp(exp(a)),
the inner `exp(a) - log(x) ≤ 0` so the clamped log gives 0. Hence
eval = `exp(c)` (constant) for `x ≥ exp(exp(a))`.

But `inv_x x = 1/x` is non-constant (1/x ≠ 1/(x+1) for x > 0). So
sampling at two large points x_1, x_2 ≥ exp(exp(a)) forces
`exp(c) = 1/x_1 = 1/x_2`, hence `x_1 = x_2`, contradiction for any
distinct samples.

Concretely: sample at `x_1 = max(exp(exp a), 1)` and `x_2 = x_1 + 1`.
Both ≥ exp(exp(a)) by construction. Both samples force eval = exp(c),
so `1/x_1 = 1/x_2 = exp(c)`, hence `1/x_1 = 1/x_2`, contradicting
`x_1 ≠ x_2`.

The cleanest packaging: an `eventually_constant_not_inv_x` lemma. -/

/-- Helper: `1 / 1 ≠ 1 / (1 + 1)`, i.e., `1 ≠ 1/(1+1)`. The closure key
for "eventually constant" depth-2 cases. Proven via the chain:
multiplying `1 = 1/(1+1)` by `(1+1)` gives `1+1 = 1`, contradicting
`one_lt_one_plus_one`. -/
private theorem one_ne_one_div_two : (1 : Real) ≠ 1 / (1 + 1) := by
  intro h
  have h_pos : (0 : Real) < 1 + 1 :=
    Real.add_pos Real.zero_lt_one_ax Real.zero_lt_one_ax
  have h_ne : (1 + 1 : Real) ≠ 0 := Real.ne_of_gt h_pos
  have h_mul_inv : (1 + 1 : Real) * (1 / (1 + 1)) = 1 :=
    Real.mul_inv (1 + 1) h_ne
  rw [← h] at h_mul_inv
  rw [Real.mul_one_ax] at h_mul_inv
  -- h_mul_inv : 1 + 1 = 1
  have h_lt : (1 : Real) < 1 + 1 := one_lt_one_plus_one
  rw [h_mul_inv] at h_lt
  exact Real.lt_irrefl_ax _ h_lt

/-- **The eventually-constant disproof helper for `inv_x`.** If `f`
is eventually constant on `[N, ∞)` and `N ≤ 1`, then `f ≠ inv_x`.

Sample at `x = 1` (forces `c = 1/1 = 1`) and at `x = 1 + 1` (forces
`c = 1/(1+1)`). So `1 = c = 1/(1+1)`, contradicting `one_ne_one_div_two`.

This is the inv_x analog of `eventually_constant_not_x_plus_one` from
`EMLAdditionClosureFailure.lean`. The depth-2 clamp-trigger cases all
plug into this. -/
theorem eventually_constant_not_inv_x (f : Real → Real)
    (c N : Real) (hN : ∀ x : Real, N ≤ x → f x = c) (hN_le_one : N ≤ 1) :
    ¬ (∀ x : Real, f x = inv_x x) := by
  intro hsum
  have h_one_le_two : (1 : Real) ≤ 1 + 1 := Real.le_of_lt one_lt_one_plus_one
  have hN_le_two : N ≤ 1 + 1 := Real.le_trans hN_le_one h_one_le_two
  have h1 : c = inv_x 1 := (hN 1 hN_le_one).symm.trans (hsum 1)
  have h2 : c = inv_x (1 + 1) := (hN (1 + 1) hN_le_two).symm.trans (hsum (1 + 1))
  have heq : inv_x 1 = inv_x (1 + 1) := h1.symm.trans h2
  simp only [inv_x] at heq
  rw [one_div_one_eq_one] at heq
  -- heq : 1 = 1/(1+1)
  exact one_ne_one_div_two heq

/- HONEST SCOPING NOTE — not a declaration.

The `eventually_constant_not_inv_x` helper above requires N ≤ 1 so
that 1 and 1+1 are both in the constant region.

For shapes like `eml(const c, eml(const a, var))`, the eval becomes
constant exp(c) only for x ≥ exp(exp a), and exp(exp a) > 1 always
(by one_lt_exp_exp). So this helper does NOT directly close that
shape. A larger-sample variant
  eventually_constant_not_inv_x_at_N (N : Real) (hN_pos : 0 < N)
sampling at x = N+1 and x = N+1+1 instead of 1 and 1+1 would be
needed. We ship just the N ≤ 1 helper as the foundational case;
the threshold-dependent application is left for follow-up
sessions, mirroring the same gap in
`eventually_constant_not_x_plus_one` from
EMLAdditionClosureFailure (which has the same N ≤ 1 limitation).
-/

end MachLib
