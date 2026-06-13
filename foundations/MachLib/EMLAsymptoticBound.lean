import MachLib.Asymptotics
import MachLib.EMLHierarchyIterExp

/-!
# EML Asymptotic Bound — every TAME EMLTree is eventually dominated by iter_exp

This file ships the load-bearing theorem identified in
`OVERNIGHT_HANDOFF_2026_06_13.md`:

  **Every TAME EMLTree of depth k has eval eventually ≤ `iter_exp (k+1) x`.**

The TAME restriction handles the clamped-log discontinuity: when an
`eml t1 t2` subtree has `t2.eval x ∈ (0, 1)` for arbitrarily large x,
the term `-log_clamped(t2.eval x)` can grow without bound (specifically,
it equals `-log(t2.eval x)` which goes to `+∞` as t2.eval x → 0+).
TAME excludes this case by requiring every eml-subtree's t2-argument
to eventually stay above some positive constant.

This is the "Route (b)" of the handoff doc:

  > Two routes: bound |t.eval x| via triangle inequality, OR restrict to
  > subtrees where t2.eval is bounded below eventually.

Route (a) (triangle-inequality with absolute values) requires additional
machinery — bounding |log(t2.eval x)| by both |t2.eval x| (when t2 ≥ 1)
AND `1/|t2.eval x|` (when 0 < t2 < 1), which doesn't give a clean
iter_exp bound when t2 → 0+. Route (b) is the cleaner Lean-side
formalization for now.

## What this DOES

- Defines `EMLTree.Tame` inductively: every eml-subtree's t2 has
  eval eventually ≥ 1.
- Proves `tame_eval_eventually_le : every TAME EMLTree t has eval
  eventually ≤ iter_exp (t.depth + 1)`.
- Proves the special case `iter_exp_tree_is_tame` — the canonical
  EMLTree for iter_exp k IS tame (its t2 is always `const 1`,
  trivially ≥ 1).

## What this does NOT do

- Does not prove the bound for all EMLTrees (the clamped-log case
  is genuinely unbounded). The TAME restriction excludes those.
- Does not directly close Lambert-W any-depth or gamma any-depth.
  Both of those barriers still need either (a) a proof that the
  W-realizing / Γ-realizing trees are TAME (probably hard), OR
  (b) a different barrier argument entirely.

  However, the substrate built here is reusable: any future
  "EML can't express function f" argument can leverage `tame_eval_eventually_le`
  when it applies, and use a different argument when it doesn't.

## New axioms introduced (1, classical-true)

1. `log_le_id_at_one : Real.log x ≤ x` for `1 ≤ x`. Classical
   inequality `log x ≤ x - 1 ≤ x` for x ≥ 1. ~30-line discharge
   from MachLib's `exp_log` + the strict inequality from
   `exp_grows_strictly` would close this, but kept as an axiom
   here to keep the file focused on the structural theorem.

Net axiom delta: +1 from this file.
-/

namespace MachLib
namespace EMLTree

open Real

/-! ## TAME predicate — every eml-subtree's t2 is eventually ≥ 1 -/

/-- An EMLTree is **tame** if every `eml(t1, t2)` subtree has
`t2.eval x ≥ 1` for all `x ≥ N` for some `N` (possibly depending on
the subtree).

For TAME trees, the clamped-log discontinuity doesn't trigger:
`log_clamped(t2.eval x) = log(t2.eval x) ≥ 0` eventually, so the
`- log_clamped` term in `t.eval` is bounded above by 0 eventually. -/
inductive Tame : EMLTree → Prop
  | const (c : Real) : Tame (const c)
  | var : Tame var
  | eml (t1 t2 : EMLTree)
      (ht1 : Tame t1) (ht2 : Tame t2)
      (heventually : ∃ N : Real, ∀ x : Real, N ≤ x → 1 ≤ t2.eval x) :
      Tame (eml t1 t2)

/-! ## Supporting axioms for the structural theorem -/

/-- `log x ≤ x` for `x ≥ 1`. Classical inequality (log x ≤ x - 1
≤ x for x ≥ 1). Discharge path: from `exp_log` + `exp_grows_strictly`
in ~30 lines. -/
axiom log_le_id_at_one (x : Real) (hx : 1 ≤ x) : Real.log x ≤ x

/-! ## The structural theorem -/

/-- **The EML asymptotic bound (TAME case).**

For every TAME EMLTree `t`, `t.eval x` is eventually ≤ `iter_exp (t.depth + 1) x`.

Proof structure: induction on the TAME predicate (= induction on
EMLTree with the tame side conditions threaded through).

  - **Base case `const c`**: depth = 0. Bound: `c ≤ iter_exp 1 x = exp x`.
    For x large enough, `exp x ≥ c` (since exp is unbounded). Threshold:
    `N = max(c, 0)` works because for `x ≥ N`, `x ≥ c` and
    `exp x ≥ x ≥ c` (using `exp_grows_strictly`).
  - **Base case `var`**: depth = 0. Bound: `x ≤ iter_exp 1 x = exp x`.
    Always true by `exp_grows_strictly`.
  - **Inductive case `eml t1 t2`**: depth = 1 + max t1.depth t2.depth.
    Bound: `exp(t1.eval x) - log_clamped(t2.eval x) ≤ iter_exp(depth+1) x`.

    For `x ≥ N_t2`, `t2.eval x ≥ 1` (TAME), so `log_clamped(t2.eval x) = log(t2.eval x) ≥ 0`,
    so `- log_clamped(t2.eval x) ≤ 0`. Thus `t.eval x ≤ exp(t1.eval x)`.

    By IH on t1, `t1.eval x ≤ iter_exp(t1.depth + 1) x` eventually.
    Then `exp(t1.eval x) ≤ exp(iter_exp(t1.depth + 1) x) = iter_exp(t1.depth + 2) x`
    by `exp_monotone`. And `t1.depth + 2 ≤ depth + 1` since
    `depth = 1 + max(t1.depth, t2.depth) ≥ 1 + t1.depth`. So
    `iter_exp(t1.depth + 2) x ≤ iter_exp(depth + 1) x` by
    `iter_exp_strict_lt` (or equality when t1.depth = max).
-/
theorem tame_eval_eventually_le (t : EMLTree) (htame : Tame t) :
    EventuallyLE (fun x => t.eval x) (iter_exp (t.depth + 1)) := by
  induction htame with
  | const c =>
    -- Goal: ∃ N, ∀ x ≥ N, (const c).eval x ≤ iter_exp ((const c).depth + 1) x
    -- (const c).eval x = c; (const c).depth = 0; iter_exp 1 x = exp x.
    -- Want: c ≤ exp x for x ≥ N. Choose N = max(c, 0).
    -- For x ≥ N: x ≥ c (since N ≥ c) AND x ≥ 0 (since N ≥ 0).
    -- exp_grows_strictly: x < exp x. So exp x > x ≥ c.
    refine ⟨c, ?_⟩
    intro x hx
    show c ≤ Real.exp x
    -- c ≤ x < exp x
    exact le_trans hx (le_of_lt (exp_grows_strictly x))
  | var =>
    -- Goal: ∃ N, ∀ x ≥ N, var.eval x ≤ iter_exp (var.depth + 1) x
    -- var.eval x = x; var.depth = 0; iter_exp 1 x = exp x.
    -- Want: x ≤ exp x. Always true.
    refine ⟨0, ?_⟩
    intro x _
    show x ≤ Real.exp x
    exact le_of_lt (exp_grows_strictly x)
  | eml t1 t2 ht1 ht2 heventually ih1 _ =>
    -- Goal: ∃ N, ∀ x ≥ N, (eml t1 t2).eval x ≤ iter_exp ((eml t1 t2).depth + 1) x
    -- (eml t1 t2).eval x = exp(t1.eval x) - log(t2.eval x)
    -- (eml t1 t2).depth = 1 + max t1.depth t2.depth
    -- iter_exp (depth + 1) = exp ∘ iter_exp depth
    obtain ⟨N1, hN1⟩ := ih1
    obtain ⟨N2, hN2⟩ := heventually
    refine ⟨max N1 N2, ?_⟩
    intro x hx
    have hN1_le : N1 ≤ x := le_trans (le_max_left N1 N2) hx
    have hN2_le : N2 ≤ x := le_trans (le_max_right N1 N2) hx
    have h_t1_bound : t1.eval x ≤ iter_exp (t1.depth + 1) x := hN1 x hN1_le
    have h_t2_pos : 1 ≤ t2.eval x := hN2 x hN2_le
    -- (eml t1 t2).eval x = exp(t1.eval x) - log(t2.eval x)
    show Real.exp (t1.eval x) - Real.log (t2.eval x)
       ≤ iter_exp ((eml t1 t2).depth + 1) x
    -- Step 1: log(t2.eval x) ≥ 0 since t2.eval x ≥ 1.
    -- Use: log monotone via exp_log (and exp_monotone for strict checks).
    -- Specifically: log(1) = 0 (log_one), and log monotone for y ≥ 1 means
    -- log(t2.eval x) ≥ log(1) = 0.
    --
    -- Direct route: log(t2.eval x) ≥ 0 iff exp(log(t2.eval x)) ≥ exp(0) = 1.
    -- Since exp(log y) = y for y > 0, and t2.eval x ≥ 1 > 0, this gives
    -- t2.eval x ≥ 1 ⇔ exp(log(t2.eval x)) ≥ 1.
    -- The forward direction (≥ 1 ⟹ log ≥ 0) is what we need; use the
    -- existing exp_log + a small monotonicity check.
    have hy_pos : 0 < t2.eval x :=
      lt_of_lt_of_le zero_lt_one_ax h_t2_pos
    have h_exp_log : Real.exp (Real.log (t2.eval x)) = t2.eval x :=
      exp_log hy_pos
    have h_log_nn : 0 ≤ Real.log (t2.eval x) := by
      -- Use lt_total to case-split: 0 < log, 0 = log, or log < 0.
      rcases lt_total 0 (Real.log (t2.eval x)) with h | h | h
      · exact le_of_lt h
      · rw [← h]; exact le_refl _
      · -- log < 0 ⟹ exp(log) ≤ exp(0) = 1 ⟹ t2.eval x ≤ 1.
        -- Combined with t2.eval x ≥ 1 gives t2.eval x = 1, so log = log 1 = 0,
        -- contradicting log < 0.
        exfalso
        have h_step : Real.exp (Real.log (t2.eval x)) ≤ Real.exp 0 :=
          exp_monotone _ _ (le_of_lt h)
        rw [h_exp_log, exp_zero] at h_step
        -- h_step : t2.eval x ≤ 1
        have heq : t2.eval x = 1 := le_antisymm h_step h_t2_pos
        rw [heq, log_one] at h
        exact lt_irrefl_ax 0 h
    -- Step 2: exp(t1.eval x) - log(t2.eval x) ≤ exp(t1.eval x).
    -- Subtract a non-negative quantity → ≤.
    have h_drop_log : Real.exp (t1.eval x) - Real.log (t2.eval x)
                    ≤ Real.exp (t1.eval x) := by
      -- Use sub_le_self: a - b ≤ a iff b ≥ 0.
      -- MachLib may not have sub_le_self directly. Derive manually.
      rw [sub_def]
      -- Goal: exp(t1) + -log(t2) ≤ exp(t1)
      -- = exp(t1) + (-log(t2)) ≤ exp(t1) + 0
      -- iff -log(t2) ≤ 0.
      have h_neg_log_nonpos : -Real.log (t2.eval x) ≤ 0 := by
        -- -y ≤ 0 iff y ≥ 0. Use add_nonneg style argument.
        -- Direct: y ≥ 0 → -y ≤ 0 via add_neg_self.
        -- Add log to both sides: -log + log ≤ 0 + log, i.e., 0 ≤ log.
        -- Already have h_log_nn : 0 ≤ log.
        -- Use: rewrite 0 = -log + log (via neg_add_self),
        -- then ≤ becomes log ≤ log + log, hmm not clean.
        --
        -- Cleanest: use add_lt_add_left or direct calculation.
        -- If 0 ≤ log, then 0 + 0 ≤ log + 0, etc. Not directly.
        -- Use: -y + y = 0 (neg_add_self), so -y = -y + 0 ≤ -y + y = 0 iff 0 ≤ y.
        -- Pattern: -y ≤ 0 ↔ 0 ≤ y via "add y to both sides".
        --
        -- Concrete: rewrite goal as -log + 0 ≤ -log + log (after adding log).
        -- Wait that gives log + (-log) ≤ log + 0... ugh.
        --
        -- Skip: use le_neg_add or similar from MachLib.
        -- Simplest direct: rewrite goal using neg_eq_neg_one_mul or similar.
        --
        -- Let me just use a chain of basic ops.
        have h_zero_le : (0 : Real) ≤ -Real.log (t2.eval x) + Real.log (t2.eval x) := by
          rw [neg_add_self]; exact le_refl _
        -- Add (-log) to both sides via add_lt_add_left after splitting le.
        -- Actually use le_trans + the rewrite.
        -- We have 0 ≤ log. Want -log ≤ 0.
        -- This is equivalent to log ≥ 0 (i.e., what we have). Use:
        -- -log + log = 0, so -log = 0 - log = -log. Tautology.
        -- The lemma we need: 0 ≤ y → -y ≤ 0. Standard.
        --
        -- Construction: -y ≤ 0 ↔ -y + y ≤ 0 + y ↔ 0 ≤ y. The bi-implication
        -- uses add_lt_add_left (and its le version).
        rcases le_iff_lt_or_eq 0 (Real.log (t2.eval x)) |>.mp h_log_nn with hlt | heq
        · -- log > 0 → -log < 0 → -log ≤ 0.
          -- add_lt_add_left hlt (-log): -log + 0 < -log + log = 0.
          have := add_lt_add_left hlt (-Real.log (t2.eval x))
          rw [add_zero, neg_add_self] at this
          exact le_of_lt this
        · -- log = 0 → -log = 0 ≤ 0.
          rw [← heq, neg_zero]
          exact le_refl _
      -- Now goal: exp(t1) + -log(t2) ≤ exp(t1).
      -- Case split on h_neg_log_nonpos: -log < 0 (strict) or -log = 0.
      rcases le_iff_lt_or_eq (-Real.log (t2.eval x)) 0 |>.mp h_neg_log_nonpos with hlt | heq
      · -- -log < 0: add_lt_add_left gives exp + -log < exp + 0 = exp.
        have hstep := add_lt_add_left hlt (Real.exp (t1.eval x))
        rw [add_zero] at hstep
        exact le_of_lt hstep
      · -- -log = 0: rewrite to get exp + 0 = exp; then refl.
        rw [heq, add_zero]
        exact le_refl _
    -- Step 3: exp(t1.eval x) ≤ exp(iter_exp (t1.depth + 1) x)
    --                       = iter_exp (t1.depth + 2) x.
    have h_exp_bound : Real.exp (t1.eval x)
                     ≤ Real.exp (iter_exp (t1.depth + 1) x) :=
      exp_monotone _ _ h_t1_bound
    have h_exp_iter : Real.exp (iter_exp (t1.depth + 1) x)
                    = iter_exp (t1.depth + 1 + 1) x := by
      show Real.exp (iter_exp (t1.depth + 1) x)
         = iter_exp (t1.depth + 2) x
      -- iter_exp (k+1) x = exp (iter_exp k x), so iter_exp (k+2) x =
      -- exp (iter_exp (k+1) x). Direct from definition.
      rfl
    -- Step 4: iter_exp (t1.depth + 2) x ≤ iter_exp ((eml t1 t2).depth + 1) x.
    have h_depth : t1.depth + 2 ≤ (eml t1 t2).depth + 1 := by
      show t1.depth + 2 ≤ (1 + max t1.depth t2.depth) + 1
      have : t1.depth ≤ max t1.depth t2.depth := Nat.le_max_left _ _
      omega
    have h_iter_bound : iter_exp (t1.depth + 2) x
                      ≤ iter_exp ((eml t1 t2).depth + 1) x := by
      rcases Nat.lt_or_eq_of_le h_depth with hlt | heq
      · exact le_of_lt (iter_exp_strict_lt hlt x)
      · rw [heq]; exact le_refl _
    -- Combine: t.eval x ≤ exp(t1.eval x) ≤ exp(iter_exp (t1.depth+1) x)
    --                 = iter_exp (t1.depth + 2) x ≤ iter_exp (depth + 1) x.
    rw [h_exp_iter] at h_exp_bound
    exact le_trans (le_trans h_drop_log h_exp_bound) h_iter_bound

/-! ## Corollary: iter_exp_tree is TAME -/

/-- The canonical EMLTree for `iter_exp k` is tame. -/
theorem iter_exp_tree_is_tame (k : Nat) : Tame (iter_exp_tree k) := by
  induction k with
  | zero =>
    show Tame var
    exact Tame.var
  | succ n ih =>
    show Tame (eml (iter_exp_tree n) (const 1))
    refine Tame.eml _ _ ih (Tame.const 1) ?_
    -- (const 1).eval x = 1 for all x, so eventually ≥ 1.
    refine ⟨0, ?_⟩
    intro x _
    show (1 : Real) ≤ (1 : Real)
    exact le_refl _

end EMLTree
end MachLib
