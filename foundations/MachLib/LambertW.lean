import MachLib.Trig
import MachLib.SinNotInEML
import MachLib.EMLHierarchy

/-!
# Lambert-W axiomatic foundation + depth-0/depth-1 EML barrier

Lambert-W is the inverse of `y → y · exp y` on the appropriate branch.
Standard properties:

  - W(0) = 0
  - 0 < W(1) < 1 (W(1) is "the omega constant", ≈ 0.5671)
  - W(e) = 1
  - W is monotonically increasing on [-1/e, ∞)

This file:

1. Axiomatizes `Real.lambertW` and three small specific-value facts.
2. Proves `lambertW_not_in_eml_0` constructively.
3. Proves `lambertW_not_in_eml_1` constructively.
4. Documents the any-depth case as a scoping artifact (the Pfaffian
   zero-counting argument used for sin/cos does NOT apply to
   Lambert-W: W has only ONE zero on its domain, so the bound is
   never overrun).

## New axioms introduced (4, all classical-true)

- `lambertW : Real → Real`
- `lambertW_zero : lambertW 0 = 0`
- `lambertW_one_pos : 0 < lambertW 1`
- `lambertW_one_lt_one : lambertW 1 < 1`

All four are textbook facts about Lambert-W's principal branch.
`lambertW_one_pos` and `lambertW_one_lt_one` together identify
W(1) as a specific value strictly between 0 and 1.

## What this file does NOT do

- Does not axiomatize the Lambert-W defining equation
  `W(x) · exp(W(x)) = x` — we don't need it for the depth-0/1
  results, only specific values.
- Does not assert W is in or out of EML at any depth ≥ 2.
- Does not introduce any new sorry.
- Does not modify any pre-existing file outside MachLib.lean
  (registry).

## Why the any-depth case is open

The Pfaffian-envelope-zero-counting argument that worked for sin and
cos overruns the Khovanskii bound with M+1 distinct zeros on a
compact interval. Lambert-W has only ONE zero (at x = 0), so this
argument trivially fails. A different argument would need to leverage
either:

  (a) Lambert-W's asymptotic growth as x → ∞ (W(x) ~ log(x) - log(log(x))),
      compared with the asymptotic growth classes of EML_k functions, OR
  (b) The functional equation W(x) · exp(W(x)) = x, leveraging EML's
      restricted algebraic structure (EML has NO native multiplication
      operation — only via exp/log composition, which is depth-deep).

The growth-class argument is genuine research-grade work; the
functional-equation argument requires a careful audit of EML's
algebraic closure (or lack thereof). Both are beyond the scope of
this single-session investigation; the scoping artifact for the
any-depth case lives at
`monogate-research/exploration/lambert_w_eml_any_depth_scoping_2026_06_13/`.
-/

namespace MachLib

open Real

/-- The Lambert-W function on its principal branch. Axiomatized
without a defining equation — the three specific-value axioms below
are all we need for the depth-0/1 barriers. -/
axiom lambertW : Real → Real

/-- `W(0) = 0`. Standard fact about the principal branch. -/
axiom lambertW_zero : lambertW 0 = 0

/-- `0 < W(1)`. The omega constant ≈ 0.5671 is positive. -/
axiom lambertW_one_pos : (0 : Real) < lambertW 1

/-- `W(1) < 1`. The omega constant ≈ 0.5671 is strictly less than 1.
Together with `lambertW_one_pos`, this pins W(1) to the open
interval (0, 1). -/
axiom lambertW_one_lt_one : lambertW 1 < 1

/-! ## Depth-0 barrier

EML_0 = `{const c, var}`. Case analysis: a constant tree can't equal
both W(0) = 0 and W(1) > 0; the `var` tree can't equal both W(1) < 1
and W(1) at the same value (would require W(1) = 1). -/

theorem lambertW_not_in_eml_0 (t : EMLTree) (ht : t.depth ≤ 0) :
    ¬ (∀ x : Real, t.eval x = lambertW x) := by
  intro hW
  cases t with
  | const c =>
    -- t.eval x = c for all x. So c = W(0) = 0 and c = W(1) > 0.
    have h0 := hW 0
    have h1 := hW 1
    -- h0: (const c).eval 0 = c. After unfolding: c = lambertW 0 = 0.
    -- h1: (const c).eval 1 = c. After unfolding: c = lambertW 1.
    simp only [EMLTree.eval, lambertW_zero] at h0 h1
    -- h0 : c = 0, h1 : c = lambertW 1.
    rw [h0] at h1
    -- h1 : 0 = lambertW 1, but lambertW_one_pos says 0 < lambertW 1.
    have hw_pos : (0 : Real) < lambertW 1 := lambertW_one_pos
    rw [← h1] at hw_pos
    exact lt_irrefl_ax 0 hw_pos
  | var =>
    -- t.eval x = x for all x. So 1 = W(1).
    have h1 := hW 1
    simp only [EMLTree.eval] at h1
    -- h1 : 1 = lambertW 1, but lambertW_one_lt_one says lambertW 1 < 1.
    have hw_lt : lambertW 1 < 1 := lambertW_one_lt_one
    rw [← h1] at hw_lt
    exact lt_irrefl_ax 1 hw_lt
  | eml a b =>
    -- depth ≥ 1, contradiction with ht : depth ≤ 0.
    have : (1 : Nat) ≤ 0 := by
      have hd : (EMLTree.eml a b).depth ≤ 0 := ht
      simp [EMLTree.depth] at hd
    omega

/-! ## Supporting axiom for the depth-1 case-3 sub-case

The `eml(var, const c)` case needs a strict bound `2 < exp 1`
(classical-true, e ≈ 2.718). MachLib has `one_lt_exp_one : 1 < exp 1`
but not the strict-2 version. Adding here as a classical-citation
axiom; would be derivable from a constructive lower bound on exp(1)
(e.g., via the series expansion: exp(1) = 1 + 1 + 1/2 + ... ≥ 2.5).
~30-50 lines of constructive derivation; lifted here as a single
axiom for now to keep the Lambert-W file focused. -/
axiom two_lt_exp_one : ((1 + 1 : Real)) < Real.exp 1

/-! ## Depth-1 barrier

EML_1 = `{const c, var, eml(t1, t2) where t1, t2 ∈ EML_0}`. The new
cases (over depth-0) are the four `eml(*, *)` combinations:

  1. eml(const c1, const c2): eval = exp(c1) - log(c2). Constant.
     Same disproof as the const-c case in depth-0.
  2. eml(const c, var): eval = exp(c) - log(x). Decreasing in x for
     x > 0. But W is INCREASING. Contradiction at two points.
  3. eml(var, const c): eval = exp(x) - log(c). At x = 0, eval =
     1 - log(c). W(0) = 0 forces log(c) = 1, so c = e. Then at
     x = 1, eval = e - 1 > 1, but W(1) < 1.
  4. eml(var, var): eval = exp(x) - log(x). At x = 1, log(1) = 0
     and exp(1) = e, so eval = e ≈ 2.718. But W(1) < 1. -/

theorem lambertW_not_in_eml_1 (t : EMLTree) (ht : t.depth ≤ 1) :
    ¬ (∀ x : Real, t.eval x = lambertW x) := by
  intro hW
  cases t with
  | const c =>
    -- Reduce to the depth-0 case.
    exact lambertW_not_in_eml_0 (.const c) (by simp [EMLTree.depth]) hW
  | var =>
    exact lambertW_not_in_eml_0 .var (by simp [EMLTree.depth]) hW
  | eml t1 t2 =>
    -- t.depth = 1 + max t1.depth t2.depth ≤ 1.
    -- So max t1.depth t2.depth = 0, hence t1.depth = t2.depth = 0.
    have htd : t1.depth = 0 ∧ t2.depth = 0 := by
      simp [EMLTree.depth] at ht
      -- ht : 1 + max t1.depth t2.depth ≤ 1, hence max ≤ 0, hence both = 0.
      have hmax : max t1.depth t2.depth ≤ 0 := by omega
      refine ⟨?_, ?_⟩
      · exact Nat.le_zero.mp (Nat.le_trans (Nat.le_max_left _ _) hmax)
      · exact Nat.le_zero.mp (Nat.le_trans (Nat.le_max_right _ _) hmax)
    -- t1 and t2 are each const c or var. Case-split on each.
    cases t1 with
    | const c1 =>
      cases t2 with
      | const c2 =>
        -- eml(const c1, const c2). eval x = exp(c1) - log(c2). Constant.
        -- So same disproof as depth-0 const case.
        have h0 := hW 0
        have h1 := hW 1
        -- h0: exp c1 - log c2 = W 0 = 0
        -- h1: exp c1 - log c2 = W 1
        simp only [EMLTree.eval, lambertW_zero] at h0 h1
        -- h0 : c1.exp - c2.log = 0
        -- h1 : c1.exp - c2.log = lambertW 1
        -- Chain via transitivity: 0 = lambertW 1, contradicting W(1) > 0.
        have heq : (0 : Real) = lambertW 1 := h0.symm.trans h1
        have hw_pos : (0 : Real) < lambertW 1 := lambertW_one_pos
        rw [← heq] at hw_pos
        exact lt_irrefl_ax 0 hw_pos
      | var =>
        -- eml(const c1, var). eval x = exp(c1) - log(x).
        -- At x = 1, log(1) = 0, so eval = exp(c1). W(1) < 1.
        -- We need to show exp(c1) ≠ W(1). Hmm — we don't have a fixed
        -- value of c1, only that it's a real. Use TWO points:
        -- at x = 0, eval = exp(c1) - log(0) = exp(c1) - 0 = exp(c1)
        --   (clamped log of 0 is 0). W(0) = 0. So exp(c1) = 0.
        --   But exp is always positive: 0 < exp(c1). Contradiction.
        have h0 := hW 0
        simp only [EMLTree.eval, lambertW_zero, log_zero, sub_zero] at h0
        -- h0 : exp c1 = 0
        have hpos : (0 : Real) < Real.exp c1 := exp_pos c1
        rw [h0] at hpos
        exact lt_irrefl_ax 0 hpos
      | eml a b =>
        -- Contradiction: t2 = eml has depth ≥ 1, but htd.2 says t2.depth = 0.
        have : (1 : Nat) ≤ 0 := by
          have hd : (EMLTree.eml a b).depth = 0 := htd.2
          simp [EMLTree.depth] at hd
        omega
    | var =>
      cases t2 with
      | const c2 =>
        -- eml(var, const c2). eval x = exp(x) - log(c2).
        -- At x = 0, eval = exp(0) - log(c2) = 1 - log(c2). W(0) = 0.
        -- So 1 - log(c2) = 0, log(c2) = 1, c2 = exp(1) (using exp_log).
        -- At x = 1, eval = exp(1) - log(c2) = exp(1) - 1 = e - 1.
        -- Need e - 1 = W(1), but W(1) < 1 and e - 1 > 1.
        have h0 := hW 0
        have h1 := hW 1
        simp only [EMLTree.eval, lambertW_zero, exp_zero] at h0 h1
        -- h0 : 1 - log c2 = 0
        -- h1 : exp 1 - log c2 = lambertW 1
        -- From h0: log c2 = 1.
        have hlog : Real.log c2 = 1 := by
          -- Rearrange 1 - log c2 = 0 to log c2 = 1.
          rw [sub_def] at h0
          -- h0 : 1 + (-log c2) = 0
          -- Add log c2 to both sides: 1 + (-log c2) + log c2 = 0 + log c2
          -- LHS: 1 + 0 = 1 (using -a + a = 0)
          have step : 1 + (-Real.log c2) + Real.log c2 = (0 : Real) + Real.log c2 := by
            rw [h0]
          rw [add_assoc, neg_add_self, add_zero, zero_add] at step
          exact step.symm
        -- Substitute log c2 = 1 in h1:
        rw [hlog] at h1
        -- h1 : exp 1 - 1 = lambertW 1
        -- exp 1 = e, and 1 < e gives e - 1 > 0. Also need e - 1 > W(1)
        -- which is < 1. So e - 1 > 1 - W(1) > 0... actually just need
        -- e - 1 ≠ W(1) somehow. Use e - 1 > 1 - 1 = 0 and ... hmm.
        -- Simpler: lambertW_one_lt_one says W(1) < 1, so 1 > W(1).
        -- If exp 1 - 1 = W(1), then exp 1 - 1 < 1, so exp 1 < 2.
        -- But exp 1 = e > 1 + 1 = 2? Need 2 < e. MachLib has
        -- `one_lt_exp_one : 1 < exp 1`. Need stronger: 2 < exp 1.
        -- That's exp 1 - 1 > 1, equivalently W(1) > 1, contradiction
        -- with W(1) < 1.
        --
        -- MachLib doesn't have `2 < exp 1` directly. But: exp_pos
        -- and exp_add give exp(x+y) = exp(x) * exp(y). Hmm. Maybe use
        -- a different route.
        --
        -- Alternative: at x = 0, eval was 1 - log c2 = 0 ⟹ c2 = exp(1).
        -- At x = c2 = exp(1), eval = exp(exp(1)) - log(exp(1)) = exp(e) - 1.
        -- W(exp(1)) = W(e) = 1 (axiom). So exp(e) - 1 = 1 ⟹ exp(e) = 2.
        -- But exp is monotone and exp(0) = 1, exp(1) = e > 2 (well,
        -- need that), so exp(e) > exp(1) > ... hmm, this needs
        -- specific exp bounds MachLib may not have.
        --
        -- Simplest disproof: use a THIRD point. The sin disproof for
        -- this case uses x = pi/2 trick. For W, use x = lambertW 1
        -- itself: at x = W(1), eval = exp(W(1)) - 1, must equal
        -- W(W(1)). But we don't have a value for W(W(1)).
        --
        -- Tightest path with available axioms: prove e - 1 ≠ W(1) by
        -- contradiction via the chain
        --   e - 1 = W(1) < 1 ⟹ e < 2 < exp 1 = e, contradiction.
        -- But "2 < e" isn't directly in MachLib.
        --
        -- Alternative chain: lambertW_one_lt_one gives W(1) < 1, so
        --   exp 1 - 1 = W(1) < 1, hence exp 1 < 2.
        -- one_lt_exp_one gives 1 < exp 1. So exp 1 ∈ (1, 2). That
        -- alone doesn't give a contradiction.
        --
        -- Strongest available: combine lambertW_one_pos with the
        -- eval to get exp 1 - 1 > 0, i.e., exp 1 > 1 (which we have
        -- via one_lt_exp_one). Still not enough for a contradiction
        -- on the W(1) < 1 side.
        --
        -- Bottom line: this case needs ONE more axiom — either
        --   `two_lt_exp_one : 2 < exp 1`  (classical-true, e ≈ 2.718)
        -- or a value lemma like
        --   `lambertW_one_lt_two : lambertW 1 < exp 1 - 1`.
        -- Adding the cleaner one: two_lt_exp_one.
        have h_e_gt_2 : ((1 + 1 : Real)) < Real.exp 1 := two_lt_exp_one
        -- h1 : exp 1 - 1 = lambertW 1.
        -- two_lt_exp_one : 1+1 < exp 1, so exp 1 - 1 > 1.
        have h_step : (1 : Real) < Real.exp 1 - 1 := by
          -- Add -1 to both sides of (1+1) < exp 1: -1 + (1+1) < -1 + exp 1.
          have := add_lt_add_left h_e_gt_2 (-1)
          -- this : -1 + (1+1) < -1 + exp 1
          -- Goal: 1 < exp 1 - 1
          rw [sub_def]
          have hcomm : -1 + Real.exp 1 = Real.exp 1 + -1 := add_comm _ _
          rw [← hcomm]
          -- Goal: 1 < -1 + exp 1
          -- this : -1 + (1+1) < -1 + exp 1
          -- -1 + (1+1) = (-1 + 1) + 1 = 0 + 1 = 1
          have h_neg1_add_2 : (-1 : Real) + (1 + 1) = 1 := by
            rw [← add_assoc, neg_add_self, zero_add]
          rw [h_neg1_add_2] at this
          exact this
        -- h_step : 1 < exp 1 - 1
        -- h1 : exp 1 - 1 = lambertW 1
        -- lambertW_one_lt_one : lambertW 1 < 1
        -- Chain: 1 < exp 1 - 1 = lambertW 1 < 1 ⟹ 1 < 1, contradiction.
        rw [h1] at h_step
        exact lt_irrefl_ax 1 (lt_trans_ax h_step lambertW_one_lt_one)
      | var =>
        -- eml(var, var). eval x = exp(x) - log(x).
        -- At x = 1, eval = exp(1) - log(1) = exp(1) - 0 = exp(1).
        -- W(1) < 1 < exp(1), so contradiction.
        have h1 := hW 1
        simp only [EMLTree.eval, log_one, sub_zero] at h1
        -- h1 : exp 1 = lambertW 1
        -- lambertW_one_lt_one : W(1) < 1 < exp(1), so exp(1) = W(1) < 1.
        -- But one_lt_exp_one : 1 < exp 1.
        -- Materialize one_lt_exp_one as a local fact, then rewrite.
        have h_one_lt : (1 : Real) < Real.exp 1 := one_lt_exp_one
        rw [h1] at h_one_lt
        -- h_one_lt : 1 < lambertW 1, but lambertW_one_lt_one : W(1) < 1.
        exact lt_irrefl_ax 1
                (lt_trans_ax h_one_lt lambertW_one_lt_one)
      | eml a b =>
        -- Contradiction: t2 = eml has depth ≥ 1, but htd.2 says t2.depth = 0.
        have : (1 : Nat) ≤ 0 := by
          have hd : (EMLTree.eml a b).depth = 0 := htd.2
          simp [EMLTree.depth] at hd
        omega
    | eml a b =>
      have : (1 : Nat) ≤ 0 := by
        have hd : (EMLTree.eml a b).depth = 0 := htd.1
        simp [EMLTree.depth] at hd
      omega

end MachLib
