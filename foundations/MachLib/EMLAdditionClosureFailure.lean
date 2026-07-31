import MachLib.SinNotInEML
import MachLib.EMLHierarchy
import MachLib.LambertW   -- for two_lt_exp_one
import MachLib.Ring       -- for neg_neg_helper

/-!
# EML Addition-Closure Failure (partial result, depth ≤ 1)

This file ships a CONCRETE bounded result on EML's expressive
limitations identified during the 2026-06-13 overnight Lambert-W
investigation:

  **The function `f(x) = x + 1` is NOT in EML at depth ≤ 1.**

Since `const 1` and `var` are both in EML (at depth 0), this
PROVES that EML is NOT closed under addition AT DEPTH ≤ 1 — there's
no EMLTree of depth ≤ 1 that expresses the sum of `const 1` and `var`.

**SUPERSEDED 2026-07-31 — READ THIS BEFORE THE REST OF THE FILE.**
The any-depth case (whether `x + 1` is expressible at ANY finite
EMLTree depth) was the structural conjecture surfaced by the
Lambert-W investigation. **It is FALSE.** `x + 1` is an EML tree at
depth 4; see `x_plus_one_in_eml` at the end of this file. EML IS
closed under adding an arbitrary real constant
(`eml_const_offset_closure`).

The depth-≤1 results below remain TRUE and are unaffected — they are
correct statements about depth ≤ 1 that simply do not extend. The
prose in the middle of this file that treats the any-depth case as
open is left in place, marked, because the file is also the record of
how the wrong expectation was held.

## What this DOES

- Proves `x_plus_one_not_in_eml_0` constructively (case analysis on
  the two depth-0 EMLTree shapes).
- Proves `x_plus_one_not_in_eml_1` constructively (case analysis on
  the 5 additional depth-1 shapes).
- Documents the structural obstacle for depth ≥ 2.

## What this does NOT do

- Did NOT close the any-depth case when written. **It is now closed,
  negatively, at the end of this file** — neither (a) nor (b) below
  was needed, because the conjecture was false and a depth-4 witness
  settles it. Both routes are preserved as written, because both
  presupposed the conjecture was true:
  (a) A structural induction argument that handles arbitrary
      depth without case explosion (currently no clean path
      identified — see the Lambert-W candidate analysis).
  (b) A multi-week brute-force-each-depth approach with shared
      structural lemmas (not scoped here).

## Why this is the right partial result to ship

The Lambert-W any-depth barrier surfaced "is EML closed under
addition?" as a tractable-looking residual question. This file's
result PROVES it ISN'T closed at small depths, which is a real
contribution to the EML expressiveness story even without the
any-depth result. Future research can extend depth-by-depth or
find a structural argument.

The proof structure ports directly from the Lambert-W depth-0/1
case analysis, demonstrating that EML's expressive limitations at
small depths can be characterized cleanly by enumerating shapes
and checking specific values.

## No new axioms

This file introduces zero new axioms. All proofs use only existing
MachLib primitives (`exp_zero`, `exp_pos`, `log_zero`, `log_one`,
`zero_lt_one_ax`, `one_lt_exp_one`, `lt_irrefl_ax`, `lt_trans_ax`).
-/

namespace MachLib

open Real

/-! ## Helper: `1 = 1 + 1 → False` (zero ≠ one cancellation) -/

private theorem one_eq_two_implies_false (h : (1 : Real) = 1 + 1) : False := by
  -- Subtract 1 from both sides: -1 + 1 = -1 + (1 + 1), i.e., 0 = 1.
  have step : -(1 : Real) + 1 = -1 + (1 + 1) := by rw [← h]
  rw [neg_add_self, ← add_assoc, neg_add_self, zero_add] at step
  -- step : 0 = 1
  have hz : (0 : Real) < 1 := zero_lt_one_ax
  rw [← step] at hz
  exact lt_irrefl_ax 0 hz

/-- Generalization of `one_eq_two_implies_false`: for any `a : Real`,
`a = a + 1 → False`. Reusable for any asymptotic-classification
disproof that reduces to "constant value equals constant value + 1". -/
private theorem a_eq_a_plus_one_false (a : Real) (h : a = a + 1) : False := by
  -- Subtract a from both sides via congrArg of (· + -a):
  have step : a + (-a) = (a + 1) + (-a) := by
    rw [← h]
  rw [add_neg] at step
  -- step : 0 = (a + 1) + -a
  -- Simplify RHS: (a + 1) + -a = a + 1 + -a = a + -a + 1 = 0 + 1 = 1.
  rw [add_assoc, add_comm 1 (-a), ← add_assoc, add_neg, zero_add] at step
  -- step : 0 = 1
  have hz : (0 : Real) < 1 := zero_lt_one_ax
  rw [← step] at hz
  exact lt_irrefl_ax 0 hz

/-- **The asymptotic-classification anchor for depth ≥ 2.** If a
function `f : Real → Real` is eventually constant (takes the same
value `c` for all `x ≥ N`), then `f` is not eventually equal to
`x + 1`. The contradiction comes from `f N = c = N + 1` and
`f (N + 1) = c = N + 2`, giving `N + 1 = N + 2`, hence `0 = 1`.

This is the load-bearing helper for ANY depth-2 (or deeper)
subcase where the eval becomes constant for large x — which
happens whenever the clamped log triggers, i.e., when an inner
sub-evaluation reaches ≤ 0 asymptotically. -/
theorem eventually_constant_not_x_plus_one (f : Real → Real)
    (c N : Real) (hN : ∀ x : Real, N ≤ x → f x = c) :
    ¬ (∀ x : Real, f x = x + 1) := by
  intro hsum
  -- Sample at two points x = N and x = N + 1, both ≥ N.
  have h_N1_geq : N ≤ N + 1 := by
    have := add_lt_add_left zero_lt_one_ax N
    rw [add_zero] at this
    exact le_of_lt this
  have hc1 : c = N + 1 := (hN N (le_refl _)).symm.trans (hsum N)
  have hc2 : c = N + 1 + 1 := (hN (N + 1) h_N1_geq).symm.trans (hsum (N + 1))
  -- Combining: N + 1 = (N + 1) + 1, hence 0 = 1 via a_eq_a_plus_one_false.
  exact a_eq_a_plus_one_false (N + 1) (hc1.symm.trans hc2)

/-! ## The target function and depth-0 proof -/

/-- `x + 1` is not expressible by any depth-0 EMLTree. The two
depth-0 shapes are `const c` (constant, can't be x + 1) and `var`
(`var.eval x = x ≠ x + 1`). -/
theorem x_plus_one_not_in_eml_0 (t : EMLTree) (ht : t.depth ≤ 0) :
    ¬ (∀ x : Real, t.eval x = x + 1) := by
  intro hsum
  cases t with
  | const c =>
    -- t.eval x = c for all x. So c = 0 + 1 = 1 and c = 1 + 1 = 2.
    have h0 := hsum 0
    have h1 := hsum 1
    simp only [EMLTree.eval] at h0 h1
    -- h0 : c = 0 + 1 = 1; h1 : c = 1 + 1.
    -- So 1 = c = 1 + 1. Use the helper for the rest.
    have heq : (0 : Real) + 1 = 1 + 1 := h0.symm.trans h1
    rw [zero_add] at heq
    exact one_eq_two_implies_false heq
  | var =>
    -- t.eval x = x for all x. So x = x + 1, i.e., 0 = 1.
    have h0 := hsum 0
    simp only [EMLTree.eval] at h0
    -- h0 : 0 = 0 + 1 = 1.
    rw [zero_add] at h0
    have hz : (0 : Real) < 1 := zero_lt_one_ax
    rw [← h0] at hz
    exact lt_irrefl_ax 0 hz
  | eml _ _ =>
    -- depth ≥ 1, contradiction with ht : depth ≤ 0.
    simp [EMLTree.depth] at ht

/-! ## Depth-1 proof: case analysis on the 4 eml subcases -/

/-- `x + 1` is not expressible by any depth-≤-1 EMLTree. New cases
over depth-0 are the four `eml(t1, t2)` combinations with `t1, t2`
each `const c` or `var`:

  1. `eml(const c1, const c2)`: still constant; same as depth-0
     const disproof.
  2. `eml(const c, var)`: at `x = 0`, eval = `exp(c) - log(0) = exp(c)`
     (clamped log). Need `= 1`, so `c = 0`. Then at `x = 1`, eval
     `= 1 - log(1) = 1 ≠ 2`.
  3. `eml(var, const c)`: at `x = 0`, eval = `exp(0) - log(c) =
     1 - log(c)`. Need `= 1`, so `log(c) = 0`, `c = 1`. At `x = 1`,
     eval = `e - 0 = e`. Need `= 2`, so `e = 2`. False (using
     `one_lt_exp_one : 1 < exp 1 = e`).
  4. `eml(var, var)`: at `x = 1`, eval = `exp(1) - log(1) = e - 0 =
     e`. Need `= 2`. Same disproof as case 3. -/
theorem x_plus_one_not_in_eml_1 (t : EMLTree) (ht : t.depth ≤ 1) :
    ¬ (∀ x : Real, t.eval x = x + 1) := by
  intro hsum
  cases t with
  | const c =>
    exact x_plus_one_not_in_eml_0 (.const c) (by simp [EMLTree.depth]) hsum
  | var =>
    exact x_plus_one_not_in_eml_0 .var (by simp [EMLTree.depth]) hsum
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
        -- eml(const c1, const c2): eval = exp(c1) - log(c2) (constant).
        have h0 := hsum 0
        have h1 := hsum 1
        simp only [EMLTree.eval] at h0 h1
        -- h0 : exp(c1) - log(c2) = 0 + 1 = 1
        -- h1 : exp(c1) - log(c2) = 1 + 1 = 2
        rw [zero_add] at h0
        -- h0 : exp(c1) - log(c2) = 1
        -- h1 : exp(c1) - log(c2) = 1 + 1
        -- So 1 = 1 + 1; use helper.
        have heq : (1 : Real) = 1 + 1 := h0.symm.trans h1
        exact one_eq_two_implies_false heq
      | var =>
        -- eml(const c, var): eval x = exp(c) - log(x).
        -- At x = 0: exp(c) - 0 = exp(c). Need = 1.
        -- At x = 1: exp(c) - 0 = exp(c). Need = 2.
        -- So exp(c) = 1 AND exp(c) = 2; contradiction.
        have h0 := hsum 0
        have h1 := hsum 1
        simp only [EMLTree.eval, log_zero, log_one, sub_zero] at h0 h1
        rw [zero_add] at h0
        -- h0 : exp(c1) = 1
        -- h1 : exp(c1) = 1 + 1
        have heq : (1 : Real) = 1 + 1 := h0.symm.trans h1
        exact one_eq_two_implies_false heq
      | eml a b =>
        have : (1 : Nat) ≤ 0 := by
          have hd : (EMLTree.eml a b).depth ≤ 0 := Nat.le_of_eq htd.2
          simp [EMLTree.depth] at hd
        omega
    | var =>
      cases t2 with
      | const c2 =>
        -- eml(var, const c): eval x = exp(x) - log(c).
        -- At x = 0: 1 - log(c). Need = 1, so log(c) = 0.
        -- At x = 1: exp(1) - log(c) = e - 0 = e. Need = 2.
        -- Need e = 2; but one_lt_exp_one says 1 < e, and we
        -- need a separate argument to rule out e = 2.
        -- Actually: at x = 1, eval = e - log(c) = 2. Combined
        -- with log(c) = 0 (from x = 0 equation), get e = 2.
        -- Contradiction with one_lt_exp_one: 1 < e, so e ≠ 1.
        -- But we need e ≠ 2, which is stronger.
        --
        -- Hmm, MachLib doesn't have a "e ≠ 2" axiom. Use:
        -- one_lt_exp_one : 1 < exp 1. So exp 1 > 1.
        -- We don't have exp 1 < 2 or exp 1 ≠ 2 directly.
        --
        -- Alternative: use a THIRD point. At x = 2: eval = exp(2)
        -- - 0 = exp(2). Need = 3. So exp(2) = 3.
        -- And exp(2) = exp(1)·exp(1) = e·e. If e = 2 and e² = 3,
        -- then 4 = 3, contradiction.
        --
        -- This requires exp_add to multiply exp(2) = exp(1)·exp(1).
        -- And then arithmetic on (1+1)² = 4. Both available.
        --
        -- For simplicity, just use the contradiction from x = 0
        -- and x = 1 evaluations + one_lt_exp_one to get e > 1,
        -- and the second equation e = 2 implies 1 < 2, which is
        -- consistent (doesn't give a direct contradiction).
        --
        -- Hmm so we genuinely need a stronger axiom or a longer
        -- argument. For NOW, lift this as a lifted axiom.
        --
        -- Actually wait: at x = 0, eval = exp(0) - log(c) =
        -- 1 - log(c) (using exp_zero). Need 1 - log(c) = 1
        -- (since x + 1 at x = 0 is 1). So log(c) = 0.
        --
        -- At x = 1, eval = exp(1) - log(c) = e - 0 = e. Need = 2.
        -- So e = 2. Contradicts the classical fact e ≈ 2.718.
        --
        -- MachLib has `two_lt_exp_one : (1+1) < exp 1` in
        -- LambertW.lean. So e > 2. Combined with e = 2: 2 < 2,
        -- contradiction.
        --
        -- But that imports LambertW which imports this file...
        -- circular dependency. Just inline the small fact.
        have h0 := hsum 0
        have h1 := hsum 1
        simp only [EMLTree.eval, exp_zero, log_one] at h0 h1
        rw [zero_add] at h0
        -- h0 : 1 - log(c2) = 1
        -- h1 : exp 1 - log(c2) = 1 + 1
        -- From h0: log(c2) = 0 (derive via add cancellation).
        have hlog : Real.log c2 = 0 := by
          -- h0 : 1 - log c2 = 1. Convert to additive form, cancel
          -- the 1 on both sides, derive log c2 = 0.
          rw [sub_def] at h0
          -- h0 : 1 + -log c2 = 1
          -- Add -1 on the left of both sides:
          have step1 : (-1 : Real) + (1 + -Real.log c2) = -1 + 1 := by rw [h0]
          -- LHS: rewrite via associativity, neg_add_self, zero_add.
          rw [← add_assoc, neg_add_self, zero_add] at step1
          -- step1 : -log c2 = 0 (both LHS and RHS -1+1 got reduced)
          -- Derive log c2 = 0 from -log c2 = 0:
          -- log c2 = -(-log c2) = -0 = 0.
          -- Derive log c2 = 0 from -log c2 = 0 by negating both sides
          -- and using the double-negation lemma.
          have step2 : -(-Real.log c2) = -(0 : Real) := by rw [step1]
          -- step2 : -(-log c2) = -0
          rw [neg_zero] at step2
          -- step2 : -(-log c2) = 0
          -- Now use the explicit equation -(-a) = a.
          have hnn : -(-Real.log c2) = Real.log c2 := neg_neg_helper (Real.log c2)
          rw [hnn] at step2
          -- step2 : log c2 = 0
          exact step2
        rw [hlog, sub_def, neg_zero, add_zero] at h1
        -- h1 : exp 1 = 1 + 1
        -- Use two_lt_exp_one : (1+1) < exp 1 from LambertW.
        -- Combined with h1 (exp 1 = 1+1): substitute to get
        -- 1+1 < 1+1, contradicting lt_irrefl_ax.
        have h_strict : ((1 + 1 : Real)) < Real.exp 1 := two_lt_exp_one
        rw [← h1] at h_strict
        exact lt_irrefl_ax _ h_strict
      | var =>
        -- eml(var, var): eval x = exp(x) - log(x).
        -- At x = 1: exp(1) - log(1) = e - 0 = e. Need = 2.
        -- Same e = 2 issue; same disproof using two_lt_exp_one.
        have h1 := hsum 1
        simp only [EMLTree.eval, log_one, sub_zero] at h1
        -- h1 : exp 1 = 1 + 1
        have h_strict : ((1 + 1 : Real)) < Real.exp 1 := two_lt_exp_one
        rw [← h1] at h_strict
        exact lt_irrefl_ax _ h_strict
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

/-! ## Depth-2 partial: the all-constants subcase

Demonstrates the depth-2 proof pattern. The full case analysis
(32 subcases) is scoped in
`monogate-research/exploration/eml_addition_closure_depth2_scoping_2026_06_13/`
as multi-session work. This single subcase shows the pattern works
and provides a building block.

The cleanest depth-2 closure is the "all-constants" case:
`t = eml(t1, t2)` where BOTH t1 and t2 have eval constant in x.
Concretely: `t1 = eml(const a, const b)` and `t2 = eml(const a',
const b')`. Eval is constant; can't equal x + 1.

This generalizes via the LEMMA below, which closes ANY case where
eval is constant. -/

/-- If a function `f : Real → Real` is constant (takes the same
value at x = 0 and x = 1), then it can't equal `x + 1`. The
contradiction comes from `(x + 1)(0) = 1 ≠ 2 = (x + 1)(1)`. -/
private theorem constant_function_not_x_plus_one (f : Real → Real)
    (hconst : f 0 = f 1) :
    ¬ (∀ x : Real, f x = x + 1) := by
  intro hsum
  have h0 := hsum 0
  have h1 := hsum 1
  rw [zero_add] at h0
  -- h0 : f 0 = 1
  -- h1 : f 1 = 1 + 1
  -- hconst : f 0 = f 1
  -- Chain: 1 = f 0 = f 1 = 1 + 1.
  have heq : (1 : Real) = 1 + 1 := h0.symm.trans (hconst.trans h1)
  exact one_eq_two_implies_false heq

/-- Specific depth-2 case: `t = eml(eml(const a, const b),
eml(const a', const b'))`. Both subtrees are constant-valued, so
the outer eval is also constant. Closed via
`constant_function_not_x_plus_one`. -/
theorem x_plus_one_not_in_eml_2_all_constants
    (a b a' b' : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (EMLTree.eml (.const a) (.const b))
                     (EMLTree.eml (.const a') (.const b'))).eval x = x + 1) := by
  apply constant_function_not_x_plus_one
  -- Show eval is constant: eval 0 = eval 1.
  show (EMLTree.eml (EMLTree.eml (.const a) (.const b))
                    (EMLTree.eml (.const a') (.const b'))).eval 0
     = (EMLTree.eml (EMLTree.eml (.const a) (.const b))
                    (EMLTree.eml (.const a') (.const b'))).eval 1
  -- Both unfold to exp(exp(a) - log(b)) - log_clamped(exp(a') - log(b')).
  -- No x dependence anywhere.
  rfl

/-! ## Asymptotic-classification subcase: eml(const c1, eml(const c2, var))

This is a depth-2 subcase where the function is NOT constant in x
(unlike all-constants) but IS eventually constant. The mechanism:

  t.eval x = exp(c1) - log_clamped(exp(c2) - log(x))

For x ≥ exp(exp(c2)):
  - log(x) ≥ log(exp(exp(c2))) = exp(c2)  (using log_lt_log + log_exp)
  - So exp(c2) - log(x) ≤ 0
  - Hence log_clamped(exp(c2) - log(x)) = 0 (by log_nonpos)
  - Hence t.eval x = exp(c1) - 0 = exp(c1)  (constant!)

Then apply `eventually_constant_not_x_plus_one` with N = exp(exp(c2))
and c = exp(c1).

This is the FIRST concrete subcase where the asymptotic-classification
approach beats specific-value algebra: at small x, the function IS
non-trivial; only at large x does it collapse to a constant. -/

theorem x_plus_one_not_in_eml_2_eml_const_eml_const_var
    (c1 c2 : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.const c1)
                     (EMLTree.eml (.const c2) .var)).eval x = x + 1) := by
  apply eventually_constant_not_x_plus_one _ (Real.exp c1) (Real.exp (Real.exp c2))
  intro x hx
  -- Goal: t.eval x = exp c1, given x ≥ exp(exp c2).
  show Real.exp c1 - Real.log (Real.exp c2 - Real.log x) = Real.exp c1
  -- Step 1: show log x ≥ exp c2.
  have h_exp_c2_pos : (0 : Real) < Real.exp (Real.exp c2) := exp_pos _
  have hx_pos : (0 : Real) < x := lt_of_lt_of_le h_exp_c2_pos hx
  -- log is monotone on positives. log(x) ≥ log(exp(exp c2)) = exp c2.
  rcases (le_iff_lt_or_eq (Real.exp (Real.exp c2)) x).mp hx with hxlt | hxeq
  · -- x > exp(exp c2): strict.
    have hlog_lt : Real.log (Real.exp (Real.exp c2)) < Real.log x :=
      log_lt_log h_exp_c2_pos hxlt
    rw [log_exp] at hlog_lt
    -- hlog_lt : exp c2 < log x
    -- So exp c2 - log x < 0.
    have h_diff_neg : Real.exp c2 - Real.log x < 0 := by
      -- (exp c2) + (-log x) < 0 iff exp c2 < log x.
      rw [sub_def]
      -- Goal: exp c2 + -log x < 0
      have step := add_lt_add_left hlog_lt (-Real.log x)
      -- step : -log x + exp c2 < -log x + log x
      rw [neg_add_self] at step
      -- step : -log x + exp c2 < 0
      rw [add_comm] at step
      exact step
    have h_log_zero : Real.log (Real.exp c2 - Real.log x) = 0 :=
      log_nonpos (le_of_lt h_diff_neg)
    rw [h_log_zero, sub_def, neg_zero, add_zero]
  · -- x = exp(exp c2): equality. log x = log(exp(exp c2)) = exp c2.
    -- So exp c2 - log x = 0. log_clamped(0) = log_zero = 0.
    rw [← hxeq]
    rw [log_exp]
    -- Goal: exp c1 - log (exp c2 - exp c2) = exp c1
    -- exp c2 - exp c2 = 0
    have h_self_diff : Real.exp c2 - Real.exp c2 = (0 : Real) := by
      rw [sub_def, add_neg]
    rw [h_self_diff, log_zero, sub_def, neg_zero, add_zero]

/-! ## Depth-2 partial result

The depth-2 case has 32 new subcases beyond depth-1 (each of t1, t2
in eml(t1, t2) can be one of 6 depth-≤-1 shapes, minus the 4
covered by reducing to depth-1). Below we close the SHAPES WHERE
THE CLAMPED LOG TRIGGERS — i.e., where t2.eval reaches 0 or
non-positive — because those reduce eval to `exp(t1.eval x) -
0 = exp(t1.eval x)`, and `exp(t1.eval x) = x + 1` constraints
collapse to a small number of equations.

Cases NOT closed here (remain OPEN for future work):

  - eml(t1, t2) where t2.eval stays strictly positive for all x:
    full case explosion with specific-value algebra. 24 of 32
    new subcases. Need either:
    (a) Brute-force per-subcase, OR
    (b) A clean asymptotic classification using
        EMLAsymptoticBound.

This file ships the SIMPLER half — about 8 of 32 subcases —
extending the depth-1 result with a clean structural argument
for the clamped-log-triggered shapes.

For the remaining 24, see scoping in
`monogate-research/exploration/lambert_w_all_candidates_attempt_2026_06_13/`
(the addition-closure conjecture remains open at depth ≥ 2 for
clamped-log-non-trivial shapes).

## Note on imports

The depth-1 proof reuses `two_lt_exp_one : (1+1) < exp 1` from
`MachLib.LambertW` (where it was lifted as a classical-citation
axiom for the parallel Lambert-W depth-1 disproof). NO new axioms
introduced in this file — just structural reuse of the same
classical fact.

## The any-depth conjecture (REFUTED 2026-07-31 — see end of file)

For depth k ≥ 2, the case analysis explodes (depth-2 has 36
subcases, depth-k has ~2^k). Whether `x + 1 ∉ EML` at any depth is
the OPEN structural conjecture that, if resolved positively, would
prove EML is not closed under addition at any finite depth.

**It was not resolved positively. `x_plus_one_in_eml` exhibits a
depth-4 witness, so the case explosion below was an explosion in a
direction with no theorem at the end of it.** The paragraph above is
kept verbatim rather than rewritten: it is an accurate record of why
the search went the way it did, and the 36-subcase count is still
correct.

See `monogate-research/exploration/lambert_w_all_candidates_attempt_2026_06_13/`
for the obstacle analysis showing why structural induction is hard:
the addition `a + b` for general EML expressions appears to have
the same recursive expression-needed structure that derailed the
Lambert-W functional-equation argument.

The depth-≤-1 result here is the bounded shippable contribution
that the Lambert-W investigation surfaced: extends EML's
expressiveness story with a concrete "this specific function is
not in EML at small depths" theorem.
-/

/-! ## THE ANY-DEPTH CONJECTURE IS FALSE — `x + 1 ∈ EML` at depth 4

**Added 2026-07-31 (E2 session 1).** The file above closes `x + 1 ∉ EML` at depth ≤ 1 and scopes the
remaining depth-2 subcases; the surrounding notes state the any-depth case as an open structural
conjecture. **It is false, and the witness is small.**

### The gadget: `eml` can NEGATE a subtree

`eml` offers `exp` of its first argument and `−log` of its second. Since `log ∘ exp = id`, wrapping a
tree `t` so that its value passes through `exp` and then lands in a *divisor* position returns the value
itself, with a minus sign:

```
negOffset c t  :=  eml (const c) (eml t (const 1))
eval           =   exp c − log (exp (t.eval x) − log 1)
               =   exp c − t.eval x                        -- EXACTLY, for all real x
```

No positivity side-condition: `exp (t.eval x) > 0` always, so the `log` is never clamped and the
identity is unconditional.

### Why the intuition said otherwise

The obstacle analysis reasoned that EML has no addition constructor and that `log` only ever appears
*subtracted*, so a `+x` term has nowhere to come from. That is right about one application and wrong
about two. **You cannot add, but you can negate — and negating twice adds.** `x + 1` is
`2 − (1 − x)`, and each subtraction is one `negOffset`. Depth cost is `+2` per negation, so the
witness sits at depth 4.

This is the depth-1 result's own lesson read at the wrong scale: the case analysis at depth ≤ 1 is
genuinely exhaustive, and it created an impression of an obstruction that the depth-2 scoping note
then inherited. The 24 open subcases were never the frontier. -/

/-- `exp` of a tree, with the divisor neutralised: `eml t (const 1)` evaluates to `exp (t.eval x)`,
because `log 1 = 0`. The building block of the negation gadget. -/
noncomputable def expOf (t : EMLTree) : EMLTree := .eml t (.const 1)

theorem expOf_eval (t : EMLTree) (x : Real) : (expOf t).eval x = Real.exp (t.eval x) := by
  simp [expOf, EMLTree.eval, log_one, sub_zero]

theorem expOf_depth (t : EMLTree) : (expOf t).depth = 1 + t.depth := by
  simp [expOf, EMLTree.depth]

/-- **The negation gadget.** `negOffset c t` evaluates to `exp c − t.eval x`, exactly and for every
real `x`. This is the constructor the addition-closure obstacle analysis assumed EML did not have. -/
noncomputable def negOffset (c : Real) (t : EMLTree) : EMLTree := .eml (.const c) (expOf t)

theorem negOffset_eval (c : Real) (t : EMLTree) (x : Real) :
    (negOffset c t).eval x = Real.exp c - t.eval x := by
  simp only [negOffset, expOf, EMLTree.eval, log_one, sub_zero, log_exp]

theorem negOffset_depth (c : Real) (t : EMLTree) : (negOffset c t).depth = 2 + t.depth := by
  simp only [negOffset, expOf, EMLTree.depth, Nat.zero_max, Nat.max_zero]
  omega

/-- The witness: `2 − (1 − x)`. -/
noncomputable def xPlusOneTree : EMLTree := negOffset (Real.log (1 + 1)) (negOffset 0 .var)

/-- **`x + 1` IS an EML tree.** Exact, for every real `x`, with no side-condition. -/
theorem xPlusOneTree_eval (x : Real) : xPlusOneTree.eval x = x + 1 := by
  rw [xPlusOneTree, negOffset_eval, negOffset_eval]
  rw [exp_zero, exp_log (add_pos one_pos one_pos)]
  simp only [EMLTree.eval]
  mach_ring

theorem xPlusOneTree_depth : xPlusOneTree.depth = 4 := by
  simp [xPlusOneTree, negOffset_depth, EMLTree.depth]

/-- **The any-depth conjecture, refuted.** There is no depth at which `x + 1` becomes unreachable,
because it is reachable at depth 4. Contrast `x_plus_one_not_in_eml_1` above, which remains true: the
depth-≤1 result is correct and simply does not extend. -/
theorem x_plus_one_in_eml : ∃ t : EMLTree, (∀ x : Real, t.eval x = x + 1) ∧ t.depth = 4 :=
  ⟨xPlusOneTree, xPlusOneTree_eval, xPlusOneTree_depth⟩

/-- **The general form: EML is closed under adding an arbitrary real constant**, at a cost of depth 4.
Given any tree `t`, `negOffset (log (K + c)) (negOffset (log K) t)` evaluates to `t.eval x + c` provided
both `K > 0` and `K + c > 0` — and such a `K` exists for every real `c`, so the closure is unrestricted.
Stated with the two constants explicit rather than chosen, because the choice is the only content. -/
theorem eml_const_offset_closure (t : EMLTree) {K c : Real} (hK : 0 < K) (hKc : 0 < K + c) (x : Real) :
    (negOffset (Real.log (K + c)) (negOffset (Real.log K) t)).eval x = t.eval x + c := by
  rw [negOffset_eval, negOffset_eval, exp_log hK, exp_log hKc]
  mach_mpoly [K, c, t.eval x]

/-- Such a `K` always exists, so `eml_const_offset_closure` is genuinely unrestricted in `c`:
take `K = 1` when `c ≥ 0`, and `K = 1 − c` when `c < 0`. -/
theorem eml_const_offset_witness (c : Real) : ∃ K : Real, 0 < K ∧ 0 < K + c := by
  rcases lt_total c 0 with h | h | h
  · refine ⟨1 - c, sub_pos_of_lt (lt_trans_ax h one_pos), ?_⟩
    have heq : (1 : Real) - c + c = 1 := by mach_mpoly [c]
    rw [heq]; exact one_pos
  · refine ⟨1, one_pos, ?_⟩
    rw [h, add_zero]; exact one_pos
  · exact ⟨1, one_pos, add_pos one_pos h⟩

/-! ### The general form: EML IS closed under addition when one summand is positive

The `x + 1` witness is a special case of something larger, and the larger statement is what the
2026-06-13 exploration note actually conjectured against. From
`exploration/lambert_w_all_candidates_attempt_2026_06_13/FINDINGS.md`:

> **Sub-sub-problem:** can EML express addition `a + b` of two arbitrary EML expressions a, b? …
> **Result:** EML's grammar appears to NOT support general addition. Specifically, I conjecture but
> cannot prove that `EMLTree.eval` is closed under `+` only in restricted cases.

**It supports general addition, subject to one positivity side-condition.** The note's own attempt
stalled at `p = log(a + b + log q)` and called it circular — which it is, along that route. The
non-circular route goes through `log ∘ exp = id` instead, and needs `exp ∘ log = id`, which is where
positivity enters and is the only place it enters. -/

/-- `log` of a subtree, exactly and unconditionally: `1 − (1 − log (t.eval x))`. -/
noncomputable def logTree (t : EMLTree) : EMLTree := negOffset 0 (.eml (.const 0) t)

theorem logTree_eval (t : EMLTree) (x : Real) :
    (logTree t).eval x = Real.log (t.eval x) := by
  rw [logTree, negOffset_eval]
  simp only [EMLTree.eval, exp_zero]
  mach_mpoly [Real.log (t.eval x)]

/-- **Exact subtraction**, given that the left operand is positive. Positivity is needed for
`exp (log a) = a` and nowhere else — the `−b` half is unconditional, since `log (exp b) = b` always. -/
noncomputable def subTree (a b : EMLTree) : EMLTree := .eml (logTree a) (expOf b)

theorem subTree_eval {a : EMLTree} (b : EMLTree) {x : Real} (ha : 0 < a.eval x) :
    (subTree a b).eval x = a.eval x - b.eval x := by
  simp only [subTree, EMLTree.eval, logTree_eval, expOf_eval, log_exp, exp_log ha]

/-- **Exact addition.** `a + b = (a − (1 − b)) + 1`, with the outer `+1` supplied by the negation
gadget applied twice. Same single side-condition: `a` positive at the point of evaluation. -/
noncomputable def addTree (a b : EMLTree) : EMLTree :=
  negOffset (Real.log (1 + 1)) (negOffset 0 (subTree a (negOffset 0 b)))

/-- **EML IS closed under addition wherever the left summand is positive** — refuting the
"EML's grammar appears to NOT support general addition" conjecture of 2026-06-13 in its general form,
not merely for the `x + 1` instance. By commutativity of `+` it is enough that *either* summand be
positive: apply this with the arguments swapped. -/
theorem addTree_eval {a : EMLTree} (b : EMLTree) {x : Real} (ha : 0 < a.eval x) :
    (addTree a b).eval x = a.eval x + b.eval x := by
  rw [addTree, negOffset_eval, negOffset_eval, subTree_eval (negOffset 0 b) ha,
    negOffset_eval]
  rw [exp_zero, exp_log (add_pos one_pos one_pos)]
  mach_mpoly [a.eval x, b.eval x]

/-- Where the positivity is NOT removable, stated so the result is not read as stronger than it is.
`exp (log u) = u` fails for `u ≤ 0` because `MachLib.Real.log` is total and returns a junk value there
— the same totalization artifact the E5 arm characterised. So `subTree`/`addTree` are exact
**pointwise, wherever `a` is positive**, and say nothing at points where it is not. A tree unbounded
below (e.g. `1 − x`) therefore cannot serve as the left summand globally, and no constant shift repairs
that, since shifting changes the sum. -/
theorem subTree_eval_needs_positivity :
    ∃ (a b : EMLTree) (x : Real), (subTree a b).eval x ≠ a.eval x - b.eval x := by
  refine ⟨.const 0, .const 0, 0, ?_⟩
  simp only [subTree, EMLTree.eval, logTree_eval, expOf_eval, log_exp]
  rw [log_zero, exp_zero]
  intro h
  have h1 : (1 : Real) - 0 = 1 := by mach_mpoly []
  have h2 : (0 : Real) - 0 = 0 := by mach_mpoly []
  rw [h1, h2] at h
  exact absurd h.symm (ne_of_lt one_pos)

/-! Small rearrangement lemmas, factored out because `mach_mpoly` resolves its atom list against the
enclosing *statement's* binders and cannot see variables introduced by `intro`/`obtain` inside a proof.
Stating them at top level is the cheapest way to keep the atoms in scope. -/

private theorem neg_add_eq_sub (a b : Real) : -b + a = a - b := by mach_mpoly [a, b]
private theorem negSubOne_add_self (y : Real) : -y - 1 + y = -1 := by mach_mpoly [y]
private theorem neg_one_add_one : (-1 : Real) + 1 = 0 := by mach_mpoly []
private theorem neg_negSubOne_sub_one (y : Real) : -(-y - 1) - 1 = y := by mach_mpoly [y]

/-! ### Is depth 4 minimal? The necessary condition, and depth 2 closed

`x_plus_one_not_in_eml_1` closes depth ≤ 1 by enumeration; the witness sits at depth 4; **depths 2 and
3 were left unexamined**, which means the file shipped a witness and no bound. This section closes
depth 2 and states exactly what depth 3 needs.

The move that avoids the 36-case explosion the original scoping note budgeted for: **do not enumerate
the shapes — constrain the divisor.** Any witness at all, of any shape, must have a divisor subtree
that grows at least like `exp (−x − 1)` as `x → −∞`, and that single inequality does the work that
case analysis was being asked to do. -/

/-- **The necessary condition on every witness, enumeration-free.** If `eml t1 t2` evaluates to `x + 1`
at some `x < −1`, then `t2.eval x ≥ exp (−x − 1)`.

The proof is three lines of content: `exp` of the dividend is positive, so `log (t2.eval x)` exceeds
`−x − 1`, which is itself positive when `x < −1`; a non-positive `t2.eval x` would make that `log` equal
`0` by MachLib's convention and contradict it; so `t2.eval x` is positive and `exp ∘ log` inverts.

**The totalization convention is load-bearing here in the helpful direction** — `log ≤ 0 ↦ 0` is what
lets a positivity fact be *derived* rather than assumed. -/
theorem witness_divisor_ge {t1 t2 : EMLTree} {x : Real}
    (hx : x < -1) (h : (EMLTree.eml t1 t2).eval x = x + 1) :
    Real.exp (-x - 1) ≤ t2.eval x := by
  simp only [EMLTree.eval] at h
  have hkey : Real.log (t2.eval x) = Real.exp (t1.eval x) - (x + 1) := by
    rw [← h]; mach_mpoly [Real.exp (t1.eval x), Real.log (t2.eval x), x]
  have hxpos : (0 : Real) < -x - 1 := by
    have h1 : x + 1 < 0 := by
      have := add_lt_add_left hx 1
      have e1 : (1 : Real) + x = x + 1 := by mach_mpoly [x]
      have e2 : (1 : Real) + -1 = 0 := by mach_mpoly []
      rw [e1, e2] at this; exact this
    have := add_lt_add_left h1 (-x - 1)
    have e3 : -x - 1 + (x + 1) = 0 := by mach_mpoly [x]
    have e4 : -x - 1 + 0 = -x - 1 := by mach_mpoly [x]
    rw [e3, e4] at this; exact this
  have hlog : -x - 1 < Real.log (t2.eval x) := by
    rw [hkey]
    have hp : (0 : Real) < Real.exp (t1.eval x) := exp_pos _
    have := add_lt_add_left hp (-(x + 1))
    have e5 : -(x + 1) + 0 = -x - 1 := by mach_mpoly [x]
    have e6 : -(x + 1) + Real.exp (t1.eval x) = Real.exp (t1.eval x) - (x + 1) := by
      mach_mpoly [x, Real.exp (t1.eval x)]
    rw [e5, e6] at this; exact this
  have ht2pos : 0 < t2.eval x := by
    rcases lt_total 0 (t2.eval x) with hp | he | hn
    · exact hp
    · exfalso
      rw [log_nonpos (le_of_eq he.symm)] at hlog
      exact lt_irrefl_ax 0 (lt_trans_ax hxpos hlog)
    · exfalso
      rw [log_nonpos (le_of_lt hn)] at hlog
      exact lt_irrefl_ax 0 (lt_trans_ax hxpos hlog)
  calc Real.exp (-x - 1) ≤ Real.exp (Real.log (t2.eval x)) := exp_monotone (le_of_lt hlog)
    _ = t2.eval x := exp_log ht2pos

/-- Every tree of depth ≤ 1 is **bounded above by a constant on the negative axis**. Four real shapes
survive the depth bound, and on `x < 0` each collapses: `log x` is `0` by convention, and `exp x ≤ 1`. -/
theorem depth_le_one_bounded_above (t : EMLTree) (ht : t.depth ≤ 1) :
    ∃ M : Real, ∀ x : Real, x < 0 → t.eval x ≤ M := by
  cases t with
  | const c => exact ⟨c, fun _ _ => le_refl c⟩
  | var => exact ⟨0, fun _ hx => le_of_lt hx⟩
  | eml a b =>
    simp only [EMLTree.depth] at ht
    have hab : max a.depth b.depth = 0 := by omega
    have ha : a.depth = 0 := by
      have := Nat.le_max_left a.depth b.depth; omega
    have hb : b.depth = 0 := by
      have := Nat.le_max_right a.depth b.depth; omega
    cases a with
    | eml _ _ => simp only [EMLTree.depth] at ha; omega
    | const c =>
      cases b with
      | eml _ _ => simp only [EMLTree.depth] at hb; omega
      | const d => exact ⟨Real.exp c - Real.log d, fun _ _ => le_refl _⟩
      | var =>
        refine ⟨Real.exp c, ?_⟩
        intro x hx
        simp only [EMLTree.eval, log_nonpos (le_of_lt hx), sub_zero]
        exact le_refl _
    | var =>
      cases b with
      | eml _ _ => simp only [EMLTree.depth] at hb; omega
      | const d =>
        refine ⟨1 - Real.log d, ?_⟩
        intro x hx
        simp only [EMLTree.eval]
        have h1 : Real.exp x ≤ 1 := exp_le_one_of_nonpos (le_of_lt hx)
        have := add_le_add_left h1 (-Real.log d)
        rw [neg_add_eq_sub, neg_add_eq_sub] at this; exact this
      | var =>
        refine ⟨1, ?_⟩
        intro x hx
        simp only [EMLTree.eval, log_nonpos (le_of_lt hx), sub_zero]
        exact exp_le_one_of_nonpos (le_of_lt hx)

/-- **`x + 1 ∉ EML` at depth ≤ 2.** Not by enumerating 36 shapes: the divisor of any witness must
outgrow `exp (−x − 1)`, a depth-≤1 divisor is bounded by a constant, and `exp` beats every constant. -/
theorem x_plus_one_not_in_eml_2 (t : EMLTree) (ht : t.depth ≤ 2) :
    ¬ (∀ x : Real, t.eval x = x + 1) := by
  intro hsum
  cases t with
  | const c => exact x_plus_one_not_in_eml_0 (.const c) (by simp [EMLTree.depth]) hsum
  | var => exact x_plus_one_not_in_eml_0 .var (by simp [EMLTree.depth]) hsum
  | eml t1 t2 =>
    simp only [EMLTree.depth] at ht
    have hd2 : t2.depth ≤ 1 := by
      have := Nat.le_max_right t1.depth t2.depth; omega
    obtain ⟨M, hM⟩ := depth_le_one_bounded_above t2 hd2
    -- pick `y > 0` with `M < exp y`, then evaluate at `x = -y - 1 < -1`.
    obtain ⟨y, hy0, hyM⟩ : ∃ y : Real, 0 < y ∧ M < Real.exp y := by
      rcases lt_total M 0 with hm | hm | hm
      · exact ⟨1, one_pos, lt_trans_ax hm (lt_trans_ax one_pos (exp_grows_strictly_thm 1))⟩
      · exact ⟨1, one_pos, hm ▸ lt_trans_ax one_pos (exp_grows_strictly_thm 1)⟩
      · refine ⟨M + 1, ?_, ?_⟩
        · exact add_pos hm one_pos
        · have h1 : M < M + 1 := by
            have := add_lt_add_left one_pos M
            have e : M + 0 = M := by mach_mpoly [M]
            rw [e] at this; exact this
          exact lt_trans_ax h1 (exp_grows_strictly_thm (M + 1))
    have hxlt : -y - 1 < -1 := by
      have := add_lt_add_left hy0 (-y - 1)
      rw [add_zero, negSubOne_add_self] at this; exact this
    have hxneg : -y - 1 < 0 :=
      lt_trans_ax hxlt (by
        have := add_lt_add_left one_pos (-1 : Real)
        rw [add_zero, neg_one_add_one] at this; exact this)
    have hge := witness_divisor_ge hxlt (hsum (-y - 1))
    have hey : Real.exp (-(-y - 1) - 1) = Real.exp y := by
      rw [neg_negSubOne_sub_one]
    rw [hey] at hge
    exact absurd (lt_of_lt_of_le hyM (le_trans hge (hM _ hxneg))) (lt_irrefl_ax M)

/-! ### Depth 3: what is left, and why it is a separate session rather than a longer one

**Minimality is NOT established.** `x_plus_one_not_in_eml_2` plus the depth-4 witness leaves depth 3
open, so the honest statement is *"a witness exists at depth 4 and none exists below depth 3"* — not
*"4 is minimal"*.

`witness_divisor_ge` still applies at depth 3 and still does the enumeration-free half: the divisor is a
tree of depth ≤ 2 and must satisfy `t2.eval x ≥ exp (−x − 1)`. What breaks is the *other* half.
`depth_le_one_bounded_above` does not lift, and the reason is precisely the negation gadget this file
just shipped:

```
(eml t1 (eml var (const 1))).eval x = exp (t1.eval x) − x
```

which is **unbounded above on the negative axis**. So depth-≤2 trees are not constant-bounded, and the
one-line "exp beats every constant" finish is unavailable.

**The bound that should replace it**, with the shape it has to have:

> `∀ t, t.depth ≤ 2 → ∃ A N, ∀ x ≤ N, t.eval x ≤ A − x`

— at most *linear* growth as `x → −∞`, against the divisor's required *exponential* growth. The
dividend half factors cleanly (`exp` is monotone, so `depth_le_one_bounded_above` bounds
`exp (t1.eval x)` by a constant). The divisor half needs `log (t2.eval x) ≥ x + C` for depth-≤1 `t2`,
and **that is where the `N` becomes necessary rather than cosmetic**: for `t2 = eml var (const b)` with
`log b > 0`, `t2.eval x = exp x − log b` passes through `0` at a finite `x`, sending `log` to `−∞` there.
The bound only holds once `x` is negative enough that `exp x − log b` has gone negative and MachLib's
convention clamps the `log` to `0`.

So the missing lemma is an *eventually*-shaped statement about the `x → −∞` end, and MachLib's
asymptotic vocabulary (`EventuallyAtMost` and friends in `EMLAsymptoticClass`) is built for `x → +∞`.
Closing depth 3 means either mirroring that vocabulary or inlining the threshold, plus a super-linear
growth fact for `exp` — `exp y > 2y − 2` for `y > 1`, available from the `two_lt_exp_one` this file
already imports.

**Recorded as scoped, not attempted.** The estimate is one focused session; the reason it is not this
one is that it is a different piece of work with a different failure mode, and bolting it on would make
a clean depth-2 result and a half-finished depth-3 result share a commit. -/

end MachLib
