/-
MachLib.ForgeTest — RED/GREEN test suite for forge Phase D obligations.

Each theorem below is the shape forge's `_render_theorem` method emits
for a function with interval-bound refinements.  The proof bodies show
the progression from `sorry` (RED) to closed proofs via the new
`MachLib.Forge.Interval` lemma library (GREEN).

Theorem naming mirrors the forge convention:
  `<function_name>_spec`
-/

import MachLib.Forge

namespace MachLib
namespace Real

/-!
## T-01  halve_in_unit
The motivating example from the task brief.
  `noncomputable def halve (x : Real) : Real := x * 0.5`
  Refinement: `h_x : 0 ≤ x ∧ x ≤ 1`
  Goal:       `0 ≤ halve x ∧ halve x ≤ 1`
-/

noncomputable def halve (x : Real) : Real := x * (0.5 : Real)

-- RED skeleton: this is exactly what forge Phase D currently emits.
-- It type-checks (sorry is accepted) but leaves an open obligation.
theorem halve_in_unit_sorry (x : Real)
    (h_x : ((0 : Real) ≤ x) ∧ (x ≤ (1 : Real))) :
    ((0 : Real) ≤ halve x) ∧ (halve x ≤ (1 : Real)) := by
  unfold halve
  sorry

-- GREEN: closed via interval lemmas.
theorem halve_in_unit (x : Real)
    (h_x : ((0 : Real) ≤ x) ∧ (x ≤ (1 : Real))) :
    ((0 : Real) ≤ halve x) ∧ (halve x ≤ (1 : Real)) := by
  unfold halve
  exact interval_scale_unit_lit x (0.5 : Real)
    (by lit_pos)
    (interval_scale_unit_lit_le (by lit_pos) (by lit_pos))
    h_x.1 h_x.2

/-!
## T-02  double_upper_bound
  `noncomputable def double (x : Real) : Real := x * 2.0`
  Refinement: `h_x : 0 ≤ x ∧ x ≤ 1`
  Goal:       `0 ≤ double x ∧ double x ≤ 2.0`
-/

noncomputable def double (x : Real) : Real := x * (2.0 : Real)

-- GREEN: lower via interval_scale_lower, upper via interval_scale_upper + one_mul_thm.
theorem double_upper_bound (x : Real)
    (h_x : ((0 : Real) ≤ x) ∧ (x ≤ (1 : Real))) :
    ((0 : Real) ≤ double x) ∧ (double x ≤ (2.0 : Real)) := by
  unfold double
  constructor
  · exact interval_scale_lower x (2.0 : Real) (by lit_pos) h_x.1
  · -- interval_scale_upper gives x * 2.0 ≤ 1 * 2.0; simplify 1 * 2.0 = 2.0.
    have h := interval_scale_upper x (2.0 : Real) (1 : Real) (by lit_pos) h_x.2
    rwa [one_mul_thm] at h

/-!
## T-03  saturate
  `noncomputable def saturate (x : Real) : Real := max 0 (min x 1)`
  Goal: if `0 ≤ x ∧ x ≤ 1`, then `0 ≤ saturate x ∧ saturate x ≤ 1`.
-/

noncomputable def saturate (x : Real) : Real := max 0 (min x 1)

-- `saturate` maps any `x` into [0,1] unconditionally; the h_x hypothesis
-- is accepted (forge always emits it) but not needed by this proof.
theorem saturate_in_unit (x : Real)
    (_h_x : ((0 : Real) ≤ x) ∧ (x ≤ (1 : Real))) :
    ((0 : Real) ≤ saturate x) ∧ (saturate x ≤ (1 : Real)) := by
  unfold saturate
  constructor
  · -- max 0 _ ≥ 0: use max_nonneg_left with ha : 0 ≤ 0 (reflexivity).
    exact max_nonneg_left (le_refl 0)
  · -- max 0 (min x 1) ≤ 1: show both branches ≤ 1.
    -- Branch 0: 0 ≤ 1 (zero_lt_one_ax weakened).
    -- Branch min x 1: min x 1 ≤ 1 (min_le_right).
    unfold max
    by_cases h : (0 : Real) ≤ min x 1
    · rw [if_pos h]; exact min_le_right x 1
    · rw [if_neg h]; exact le_of_lt zero_lt_one_ax

/-!
## T-04  add_halves (two unit-interval inputs summed with half-weights)
  `noncomputable def add_halves (x y : Real) : Real := x * 0.5 + y * 0.5`
  Refinements: `h_x : 0 ≤ x ∧ x ≤ 1`, `h_y : 0 ≤ y ∧ y ≤ 1`
  Goal: `0 ≤ add_halves x y ∧ add_halves x y ≤ 1`
-/

noncomputable def add_halves (x y : Real) : Real :=
  x * (0.5 : Real) + y * (0.5 : Real)

theorem add_halves_in_unit (x y : Real)
    (h_x : ((0 : Real) ≤ x) ∧ (x ≤ (1 : Real)))
    (h_y : ((0 : Real) ≤ y) ∧ (y ≤ (1 : Real))) :
    ((0 : Real) ≤ add_halves x y) ∧ (add_halves x y ≤ (1 : Real)) := by
  unfold add_halves
  exact interval_add_scale x y
    (0.5 : Real) (0.5 : Real)
    (by lit_pos) (by lit_pos)
    (interval_scale_unit_lit_le (by lit_pos) (by lit_pos))
    (interval_scale_unit_lit_le (by lit_pos) (by lit_pos))
    h_x.1 h_x.2 h_y.1 h_y.2

/-!
## T-05  deficit (saturation deficit: 1 - x)
  `noncomputable def deficit (x : Real) : Real := 1 - x`
  Refinement: `h_x : 0 ≤ x ∧ x ≤ 1`
  Goal: `0 ≤ deficit x ∧ deficit x ≤ 1`
-/

noncomputable def deficit (x : Real) : Real := 1 - x

theorem deficit_in_unit (x : Real)
    (h_x : ((0 : Real) ≤ x) ∧ (x ≤ (1 : Real))) :
    ((0 : Real) ≤ deficit x) ∧ (deficit x ≤ (1 : Real)) := by
  unfold deficit
  exact interval_one_minus x h_x.1 h_x.2

/-!
## T-06  ratio (bounded division)
  `noncomputable def ratio (x d : Real) : Real := x / d`
  Refinements: `h_x : 0 ≤ x ∧ x ≤ 1`, `h_d : 1 ≤ d`
  Goal: `0 ≤ ratio x d ∧ ratio x d ≤ 1`
-/

noncomputable def ratio (x d : Real) : Real := x / d

theorem ratio_in_unit (x d : Real)
    (h_x : ((0 : Real) ≤ x) ∧ (x ≤ (1 : Real)))
    (h_d : (1 : Real) ≤ d) :
    ((0 : Real) ≤ ratio x d) ∧ (ratio x d ≤ (1 : Real)) := by
  unfold ratio
  have hd_pos : (0 : Real) < d := lt_of_lt_of_le zero_lt_one_ax h_d
  constructor
  · exact div_nonneg_of_nonneg_pos h_x.1 hd_pos
  · exact interval_div_unit x d hd_pos h_x.2 h_d

/-!
## T-07  nonneg_product
  `noncomputable def nonneg_prod (a b : Real) : Real := a * b`
  Refinements: `h_a : 0 ≤ a`, `h_b : 0 ≤ b`
  Goal: `0 ≤ nonneg_prod a b`
-/

noncomputable def nonneg_prod (a b : Real) : Real := a * b

theorem nonneg_product (a b : Real)
    (h_a : (0 : Real) ≤ a) (h_b : (0 : Real) ≤ b) :
    (0 : Real) ≤ nonneg_prod a b := by
  unfold nonneg_prod
  exact mul_nonneg h_a h_b

/-!
## T-08  interval_conjunction_extraction
Tests that raw conjunction hypotheses from forge can be destructured
and fed to lemmas individually.
-/

theorem interval_conjunction_extraction (x : Real)
    (h : ((0 : Real) ≤ x) ∧ (x ≤ (1 : Real))) :
    (0 : Real) ≤ x * (0.5 : Real) :=
  interval_scale_lower x (0.5 : Real) (by lit_pos) h.1

end Real
end MachLib
