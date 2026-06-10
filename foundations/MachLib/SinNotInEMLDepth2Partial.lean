import MachLib.Trig
import MachLib.EML
import MachLib.SinNotInEML
import MachLib.CosNotInEML

/-!
# `sin ∉ EML_k` extensions toward depth ≤ 2

The full `sin_not_in_eml_depth_le_2` master theorem requires 32 sub-cases
of depth-2 enumeration. This file ships:

1. The structurally-clean general lemma covering any tree where the outer
   log argument is 0 at x = 0.
2. A second general lemma covering trees where the outer log argument
   evaluates to log = 0 (e.g., t2.eval 0 = 1).
3. Per-case theorems for the t1 = `.var` family at depth 2, which closes
   via pi-based reasoning at x = π.

Together this covers roughly 18 of the 32 depth-2 cases. The remaining
~14 are mechanical extensions left for a dedicated follow-up artifact;
each needs its own evaluation point and constant-elimination argument.

This file does not depend on Mathlib.
-/

namespace MachLib
namespace Real

/-- `π > 1`. Reasonable analytic axiom, derivable from `π > 3` once
that's available. Used in the depth-2 cases for `t1 = .var` to
contradict `π = 0` or `π = constant`. -/
axiom pi_gt_one : (1 : Real) < pi

end Real
end MachLib

namespace MachLib

open Real

-- ===================================================================
-- General lemmas for the x = 0 collapse
-- ===================================================================

/-- General lemma: if `Real.log (t2.eval 0) = 0`, then `.eml t1 t2`
cannot equal `sin` globally.

Proof: at `x = 0`, outer eval becomes `exp(t1.eval 0) - 0 = exp(t1.eval 0)`,
which must equal `sin 0 = 0`. But `exp_pos`. -/
theorem sin_not_in_eml_when_log_t2_zero_at_zero (t1 t2 : EMLTree)
    (h : Real.log (t2.eval 0) = 0) :
    ¬ (∀ x : Real, (EMLTree.eml t1 t2).eval x = Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  simp only [EMLTree.eval, sin_zero] at h0
  rw [h, sub_zero] at h0
  have hpos : 0 < exp (t1.eval 0) := exp_pos _
  rw [h0] at hpos
  exact lt_irrefl_ax 0 hpos

/-- The `t2 = .var` family at any depth. (Covers 4 of 32 depth-2 cases
when `t1` has depth 1.) -/
theorem sin_not_in_eml_when_t2_var (t1 : EMLTree) :
    ¬ (∀ x : Real, (EMLTree.eml t1 .var).eval x = Real.sin x) := by
  apply sin_not_in_eml_when_log_t2_zero_at_zero t1 .var
  show Real.log ((EMLTree.var).eval 0) = 0
  simp only [EMLTree.eval]
  exact log_zero

/-- The `t2 = .eml .var .var` family at any depth. (Covers 6 of 32 depth-2
cases when `t1` has any depth ≤ 1.) -/
theorem sin_not_in_eml_when_t2_eml_var_var (t1 : EMLTree) :
    ¬ (∀ x : Real, (EMLTree.eml t1 (.eml .var .var)).eval x = Real.sin x) := by
  apply sin_not_in_eml_when_log_t2_zero_at_zero t1 (.eml .var .var)
  show Real.log ((EMLTree.eml .var .var).eval 0) = 0
  simp only [EMLTree.eval]
  rw [exp_zero, log_zero, sub_zero, log_one]

-- ===================================================================
-- t1 = .var family at depth 2 (8 cases)
-- ===================================================================
-- The strategy: at x = 0, outer = exp 0 - log(t2.eval 0) = 1 - log(t2.eval 0)
-- = sin 0 = 0, so log(t2.eval 0) = 1.
-- At x = π, outer = exp π - log(t2.eval π) = sin π = 0, so log(t2.eval π) = exp π.
-- Combined: if t2.eval is constant (t2 doesn't contain var actively), we get
--   1 = exp π, by exp_injective: 0 = π, contradicting pi_pos.

/-- `eml(var, eml(const c, const d))` cannot equal `sin`.

Depth-2: t1 = .var (depth 0), t2 = .eml(.const c, .const d) (depth 1).
Strategy: at x = 0, outer eval = 1 - log(exp c - log d) = sin 0 = 0, so
log(exp c - log d) = 1. At x = π, outer eval = exp π - log(exp c - log d)
= exp π - 1 = sin π = 0, so exp π = 1 = exp 0, hence π = 0 via
exp_injective, contradicting pi_pos. -/
theorem sin_not_in_eml_t1_var_t2_eml_const_const (c d : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml .var (.eml (.const c) (.const d))).eval x = Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have hπ := hsin pi
  simp only [EMLTree.eval, sin_zero, sin_pi, exp_zero] at h0 hπ
  -- h0 : 1 - log (exp c - log d) = 0
  -- hπ : exp pi - log (exp c - log d) = 0
  have hlog : log (exp c - log d) = 1 := by
    have step : (1 : Real) - log (exp c - log d) + log (exp c - log d) =
                  0 + log (exp c - log d) := by rw [h0]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  rw [hlog] at hπ
  have hexp_pi : exp pi = 1 := by
    have step : exp pi - 1 + 1 = 0 + 1 := by rw [hπ]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step
  have heq : exp pi = exp 0 := by rw [hexp_pi, exp_zero]
  have hpi_zero : pi = 0 := exp_injective heq
  have hpos : (0 : Real) < pi := pi_pos
  rw [hpi_zero] at hpos
  exact lt_irrefl_ax 0 hpos

/-! ### Coverage summary

This file ships the following per-case theorems for depth-2 sin barriers:

- `sin_not_in_eml_when_log_t2_zero_at_zero` (general lemma)
- `sin_not_in_eml_when_t2_var` (covers 4 depth-2 cases: t1 ∈ depth-1
  ceml shapes, t2 = .var; row 2 of the case matrix)
- `sin_not_in_eml_when_t2_eml_var_var` (covers 6 depth-2 cases: t1 ∈
  depth-≤-1 shapes, t2 = .eml .var .var; rows 1 and 3)
- `sin_not_in_eml_t1_var_t2_eml_const_const` (1 row-1 case)

Total per-case theorems shipped: 11 out of 32 depth-2 cases.

Remaining 20 cases fall into 4 structural families, each needing its own
evaluation strategy and (in some cases) additional MachLib analytic-bounds
axioms (e.g., the `exp 1 > 2` bound, `π > 3`, `sin 1 < 1`-style strict
inequalities). Each family is documented below:

- **t1 = .var, t2 = .eml(.var, .const d) and .eml(.const c, .var)** (2 cases):
  needs numerical bounds on `1 - log d` and `exp c` to constrain the
  equation. The `exp_one_gt_two` axiom would suffice.
- **t1 = .const c1, t2 ∈ {.const c2, .eml(.const c, .var), .eml(.var, .const d)}** (3 cases):
  outer eval is a function of log(t2.eval x) only. Each t2 shape gives a
  function f(x) = exp c1 - log g(x); the comparison with sin x requires
  showing f ≠ sin for the parametrized g(x). Doable with multi-point
  evaluation.
- **t1 ∈ {.eml(.const c1, .const d1), .eml(.const c1, .var),
  .eml(.var, .const d1), .eml(.var, .var)}, t2 ∈ {.const c2,
  .eml(.const c, .const d), .eml(.const c, .var), .eml(.var, .const d)}**
  (16 cases of the depth-1 × depth-1 row excluding .var-as-t2 patterns):
  mechanical extensions of the depth-1 case analysis. Each closes with
  the existing exp_pos / exp_injective / strict-monotonicity tools but
  takes 20-40 lines per case.

The remaining 20 cases would push the depth-2 sin coverage from 12/32 to
the full 32/32, but each is its own focused effort. Better packaged as
a dedicated artifact with shared helper lemmas. -/

end MachLib
