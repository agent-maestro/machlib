import MachLib.Trig
import MachLib.EML
import MachLib.SinNotInEML
import MachLib.CosNotInEML
import MachLib.SinNotInEMLDepth2Partial
import MachLib.Ring

/-!
# Depth-2 sin barrier sweep — infrastructure + per-case theorems

Adds numerical-bounds + sin-positivity infrastructure to MachLib, then
sweeps the depth-2 sin barrier cases that close cleanly with it.

No Mathlib dependency. Zero-Mathlib gate stays PASS.
-/

namespace MachLib
namespace Real

/-- Taylor lower bound: `1 + x < exp x` for `x > 0`. -/
axiom exp_gt_one_plus_self : ∀ x : Real, 0 < x → 1 + x < exp x

/-- `log x < x` for `x > 0`. Standard log < self bound. -/
axiom log_lt_self_of_pos : ∀ x : Real, 0 < x → log x < x

/-- `0 < sin 1`. Follows from `sin_pos_on_open_zero_pi` (0 < 1 < π). -/
axiom sin_one_pos : (0 : Real) < sin 1

/-- `exp x > 2x` for all real `x`. Stronger than `exp_gt_one_plus_self`,
needed to close cases where two-point evaluation forces
`exp(exp π) - exp π = exp 1 - 1`. Standard fact: `f(x) = exp x - 2x` has
`f(log 2) = 2 - 2 log 2 > 0` as its minimum (convex function), so `f > 0`
everywhere. -/
axiom exp_gt_two_x : ∀ x : Real, (1 + 1) * x < exp x

/-- `exp 1 > 1 + 1`. Direct corollary. -/
theorem exp_one_gt_two : (1 + 1 : Real) < exp 1 :=
  exp_gt_one_plus_self 1 zero_lt_one_ax

/-- `log` is injective on positive reals. From `exp_log` (both sides). -/
theorem log_injective_pos {x y : Real}
    (hx : 0 < x) (hy : 0 < y) (h : log x = log y) : x = y := by
  have hex : exp (log x) = x := exp_log hx
  have hey : exp (log y) = y := exp_log hy
  rw [h] at hex
  exact hex.symm.trans hey

/-- `log y > 0 → y > 0`. Contrapositive of MachLib's `log` convention
(`y ≤ 0 → log y = 0`). -/
theorem log_pos_arg_pos {y : Real} (h : 0 < log y) : 0 < y := by
  rcases lt_total 0 y with hlt | heq | hgt
  · exact hlt
  · -- y = 0, log 0 = 0 by convention, so 0 < 0 → contradiction.
    rw [← heq] at h
    have : log 0 = 0 := by
      unfold log
      exact dif_neg (lt_irrefl_ax 0)
    rw [this] at h
    exact (lt_irrefl_ax 0 h).elim
  · -- y < 0, log y = 0 by convention.
    have hne_pos : ¬ (0 < y) := fun hy => lt_irrefl_ax 0 (lt_trans_ax hy hgt)
    have hlog_zero : log y = 0 := by
      unfold log
      exact dif_neg hne_pos
    rw [hlog_zero] at h
    exact (lt_irrefl_ax 0 h).elim

end Real
end MachLib

namespace MachLib

open Real

-- ===================================================================
-- Shared helper: cancel a common constant subtrahend between two
-- equations.
-- ===================================================================

/-- If `a - k = 0` and `b - k = 0`, then `a = b`. -/
private theorem cancel_const_sub {a b k : Real}
    (h0 : a - k = 0) (h1 : b - k = 0) : a = b := by
  have step : a + (-k) = b + (-k) := by
    rw [← sub_def, ← sub_def]
    exact h0.trans h1.symm
  calc a = a + (-k) + k := by rw [add_assoc, neg_add_self, add_zero]
    _ = b + (-k) + k := by rw [step]
    _ = b := by rw [add_assoc, neg_add_self, add_zero]


-- ===================================================================
-- Row 2: t1 = depth-1 ceml shape, t2 = .const c2 (4 cases)
-- ===================================================================

/-- Row 2: t1 = `.eml(.const c1, .const d1)`, t2 = `.const c2`. Constant. -/
theorem sin_not_in_eml_t1_cc_t2_const (c1 d1 c2 : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml (.const c1) (.const d1)) (.const c2)).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have h1 := hsin (pi / (1 + 1))
  simp only [EMLTree.eval, sin_zero, sin_pi_div_two] at h0 h1
  rw [h0] at h1
  exact zero_ne_one_ax h1

/-- Row 2: t1 = `.eml(.const c1, .var)`, t2 = `.const c2`. -/
theorem sin_not_in_eml_t1_cv_t2_const (c1 c2 : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml (.const c1) .var) (.const c2)).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have h1 := hsin 1
  simp only [EMLTree.eval, sin_zero, log_zero, log_one, sub_zero] at h0 h1
  rw [h0] at h1
  -- h1 : 0 = sin 1
  have hpos : (0 : Real) < sin 1 := sin_one_pos
  rw [← h1] at hpos
  exact lt_irrefl_ax 0 hpos

/-- Row 2: t1 = `.eml(.var, .const d1)`, t2 = `.const c2`. -/
theorem sin_not_in_eml_t1_vc_t2_const (d1 c2 : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml .var (.const d1)) (.const c2)).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have hπ := hsin pi
  simp only [EMLTree.eval, sin_zero, sin_pi, exp_zero] at h0 hπ
  -- h0 : exp(1 - log d1) - log c2 = 0
  -- hπ : exp(exp pi - log d1) - log c2 = 0
  have heq : exp (1 - log d1) = exp (exp pi - log d1) :=
    cancel_const_sub h0 hπ
  have hsubeq : (1 : Real) - log d1 = exp pi - log d1 := exp_injective heq
  -- Cancel -log d1: 1 = exp pi.
  have hone : (1 : Real) = exp pi := by
    have step : (1 - log d1) + log d1 = (exp pi - log d1) + log d1 := by
      rw [hsubeq]
    rw [sub_def, add_assoc, neg_add_self, add_zero,
        sub_def, add_assoc, neg_add_self, add_zero] at step
    exact step
  -- exp 0 = 1 = exp pi → 0 = pi.
  have hexp_eq : exp 0 = exp pi := by rw [exp_zero]; exact hone
  have hpi_zero : (0 : Real) = pi := exp_injective hexp_eq
  have hpos : (0 : Real) < pi := pi_pos
  rw [← hpi_zero] at hpos
  exact lt_irrefl_ax 0 hpos

/-- Row 2: t1 = `.eml(.var, .var)`, t2 = `.const c2`. Uses
`exp_gt_one_plus_self` + `log_lt_self_of_pos`. -/
theorem sin_not_in_eml_t1_vv_t2_const (c2 : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml .var .var) (.const c2)).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have hπ := hsin pi
  simp only [EMLTree.eval, sin_zero, sin_pi, exp_zero, log_zero, sub_zero] at h0 hπ
  -- h0 : exp 1 - log c2 = 0
  -- hπ : exp(exp pi - log pi) - log c2 = 0
  have heq : exp 1 = exp (exp pi - log pi) :=
    cancel_const_sub h0 hπ
  have hsubeq : (1 : Real) = exp pi - log pi := exp_injective heq
  -- Rearrange: exp pi = 1 + log pi.
  have hexp_pi_eq : exp pi = 1 + log pi := by
    have step : (1 : Real) + log pi = (exp pi - log pi) + log pi := by
      rw [← hsubeq]
    rw [sub_def, add_assoc, neg_add_self, add_zero] at step
    exact step.symm
  -- log pi < pi, so 1 + log pi < 1 + pi, so exp pi < 1 + pi.
  have hB : log pi < pi := log_lt_self_of_pos pi pi_pos
  have hlt1 : (1 : Real) + log pi < 1 + pi := add_lt_add_left hB 1
  rw [← hexp_pi_eq] at hlt1
  -- hlt1 : exp pi < 1 + pi
  -- But exp pi > 1 + pi.
  have hA : (1 : Real) + pi < exp pi := exp_gt_one_plus_self pi pi_pos
  exact lt_irrefl_ax _ (lt_trans_ax hlt1 hA)

-- ===================================================================
-- Row 1: t1 = const or var (depth 0), t2 = depth-1 ceml shape
-- The two t2 = .eml(.var, .var) cases are covered by the prior file's
-- corollary. The t2 = .eml(.const, .const) case for t1 = .var is also
-- prior. Remaining: 5 cases (we close 4 here).
-- ===================================================================

/-- Row 1: t1 = `.const c1`, t2 = `.eml(.const c, .const d)`. Constant. -/
theorem sin_not_in_eml_t1_const_t2_eml_cc (c1 c d : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.const c1) (.eml (.const c) (.const d))).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have h1 := hsin (pi / (1 + 1))
  simp only [EMLTree.eval, sin_zero, sin_pi_div_two] at h0 h1
  rw [h0] at h1
  exact zero_ne_one_ax h1

/-- Row 1: t1 = `.const c1`, t2 = `.eml(.const c, .var)`. -/
theorem sin_not_in_eml_t1_const_t2_eml_cv (c1 c : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.const c1) (.eml (.const c) .var)).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have h1 := hsin 1
  simp only [EMLTree.eval, sin_zero, log_zero, log_one, sub_zero, log_exp] at h0 h1
  -- h0 : exp c1 - c = 0
  -- h1 : exp c1 - c = sin 1
  rw [h0] at h1
  have hpos : (0 : Real) < sin 1 := sin_one_pos
  rw [← h1] at hpos
  exact lt_irrefl_ax 0 hpos

/-- Row 1: t1 = `.var`, t2 = `.eml(.const c, .var)`. Uses
`exp_one_gt_two`. -/
theorem sin_not_in_eml_t1_var_t2_eml_cv (c : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml .var (.eml (.const c) .var)).eval x = Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have h1 := hsin 1
  simp only [EMLTree.eval, sin_zero, exp_zero, log_zero, log_one, sub_zero,
             log_exp] at h0 h1
  -- h0 : 1 - c = 0
  -- h1 : exp 1 - c = sin 1
  have hc : c = 1 := by
    have step : (1 : Real) - c + c = 0 + c := by rw [h0]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  rw [hc] at h1
  -- h1 : exp 1 - 1 = sin 1
  -- exp 1 > 2, so exp 1 - 1 > 1
  have hgt : (1 : Real) < exp 1 - 1 := by
    have hA : (1 + 1 : Real) < exp 1 := exp_one_gt_two
    have step := add_lt_add_left hA (-1)
    -- step : -1 + (1 + 1) < -1 + exp 1
    rw [← add_assoc, neg_add_self, zero_add,
        add_comm (-1 : Real) (exp 1), ← sub_def] at step
    exact step
  have hsin_le : sin 1 ≤ 1 := sin_le_one 1
  rw [h1] at hgt
  exact lt_irrefl_ax _ (lt_of_lt_of_le hgt hsin_le)

/-- Row 1: t1 = `.const c1`, t2 = `.eml(.var, .const d)`. Uses
`log_injective_pos`. -/
theorem sin_not_in_eml_t1_const_t2_eml_vc (c1 d : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.const c1) (.eml .var (.const d))).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have hπ := hsin pi
  simp only [EMLTree.eval, sin_zero, sin_pi, exp_zero] at h0 hπ
  -- h0 : exp c1 - log(1 - log d) = 0
  -- hπ : exp c1 - log(exp pi - log d) = 0
  -- Derive log(1 - log d) = log(exp pi - log d) = exp c1.
  have hlog_eq_lhs : exp c1 = log (1 - log d) := by
    have step : exp c1 - log (1 - log d) + log (1 - log d) =
                  0 + log (1 - log d) := by rw [h0]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step
  have hlog_eq_rhs : exp c1 = log (exp pi - log d) := by
    have step : exp c1 - log (exp pi - log d) + log (exp pi - log d) =
                  0 + log (exp pi - log d) := by rw [hπ]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step
  have hexp_c1_pos : 0 < exp c1 := exp_pos c1
  -- log(1 - log d) > 0 → 1 - log d > 0
  have hlhs_pos : (0 : Real) < 1 - log d := by
    apply log_pos_arg_pos
    rw [← hlog_eq_lhs]; exact hexp_c1_pos
  have hrhs_pos : (0 : Real) < exp pi - log d := by
    apply log_pos_arg_pos
    rw [← hlog_eq_rhs]; exact hexp_c1_pos
  -- Apply log injectivity: 1 - log d = exp pi - log d.
  have hlog_eq : log (1 - log d) = log (exp pi - log d) :=
    hlog_eq_lhs.symm.trans hlog_eq_rhs
  have hsub_eq : (1 : Real) - log d = exp pi - log d :=
    log_injective_pos hlhs_pos hrhs_pos hlog_eq
  -- Cancel -log d: 1 = exp pi.
  have hone : (1 : Real) = exp pi := by
    have step : (1 - log d) + log d = (exp pi - log d) + log d := by
      rw [hsub_eq]
    rw [sub_def, add_assoc, neg_add_self, add_zero,
        sub_def, add_assoc, neg_add_self, add_zero] at step
    exact step
  -- exp 0 = 1 = exp pi → 0 = pi.
  have hexp_eq : exp 0 = exp pi := by rw [exp_zero]; exact hone
  have hpi_zero : (0 : Real) = pi := exp_injective hexp_eq
  have hpos : (0 : Real) < pi := pi_pos
  rw [← hpi_zero] at hpos
  exact lt_irrefl_ax 0 hpos

-- Row 1 cases deferred:
-- - t1 = .const c1, t2 = .eml(.var, .const d): needs log-injectivity-on-positives
--   infrastructure not yet in MachLib. The argument: from exp c1 - log(...) = 0
--   at two points, derive log of both inner args are equal, hence (via log
--   injectivity on positives) the inner args are equal, hence exp π = 1 hence
--   π = 0. Deferred to a dedicated log-injectivity artifact.
-- - t1 = .var, t2 = .eml(.var, .const d): same shape with extra exp on the
--   outer t1, deferred for the same reason.

-- ===================================================================
-- Row 3: t2 = .eml(.const c, .const d) family (4 cases)
-- t2.eval is constant; outer eval is same shape as Row 2.
-- ===================================================================

/-- Row 3: t1 = `.eml(.const c1, .const d1)`, t2 = `.eml(.const c, .const d)`.
Both subtrees constant; eval is constant. -/
theorem sin_not_in_eml_t1_cc_t2_eml_cc (c1 d1 c d : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml (.const c1) (.const d1))
                     (.eml (.const c) (.const d))).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have h1 := hsin (pi / (1 + 1))
  simp only [EMLTree.eval, sin_zero, sin_pi_div_two] at h0 h1
  rw [h0] at h1
  exact zero_ne_one_ax h1

/-- Row 3: t1 = `.eml(.const c1, .var)`, t2 = `.eml(.const c, .const d)`. -/
theorem sin_not_in_eml_t1_cv_t2_eml_cc (c1 c d : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml (.const c1) .var)
                     (.eml (.const c) (.const d))).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have h1 := hsin 1
  simp only [EMLTree.eval, sin_zero, log_zero, log_one, sub_zero] at h0 h1
  rw [h0] at h1
  have hpos : (0 : Real) < sin 1 := sin_one_pos
  rw [← h1] at hpos
  exact lt_irrefl_ax 0 hpos

/-- Row 3: t1 = `.eml(.var, .const d1)`, t2 = `.eml(.const c, .const d)`. -/
theorem sin_not_in_eml_t1_vc_t2_eml_cc (d1 c d : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml .var (.const d1))
                     (.eml (.const c) (.const d))).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have hπ := hsin pi
  simp only [EMLTree.eval, sin_zero, sin_pi, exp_zero] at h0 hπ
  have heq : exp (1 - log d1) = exp (exp pi - log d1) :=
    cancel_const_sub h0 hπ
  have hsubeq : (1 : Real) - log d1 = exp pi - log d1 := exp_injective heq
  have hone : (1 : Real) = exp pi := by
    have step : (1 - log d1) + log d1 = (exp pi - log d1) + log d1 := by
      rw [hsubeq]
    rw [sub_def, add_assoc, neg_add_self, add_zero,
        sub_def, add_assoc, neg_add_self, add_zero] at step
    exact step
  have hexp_eq : exp 0 = exp pi := by rw [exp_zero]; exact hone
  have hpi_zero : (0 : Real) = pi := exp_injective hexp_eq
  have hpos : (0 : Real) < pi := pi_pos
  rw [← hpi_zero] at hpos
  exact lt_irrefl_ax 0 hpos

/-- Row 3: t1 = `.eml(.var, .var)`, t2 = `.eml(.const c, .const d)`. -/
theorem sin_not_in_eml_t1_vv_t2_eml_cc (c d : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml .var .var)
                     (.eml (.const c) (.const d))).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have hπ := hsin pi
  simp only [EMLTree.eval, sin_zero, sin_pi, exp_zero, log_zero, sub_zero] at h0 hπ
  have heq : exp 1 = exp (exp pi - log pi) :=
    cancel_const_sub h0 hπ
  have hsubeq : (1 : Real) = exp pi - log pi := exp_injective heq
  have hexp_pi_eq : exp pi = 1 + log pi := by
    have step : (1 : Real) + log pi = (exp pi - log pi) + log pi := by
      rw [← hsubeq]
    rw [sub_def, add_assoc, neg_add_self, add_zero] at step
    exact step.symm
  have hB : log pi < pi := log_lt_self_of_pos pi pi_pos
  have hlt1 : (1 : Real) + log pi < 1 + pi := add_lt_add_left hB 1
  rw [← hexp_pi_eq] at hlt1
  have hA : (1 : Real) + pi < exp pi := exp_gt_one_plus_self pi pi_pos
  exact lt_irrefl_ax _ (lt_trans_ax hlt1 hA)

-- ===================================================================
-- Row 3: t2 = .eml(.const c, .var) family (3 of 4 cases)
-- t2.eval x = exp c - log x. At x=0 and x=1, log 0 = log 1 = 0, so
-- t2.eval(0) = t2.eval(1) = exp c. Same argument as Row 2 cv:
-- log(exp c) = c, eval at 0 and 1 both yield exp(t1.eval(0/1)) - c.
-- For most t1, t1.eval(0) = t1.eval(1), giving sin 0 = 0 ≠ sin 1.
-- ===================================================================

/-- Row 3 cv: t1 = `.eml(.const c1, .const d1)`, t2 = `.eml(.const c, .var)`. -/
theorem sin_not_in_eml_t1_cc_t2_eml_cv (c1 d1 c : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml (.const c1) (.const d1))
                     (.eml (.const c) .var)).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have h1 := hsin 1
  simp only [EMLTree.eval, sin_zero, log_zero, log_one, sub_zero, log_exp] at h0 h1
  -- h0 : exp(exp c1 - log d1) - c = 0
  -- h1 : exp(exp c1 - log d1) - c = sin 1
  rw [h0] at h1
  have hpos : (0 : Real) < sin 1 := sin_one_pos
  rw [← h1] at hpos
  exact lt_irrefl_ax 0 hpos

/-- Row 3 cv: t1 = `.eml(.const c1, .var)`, t2 = `.eml(.const c, .var)`. -/
theorem sin_not_in_eml_t1_cv_t2_eml_cv (c1 c : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml (.const c1) .var)
                     (.eml (.const c) .var)).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have h1 := hsin 1
  simp only [EMLTree.eval, sin_zero, log_zero, log_one, sub_zero, log_exp] at h0 h1
  -- h0 : exp(exp c1) - c = 0
  -- h1 : exp(exp c1) - c = sin 1
  rw [h0] at h1
  have hpos : (0 : Real) < sin 1 := sin_one_pos
  rw [← h1] at hpos
  exact lt_irrefl_ax 0 hpos

/-- Row 3 cv: t1 = `.eml(.var, .var)`, t2 = `.eml(.const c, .var)`. Uses
the strict exp(exp 1) > 1 + exp 1 bound. -/
theorem sin_not_in_eml_t1_vv_t2_eml_cv (c : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml .var .var)
                     (.eml (.const c) .var)).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have h1 := hsin 1
  simp only [EMLTree.eval, sin_zero, exp_zero, log_zero, log_one, sub_zero,
             log_exp] at h0 h1
  -- h0 : exp 1 - c = 0
  -- h1 : exp(exp 1) - c = sin 1
  -- From h0: c = exp 1. Then h1: exp(exp 1) - exp 1 = sin 1.
  -- But exp(exp 1) > 1 + exp 1 (Taylor), so exp(exp 1) - exp 1 > 1 ≥ sin 1.
  have hc : c = exp 1 := by
    have step : exp 1 - c + c = 0 + c := by rw [h0]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  rw [hc] at h1
  -- h1 : exp(exp 1) - exp 1 = sin 1
  -- exp(exp 1) > 1 + exp 1
  have hexp_pos : (0 : Real) < exp 1 := exp_pos 1
  have hA : 1 + exp 1 < exp (exp 1) := exp_gt_one_plus_self (exp 1) hexp_pos
  -- exp(exp 1) - exp 1 > 1:
  --   1 + exp 1 < exp(exp 1), so exp(exp 1) - exp 1 > 1
  have hgt1 : (1 : Real) < exp (exp 1) - exp 1 := by
    -- exp(exp 1) - exp 1 = exp(exp 1) + (-exp 1)
    -- 1 + exp 1 < exp(exp 1)
    -- 1 + exp 1 + (-exp 1) < exp(exp 1) + (-exp 1)
    -- 1 < exp(exp 1) - exp 1
    have step := add_lt_add_left hA (-exp 1)
    -- step : -exp 1 + (1 + exp 1) < -exp 1 + exp(exp 1)
    rw [← add_assoc, add_comm (-exp 1) 1, add_assoc, neg_add_self, add_zero] at step
    -- step : 1 < -exp 1 + exp(exp 1)
    rw [add_comm (-exp 1) (exp (exp 1)), ← sub_def] at step
    exact step
  -- sin 1 ≤ 1
  have hsin_le : sin 1 ≤ 1 := sin_le_one 1
  -- So exp(exp 1) - exp 1 > 1 ≥ sin 1, but h1 says they're equal.
  rw [h1] at hgt1
  -- hgt1 : 1 < sin 1
  exact lt_irrefl_ax _ (lt_of_lt_of_le hgt1 hsin_le)

/-- Row 3 cv vc: t1 = `.eml(.var, .const d1)`, t2 = `.eml(.const c, .var)`.
Closure via the chain `exp(exp(1 - log d1)) - log π = exp(exp(exp π - log d1))`
derived from (E0) and (Eπ), plus `exp π > 1` ⇒ contradiction with
`log π > 0`. -/
theorem sin_not_in_eml_t1_vc_t2_eml_cv (d1 c : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml .var (.const d1)) (.eml (.const c) .var)).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have hπ := hsin pi
  simp only [EMLTree.eval, sin_zero, sin_pi, exp_zero, log_zero, sub_zero] at h0 hπ
  rw [log_exp] at h0
  -- h0 : exp(1 - log d1) - c = 0
  have hc_eq : c = exp (1 - log d1) := by
    have step : exp (1 - log d1) - c + c = 0 + c := by rw [h0]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  -- hπ : exp(exp pi - log d1) - log(exp c - log pi) = 0
  have hπ_log : log (exp c - log pi) = exp (exp pi - log d1) := by
    have step : exp (exp pi - log d1) - log (exp c - log pi) + log (exp c - log pi) =
                  0 + log (exp c - log pi) := by rw [hπ]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  -- log of (exp c - log pi) is exp(...) > 0, so by log_pos_arg_pos, arg > 0.
  have hsub_pos : 0 < exp c - log pi := by
    apply log_pos_arg_pos
    rw [hπ_log]; exact exp_pos _
  -- Apply exp_log: exp c - log pi = exp(exp(exp pi - log d1)).
  have hπ_eq : exp c - log pi = exp (exp (exp pi - log d1)) := by
    have h : exp (log (exp c - log pi)) = exp (exp (exp pi - log d1)) := by rw [hπ_log]
    rw [exp_log hsub_pos] at h
    exact h
  -- Substitute c = exp(1 - log d1) into exp c:
  rw [hc_eq] at hπ_eq
  -- hπ_eq : exp(exp(1 - log d1)) - log pi = exp(exp(exp pi - log d1))
  -- Show 1 - log d1 < exp pi - log d1, hence (via exp twice) the RHS > exp(exp(1 - log d1)).
  have hexp_pi_gt_one : (1 : Real) < exp pi := by
    have step : exp 0 < exp pi := exp_lt pi_pos
    rw [exp_zero] at step
    exact step
  have h_step1 : 1 - log d1 < exp pi - log d1 := by
    have step := add_lt_add_left hexp_pi_gt_one (-log d1)
    rw [add_comm (-log d1) 1, add_comm (-log d1) (exp pi), ← sub_def, ← sub_def] at step
    exact step
  have h_step2 : exp (1 - log d1) < exp (exp pi - log d1) := exp_lt h_step1
  have h_step3 : exp (exp (1 - log d1)) < exp (exp (exp pi - log d1)) := exp_lt h_step2
  -- log pi > 0 from pi > 1.
  have hlog_pi_pos : 0 < log pi := by
    have step : log 1 < log pi := log_lt_log zero_lt_one_ax pi_gt_one
    rw [log_one] at step
    exact step
  -- Hence A - log pi < A (where A = exp(exp(1 - log d1))).
  have hsub_lt : exp (exp (1 - log d1)) - log pi < exp (exp (1 - log d1)) := by
    have hneg : -log pi < 0 := by
      have step1 := add_lt_add_left hlog_pi_pos (-log pi)
      rw [add_zero, neg_add_self] at step1
      exact step1
    have step := add_lt_add_left hneg (exp (exp (1 - log d1)))
    rw [add_zero, ← sub_def] at step
    exact step
  -- Rewrite h_step3 via hπ_eq to get A < A - log pi.
  rw [← hπ_eq] at h_step3
  -- h_step3 : A < A - log pi; hsub_lt : A - log pi < A. Transitive contradiction.
  exact lt_irrefl_ax _ (lt_trans_ax h_step3 hsub_lt)

/-- Row 3 vc family: t1 = `.eml(.const c1, .const d1)`, t2 = `.eml(.var, .const d)`.
Uses `log_injective_pos`. -/
theorem sin_not_in_eml_t1_cc_t2_eml_vc (c1 d1 d : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml (.const c1) (.const d1))
                     (.eml .var (.const d))).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have hπ := hsin pi
  simp only [EMLTree.eval, sin_zero, sin_pi, exp_zero] at h0 hπ
  -- h0 : exp(exp c1 - log d1) - log(1 - log d) = 0
  -- hπ : exp(exp c1 - log d1) - log(exp pi - log d) = 0
  -- Both = exp(exp c1 - log d1).
  have hlog_eq_lhs : exp (exp c1 - log d1) = log (1 - log d) := by
    have step : exp (exp c1 - log d1) - log (1 - log d) + log (1 - log d) =
                  0 + log (1 - log d) := by rw [h0]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step
  have hlog_eq_rhs : exp (exp c1 - log d1) = log (exp pi - log d) := by
    have step : exp (exp c1 - log d1) - log (exp pi - log d) +
                  log (exp pi - log d) =
                  0 + log (exp pi - log d) := by rw [hπ]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step
  have hexp_pos : 0 < exp (exp c1 - log d1) := exp_pos _
  have hlhs_pos : (0 : Real) < 1 - log d := by
    apply log_pos_arg_pos
    rw [← hlog_eq_lhs]; exact hexp_pos
  have hrhs_pos : (0 : Real) < exp pi - log d := by
    apply log_pos_arg_pos
    rw [← hlog_eq_rhs]; exact hexp_pos
  have hlog_eq : log (1 - log d) = log (exp pi - log d) :=
    hlog_eq_lhs.symm.trans hlog_eq_rhs
  have hsub_eq : (1 : Real) - log d = exp pi - log d :=
    log_injective_pos hlhs_pos hrhs_pos hlog_eq
  have hone : (1 : Real) = exp pi := by
    have step : (1 - log d) + log d = (exp pi - log d) + log d := by
      rw [hsub_eq]
    rw [sub_def, add_assoc, neg_add_self, add_zero,
        sub_def, add_assoc, neg_add_self, add_zero] at step
    exact step
  have hexp_eq : exp 0 = exp pi := by rw [exp_zero]; exact hone
  have hpi_zero : (0 : Real) = pi := exp_injective hexp_eq
  have hpos : (0 : Real) < pi := pi_pos
  rw [← hpi_zero] at hpos
  exact lt_irrefl_ax 0 hpos

/-- Row 1: t1 = `.var`, t2 = `.eml(.var, .const d)`. Closure via the
key equation `exp(exp π) - exp 1 = exp π - 1` (derived by cancelling
`log d` between the two evaluation points) plus `exp_gt_two_x` for
the strict inequality. Uses `MachLib.Ring`'s `neg_add` and
`neg_neg_helper` for the algebraic cancellation. -/
theorem sin_not_in_eml_t1_var_t2_eml_vc (d : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml .var (.eml .var (.const d))).eval x = Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have hπ := hsin pi
  simp only [EMLTree.eval, sin_zero, sin_pi, exp_zero] at h0 hπ
  -- h0 : 1 - log(1 - log d) = 0
  -- hπ : exp pi - log(exp pi - log d) = 0
  -- Extract log values.
  have hlog0 : log (1 - log d) = 1 := by
    have step : 1 - log (1 - log d) + log (1 - log d) =
                  0 + log (1 - log d) := by rw [h0]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  have hlogπ : log (exp pi - log d) = exp pi := by
    have step : exp pi - log (exp pi - log d) + log (exp pi - log d) =
                  0 + log (exp pi - log d) := by rw [hπ]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  -- Extract positivity via log_pos_arg_pos.
  have hpos0 : 0 < 1 - log d := by
    apply log_pos_arg_pos; rw [hlog0]; exact zero_lt_one_ax
  have hposπ : 0 < exp pi - log d := by
    apply log_pos_arg_pos; rw [hlogπ]; exact exp_pos pi
  -- Apply exp_log.
  have hA : 1 - log d = exp 1 := by
    have : exp (log (1 - log d)) = exp 1 := by rw [hlog0]
    rw [exp_log hpos0] at this; exact this
  have hB : exp pi - log d = exp (exp pi) := by
    have : exp (log (exp pi - log d)) = exp (exp pi) := by rw [hlogπ]
    rw [exp_log hposπ] at this; exact this
  -- Key equation: exp(exp pi) - exp 1 = exp pi - 1. Derived by
  -- (exp pi - log d) - (1 - log d) = exp pi - 1 [algebraic cancellation].
  have hkey : exp (exp pi) - exp 1 = exp pi - 1 := by
    rw [← hB, ← hA]
    -- goal: (exp pi - log d) - (1 - log d) = exp pi - 1
    rw [sub_def, sub_def, sub_def, neg_add, neg_neg_helper,
        add_assoc, ← add_assoc (-log d) (-1) (log d),
        add_comm (-log d) (-1),
        add_assoc (-1) (-log d) (log d), neg_add_self, add_zero,
        ← sub_def]
  -- Now derive contradiction via exp_gt_two_x.
  -- 2 * exp pi < exp(exp pi).
  have hexp_gt : (1 + 1) * exp pi < exp (exp pi) := exp_gt_two_x (exp pi)
  -- 2 * exp pi - exp 1 < exp(exp pi) - exp 1.
  have hC1 : (1 + 1) * exp pi - exp 1 < exp (exp pi) - exp 1 := by
    have step := add_lt_add_left hexp_gt (-exp 1)
    rw [add_comm (-exp 1) ((1+1) * exp pi), add_comm (-exp 1) (exp (exp pi)),
        ← sub_def, ← sub_def] at step
    exact step
  -- Substitute hkey: 2 * exp pi - exp 1 < exp pi - 1.
  rw [hkey] at hC1
  -- Derive: exp pi - 1 < (1+1) * exp pi - exp 1.
  -- Equivalent: -1 < exp pi - exp 1 (since (1+1) * exp pi - exp 1 = exp pi + (exp pi - exp 1)).
  -- exp pi - exp 1 > 0 from exp_lt(pi_gt_one), and -1 < 0.
  have hpi_gt_exp1 : exp 1 < exp pi := exp_lt pi_gt_one
  have hsub_pos : 0 < exp pi - exp 1 := by
    have step := add_lt_add_left hpi_gt_exp1 (-exp 1)
    rw [neg_add_self, add_comm (-exp 1) (exp pi), ← sub_def] at step
    exact step
  have hneg_one_neg : (-1 : Real) < 0 := by
    have step := add_lt_add_left zero_lt_one_ax (-1)
    rw [add_zero, neg_add_self] at step
    exact step
  have hneg_one_lt_sub : (-1 : Real) < exp pi - exp 1 :=
    lt_trans_ax hneg_one_neg hsub_pos
  have h_two_pi_eq : (1 + 1) * exp pi - exp 1 = exp pi + (exp pi - exp 1) := by
    rw [mul_comm, mul_distrib, mul_one_ax, sub_def, sub_def, add_assoc]
  have h2pi_gt : exp pi - 1 < (1 + 1) * exp pi - exp 1 := by
    rw [h_two_pi_eq]
    have step := add_lt_add_left hneg_one_lt_sub (exp pi)
    rw [← sub_def] at step
    exact step
  exact lt_irrefl_ax _ (lt_trans_ax h2pi_gt hC1)

/-- Row 3 cv vc: t1 = `.eml(.const c1, .var)`, t2 = `.eml(.var, .const d)`.
Uses sign argument: LHS positive (exp π - 1 > 0), RHS negative
(exp(exp(exp c1) / π) - exp(exp(exp c1)) < 0 since exp c1 - log π <
exp c1). -/
theorem sin_not_in_eml_t1_cv_t2_eml_vc (c1 d : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml (.const c1) .var) (.eml .var (.const d))).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have hπ := hsin pi
  simp only [EMLTree.eval, sin_zero, sin_pi, exp_zero, log_zero, sub_zero] at h0 hπ
  -- h0 : exp(exp c1) - log(1 - log d) = 0
  -- hπ : exp(exp c1 - log pi) - log(exp pi - log d) = 0
  -- Strategy: derive exp pi - log d < 1 - log d, then cancel -log d to
  -- get exp pi < 1, contradicting exp pi > 1.
  have hlog_lhs_eq : log (1 - log d) = exp (exp c1) := by
    have step : exp (exp c1) - log (1 - log d) + log (1 - log d) =
                  0 + log (1 - log d) := by rw [h0]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  have hlog_rhs_eq : log (exp pi - log d) = exp (exp c1 - log pi) := by
    have step : exp (exp c1 - log pi) - log (exp pi - log d) + log (exp pi - log d) =
                  0 + log (exp pi - log d) := by rw [hπ]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  have hpos1 : 0 < 1 - log d := by
    apply log_pos_arg_pos
    rw [hlog_lhs_eq]; exact exp_pos _
  have hpos_pi : 0 < exp pi - log d := by
    apply log_pos_arg_pos
    rw [hlog_rhs_eq]; exact exp_pos _
  have hone_minus : 1 - log d = exp (exp (exp c1)) := by
    have step : exp (log (1 - log d)) = exp (exp (exp c1)) := by rw [hlog_lhs_eq]
    rw [exp_log hpos1] at step
    exact step
  have hexp_minus : exp pi - log d = exp (exp (exp c1 - log pi)) := by
    have step : exp (log (exp pi - log d)) = exp (exp (exp c1 - log pi)) := by
      rw [hlog_rhs_eq]
    rw [exp_log hpos_pi] at step
    exact step
  -- log pi > 0 from pi > 1:
  have hlog_pi_pos : 0 < log pi := by
    have step : log 1 < log pi := log_lt_log zero_lt_one_ax pi_gt_one
    rw [log_one] at step
    exact step
  -- exp c1 - log pi < exp c1 (since log pi > 0):
  have hsubexp : exp c1 - log pi < exp c1 := by
    have hneg : -log pi < 0 := by
      have step := add_lt_add_left hlog_pi_pos (-log pi)
      rw [add_zero, neg_add_self] at step
      exact step
    have step := add_lt_add_left hneg (exp c1)
    rw [add_zero, ← sub_def] at step
    exact step
  -- Hence exp(exp c1 - log pi) < exp(exp c1):
  have hexp_sub : exp (exp c1 - log pi) < exp (exp c1) := exp_lt hsubexp
  -- And exp(exp(exp c1 - log pi)) < exp(exp(exp c1)):
  have hdouble_exp : exp (exp (exp c1 - log pi)) < exp (exp (exp c1)) := exp_lt hexp_sub
  -- Substitute via hone_minus and hexp_minus: exp pi - log d < 1 - log d.
  rw [← hexp_minus, ← hone_minus] at hdouble_exp
  -- Cancel -log d via add_lt_add_left + comm:
  have hcanc : exp pi < 1 := by
    have step : log d + (exp pi - log d) < log d + (1 - log d) :=
      add_lt_add_left hdouble_exp (log d)
    -- Simplify both sides: log d + (a - log d) = a.
    rw [sub_def, sub_def, ← add_assoc, ← add_assoc,
        add_comm (log d) (exp pi), add_comm (log d) 1,
        add_assoc, add_assoc, add_neg, add_zero, add_zero] at step
    exact step
  -- exp pi > 1 from pi > 0:
  have hpi_pos : 0 < pi := pi_pos
  have hexp_pi_gt_one : (1 : Real) < exp pi := by
    have step : exp 0 < exp pi := exp_lt hpi_pos
    rw [exp_zero] at step
    exact step
  exact lt_irrefl_ax _ (lt_trans_ax hcanc hexp_pi_gt_one)

-- ===================================================================
-- Helpers for the final case (Row 3 vc-vc).
-- ===================================================================

/-- `log y < y - 1` for `1 < y`. Derived from `exp_gt_one_plus_self`. -/
private theorem log_lt_sub_one_helper {y : Real} (hy : 1 < y) : log y < y - 1 := by
  have hpos : (0 : Real) < y := lt_trans_ax zero_lt_one_ax hy
  have hlog_pos : (0 : Real) < log y := by
    have step : log 1 < log y := log_lt_log zero_lt_one_ax hy
    rw [log_one] at step
    exact step
  have h := exp_gt_one_plus_self (log y) hlog_pos
  rw [exp_log hpos] at h
  -- h : 1 + log y < y
  -- Goal: log y < y - 1.
  -- log y + 1 = 1 + log y < y, so log y < y - 1.
  have step1 : log y + 1 < y := by rw [add_comm] at h; exact h
  have step2 := add_lt_add_left step1 (-1)
  -- step2 : -1 + (log y + 1) < -1 + y
  -- Simplify LHS: -1 + (log y + 1) = log y + (-1 + 1) = log y + 0 = log y (via comm + assoc + neg_add_self).
  rw [← add_assoc, add_comm (-1) (log y), add_assoc, neg_add_self,
      add_zero, add_comm (-1) y, ← sub_def] at step2
  exact step2

/-- `log 2 < 1`, where `2 = 1 + 1`. Derived from `exp_one_gt_two`. -/
private theorem log_two_lt_one_helper : log ((1 : Real) + 1) < 1 := by
  have h2_pos : (0 : Real) < 1 + 1 := by
    have step := add_lt_add_left zero_lt_one_ax 1
    rw [add_zero] at step
    exact lt_trans_ax zero_lt_one_ax step
  have step : log (1 + 1) < log (exp 1) := log_lt_log h2_pos exp_one_gt_two
  rw [log_exp] at step
  exact step

/-- Multiplicative monotonicity: `0 < c → a < b → c * a < c * b`.
Derived from `mul_pos` + algebra. -/
private theorem mul_lt_mul_left_helper {c : Real} (hc : 0 < c) {a b : Real}
    (h : a < b) : c * a < c * b := by
  -- b - a > 0.
  have hba_pos : (0 : Real) < b - a := by
    have step := add_lt_add_left h (-a)
    rw [neg_add_self, add_comm (-a) b, ← sub_def] at step
    exact step
  -- c * (b - a) > 0.
  have hprod : (0 : Real) < c * (b - a) := mul_pos hc hba_pos
  -- c * (b - a) = c * b - c * a (distributivity).
  have hdistr : c * (b - a) = c * b - c * a := by
    have e1 : (b - a) = b + -a := sub_def _ _
    have e2 : c * b - c * a = c * b + -(c * a) := sub_def _ _
    rw [e1, e2, mul_distrib, mul_neg]
  rw [hdistr] at hprod
  -- hprod : 0 < c * b - c * a.
  -- Hence c * a < c * b.
  have step := add_lt_add_left hprod (c * a)
  rw [add_zero] at step
  -- step : c * a < c * a + (c * b - c * a).
  -- Simplify RHS: c * a + (c * b - c * a) = c * b.
  have heq : c * a + (c * b - c * a) = c * b := by
    have e3 : c * b - c * a = c * b + -(c * a) := sub_def _ _
    rw [e3, ← add_assoc, add_comm (c * a) (c * b), add_assoc, add_neg, add_zero]
  rw [heq] at step
  exact step

/-- `a ≤ 0 → log a = 0` (MachLib convention). -/
private theorem log_of_nonpos {a : Real} (ha : ¬ (0 < a)) : log a = 0 := by
  unfold log
  exact dif_neg ha

/-- Mean-value lower bound: `exp(a) * (b - a) < exp(b) - exp(a)` for `a < b`. -/
private theorem exp_sub_exp_gt_helper {a b : Real} (hab : a < b) :
    exp a * (b - a) < exp b - exp a := by
  have hba_pos : (0 : Real) < b - a := by
    have step := add_lt_add_left hab (-a)
    rw [neg_add_self, add_comm (-a) b, ← sub_def] at step
    exact step
  have h1 : 1 + (b - a) < exp (b - a) := exp_gt_one_plus_self _ hba_pos
  have hexp_a_pos : (0 : Real) < exp a := exp_pos _
  -- Multiply by exp a.
  have h2 : exp a * (1 + (b - a)) < exp a * exp (b - a) :=
    mul_lt_mul_left_helper hexp_a_pos h1
  -- exp a * exp (b - a) = exp b.
  have hcomb : exp a * exp (b - a) = exp b := by
    rw [← exp_add]
    congr 1
    rw [sub_def, ← add_assoc, add_comm a b, add_assoc, add_neg, add_zero]
  rw [hcomb] at h2
  -- h2 : exp a * (1 + (b - a)) < exp b.
  -- exp a * (1 + (b - a)) = exp a + exp a * (b - a).
  have heq2 : exp a * (1 + (b - a)) = exp a + exp a * (b - a) := by
    rw [mul_distrib, mul_one_ax]
  rw [heq2] at h2
  -- h2 : exp a + exp a * (b - a) < exp b.
  -- Subtract exp a from both sides.
  have step := add_lt_add_left h2 (-exp a)
  rw [← add_assoc, neg_add_self, zero_add, add_comm (-exp a) (exp b), ← sub_def] at step
  exact step

end MachLib
