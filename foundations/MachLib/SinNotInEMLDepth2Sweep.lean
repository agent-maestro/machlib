import MachLib.Trig
import MachLib.EML
import MachLib.SinNotInEML
import MachLib.CosNotInEML
import MachLib.SinNotInEMLDepth2Partial

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

-- Row 3 cv t1 = .eml(.var, .const d1): deferred — needs cleaner cancellation
-- of (exp c1 - log d1) between two evaluation points where the t1 inner
-- variable is non-zero.

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

-- Remaining 5 cases deferred (require either log injectivity beyond the
-- positives covered above, or sharper exp(exp π) numerical bounds):
-- - Row 1: t1 = .var, t2 = .eml(.var, .const d)
-- - Row 3 cv: t1 = .eml(.var, .const d1), t2 = .eml(.const c, .var)
-- - Row 3 vc: t1 ∈ {.eml(.const c1, .var), .eml(.var, .const d1), .eml(.var, .var)},
--   t2 = .eml(.var, .const d) (3 cases)

end MachLib
