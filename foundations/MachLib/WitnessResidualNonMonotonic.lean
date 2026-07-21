import MachLib.WitnessResidualBoundedNonConstant

/-!
# Answering the open question: NOT every bounded, non-simple EML tree is monotonic

The previous file's counterexample was strictly monotonic — leaving open whether EVERY bounded,
non-constant, non-`RightChildrenSimplePositive` tree is similarly monotonic (which would close
the whole witness-finding residual via the cheap injectivity/periodicity argument). This file
answers that question: **NO.** Worked out on paper, checked numerically, then formalized — using
an EXACT algebraic sign characterization that needs no derivatives at all.

**The tree.** `T := eml var (eml (eml var (const 1)) (eml var (const 2)))` — depth 3, `T`'s right
child (`B`) has ITS OWN right child (`D = eml var (const 2)`) that genuinely CROSSES ZERO,
triggering `log`'s clamp. This clamp transition is exactly what breaks monotonicity: on one side
of it `T` is forced to the exact constant `0`; on the other side it is governed by a DIFFERENT
formula that dips negative before climbing positive.

**The exact sign characterization (no derivatives needed).** Write `x0 := log(log 2)` (where
`D` crosses zero) and, for `x > x0`, `v := exp(x) - log 2 > 0` (`D`'s own value). Then:
- `x ≤ x0` (the clamped region): `T.eval x = 0` EXACTLY (`log(exp(exp x)) = exp x` cancels
  against the leading term, via `log_exp` applied twice through the clamp).
- `x > x0`: `T.eval x > 0 ⟺ v > 1`, and `T.eval x < 0 ⟺ v < 1` — proved by applying `exp`
  (strictly increasing) to the candidate inequality and using `exp∘log = id`, exactly the same
  one-step trick used throughout this whole sub-arc, needing no calculus at all.

**The valley witness.** Three points: `x_a := x0` (`T = 0`), `x_b` with `v = 1/2` (`T < 0`),
`x_c` with `v = 2` (`T > 0`), `x_a < x_b < x_c`. `T(x_a) > T(x_b)` (a decrease) but
`T(x_b) < T(x_c)` (an increase) — `T` is neither monotonically increasing nor decreasing.
Numerically verified first (`T(x0)=0`, `T(x_b)≈-0.191`, `T(x_c)≈0.048`).

**What this settles.** The cheap injectivity/periodicity closure from the previous entry does
NOT generalize to the whole residual — some bounded, non-`RightChildrenSimplePositive` trees are
genuinely non-monotonic, so ruling them out (if possible at all) needs the heavier zero-counting
machinery this arc built earlier, not the free shortcut.

(Note: `Real` has no `OfNat` instance for bare numeral `2` — every constant here is written as
`(1+1 : Real)`, matching the established codebase convention.)
-/

namespace MachLib
namespace Real

/-- The concrete tree: `eml var (eml (eml var (const 1)) (eml var (const (1+1))))`. -/
noncomputable def nonMonotonicWitness : EMLTree :=
  EMLTree.eml EMLTree.var
    (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const 1))
      (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1))))

/-- The clamp boundary: where `D.eval x = exp x - log(1+1)` crosses zero. -/
noncomputable def nonMonotonicWitness_x0 : Real := Real.log (Real.log (1 + 1))

theorem nonMonotonicWitness_log2_pos : 0 < Real.log (1 + 1) :=
  log_pos_of_gt_one (by
    have h := add_lt_add_left zero_lt_one_ax (1 : Real)
    have e1 : (1 : Real) + 0 = 1 := add_zero _
    rwa [e1] at h)

/-- **Clamped region**: for `x ≤ x0`, `T.eval x = 0` exactly. -/
theorem nonMonotonicWitness_eval_clamped {x : Real} (hx : x ≤ nonMonotonicWitness_x0) :
    nonMonotonicWitness.eval x = 0 := by
  have hlog2pos := nonMonotonicWitness_log2_pos
  have hDnonpos : Real.exp x - Real.log (1 + 1) ≤ 0 := by
    rcases (le_iff_lt_or_eq x nonMonotonicWitness_x0).mp hx with h | h
    · have hexp : Real.exp x < Real.exp nonMonotonicWitness_x0 := Real.exp_lt h
      have hexp0 : Real.exp nonMonotonicWitness_x0 = Real.log (1 + 1) :=
        Real.exp_log hlog2pos
      rw [hexp0] at hexp
      have e := sub_lt_sub_right_of_lt (r := Real.log (1 + 1)) hexp
      have e2 : Real.log (1 + 1) - Real.log (1 + 1) = 0 := by mach_ring
      rw [e2] at e
      exact le_of_lt e
    · rw [h]
      have hexp0 : Real.exp nonMonotonicWitness_x0 = Real.log (1 + 1) := Real.exp_log hlog2pos
      have e : Real.exp nonMonotonicWitness_x0 - Real.log (1 + 1) = 0 := by
        rw [hexp0]; mach_ring
      exact le_of_eq e
  show Real.exp x -
      Real.log (Real.exp ((EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x)
        - Real.log ((EMLTree.eml EMLTree.var (EMLTree.const (1 + 1))).eval x)) = 0
  have hC : (EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x = Real.exp x - Real.log 1 := rfl
  have hD : (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1))).eval x
      = Real.exp x - Real.log (1 + 1) := rfl
  rw [hC, hD, log_one]
  have e1 : Real.exp x - 0 = Real.exp x := sub_zero _
  rw [e1, Real.log_nonpos hDnonpos, sub_zero, log_exp]
  mach_ring

/-- **Real-branch region**: for `x > x0`, unfolds to the two-level nested formula. -/
theorem nonMonotonicWitness_eval_real {x : Real} (hx : nonMonotonicWitness_x0 < x) :
    nonMonotonicWitness.eval x
      = Real.exp x
        - Real.log (Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log (1 + 1))) := by
  show Real.exp x -
      Real.log (Real.exp ((EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x)
        - Real.log ((EMLTree.eml EMLTree.var (EMLTree.const (1 + 1))).eval x)) = _
  have hC : (EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x = Real.exp x - Real.log 1 := rfl
  have hD : (EMLTree.eml EMLTree.var (EMLTree.const (1 + 1))).eval x
      = Real.exp x - Real.log (1 + 1) := rfl
  rw [hC, hD, log_one]
  have e1 : Real.exp x - 0 = Real.exp x := sub_zero _
  rw [e1]

/-- `D.eval x = exp x - log(1+1)` is positive on the real-branch region — the well-definedness
fact needed to keep the whole formula in `log`'s real branch. -/
theorem nonMonotonicWitness_Dpos {x : Real} (hx : nonMonotonicWitness_x0 < x) :
    0 < Real.exp x - Real.log (1 + 1) := by
  have hlog2pos := nonMonotonicWitness_log2_pos
  have hexp0 : Real.exp nonMonotonicWitness_x0 = Real.log (1 + 1) := Real.exp_log hlog2pos
  have hexp : Real.exp nonMonotonicWitness_x0 < Real.exp x := Real.exp_lt hx
  rw [hexp0] at hexp
  have e := sub_lt_sub_right_of_lt (r := Real.log (1 + 1)) hexp
  have e2 : Real.log (1 + 1) - Real.log (1 + 1) = 0 := by mach_ring
  rwa [e2] at e

/-- `B.eval x = exp(exp x) - log(D.eval x)` is positive on the real-branch region. Case-free:
`D.eval x < exp x` (subtracting a positive amount), so `log(D.eval x) < x` (`log_lt_log`); then
`x < exp x < exp(exp x)` (`exp_grows_strictly_thm` twice); chaining gives `log(D.eval x) <
exp(exp x)` directly. -/
theorem nonMonotonicWitness_Bpos {x : Real} (hx : nonMonotonicWitness_x0 < x) :
    0 < Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log (1 + 1)) := by
  have hDpos := nonMonotonicWitness_Dpos hx
  have hlog2pos := nonMonotonicWitness_log2_pos
  have hDltExp : Real.exp x - Real.log (1 + 1) < Real.exp x := by
    have h := add_lt_add_left (neg_neg_of_pos hlog2pos) (Real.exp x)
    have e1 : Real.exp x + -Real.log (1 + 1) = Real.exp x - Real.log (1 + 1) := by mach_ring
    have e2 : Real.exp x + 0 = Real.exp x := add_zero _
    rwa [e1, e2] at h
  have hlogD : Real.log (Real.exp x - Real.log (1 + 1)) < x := by
    have h := log_lt_log hDpos hDltExp
    rwa [log_exp] at h
  have hx_lt_expx : x < Real.exp x := exp_grows_strictly_thm x
  have hexpx_lt_expexpx : Real.exp x < Real.exp (Real.exp x) := exp_grows_strictly_thm (Real.exp x)
  have hchain : Real.log (Real.exp x - Real.log (1 + 1)) < Real.exp (Real.exp x) :=
    lt_trans_ax hlogD (lt_trans_ax hx_lt_expx hexpx_lt_expexpx)
  have e := sub_lt_sub_right_of_lt (r := Real.log (Real.exp x - Real.log (1 + 1))) hchain
  have e2 : Real.log (Real.exp x - Real.log (1 + 1)) - Real.log (Real.exp x - Real.log (1 + 1))
      = 0 := by mach_ring
  rwa [e2] at e

/-- **`v > 1 ⟹ T.eval x > 0`.** `v > 1` gives `log v > 0`, so `B.eval x = exp(exp x) - log v <
exp(exp x)`, so `log(B.eval x) < log(exp(exp x)) = exp x` (`log_lt_log`), so `T.eval x = exp x -
log(B.eval x) > 0`. No calculus needed. -/
theorem nonMonotonicWitness_pos_of_gt_one {x : Real} (hx : nonMonotonicWitness_x0 < x)
    (hv : 1 < Real.exp x - Real.log (1 + 1)) :
    0 < nonMonotonicWitness.eval x := by
  rw [nonMonotonicWitness_eval_real hx]
  have hBpos := nonMonotonicWitness_Bpos hx
  have hvpos : 0 < Real.log (Real.exp x - Real.log (1 + 1)) := log_pos_of_gt_one hv
  have hBlt : Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log (1 + 1))
      < Real.exp (Real.exp x) := by
    have h := add_lt_add_left (neg_neg_of_pos hvpos) (Real.exp (Real.exp x))
    have e1 : Real.exp (Real.exp x) + -Real.log (Real.exp x - Real.log (1 + 1))
        = Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log (1 + 1)) := by mach_ring
    have e2 : Real.exp (Real.exp x) + 0 = Real.exp (Real.exp x) := add_zero _
    rwa [e1, e2] at h
  have hlogB := log_lt_log hBpos hBlt
  rw [log_exp] at hlogB
  have e := sub_lt_sub_right_of_lt (r := Real.log (Real.exp (Real.exp x)
    - Real.log (Real.exp x - Real.log (1 + 1)))) hlogB
  have e2 : Real.log (Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log (1 + 1)))
      - Real.log (Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log (1 + 1))) = 0 := by
    mach_ring
  rwa [e2] at e

/-- **`0 < v < 1 ⟹ T.eval x < 0`.** `v < 1` gives `log v < 0`, so `B.eval x = exp(exp x) - log v
> exp(exp x)`, so `log(B.eval x) > log(exp(exp x)) = exp x` (`log_lt_log`), so `T.eval x = exp x -
log(B.eval x) < 0`. -/
theorem nonMonotonicWitness_neg_of_lt_one {x : Real} (hx : nonMonotonicWitness_x0 < x)
    (hv0 : 0 < Real.exp x - Real.log (1 + 1)) (hv1 : Real.exp x - Real.log (1 + 1) < 1) :
    nonMonotonicWitness.eval x < 0 := by
  rw [nonMonotonicWitness_eval_real hx]
  have hBpos := nonMonotonicWitness_Bpos hx
  have hvneg : Real.log (Real.exp x - Real.log (1 + 1)) < 0 := log_neg_of_lt_one hv0 hv1
  have hBgt : Real.exp (Real.exp x)
      < Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log (1 + 1)) := by
    have h := sub_lt_sub_left_local (Real.exp (Real.exp x)) hvneg
    have e : Real.exp (Real.exp x) - 0 = Real.exp (Real.exp x) := sub_zero _
    rwa [e] at h
  have hlogB := log_lt_log (Real.exp_pos _) hBgt
  rw [log_exp] at hlogB
  have e := sub_lt_sub_right_of_lt (r := Real.log (Real.exp (Real.exp x)
    - Real.log (Real.exp x - Real.log (1 + 1)))) hlogB
  have e2 : Real.log (Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log (1 + 1)))
      - Real.log (Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log (1 + 1))) = 0 := by
    mach_ring
  rwa [e2] at e

/-- `(X + Y) - X = Y`. `mach_ring` does not close this reliably even for bare free variables
(confirmed by isolated test) — proved manually via basic additive axioms instead, matching the
established workaround pattern for this class of `mach_ring` gap. -/
theorem add_sub_cancel_left_local (X Y : Real) : (X + Y) - X = Y := by
  rw [sub_def, add_comm X Y, add_assoc, add_neg, add_zero]

theorem one_lt_one_add_one : (1 : Real) < 1 + 1 := by
  have h := add_lt_add_left zero_lt_one_ax (1 : Real)
  have e1 : (1 : Real) + 0 = 1 := add_zero _
  rwa [e1] at h

theorem zero_lt_one_add_one : (0 : Real) < 1 + 1 := lt_trans_ax zero_lt_one_ax one_lt_one_add_one

/-- The three witness points: `x_a := x0` (`T=0`), `x_b` with `D.eval x_b = 1/(1+1)` (`T<0`),
`x_c` with `D.eval x_c = 1+1` (`T>0`). -/
noncomputable def nonMonotonicWitness_xb : Real :=
  Real.log (Real.log (1 + 1) + 1 / (1 + 1))

noncomputable def nonMonotonicWitness_xc : Real := Real.log (Real.log (1 + 1) + (1 + 1))

theorem nonMonotonicWitness_half_pos : (0 : Real) < 1 / (1 + 1) :=
  one_div_pos_of_pos zero_lt_one_add_one

theorem nonMonotonicWitness_half_lt_one : (1 : Real) / (1 + 1) < 1 :=
  div_lt_one_of_pos_lt zero_lt_one_add_one one_lt_one_add_one

theorem nonMonotonicWitness_xb_exp :
    Real.exp nonMonotonicWitness_xb = Real.log (1 + 1) + 1 / (1 + 1) := by
  have hlog2pos := nonMonotonicWitness_log2_pos
  apply Real.exp_log
  have h := add_lt_add_left nonMonotonicWitness_half_pos (Real.log (1 + 1))
  have e1 : Real.log (1 + 1) + 0 = Real.log (1 + 1) := add_zero _
  exact lt_trans_ax hlog2pos (by rwa [e1] at h)

theorem nonMonotonicWitness_xc_exp :
    Real.exp nonMonotonicWitness_xc = Real.log (1 + 1) + (1 + 1) := by
  have hlog2pos := nonMonotonicWitness_log2_pos
  apply Real.exp_log
  have h := add_lt_add_left zero_lt_one_add_one (Real.log (1 + 1))
  have e1 : Real.log (1 + 1) + 0 = Real.log (1 + 1) := add_zero _
  exact lt_trans_ax hlog2pos (by rwa [e1] at h)

theorem nonMonotonicWitness_x0_lt_xb : nonMonotonicWitness_x0 < nonMonotonicWitness_xb := by
  have hlog2pos := nonMonotonicWitness_log2_pos
  have hd : Real.log (1 + 1) < Real.log (1 + 1) + 1 / (1 + 1) := by
    have h := add_lt_add_left nonMonotonicWitness_half_pos (Real.log (1 + 1))
    have e1 : Real.log (1 + 1) + 0 = Real.log (1 + 1) := add_zero _
    rwa [e1] at h
  exact log_lt_log hlog2pos hd

theorem nonMonotonicWitness_xb_lt_xc : nonMonotonicWitness_xb < nonMonotonicWitness_xc := by
  have hlog2pos := nonMonotonicWitness_log2_pos
  have hbpos : 0 < Real.log (1 + 1) + 1 / (1 + 1) := by
    have h := add_lt_add_left nonMonotonicWitness_half_pos (Real.log (1 + 1))
    have e1 : Real.log (1 + 1) + 0 = Real.log (1 + 1) := add_zero _
    exact lt_trans_ax hlog2pos (by rwa [e1] at h)
  have hd : Real.log (1 + 1) + 1 / (1 + 1) < Real.log (1 + 1) + (1 + 1) := by
    have hhalf_lt_two : (1 : Real) / (1 + 1) < 1 + 1 :=
      lt_trans_ax nonMonotonicWitness_half_lt_one one_lt_one_add_one
    exact add_lt_add_left hhalf_lt_two (Real.log (1 + 1))
  exact log_lt_log hbpos hd

/-- `D.eval x_b = 1/(1+1)`. -/
theorem nonMonotonicWitness_D_xb :
    Real.exp nonMonotonicWitness_xb - Real.log (1 + 1) = 1 / (1 + 1) := by
  rw [nonMonotonicWitness_xb_exp]
  exact add_sub_cancel_left_local _ _

/-- `D.eval x_c = 1+1`. -/
theorem nonMonotonicWitness_D_xc :
    Real.exp nonMonotonicWitness_xc - Real.log (1 + 1) = 1 + 1 := by
  rw [nonMonotonicWitness_xc_exp]
  exact add_sub_cancel_left_local _ _

/-- **The main result: `nonMonotonicWitness` is monotonic in NEITHER direction.** Three points
`x_a < x_b < x_c`: `T(x_a) = 0`, `T(x_b) < 0` (a decrease from `a` to `b`, despite `a < b`), and
`T(x_b) < T(x_c)` (an increase from `b` to `c`) — refuting monotone-increasing (via `a`,`b`) and
monotone-decreasing (via `b`,`c`) simultaneously. -/
theorem nonMonotonicWitness_not_monotone :
    ¬ (∀ x y : Real, x < y → nonMonotonicWitness.eval x ≤ nonMonotonicWitness.eval y) ∧
    ¬ (∀ x y : Real, x < y → nonMonotonicWitness.eval y ≤ nonMonotonicWitness.eval x) := by
  have hTa : nonMonotonicWitness.eval nonMonotonicWitness_x0 = 0 :=
    nonMonotonicWitness_eval_clamped (le_refl _)
  have hTb : nonMonotonicWitness.eval nonMonotonicWitness_xb < 0 :=
    nonMonotonicWitness_neg_of_lt_one nonMonotonicWitness_x0_lt_xb
      (by rw [nonMonotonicWitness_D_xb]; exact nonMonotonicWitness_half_pos)
      (by rw [nonMonotonicWitness_D_xb]; exact nonMonotonicWitness_half_lt_one)
  have hxc_gt_x0 : nonMonotonicWitness_x0 < nonMonotonicWitness_xc :=
    lt_trans_ax nonMonotonicWitness_x0_lt_xb nonMonotonicWitness_xb_lt_xc
  have hTc : 0 < nonMonotonicWitness.eval nonMonotonicWitness_xc :=
    nonMonotonicWitness_pos_of_gt_one hxc_gt_x0
      (by rw [nonMonotonicWitness_D_xc]; exact one_lt_one_add_one)
  constructor
  · intro hmono
    have h := hmono nonMonotonicWitness_x0 nonMonotonicWitness_xb nonMonotonicWitness_x0_lt_xb
    rw [hTa] at h
    exact lt_irrefl_ax _ (lt_of_lt_of_le hTb h)
  · intro hanti
    have h := hanti nonMonotonicWitness_xb nonMonotonicWitness_xc nonMonotonicWitness_xb_lt_xc
    exact lt_irrefl_ax _ (lt_trans_ax hTc (lt_of_le_of_lt h hTb))

/-! ## Boundedness — closing the loop so the counterexample is airtight

`nonMonotonicWitness_not_monotone` alone shows this tree is non-monotonic, but for it to actually
answer "is every BOUNDED such tree monotonic," it must also be shown BOUNDED. -/

theorem add_sub_cancel_right_local (X Y : Real) : (X + Y) - Y = X := by
  rw [sub_def, add_assoc, add_neg, add_zero]

theorem add_sub_cancel_left_local2 (a b : Real) : b + (a - b) = a := by
  rw [sub_def, ← add_assoc, add_comm b a, add_assoc, add_neg, add_zero]

theorem sub_self_sub_local (a b : Real) : a - (a - b) = b := by
  have h1 : b + (a - b) = a := add_sub_cancel_left_local2 a b
  have h2 : (b + (a - b)) - (a - b) = b := add_sub_cancel_right_local b (a - b)
  rwa [h1] at h2

theorem two_mul_eq_add_self (E : Real) : (1 + 1) * E = E + E := by
  rw [mul_comm, mul_distrib, mul_one_ax]

/-- **Uniform upper bound**: `T.eval x < log(1+1)` for `x > x0` (and `T.eval x = 0 < log(1+1)`
for `x ≤ x0`, giving a bound on ALL of `ℝ`). Chain: `log D < D` (`log_lt_self_of_pos`, `D :=
exp x - log(1+1)`) gives `exp(exp x) - D < exp(exp x) - log D`; separately, `exp(exp x) =
(1+1)·exp D` (`exp_add` + `exp_log`) combined with `D < exp D` (`exp_grows_strictly_thm`) gives
`exp D < exp(exp x) - D`; chaining the two gives `exp D < exp(exp x) - log D`, hence (`log_lt_log`
+ `log_exp`) `D < log(exp(exp x) - log D)`, hence `T.eval x = exp x - log(exp(exp x)-log D) <
exp x - D = log(1+1)`. No calculus, no transcendental critical point — a UNIFORM bound across all
`x`, not asymptotic. -/
theorem nonMonotonicWitness_upper_bound {x : Real} (hx : nonMonotonicWitness_x0 < x) :
    nonMonotonicWitness.eval x < Real.log (1 + 1) := by
  rw [nonMonotonicWitness_eval_real hx]
  have hDpos := nonMonotonicWitness_Dpos hx
  have hA : Real.log (Real.exp x - Real.log (1 + 1)) < Real.exp x - Real.log (1 + 1) :=
    log_lt_self_of_pos _ hDpos
  have hB : Real.exp (Real.exp x) - (Real.exp x - Real.log (1 + 1))
      < Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log (1 + 1)) :=
    sub_lt_sub_left_local _ hA
  have hC1 : Real.log (1 + 1) + (Real.exp x - Real.log (1 + 1)) = Real.exp x :=
    add_sub_cancel_left_local2 (Real.exp x) (Real.log (1 + 1))
  have hC2 : Real.exp (Real.exp x)
      = Real.exp (Real.log (1 + 1)) * Real.exp (Real.exp x - Real.log (1 + 1)) := by
    have step := exp_add (Real.log (1 + 1)) (Real.exp x - Real.log (1 + 1))
    rwa [hC1] at step
  have hC3 : Real.exp (Real.log (1 + 1)) = 1 + 1 := Real.exp_log zero_lt_one_add_one
  rw [hC3] at hC2
  have hE : Real.exp x - Real.log (1 + 1) < Real.exp (Real.exp x - Real.log (1 + 1)) :=
    exp_grows_strictly_thm (Real.exp x - Real.log (1 + 1))
  have hF : Real.exp (Real.exp x - Real.log (1 + 1)) + Real.exp (Real.exp x - Real.log (1 + 1))
        - Real.exp (Real.exp x - Real.log (1 + 1))
      < Real.exp (Real.exp x - Real.log (1 + 1)) + Real.exp (Real.exp x - Real.log (1 + 1))
        - (Real.exp x - Real.log (1 + 1)) :=
    sub_lt_sub_left_local _ hE
  have hF2 : Real.exp (Real.exp x - Real.log (1 + 1))
      < Real.exp (Real.exp x - Real.log (1 + 1)) + Real.exp (Real.exp x - Real.log (1 + 1))
        - (Real.exp x - Real.log (1 + 1)) := by
    rwa [add_sub_cancel_left_local] at hF
  have hG : Real.exp (Real.exp x - Real.log (1 + 1))
      < Real.exp (Real.exp x) - (Real.exp x - Real.log (1 + 1)) := by
    rw [hC2, two_mul_eq_add_self]
    exact hF2
  have hH : Real.exp (Real.exp x - Real.log (1 + 1))
      < Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log (1 + 1)) :=
    lt_trans_ax hG hB
  have hI : Real.exp x - Real.log (1 + 1)
      < Real.log (Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log (1 + 1))) := by
    have h := log_lt_log (Real.exp_pos (Real.exp x - Real.log (1 + 1))) hH
    rwa [log_exp] at h
  have hJ : Real.exp x
        - Real.log (Real.exp (Real.exp x) - Real.log (Real.exp x - Real.log (1 + 1)))
      < Real.exp x - (Real.exp x - Real.log (1 + 1)) :=
    sub_lt_sub_left_local _ hI
  have hK : Real.exp x - (Real.exp x - Real.log (1 + 1)) = Real.log (1 + 1) :=
    sub_self_sub_local (Real.exp x) (Real.log (1 + 1))
  rwa [hK] at hJ

/-- **The counterexample, packaged.** `nonMonotonicWitness` is bounded above by `log(1+1)`
EVERYWHERE, and monotonic in NEITHER direction — a genuine, fully verified answer to "is every
bounded, non-`RightChildrenSimplePositive` EML tree monotonic": NO. -/
theorem bounded_nonmonotonic_eml_tree_exists :
    (∀ x, nonMonotonicWitness.eval x < Real.log (1 + 1)) ∧
    ¬ (∀ x y : Real, x < y → nonMonotonicWitness.eval x ≤ nonMonotonicWitness.eval y) ∧
    ¬ (∀ x y : Real, x < y → nonMonotonicWitness.eval y ≤ nonMonotonicWitness.eval x) := by
  refine ⟨fun x => ?_, nonMonotonicWitness_not_monotone.1, nonMonotonicWitness_not_monotone.2⟩
  rcases lt_total nonMonotonicWitness_x0 x with h | h | h
  · exact nonMonotonicWitness_upper_bound h
  · rw [nonMonotonicWitness_eval_clamped (le_of_eq h.symm)]
    exact nonMonotonicWitness_log2_pos
  · rw [nonMonotonicWitness_eval_clamped (le_of_lt h)]
    exact nonMonotonicWitness_log2_pos

end Real
end MachLib
