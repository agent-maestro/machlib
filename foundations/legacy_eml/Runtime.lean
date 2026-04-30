-- MonogateEML/Runtime.lean
--
-- Lean correspondence for the C / Rust libmonogate runtime
-- (D:/monogate-forge/software/runtime/c/libmonogate.h).
--
-- For each `mg_*` operator emitted by the Forge backends, this
-- file declares the mathematical Lean function it computes, and
-- proves the algebraic identity vs Mathlib's `Real.*` namespace.
--
-- The C runtime is a finite-precision implementation of these
-- definitions; precision-loss bounds proved in
-- `MonogateEML/UpperBounds.lean` translate from `ℝ` to f64
-- via the standard libm ULP guarantees (assumed as axioms).
--
-- Everything here is `noncomputable` because it bottoms out on
-- `Real.exp` / `Real.log` -- those are noncomputable in Mathlib.
-- The C / Rust runtime is what you call to actually evaluate;
-- this file specifies WHAT it computes, not HOW.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MonogateEML.Runtime

noncomputable section

-- ═════════════════════════════════════════════════════════════
-- Section 1 — Core EML primitive + 9 family operators
-- ═════════════════════════════════════════════════════════════

/-- `mg_eml(x, y) = exp(x) - log(y)`. Domain: `y > 0`. -/
def mg_eml (x y : ℝ) : ℝ := Real.exp x - Real.log y

/-- `mg_eal(x, y) = exp(x) + log(y)`. -/
def mg_eal (x y : ℝ) : ℝ := Real.exp x + Real.log y

/-- `mg_exl(x, y) = exp(x) * log(y)`. -/
def mg_exl (x y : ℝ) : ℝ := Real.exp x * Real.log y

/-- `mg_edl(x, y) = exp(x) / log(y)`. Domain: `y > 0, y ≠ 1`. -/
def mg_edl (x y : ℝ) : ℝ := Real.exp x / Real.log y

/-- `mg_epl(x, y) = exp(x) ^ log(y)`. -/
def mg_epl (x y : ℝ) : ℝ := (Real.exp x) ^ (Real.log y)

/-- `mg_lediv(x, y) = log(exp(x) / y)`. -/
def mg_lediv (x y : ℝ) : ℝ := Real.log (Real.exp x / y)

/-- `mg_elsb(x, y) = exp(x - log(y))`. Equals `exp(x) / y` when `y > 0`. -/
def mg_elsb (x y : ℝ) : ℝ := Real.exp (x - Real.log y)

/-- `mg_elad(x, y) = exp(log(x) + y)`. Equals `x * exp(y)` when `x > 0`. -/
def mg_elad (x y : ℝ) : ℝ := Real.exp (Real.log x + y)

/-- `mg_deml(x, y) = exp(-x) - log(y)`. -/
def mg_deml (x y : ℝ) : ℝ := Real.exp (-x) - Real.log y

theorem mg_eml_def (x y : ℝ) : mg_eml x y = Real.exp x - Real.log y := rfl
theorem mg_eal_def (x y : ℝ) : mg_eal x y = Real.exp x + Real.log y := rfl
theorem mg_exl_def (x y : ℝ) : mg_exl x y = Real.exp x * Real.log y := rfl
theorem mg_deml_def (x y : ℝ) : mg_deml x y = Real.exp (-x) - Real.log y := rfl

/-- `mg_elsb x y = exp x / y` on the runtime's stated domain `y > 0`. -/
theorem mg_elsb_eq_div_of_pos (x y : ℝ) (hy : 0 < y) :
    mg_elsb x y = Real.exp x / y := by
  unfold mg_elsb
  rw [Real.exp_sub, Real.exp_log hy]

/-- `mg_elad x y = x * exp y` on the runtime's stated domain `x > 0`. -/
theorem mg_elad_eq_mul_of_pos (x y : ℝ) (hx : 0 < x) :
    mg_elad x y = x * Real.exp y := by
  unfold mg_elad
  rw [Real.exp_add, Real.exp_log hx]

-- ═════════════════════════════════════════════════════════════
-- Section 2 — Standard math wrappers
-- ═════════════════════════════════════════════════════════════

def mg_exp (x : ℝ) : ℝ := Real.exp x
def mg_ln  (x : ℝ) : ℝ := Real.log x
def mg_log (x : ℝ) : ℝ := Real.log x  -- alias for mg_ln

def mg_sin (x : ℝ) : ℝ := Real.sin x
def mg_cos (x : ℝ) : ℝ := Real.cos x
def mg_tan (x : ℝ) : ℝ := Real.tan x

/-- `mg_sinh x = (exp x - exp (-x)) / 2`. The exp-form Mathlib uses. -/
def mg_sinh (x : ℝ) : ℝ := (Real.exp x - Real.exp (-x)) / 2
def mg_cosh (x : ℝ) : ℝ := (Real.exp x + Real.exp (-x)) / 2

/-- The runtime's `mg_tanh` is `(exp x - exp (-x)) / (exp x + exp (-x))`. -/
def mg_tanh (x : ℝ) : ℝ :=
  (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x))

def mg_asin  (x : ℝ) : ℝ := Real.arcsin x
def mg_acos  (x : ℝ) : ℝ := Real.arccos x

end -- close noncomputable section briefly so we can declare opaque

/-- `mg_atan` corresponds to libm's `atan`. Declared opaque so this
    file doesn't depend on the Mathlib import path for `Real.arctan`
    (which moved between Mathlib versions). The C / Rust runtime
    forwards directly to libm; no Lean algebraic identity in this
    file uses arctan. -/
opaque mg_atan : ℝ → ℝ

noncomputable section

/-- `mg_sqrt x = √x`. -/
def mg_sqrt (x : ℝ) : ℝ := Real.sqrt x

def mg_abs (x : ℝ) : ℝ := |x|

theorem mg_exp_eq_exp (x : ℝ) : mg_exp x = Real.exp x := rfl
theorem mg_ln_eq_log  (x : ℝ) : mg_ln x  = Real.log x := rfl

/-- The runtime's `mg_sinh` matches Mathlib's `Real.sinh`. -/
theorem mg_sinh_eq_real_sinh (x : ℝ) : mg_sinh x = Real.sinh x := by
  unfold mg_sinh
  rw [Real.sinh_eq]

theorem mg_cosh_eq_real_cosh (x : ℝ) : mg_cosh x = Real.cosh x := by
  unfold mg_cosh
  rw [Real.cosh_eq]

/-- The runtime's `mg_tanh` matches Mathlib's `Real.tanh`. The two
    `/2` factors in numerator and denominator cancel. -/
theorem mg_tanh_eq_real_tanh (x : ℝ) : mg_tanh x = Real.tanh x := by
  unfold mg_tanh
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have hp : Real.exp x + Real.exp (-x) ≠ 0 := by
    have h1 := Real.exp_pos x
    have h2 := Real.exp_pos (-x)
    linarith
  field_simp

-- ═════════════════════════════════════════════════════════════
-- Section 3 — Activation / growth operators
-- ═════════════════════════════════════════════════════════════

/-- `mg_sigmoid x = 1 / (1 + exp (-x))`. -/
def mg_sigmoid (x : ℝ) : ℝ := 1 / (1 + Real.exp (-x))

/-- `mg_softplus x = log (1 + exp x)`. -/
def mg_softplus (x : ℝ) : ℝ := Real.log (1 + Real.exp x)

/-- `mg_relu x = max 0 x`. -/
def mg_relu (x : ℝ) : ℝ := max 0 x

/-- `mg_logistic t K r x0 = K / (1 + exp (-r * (t - x0)))`. -/
def mg_logistic (t K r x0 : ℝ) : ℝ := K / (1 + Real.exp (-r * (t - x0)))

/-- `mg_gompertz t K r x0 = K * exp (-exp (-r * (t - x0)))`. -/
def mg_gompertz (t K r x0 : ℝ) : ℝ := K * Real.exp (-Real.exp (-r * (t - x0)))

theorem mg_sigmoid_at_zero : mg_sigmoid 0 = 1 / 2 := by
  unfold mg_sigmoid
  simp [Real.exp_zero]
  ring

/-- Logistic at the midpoint reduces to `K/2`. -/
theorem mg_logistic_at_x0 (K r x0 : ℝ) : mg_logistic x0 K r x0 = K / 2 := by
  unfold mg_logistic
  have : -r * (x0 - x0) = 0 := by ring
  rw [this, Real.exp_zero]
  ring

/-- Gompertz at the midpoint reduces to `K * exp(-1) = K / e`. -/
theorem mg_gompertz_at_x0 (K r x0 : ℝ) :
    mg_gompertz x0 K r x0 = K * Real.exp (-1) := by
  unfold mg_gompertz
  have h : -r * (x0 - x0) = 0 := by ring
  rw [h, Real.exp_zero]

-- ═════════════════════════════════════════════════════════════
-- Section 4 — Division
-- ═════════════════════════════════════════════════════════════

def mg_div (x y : ℝ) : ℝ := x / y
theorem mg_div_def (x y : ℝ) : mg_div x y = x / y := rfl

-- The C runtime's `mg_safe_div` saturates at ±DBL_MAX for `|y| < 1e-300`.
-- The Real correspondence below ignores the saturation bound (which is
-- an f64 artifact); a faithful model needs a hardware ULP axiom from
-- libm correctness postulates, deferred to a future MonogateEML/Float64.lean.

-- ═════════════════════════════════════════════════════════════
-- Section 5 — SuperBEST routing variants (Patent #01)
-- ═════════════════════════════════════════════════════════════

/-- Runtime's `mg_sigmoid_route` switches numerator/denominator on
    sign(x) to avoid `exp(-x)` overflow on the negative tail. -/
def mg_sigmoid_route (x : ℝ) : ℝ :=
  if x ≥ 0 then 1 / (1 + Real.exp (-x))
  else Real.exp x / (1 + Real.exp x)

/-- The two algebraic forms of sigmoid are exactly equal. The negative
    branch uses `exp(x) * exp(-x) = exp(0) = 1` for the cross-product. -/
theorem mg_sigmoid_route_eq_sigmoid (x : ℝ) :
    mg_sigmoid_route x = mg_sigmoid x := by
  unfold mg_sigmoid_route mg_sigmoid
  split_ifs with h
  · rfl
  · -- Goal: Real.exp x / (1 + Real.exp x) = 1 / (1 + Real.exp (-x))
    have hex   : (0 : ℝ) < Real.exp x      := Real.exp_pos x
    have henx  : (0 : ℝ) < Real.exp (-x)   := Real.exp_pos (-x)
    have hpos1 : (0 : ℝ) < 1 + Real.exp x      := by linarith
    have hpos2 : (0 : ℝ) < 1 + Real.exp (-x)   := by linarith
    have hxinv : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      have hzero : x + -x = (0 : ℝ) := by ring
      rw [hzero, Real.exp_zero]
    rw [div_eq_div_iff hpos1.ne' hpos2.ne']
    have hdistrib : Real.exp x * (1 + Real.exp (-x))
                  = Real.exp x + Real.exp x * Real.exp (-x) := by ring
    rw [hdistrib, hxinv]
    ring

/-- Runtime's `mg_tanh_route` — Padé near zero, sign at saturation,
    naive form in between. The naive form is what `mg_tanh` uses, so
    in the middle band these agree exactly. The saturation/Padé
    branches are bounded approximations (precision claim, not exact). -/
def mg_tanh_route (x : ℝ) : ℝ :=
  if |x| < 1e-8 then x
  else if |x| > 20 then (if x > 0 then 1 else -1)
  else (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x))

/-- In the middle band (1e-8 ≤ |x| ≤ 20) the routing form equals the
    naive `mg_tanh` exactly. The saturation/Padé branches need an
    ε-bound (left as TODO; standard approximation theory). -/
theorem mg_tanh_route_eq_tanh_in_middle_band
    (x : ℝ) (h1 : 1e-8 ≤ |x|) (h2 : |x| ≤ 20) :
    mg_tanh_route x = mg_tanh x := by
  unfold mg_tanh_route mg_tanh
  have hlt : ¬ (|x| < 1e-8) := not_lt.mpr h1
  have hgt : ¬ (|x| > 20)   := not_lt.mpr h2
  simp [hlt, hgt]

/-- Runtime's `mg_softplus_route`: `x` for x>20, `exp x` for x<-20,
    naive otherwise. The boundary branches are *approximations*
    (not exact equality). -/
def mg_softplus_route (x : ℝ) : ℝ :=
  if x > 20 then x
  else if x < -20 then Real.exp x
  else Real.log (1 + Real.exp x)

/-- In the middle band [-20, 20] the routing form equals naive softplus. -/
theorem mg_softplus_route_eq_softplus_in_middle_band
    (x : ℝ) (h1 : -20 ≤ x) (h2 : x ≤ 20) :
    mg_softplus_route x = mg_softplus x := by
  unfold mg_softplus_route mg_softplus
  have hlt : ¬ (x > 20) := not_lt.mpr h2
  have hgt : ¬ (x < -20) := not_lt.mpr h1
  simp [hlt, hgt]

/-- Approximation bound for the saturation branch of `softplus_route`.
    For x > 20: |softplus(x) - x| < exp(-20).

    Proof: 1 + exp(x) = exp(x)·(1 + exp(-x)), so
    log(1 + exp(x)) = x + log(1 + exp(-x)). The route returns `x`,
    so the residual is exactly log(1 + exp(-x)), which is bounded
    above by exp(-x) (via log(t) ≤ t-1) and exp(-x) < exp(-20). -/
theorem mg_softplus_route_bound_high (x : ℝ) (hx : 20 < x) :
    |mg_softplus_route x - mg_softplus x| < Real.exp (-20) := by
  have hroute : mg_softplus_route x = x := by
    unfold mg_softplus_route
    rw [if_pos hx]
  rw [hroute]
  unfold mg_softplus
  have hexpx      : (0 : ℝ) < Real.exp x      := Real.exp_pos x
  have hexpnx     : (0 : ℝ) < Real.exp (-x)   := Real.exp_pos (-x)
  have hpos_inner : (0 : ℝ) < 1 + Real.exp (-x) := by linarith
  have hxinv : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add, show x + -x = (0 : ℝ) from by ring, Real.exp_zero]
  have hfact : (1 : ℝ) + Real.exp x = Real.exp x * (1 + Real.exp (-x)) := by
    rw [mul_add, mul_one, hxinv]; ring
  have hlogsplit : Real.log (1 + Real.exp x)
                 = x + Real.log (1 + Real.exp (-x)) := by
    rw [hfact, Real.log_mul hexpx.ne' hpos_inner.ne', Real.log_exp]
  rw [hlogsplit]
  have hlog_nonneg : (0 : ℝ) ≤ Real.log (1 + Real.exp (-x)) :=
    Real.log_nonneg (by linarith)
  rw [show x - (x + Real.log (1 + Real.exp (-x)))
        = -Real.log (1 + Real.exp (-x)) from by ring,
      abs_neg, abs_of_nonneg hlog_nonneg]
  calc Real.log (1 + Real.exp (-x))
      ≤ (1 + Real.exp (-x)) - 1 := Real.log_le_sub_one_of_pos hpos_inner
    _ = Real.exp (-x)           := by ring
    _ < Real.exp (-20)          := Real.exp_lt_exp.mpr (by linarith)

end -- noncomputable section

end MonogateEML.Runtime
