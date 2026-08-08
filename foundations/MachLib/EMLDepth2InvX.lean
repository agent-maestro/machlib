import MachLib.EMLDepthCost

/-!
# `1/x` at depth 2 — the uniform reduction, and the `t2`-leaf cases

`inv_x_mem_EML` puts `1/x` in EML at **depth 6**; `inv_x_not_in_eml_1` keeps it out of `EML₁`. The
open bracket is `2 ≤ d(1/x) ≤ 6`, and closing the lower end means depth 2.

**The reduction is exact, not asymptotic.** For the left child `eml (const a) var`:

```
(eml (const a) var).eval x = exp a − log x        so     exp (that) = exp(exp a) / x
```

so `(eml t1 t2).eval x = 1/x` becomes, after multiplying through by `x`,

> **`exp (exp a) − x · log (t2.eval x) = 1`  for all `x > 0`.**

and `exp a > 0` forces **`exp (exp a) > 1`**. The `1/x`-coefficient a depth-2 tree can supply is
`0`, or `exp (exp a) ∈ (1,∞)`, or `e` — **never `1`**, which is what `1/x` needs. This is the arm's
*"`1` is the unattained infimum"*, and it is a **depth-2** fact.

**Scope.** This file closes the cases where `t2` is a **leaf**. The remaining `t2` shapes reduce to
transcendental root-separation (for `t2 = eml (const a') var`, to `e·log(exp a' − 1) = a'`) — the
wall `RESULT_FOUR_POINTS.md` hit. **`1/x ∉ EML₂` remains OPEN.**
-/

namespace MachLib

open Real

/-- `1 < exp (exp a)` for every real `a`, since `exp a > 0`. -/
theorem one_lt_exp_exp (a : Real) : 1 < exp (exp a) := by
  have h : exp 0 < exp (exp a) := exp_lt (exp_pos a)
  rw [exp_zero] at h
  exact h

/-- The left child, in multiplicative form (no division): `x · exp(exp a − log x) = exp (exp a)`. -/
theorem left_child_mul {a x : Real} (hx : 0 < x) :
    x * exp ((EMLTree.eml (EMLTree.const a) EMLTree.var).eval x) = exp (exp a) := by
  have h : (EMLTree.eml (EMLTree.const a) EMLTree.var).eval x = exp a - log x := rfl
  have hxne : x ≠ 0 := ne_of_gt hx
  rw [h, sub_def, exp_add, exp_neg_inv, exp_log hx]
  have step : x * (exp (exp a) * (1 / x)) = exp (exp a) * (x * (1 / x)) := by
    mach_mpoly [x, exp (exp a), 1 / x]
  rw [step, mul_inv x hxne]
  mach_ring

/-- **THE REDUCTION.** Exact, no limits, no asymptotics. -/
theorem depth2_reduce {a : Real} {t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) :
    exp (exp a) - x * log (t2.eval x) = 1 := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have he : exp ((EMLTree.eml (EMLTree.const a) EMLTree.var).eval x) - log (t2.eval x) = 1 / x :=
    h x hx
  have hmul : x * (exp ((EMLTree.eml (EMLTree.const a) EMLTree.var).eval x) - log (t2.eval x))
      = x * (1 / x) := by rw [he]
  rw [mul_inv x hxne] at hmul
  have hd : x * (exp ((EMLTree.eml (EMLTree.const a) EMLTree.var).eval x) - log (t2.eval x))
      = x * exp ((EMLTree.eml (EMLTree.const a) EMLTree.var).eval x) - x * log (t2.eval x) := by
    mach_mpoly [x, exp ((EMLTree.eml (EMLTree.const a) EMLTree.var).eval x), log (t2.eval x)]
  rw [hd, left_child_mul hx] at hmul
  exact hmul

/-- Once the reduction pins `exp (exp a) = 1`, `one_lt_exp_exp` closes it. -/
theorem exp_exp_eq_one_absurd {a : Real} (h : exp (exp a) = 1) : False := by
  have hlt := one_lt_exp_exp a
  rw [h] at hlt
  exact lt_irrefl_ax 1 hlt

/-- **`t2 = var` closes at the SINGLE point `x = 1`.** -/
theorem depth2_t2_var_absurd {a : Real}
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) EMLTree.var).eval x = 1 / x) :
    False := by
  have h1 := depth2_reduce h 1 one_pos
  have hv : (EMLTree.var).eval (1 : Real) = 1 := rfl
  rw [hv, log_one] at h1
  have e : exp (exp a) - (1 : Real) * 0 = exp (exp a) := by mach_ring
  rw [e] at h1
  exact exp_exp_eq_one_absurd h1

/-- **`t2` constant-valued closes on TWO points**, `x = 1` and `x = 1+1`. -/
theorem depth2_t2_const_absurd {a b : Real}
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) (EMLTree.const b)).eval x = 1 / x) :
    False := by
  have hc : ∀ y : Real, (EMLTree.const b).eval y = b := fun _ => rfl
  have h1 := depth2_reduce h 1 one_pos
  have h2 := depth2_reduce h (1 + 1) (add_pos one_pos one_pos)
  rw [hc] at h1 h2
  -- h1 : exp (exp a) - 1 * log b = 1 ;  h2 : exp (exp a) - (1+1) * log b = 1
  have hlog : log b = 0 := by
    have d : (exp (exp a) - 1 * log b) - (exp (exp a) - (1 + 1) * log b) = log b := by
      mach_mpoly [exp (exp a), log b]
    rw [h1, h2] at d
    have e : (1 : Real) - 1 = 0 := by mach_ring
    rw [e] at d
    exact d.symm
  rw [hlog] at h1
  have e : exp (exp a) - (1 : Real) * 0 = exp (exp a) := by mach_ring
  rw [e] at h1
  exact exp_exp_eq_one_absurd h1

end MachLib
