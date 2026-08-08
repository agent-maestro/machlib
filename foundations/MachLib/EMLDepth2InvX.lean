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

-- ===================================================================
-- ▸ THE `t2 = var` ROW, CLOSED FOR EVERY DEPTH-≤1 LEFT CHILD
--
-- At `x = 1` the equation forces `exp (t1.eval 1) = 1` whatever `t1` is —
-- and three of the six shapes contradict that outright.
-- ===================================================================

theorem one_lt_one_plus_one_local : (1 : Real) < 1 + 1 := by
  have step := add_lt_add_left zero_lt_one_ax 1
  have e1 : (1 : Real) + 0 = 1 := by mach_ring
  rw [e1] at step; exact step

theorem one_div_one : (1 : Real) / 1 = 1 := by
  have h := mul_inv (1 : Real) (ne_of_gt one_pos)
  have e : (1 : Real) * (1 / 1) = 1 / 1 := by mach_ring
  rw [e] at h; exact h

/-- **The pin.** Any `t1` with `eml t1 var = 1/x` satisfies `exp (t1.eval 1) = 1`. -/
theorem t2_var_pins {t1 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 EMLTree.var).eval x = 1 / x) :
    exp (t1.eval 1) = 1 := by
  have h1 := h 1 one_pos
  have hu : (EMLTree.eml t1 EMLTree.var).eval 1 = exp (t1.eval 1) - log 1 := rfl
  rw [hu, log_one, one_div_one] at h1
  have e : exp (t1.eval 1) - (0 : Real) = exp (t1.eval 1) := by mach_ring
  rw [e] at h1; exact h1

/-- Shapes whose value at `1` is `exp (something)`: `exp (exp _) = 1` is absurd. -/
theorem t2_var_left_expexp_absurd {t1 : EMLTree} {a : Real}
    (hval : t1.eval 1 = exp a)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 EMLTree.var).eval x = 1 / x) : False := by
  have hp := t2_var_pins h
  rw [hval] at hp
  exact exp_exp_eq_one_absurd hp

/-- `t1 = var`. -/
theorem t2_var_left_var_absurd
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var EMLTree.var).eval x = 1 / x) : False := by
  have hp := t2_var_pins h
  have hv : (EMLTree.var).eval (1 : Real) = 1 := rfl
  rw [hv] at hp
  have hlt : (1 : Real) < exp 1 := by
    have step : exp 0 < exp 1 := exp_lt zero_lt_one_ax
    rw [exp_zero] at step; exact step
  rw [hp] at hlt
  exact lt_irrefl_ax 1 hlt

/-- `t1 = eml (const a) var`, i.e. `t1.eval 1 = exp a`. -/
theorem t2_var_left_const_var_absurd {a : Real}
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) EMLTree.var).eval x = 1 / x) :
    False :=
  t2_var_left_expexp_absurd (by show exp a - log 1 = exp a; rw [log_one]; mach_ring) h

/-- `t1 = eml var var`, i.e. `t1.eval 1 = exp 1`. -/
theorem t2_var_left_var_var_absurd
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var).eval x = 1 / x) :
    False :=
  t2_var_left_expexp_absurd (a := 1)
    (by show exp ((EMLTree.var).eval (1:Real)) - log ((EMLTree.var).eval (1:Real)) = exp 1
        show exp (1:Real) - log (1:Real) = exp 1
        rw [log_one]; mach_ring) h

/-- **`t1` constant-valued.** The pin gives `exp K = 1`, so the tree is `1 − log x`;
`x = exp 1` then forces `0 = 1 / exp 1`, and `1 / exp 1 > 0`. -/
theorem t2_var_left_constval_absurd {t1 : EMLTree} {K : Real}
    (hconst : ∀ x : Real, t1.eval x = K)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 EMLTree.var).eval x = 1 / x) : False := by
  have hp := t2_var_pins h
  rw [hconst 1] at hp
  have he := h (exp 1) (exp_pos 1)
  have hu : (EMLTree.eml t1 EMLTree.var).eval (exp 1)
      = exp (t1.eval (exp 1)) - log (exp 1) := rfl
  rw [hu, hconst (exp 1), hp, log_exp] at he
  -- he : 1 - 1 = 1 / exp 1
  have e : (1 : Real) - 1 = 0 := by mach_ring
  rw [e] at he
  have hpos : (0 : Real) < 1 / exp 1 := one_div_pos_of_pos (exp_pos 1)
  rw [← he] at hpos
  exact lt_irrefl_ax 0 hpos

theorem t2_var_left_const_absurd {c : Real}
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.const c) EMLTree.var).eval x = 1 / x) : False :=
  t2_var_left_constval_absurd (K := c) (fun _ => rfl) h

theorem t2_var_left_const_const_absurd {a b : Real}
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml (EMLTree.const a) (EMLTree.const b)) EMLTree.var).eval x
        = 1 / x) : False :=
  t2_var_left_constval_absurd (K := exp a - log b) (fun _ => rfl) h

/-- **The last cell of the row: `t1 = eml var (const b)`.**
The pin forces `log b = exp 1`; then `x = exp 1` gives
`exp (exp (exp 1) − exp 1) − 1 = 1 / exp 1`, whose left side exceeds `1` and whose right side is
below `1`. This is the only cell in the row needing a numeric chain. -/
theorem t2_var_left_var_const_absurd {b : Real}
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const b)) EMLTree.var).eval x = 1 / x) :
    False := by
  have hp := t2_var_pins h
  have hv1 : (EMLTree.eml EMLTree.var (EMLTree.const b)).eval (1 : Real) = exp 1 - log b := rfl
  rw [hv1] at hp
  -- exp (exp 1 − log b) = 1 = exp 0, so log b = exp 1
  have hz : exp 1 - log b = 0 := by
    have h0 : exp (exp 1 - log b) = exp 0 := by rw [hp, exp_zero]
    exact exp_injective h0
  have hlogb : log b = exp 1 := by
    have e : exp 1 - log b + log b = exp 1 := by mach_ring
    rw [hz] at e
    have e2 : (0 : Real) + log b = log b := by mach_ring
    rw [e2] at e
    exact e
  -- evaluate at x = exp 1
  have he := h (exp 1) (exp_pos 1)
  have hv2 : (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const b)) EMLTree.var).eval (exp 1)
      = exp (exp (exp 1) - log b) - log (exp 1) := rfl
  rw [hv2, hlogb, log_exp] at he
  -- he : exp (exp (exp 1) − exp 1) − 1 = 1 / exp 1
  have hgap : (1 : Real) < exp (exp 1) - exp 1 := by
    have hb := exp_gt_one_plus_self (exp 1) (exp_pos 1)
    have e : 1 + exp 1 - exp 1 = (1 : Real) := by mach_ring
    have step : 1 + exp 1 - exp 1 < exp (exp 1) - exp 1 := by
      have := add_lt_add_left hb (-(exp 1))
      have e1 : -(exp 1) + (1 + exp 1) = 1 + exp 1 - exp 1 := by mach_ring
      have e2 : -(exp 1) + exp (exp 1) = exp (exp 1) - exp 1 := by mach_ring
      rw [e1, e2] at this; exact this
    rw [e] at step; exact step
  have hbig : exp 1 < exp (exp (exp 1) - exp 1) := exp_lt hgap
  have h2e : (1 : Real) < exp 1 := lt_trans_ax one_lt_one_plus_one_local two_lt_exp_one
  have hlhs : (1 : Real) < exp (exp (exp 1) - exp 1) - 1 := by
    have step : exp 1 - 1 < exp (exp (exp 1) - exp 1) - 1 := by
      have := add_lt_add_left hbig (-(1 : Real))
      have e1 : -(1 : Real) + exp 1 = exp 1 - 1 := by mach_ring
      have e2 : -(1 : Real) + exp (exp (exp 1) - exp 1)
          = exp (exp (exp 1) - exp 1) - 1 := by mach_ring
      rw [e1, e2] at this; exact this
    have hone : (1 : Real) < exp 1 - 1 := by
      have := add_lt_add_left two_lt_exp_one (-(1 : Real))
      have e1 : -(1 : Real) + (1 + 1 : Real) = 1 := by mach_ring
      have e2 : -(1 : Real) + exp 1 = exp 1 - 1 := by mach_ring
      rw [e1, e2] at this; exact this
    exact lt_trans_ax hone step
  have hrhs : (1 : Real) / exp 1 < 1 := div_lt_one_of_pos_lt (exp_pos 1) h2e
  rw [he] at hlhs
  exact lt_irrefl_ax 1 (lt_trans_ax hlhs hrhs)

/-- # **`1/x` is not `eml t1 var` for ANY depth-≤1 left child.**
The complete `t2 = var` row of the depth-2 table — all six shapes. -/
theorem inv_x_not_depth2_right_var (t1 : EMLTree) (ht : t1.depth ≤ 1) :
    ¬ (∀ x : Real, 0 < x → (EMLTree.eml t1 EMLTree.var).eval x = 1 / x) := by
  intro h
  cases t1 with
  | const c => exact t2_var_left_const_absurd h
  | var => exact t2_var_left_var_absurd h
  | eml a b =>
      cases a with
      | const c1 =>
          cases b with
          | const c2 => exact t2_var_left_const_const_absurd h
          | var => exact t2_var_left_const_var_absurd h
          | eml p q =>
              exfalso
              simp only [EMLTree.depth] at ht
              omega
      | var =>
          cases b with
          | const c2 => exact t2_var_left_var_const_absurd h
          | var => exact t2_var_left_var_var_absurd h
          | eml p q =>
              exfalso
              simp only [EMLTree.depth] at ht
              omega
      | eml p q =>
          exfalso
          simp only [EMLTree.depth] at ht
          omega

-- ===================================================================
-- ▸ THE CONSTANT-`t2` COLUMN, closed by ONE monotonicity criterion
--
-- With `t2` constant-valued the two-point system at `x = 1, 1+1` collapses to
--     E₂ + E₂ = E₁ + E₁ − 1        (Eᵢ := exp (t1.eval i))
-- so any `t1` that does NOT strictly decrease from `1` to `1+1` dies at once.
-- ===================================================================

theorem log_two_lt_one_wit : log ((1 : Real) + 1) < 1 := by
  have h := log_lt_log (add_pos one_pos one_pos) two_lt_exp_one
  rw [log_exp] at h
  exact h

theorem add_le_add_wit {a b c d : Real} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  have s1 : c + a ≤ c + b := add_le_add_left h1 c
  have s2 : b + c ≤ b + d := add_le_add_left h2 b
  have e1 : c + a = a + c := by mach_ring
  have e2 : c + b = b + c := by mach_ring
  rw [e1, e2] at s1
  exact le_trans s1 s2

/-- Reduction for constant-valued `t2`: `x·exp(t1 x) = 1 + log V · x`. -/
theorem depth2_constval_reduce {t1 t2 : EMLTree} {V : Real}
    (hV : ∀ x : Real, t2.eval x = V)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) :
    x * exp (t1.eval x) = 1 + log V * x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have he : exp (t1.eval x) - log (t2.eval x) = 1 / x := h x hx
  rw [hV] at he
  have hmul : x * (exp (t1.eval x) - log V) = x * (1 / x) := by rw [he]
  rw [mul_inv x hxne] at hmul
  have hd : x * (exp (t1.eval x) - log V)
      = x * exp (t1.eval x) - log V * x := by
    mach_mpoly [x, exp (t1.eval x), log V]
  rw [hd] at hmul
  have e2 : x * exp (t1.eval x) - log V * x + log V * x = 1 + log V * x := by rw [hmul]
  have e3 : x * exp (t1.eval x) - log V * x + log V * x = x * exp (t1.eval x) := by
    mach_mpoly [x, exp (t1.eval x), log V]
  rw [e3] at e2
  exact e2

/-- **The criterion.** If `t2` is constant-valued and `t1` does not decrease from `1` to `1+1`,
`1/x` is impossible. -/
theorem depth2_constval_mono_absurd {t1 t2 : EMLTree} {V : Real}
    (hV : ∀ x : Real, t2.eval x = V)
    (hmono : t1.eval 1 ≤ t1.eval (1 + 1))
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x) : False := by
  have r1 := depth2_constval_reduce hV h 1 one_pos
  have r2 := depth2_constval_reduce hV h (1 + 1) (add_pos one_pos one_pos)
  have hL : log V = exp (t1.eval 1) - 1 := by
    have e : (1 : Real) * exp (t1.eval 1) - 1 = 1 + log V * 1 - 1 := by rw [r1]
    have e1 : (1 : Real) * exp (t1.eval 1) - 1 = exp (t1.eval 1) - 1 := by mach_ring
    have e2 : (1 : Real) + log V * 1 - 1 = log V := by mach_ring
    rw [e1, e2] at e
    exact e.symm
  rw [hL] at r2
  -- r2 : (1+1) * E₂ = 1 + (E₁ - 1) * (1+1)
  have key : exp (t1.eval (1 + 1)) + exp (t1.eval (1 + 1))
      = exp (t1.eval 1) + exp (t1.eval 1) - 1 := by
    have a1 : (1 + 1 : Real) * exp (t1.eval (1 + 1))
        = exp (t1.eval (1 + 1)) + exp (t1.eval (1 + 1)) := by mach_ring
    have a2 : (1 : Real) + (exp (t1.eval 1) - 1) * (1 + 1)
        = exp (t1.eval 1) + exp (t1.eval 1) - 1 := by mach_ring
    rw [a1, a2] at r2
    exact r2
  have hE : exp (t1.eval 1) ≤ exp (t1.eval (1 + 1)) := exp_monotone hmono
  have hsum : exp (t1.eval 1) + exp (t1.eval 1)
      ≤ exp (t1.eval (1 + 1)) + exp (t1.eval (1 + 1)) := add_le_add_wit hE hE
  rw [key] at hsum
  -- hsum : E₁ + E₁ ≤ E₁ + E₁ - 1
  have hbad : (0 : Real) ≤ -1 := by
    have e : exp (t1.eval 1) + exp (t1.eval 1) + (-1)
        = exp (t1.eval 1) + exp (t1.eval 1) - 1 := by mach_ring
    have s := add_le_add_left hsum (-(exp (t1.eval 1) + exp (t1.eval 1)))
    have e1 : -(exp (t1.eval 1) + exp (t1.eval 1)) + (exp (t1.eval 1) + exp (t1.eval 1))
        = (0 : Real) := by mach_ring
    have e2 : -(exp (t1.eval 1) + exp (t1.eval 1))
        + (exp (t1.eval 1) + exp (t1.eval 1) - 1) = -1 := by mach_ring
    rw [e1, e2] at s
    exact s
  have : (-1 : Real) < 0 := by
    have h1 := add_lt_add_left zero_lt_one_ax (-1 : Real)
    have e1 : (-1 : Real) + 0 = -1 := by mach_ring
    have e2 : (-1 : Real) + 1 = 0 := by mach_ring
    rw [e1, e2] at h1; exact h1
  exact lt_irrefl_ax 0 (lt_of_le_of_lt hbad this)

/-- `t1 = eml (const a) var` is the one shape that DECREASES on `[1, 1+1]`, so the criterion
misses it — but `depth2_reduce` already pins it: `x·log V` must be constant, forcing `log V = 0`
and then `exp (exp a) = 1`. -/
theorem depth2_constval_left_const_var_absurd {a V : Real} {t2 : EMLTree}
    (hV : ∀ x : Real, t2.eval x = V)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) t2).eval x = 1 / x) : False := by
  have h1 := depth2_reduce h 1 one_pos
  have h2 := depth2_reduce h (1 + 1) (add_pos one_pos one_pos)
  rw [hV] at h1 h2
  have hlog : log V = 0 := by
    have d : (exp (exp a) - 1 * log V) - (exp (exp a) - (1 + 1) * log V) = log V := by
      mach_mpoly [exp (exp a), log V]
    rw [h1, h2] at d
    have e : (1 : Real) - 1 = 0 := by mach_ring
    rw [e] at d
    exact d.symm
  rw [hlog] at h1
  have e : exp (exp a) - (1 : Real) * 0 = exp (exp a) := by mach_ring
  rw [e] at h1
  exact exp_exp_eq_one_absurd h1

/-- `exp 1 ≤ exp (1+1) − log (1+1)` — the numeric step for `t1 = eml var var`. -/
theorem exp_one_le_exp_two_sub_log_two : exp 1 ≤ exp (1 + 1) - log ((1 : Real) + 1) := by
  have hsplit : exp ((1 : Real) + 1) = exp 1 * exp 1 := exp_add 1 1
  have hgt : exp 1 + exp 1 < exp 1 * exp 1 := by
    have := mul_lt_mul_of_pos_right two_lt_exp_one (exp_pos 1)
    have e : ((1 : Real) + 1) * exp 1 = exp 1 + exp 1 := by mach_ring
    rw [e] at this; exact this
  have hstep : exp 1 + 1 < exp (1 + 1) := by
    have h1 : exp 1 + 1 < exp 1 + exp 1 := by
      have := add_le_add_left (le_of_lt (lt_trans_ax one_lt_one_plus_one_local two_lt_exp_one))
        (exp 1)
      have hlt := add_lt_add_left (lt_trans_ax one_lt_one_plus_one_local two_lt_exp_one) (exp 1)
      exact hlt
    rw [hsplit]
    exact lt_trans_ax h1 hgt
  -- log (1+1) < 1 and exp 1 + 1 < exp (1+1) give the claim
  have hlog := log_two_lt_one_wit
  have : exp 1 + log ((1 : Real) + 1) < exp (1 + 1) := by
    have h2 : exp 1 + log ((1 : Real) + 1) < exp 1 + 1 := add_lt_add_left hlog (exp 1)
    exact lt_trans_ax h2 hstep
  have s := add_lt_add_left this (-log ((1 : Real) + 1))
  have e1 : -log ((1 : Real) + 1) + (exp 1 + log ((1 : Real) + 1)) = exp 1 := by mach_ring
  have e2 : -log ((1 : Real) + 1) + exp (1 + 1) = exp (1 + 1) - log ((1 : Real) + 1) := by
    mach_ring
  rw [e1, e2] at s
  exact le_of_lt s

/-- # **The constant-`t2` column, closed for every depth-≤1 left child.** -/
theorem inv_x_not_depth2_right_constval {t1 t2 : EMLTree} {V : Real}
    (ht : t1.depth ≤ 1) (hV : ∀ x : Real, t2.eval x = V) :
    ¬ (∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x) := by
  intro h
  cases t1 with
  | const c =>
      refine depth2_constval_mono_absurd hV ?_ h
      show c ≤ c
      exact le_refl c
  | var =>
      refine depth2_constval_mono_absurd hV ?_ h
      show (1 : Real) ≤ 1 + 1
      exact le_of_lt one_lt_one_plus_one_local
  | eml p q =>
      cases p with
      | const a =>
          cases q with
          | const b =>
              refine depth2_constval_mono_absurd hV ?_ h
              show exp a - log b ≤ exp a - log b
              exact le_refl (exp a - log b)
          | var => exact depth2_constval_left_const_var_absurd hV h
          | eml _ _ => exfalso; simp only [EMLTree.depth] at ht; omega
      | var =>
          cases q with
          | const b =>
              refine depth2_constval_mono_absurd hV ?_ h
              show exp 1 - log b ≤ exp (1 + 1) - log b
              have hx : exp 1 ≤ exp (1 + 1) :=
                exp_monotone (le_of_lt one_lt_one_plus_one_local)
              have s := add_le_add_wit hx (le_refl (-log b))
              have e1 : exp 1 + -log b = exp 1 - log b := by mach_ring
              have e2 : exp (1 + 1) + -log b = exp (1 + 1) - log b := by mach_ring
              rw [e1, e2] at s; exact s
          | var =>
              refine depth2_constval_mono_absurd hV ?_ h
              show exp 1 - log 1 ≤ exp (1 + 1) - log ((1 : Real) + 1)
              rw [log_one]
              have e : exp 1 - (0 : Real) = exp 1 := by mach_ring
              rw [e]
              exact exp_one_le_exp_two_sub_log_two
          | eml _ _ => exfalso; simp only [EMLTree.depth] at ht; omega
      | eml _ _ => exfalso; simp only [EMLTree.depth] at ht; omega

end MachLib
