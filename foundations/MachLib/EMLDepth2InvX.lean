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

-- ===================================================================
-- ▸ THE 6 CELLS NOBODY HAS: `t1 ∈ {const c, var}` × varying `t2`
--
-- Case 9 (both children `eml`-rooted) is covered by the arm's u1..u4 × w1..w4
-- table; the columns above cover leaf-valued `t2`. What is left is a BOUNDED
-- left child against a right child that is ≥ 1 at a small point.
-- ===================================================================

/-- **The small-point criterion.** If at some `x > 0` the left child is small enough that
`x·exp(t1 x) < 1`, while `log (t2 x) ≥ 0`, then `1/x` is impossible — because the equation forces
`x·exp(t1 x) = 1 + x·log(t2 x) ≥ 1`. -/
theorem depth2_small_point_absurd {t1 t2 : EMLTree} {x : Real}
    (hx : 0 < x)
    (hsmall : x * exp (t1.eval x) < 1)
    (hlog : 0 ≤ log (t2.eval x))
    (h : ∀ y : Real, 0 < y → (EMLTree.eml t1 t2).eval y = 1 / y) : False := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have he : exp (t1.eval x) - log (t2.eval x) = 1 / x := h x hx
  have hmul : x * (exp (t1.eval x) - log (t2.eval x)) = x * (1 / x) := by rw [he]
  rw [mul_inv x hxne] at hmul
  have hd : x * (exp (t1.eval x) - log (t2.eval x))
      = x * exp (t1.eval x) - x * log (t2.eval x) := by
    mach_mpoly [x, exp (t1.eval x), log (t2.eval x)]
  rw [hd] at hmul
  -- x·E − x·L = 1, with x·L ≥ 0, so x·E ≥ 1
  have hxL : 0 ≤ x * log (t2.eval x) := mul_nonneg (le_of_lt hx) hlog
  have hge : (1 : Real) ≤ x * exp (t1.eval x) := by
    have s := add_le_add_wit (le_refl (1 : Real)) hxL
    have e1 : (1 : Real) + 0 = 1 := by mach_ring
    rw [e1] at s
    have e2 : x * exp (t1.eval x) - x * log (t2.eval x) + x * log (t2.eval x)
        = x * exp (t1.eval x) := by mach_mpoly [x, exp (t1.eval x), log (t2.eval x)]
    have s2 : (1 : Real) + x * log (t2.eval x) = x * exp (t1.eval x) := by
      rw [← hmul]; exact e2.symm ▸ rfl
    rw [s2] at s
    exact s
  exact lt_irrefl_ax 1 (lt_of_le_of_lt hge hsmall)

/-- `0 < x ≤ 1 → log x ≤ 0`. -/
theorem log_nonpos_of_le_one {x : Real} (hx : 0 < x) (h1 : x ≤ 1) : log x ≤ 0 := by
  have h := log_le_log hx h1
  rw [log_one] at h
  exact h

/-- `t2 = eml var var` is `≥ 1` at any `0 < x ≤ 1`, so its log is `≥ 0` there. -/
theorem evv_log_nonneg {x : Real} (hx : 0 < x) (h1 : x ≤ 1) :
    0 ≤ log ((EMLTree.eml EMLTree.var EMLTree.var).eval x) := by
  have hval : (EMLTree.eml EMLTree.var EMLTree.var).eval x = exp x - log x := rfl
  have hex : (1 : Real) < exp x := by
    have h := exp_lt hx
    rw [exp_zero] at h; exact h
  have hlx : log x ≤ 0 := log_nonpos_of_le_one hx h1
  have hge : (1 : Real) ≤ exp x - log x := by
    have s := add_le_add_wit (le_of_lt hex) (by
      have := add_le_add_left hlx (-log x)
      have e1 : -log x + log x = (0 : Real) := by mach_ring
      have e2 : -log x + 0 = -log x := by mach_ring
      rw [e1, e2] at this
      exact this : (0 : Real) ≤ -log x)
    have e1 : (1 : Real) + 0 = 1 := by mach_ring
    have e2 : exp x + -log x = exp x - log x := by mach_ring
    rw [e1, e2] at s; exact s
  rw [hval]
  have h := log_le_log one_pos hge
  rw [log_one] at h
  exact h

/-- **`t1 = const c`, `t2 = eml var var`.** Witness point `x = exp (−exp c − 1)`: no division. -/
theorem depth2_const_evv_absurd {c : Real}
    (h : ∀ y : Real, 0 < y →
      (EMLTree.eml (EMLTree.const c) (EMLTree.eml EMLTree.var EMLTree.var)).eval y = 1 / y) :
    False := by
  have hx : 0 < exp (-exp c - 1) := exp_pos _
  have hneg : -exp c - 1 < 0 := by
    have hc := exp_pos c
    have s := add_lt_add_left hc (-exp c - 1)
    have e1 : -exp c - 1 + 0 = -exp c - 1 := by mach_ring
    rw [e1] at s
    have e2 : -exp c - 1 + exp c = -1 := by mach_ring
    rw [e2] at s
    have hm1 : (-1 : Real) < 0 := by
      have t := add_lt_add_left zero_lt_one_ax (-1 : Real)
      have f1 : (-1 : Real) + 0 = -1 := by mach_ring
      have f2 : (-1 : Real) + 1 = 0 := by mach_ring
      rw [f1, f2] at t; exact t
    exact lt_trans_ax s hm1
  have hx1 : exp (-exp c - 1) ≤ 1 := by
    have hlt : exp (-exp c - 1) < exp 0 := exp_lt hneg
    rw [exp_zero] at hlt
    exact le_of_lt hlt
  have hsmall : exp (-exp c - 1) * exp ((EMLTree.const c).eval (exp (-exp c - 1))) < 1 := by
    have hcv : (EMLTree.const c).eval (exp (-exp c - 1)) = c := rfl
    rw [hcv, ← exp_add]
    have hexp : -exp c - 1 + c < 0 := by
      have hcc : c < exp c := exp_grows_strictly_thm c
      have s := add_lt_add_left hcc (-exp c - 1)
      have e1 : -exp c - 1 + c = -exp c - 1 + c := by mach_ring
      have e2 : -exp c - 1 + exp c = -1 := by mach_ring
      rw [e2] at s
      have hm1 : (-1 : Real) < 0 := by
        have t := add_lt_add_left zero_lt_one_ax (-1 : Real)
        have f1 : (-1 : Real) + 0 = -1 := by mach_ring
        have f2 : (-1 : Real) + 1 = 0 := by mach_ring
        rw [f1, f2] at t; exact t
      exact lt_trans_ax s hm1
    have hlt : exp (-exp c - 1 + c) < exp 0 := exp_lt hexp
    rw [exp_zero] at hlt
    exact hlt
  exact depth2_small_point_absurd hx hsmall (evv_log_nonneg hx hx1) h

/-- **`t1 = var`, `t2 = eml var var`.** Witness point `x = exp (−(1+1))`. -/
theorem depth2_var_evv_absurd
    (h : ∀ y : Real, 0 < y →
      (EMLTree.eml EMLTree.var (EMLTree.eml EMLTree.var EMLTree.var)).eval y = 1 / y) :
    False := by
  have hneg : -(1 + 1 : Real) < 0 := by
    have t := add_lt_add_left (add_pos one_pos one_pos) (-(1 + 1) : Real)
    have f1 : (-(1 + 1) : Real) + 0 = -(1 + 1) := by mach_ring
    have f2 : (-(1 + 1) : Real) + (1 + 1) = 0 := by mach_ring
    rw [f1, f2] at t; exact t
  have hx : 0 < exp (-(1 + 1) : Real) := exp_pos _
  have hx1' : exp (-(1 + 1) : Real) < 1 := by
    have hlt : exp (-(1 + 1) : Real) < exp 0 := exp_lt hneg
    rw [exp_zero] at hlt; exact hlt
  have hx1 : exp (-(1 + 1) : Real) ≤ 1 := le_of_lt hx1'
  have hsmall : exp (-(1 + 1) : Real)
      * exp ((EMLTree.var).eval (exp (-(1 + 1) : Real))) < 1 := by
    have hv : (EMLTree.var).eval (exp (-(1 + 1) : Real)) = exp (-(1 + 1) : Real) := rfl
    rw [hv, ← exp_add]
    have hsum : -(1 + 1 : Real) + exp (-(1 + 1) : Real) < 0 := by
      have s := add_lt_add_left hx1' (-(1 + 1) : Real)
      have e : (-(1 + 1) : Real) + 1 = -1 := by mach_ring
      rw [e] at s
      have hm1 : (-1 : Real) < 0 := by
        have t := add_lt_add_left zero_lt_one_ax (-1 : Real)
        have f1 : (-1 : Real) + 0 = -1 := by mach_ring
        have f2 : (-1 : Real) + 1 = 0 := by mach_ring
        rw [f1, f2] at t; exact t
      exact lt_trans_ax s hm1
    have hlt : exp (-(1 + 1 : Real) + exp (-(1 + 1) : Real)) < exp 0 := exp_lt hsum
    rw [exp_zero] at hlt; exact hlt
  exact depth2_small_point_absurd hx hsmall (evv_log_nonneg hx hx1) h

/-- For `t2 = eml (const a') var` at the point `exp w`, `log (t2 ·) ≥ 0` whenever `w ≤ exp a' − 1`. -/
theorem ecv_log_nonneg {a' w : Real} (hw : w ≤ exp a' - 1) :
    0 ≤ log ((EMLTree.eml (EMLTree.const a') EMLTree.var).eval (exp w)) := by
  have hval : (EMLTree.eml (EMLTree.const a') EMLTree.var).eval (exp w)
      = exp a' - log (exp w) := rfl
  rw [hval, log_exp]
  have hge : (1 : Real) ≤ exp a' - w := by
    have s := add_le_add_left hw (-w + 1)
    have e1 : -w + 1 + w = (1 : Real) := by mach_ring
    have e2 : -w + 1 + (exp a' - 1) = exp a' - w := by mach_ring
    rw [e1, e2] at s; exact s
  have h := log_le_log one_pos hge
  rw [log_one] at h; exact h

/-- `y − exp y − 1 < 0` for every real `y` — the arm's canonical "exp dominates" bound. -/
theorem sub_exp_sub_one_neg (y : Real) : y - exp y - 1 < 0 := by
  have hy := exp_grows_strictly_thm y
  have s := add_lt_add_left hy (-exp y - 1 + -y)
  have e1 : -exp y - 1 + -y + y = -exp y - 1 := by mach_ring
  have e2 : -exp y - 1 + -y + exp y = -y - 1 := by mach_ring
  rw [e1, e2] at s
  -- s : -exp y - 1 < -y - 1 ; want y - exp y - 1 < 0
  have s2 := add_lt_add_left s (y + 1)
  have f1 : y + 1 + (-exp y - 1) = y - exp y := by mach_ring
  have f2 : y + 1 + (-y - 1) = (0 : Real) := by mach_ring
  rw [f1, f2] at s2
  -- s2 : y - exp y < 0
  have s3 := add_lt_add_left s2 (-1 : Real)
  have g1 : (-1 : Real) + (y - exp y) = y - exp y - 1 := by mach_ring
  have g2 : (-1 : Real) + 0 = -1 := by mach_ring
  rw [g1, g2] at s3
  have hm1 : (-1 : Real) < 0 := by
    have t := add_lt_add_left zero_lt_one_ax (-1 : Real)
    have f1 : (-1 : Real) + 0 = -1 := by mach_ring
    have f2 : (-1 : Real) + 1 = 0 := by mach_ring
    rw [f1, f2] at t; exact t
  exact lt_trans_ax s3 hm1

/-- **`t1 = const c`, `t2 = eml (const a') var`.** -/
theorem depth2_const_ecv_absurd {c a' : Real}
    (h : ∀ y : Real, 0 < y →
      (EMLTree.eml (EMLTree.const c) (EMLTree.eml (EMLTree.const a') EMLTree.var)).eval y
        = 1 / y) : False := by
  have hx : 0 < exp (exp a' - 1 - exp (exp a' - 1 + c) - 1) := exp_pos _
  have hle : exp a' - 1 - exp (exp a' - 1 + c) - 1 ≤ exp a' - 1 := by
    have hp : (0 : Real) < exp (exp a' - 1 + c) := exp_pos _
    have s := add_lt_add_left hp (exp a' - 1 - exp (exp a' - 1 + c) - 1)
    have e1 : exp a' - 1 - exp (exp a' - 1 + c) - 1 + 0
        = exp a' - 1 - exp (exp a' - 1 + c) - 1 := by mach_ring
    have e2 : exp a' - 1 - exp (exp a' - 1 + c) - 1 + exp (exp a' - 1 + c)
        = exp a' - 1 - 1 := by mach_ring
    rw [e1, e2] at s
    have hstep : exp a' - 1 - 1 ≤ exp a' - 1 := by
      have t := add_lt_add_left zero_lt_one_ax (exp a' - 1 - 1)
      have f1 : exp a' - 1 - 1 + 0 = exp a' - 1 - 1 := by mach_ring
      have f2 : exp a' - 1 - 1 + 1 = exp a' - 1 := by mach_ring
      rw [f1, f2] at t; exact le_of_lt t
    exact le_trans (le_of_lt s) hstep
  have hsmall : exp (exp a' - 1 - exp (exp a' - 1 + c) - 1)
      * exp ((EMLTree.const c).eval (exp (exp a' - 1 - exp (exp a' - 1 + c) - 1))) < 1 := by
    have hcv : (EMLTree.const c).eval
        (exp (exp a' - 1 - exp (exp a' - 1 + c) - 1)) = c := rfl
    rw [hcv, ← exp_add]
    have hneg : exp a' - 1 - exp (exp a' - 1 + c) - 1 + c < 0 := by
      have hb := sub_exp_sub_one_neg (exp a' - 1 + c)
      have e : exp a' - 1 + c - exp (exp a' - 1 + c) - 1
          = exp a' - 1 - exp (exp a' - 1 + c) - 1 + c := by mach_ring
      rw [e] at hb; exact hb
    have hlt : exp (exp a' - 1 - exp (exp a' - 1 + c) - 1 + c) < exp 0 := exp_lt hneg
    rw [exp_zero] at hlt; exact hlt
  exact depth2_small_point_absurd hx hsmall (ecv_log_nonneg hle) h

/-- **`t1 = var`, `t2 = eml (const a') var`.** Witness `exp w` with `w := A − exp(A+1) − 1`,
`A := exp a' − 1`; then `w < −2`, so `w + exp w < −1 < 0`. -/
theorem depth2_var_ecv_absurd {a' : Real}
    (h : ∀ y : Real, 0 < y →
      (EMLTree.eml EMLTree.var (EMLTree.eml (EMLTree.const a') EMLTree.var)).eval y = 1 / y) :
    False := by
  have hx : 0 < exp (exp a' - 1 - exp (exp a' - 1 + 1) - 1) := exp_pos _
  have hle : exp a' - 1 - exp (exp a' - 1 + 1) - 1 ≤ exp a' - 1 := by
    have hp : (0 : Real) < exp (exp a' - 1 + 1) := exp_pos _
    have s := add_lt_add_left hp (exp a' - 1 - exp (exp a' - 1 + 1) - 1)
    have e1 : exp a' - 1 - exp (exp a' - 1 + 1) - 1 + 0
        = exp a' - 1 - exp (exp a' - 1 + 1) - 1 := by mach_ring
    have e2 : exp a' - 1 - exp (exp a' - 1 + 1) - 1 + exp (exp a' - 1 + 1)
        = exp a' - 1 - 1 := by mach_ring
    rw [e1, e2] at s
    have hstep : exp a' - 1 - 1 ≤ exp a' - 1 := by
      have t := add_lt_add_left zero_lt_one_ax (exp a' - 1 - 1)
      have f1 : exp a' - 1 - 1 + 0 = exp a' - 1 - 1 := by mach_ring
      have f2 : exp a' - 1 - 1 + 1 = exp a' - 1 := by mach_ring
      rw [f1, f2] at t; exact le_of_lt t
    exact le_trans (le_of_lt s) hstep
  -- w < −1, hence exp w < 1 and w + exp w < 0
  have hwneg : exp a' - 1 - exp (exp a' - 1 + 1) - 1 < -1 := by
    have hb := exp_grows_strictly_thm (exp a' - 1 + 1)
    have s := add_lt_add_left hb (-exp (exp a' - 1 + 1) - 1 + -(exp a' - 1 + 1))
    have e1 : -exp (exp a' - 1 + 1) - 1 + -(exp a' - 1 + 1) + (exp a' - 1 + 1)
        = -exp (exp a' - 1 + 1) - 1 := by mach_ring
    have e2 : -exp (exp a' - 1 + 1) - 1 + -(exp a' - 1 + 1) + exp (exp a' - 1 + 1)
        = -(exp a' - 1 + 1) - 1 := by mach_ring
    rw [e1, e2] at s
    have s2 := add_lt_add_left s (exp a' - 1 + 1)
    have f1 : exp a' - 1 + 1 + (-exp (exp a' - 1 + 1) - 1)
        = exp a' - 1 - exp (exp a' - 1 + 1) - 1 + 1 := by mach_ring
    have f2 : exp a' - 1 + 1 + (-(exp a' - 1 + 1) - 1) = -1 := by mach_ring
    rw [f1, f2] at s2
    have s3 := add_lt_add_left s2 (-1 : Real)
    have g1 : (-1 : Real) + (exp a' - 1 - exp (exp a' - 1 + 1) - 1 + 1)
        = exp a' - 1 - exp (exp a' - 1 + 1) - 1 := by mach_ring
    have g2 : (-1 : Real) + -1 = -(1 + 1 : Real) := by mach_ring
    rw [g1, g2] at s3
    have hm : -(1 + 1 : Real) < -1 := by
      have t := add_lt_add_left zero_lt_one_ax (-(1 + 1) : Real)
      have p1 : (-(1 + 1) : Real) + 0 = -(1 + 1) := by mach_ring
      have p2 : (-(1 + 1) : Real) + 1 = -1 := by mach_ring
      rw [p1, p2] at t; exact t
    exact lt_trans_ax s3 hm
  have hsmall : exp (exp a' - 1 - exp (exp a' - 1 + 1) - 1)
      * exp ((EMLTree.var).eval (exp (exp a' - 1 - exp (exp a' - 1 + 1) - 1))) < 1 := by
    have hv : (EMLTree.var).eval (exp (exp a' - 1 - exp (exp a' - 1 + 1) - 1))
        = exp (exp a' - 1 - exp (exp a' - 1 + 1) - 1) := rfl
    rw [hv, ← exp_add]
    have hexp1 : exp (exp a' - 1 - exp (exp a' - 1 + 1) - 1) < 1 := by
      have hneg : exp a' - 1 - exp (exp a' - 1 + 1) - 1 < 0 := by
        have hm1 : (-1 : Real) < 0 := by
          have t := add_lt_add_left zero_lt_one_ax (-1 : Real)
          have f1 : (-1 : Real) + 0 = -1 := by mach_ring
          have f2 : (-1 : Real) + 1 = 0 := by mach_ring
          rw [f1, f2] at t; exact t
        exact lt_trans_ax hwneg hm1
      have hlt : exp (exp a' - 1 - exp (exp a' - 1 + 1) - 1) < exp 0 := exp_lt hneg
      rw [exp_zero] at hlt; exact hlt
    have hsum : exp a' - 1 - exp (exp a' - 1 + 1) - 1
        + exp (exp a' - 1 - exp (exp a' - 1 + 1) - 1) < 0 := by
      have s := add_lt_add_left hexp1 (exp a' - 1 - exp (exp a' - 1 + 1) - 1)
      have s2 := add_lt_add_left hwneg (1 : Real)
      have q1 : (1 : Real) + (exp a' - 1 - exp (exp a' - 1 + 1) - 1)
          = exp a' - 1 - exp (exp a' - 1 + 1) - 1 + 1 := by mach_ring
      have q2 : (1 : Real) + -1 = (0 : Real) := by mach_ring
      rw [q1, q2] at s2
      exact lt_trans_ax s s2
    have hlt : exp (exp a' - 1 - exp (exp a' - 1 + 1) - 1
        + exp (exp a' - 1 - exp (exp a' - 1 + 1) - 1)) < exp 0 := exp_lt hsum
    rw [exp_zero] at hlt; exact hlt
  exact depth2_small_point_absurd hx hsmall (ecv_log_nonneg hle) h

/-- **`t1 = const c`, `t2 = eml var (const b')`** — at a point where the child is already huge.

The small-point criterion cannot reach this cell: `exp x − log b'` is bounded near `0`, so its log
may be negative or (by totalisation) clamped. **Go the other way.** At a large `X` the child
`exp X − log b'` is positive and exceeds `exp (exp c)`, so `log (child) > exp c` and the tree's value
is NEGATIVE — while `1/X > 0`. -/
theorem depth2_const_evc_at {c b' X : Real} (hX : 0 < X)
    (hbig : exp (exp c) < exp X - log b')
    (h : ∀ y : Real, 0 < y →
      (EMLTree.eml (EMLTree.const c) (EMLTree.eml EMLTree.var (EMLTree.const b'))).eval y
        = 1 / y) : False := by
  have he := h X hX
  have hval : (EMLTree.eml (EMLTree.const c)
      (EMLTree.eml EMLTree.var (EMLTree.const b'))).eval X
      = exp c - log (exp X - log b') := rfl
  rw [hval] at he
  have hlog : exp c < log (exp X - log b') := by
    have hl := log_lt_log (exp_pos (exp c)) hbig
    rw [log_exp] at hl
    exact hl
  have hneg : exp c - log (exp X - log b') < 0 := by
    have s := add_lt_add_left hlog (-log (exp X - log b'))
    have e1 : -log (exp X - log b') + exp c = exp c - log (exp X - log b') := by mach_ring
    have e2 : -log (exp X - log b') + log (exp X - log b') = (0 : Real) := by mach_ring
    rw [e1, e2] at s
    exact s
  have hposv : 0 < (1 : Real) / X := one_div_pos_of_pos hX
  rw [he] at hneg
  exact lt_irrefl_ax 0 (lt_trans_ax hposv hneg)

/-- The witness: `X := exp (exp (exp c) + log b')`. Then `exp X > X > exp (exp c) + log b'`,
by `exp y > y` applied twice. -/
theorem depth2_const_evc_absurd {c b' : Real}
    (h : ∀ y : Real, 0 < y →
      (EMLTree.eml (EMLTree.const c) (EMLTree.eml EMLTree.var (EMLTree.const b'))).eval y
        = 1 / y) : False := by
  have hX : 0 < exp (exp (exp c) + log b') := exp_pos _
  have step1 : exp (exp c) + log b' < exp (exp (exp c) + log b') :=
    exp_grows_strictly_thm _
  have step2 : exp (exp (exp c) + log b') < exp (exp (exp (exp c) + log b')) :=
    exp_grows_strictly_thm _
  have hchain : exp (exp c) + log b' < exp (exp (exp (exp c) + log b')) :=
    lt_trans_ax step1 step2
  have hbig : exp (exp c) < exp (exp (exp (exp c) + log b')) - log b' := by
    have s := add_lt_add_left hchain (-log b')
    have e1 : -log b' + (exp (exp c) + log b') = exp (exp c) := by mach_ring
    have e2 : -log b' + exp (exp (exp (exp c) + log b'))
        = exp (exp (exp (exp c) + log b')) - log b' := by mach_ring
    rw [e1, e2] at s
    exact s
  exact depth2_const_evc_at hX hbig h

/-- **Uniform upper bound on the child's log:** `log (exp X − β) ≤ X + exp (−β)` for `X ≥ 0`,
for EVERY real `β`. This is what the small-point criterion could not supply. -/
theorem log_exp_sub_le {X β : Real} (hX : 0 ≤ X) :
    log (exp X - β) ≤ X + exp (-β) := by
  -- E := exp (exp (-β)) - 1 exceeds -β
  have hz : exp (-β) < exp (exp (-β)) := exp_grows_strictly_thm _
  have hnb : -β < exp (-β) := exp_grows_strictly_thm _
  have hE : -β < exp (exp (-β)) - 1 := by
    have h1 : 1 + exp (-β) < exp (exp (-β)) :=
      exp_gt_one_plus_self (exp (-β)) (exp_pos _)
    have s := add_lt_add_left h1 (-1 : Real)
    have e1 : (-1 : Real) + (1 + exp (-β)) = exp (-β) := by mach_ring
    have e2 : (-1 : Real) + exp (exp (-β)) = exp (exp (-β)) - 1 := by mach_ring
    rw [e1, e2] at s
    exact lt_trans_ax hnb s
  have hEpos : (0 : Real) ≤ exp (exp (-β)) - 1 := by
    have h1 : 1 + exp (-β) < exp (exp (-β)) :=
      exp_gt_one_plus_self (exp (-β)) (exp_pos _)
    have s := add_lt_add_left h1 (-1 : Real)
    have e1 : (-1 : Real) + (1 + exp (-β)) = exp (-β) := by mach_ring
    have e2 : (-1 : Real) + exp (exp (-β)) = exp (exp (-β)) - 1 := by mach_ring
    rw [e1, e2] at s
    exact le_of_lt (lt_trans_ax (exp_pos (-β)) s)
  -- exp X ≥ 1 scales it up
  have hX1 : (1 : Real) ≤ exp X := one_le_exp hX
  have hscale : exp (exp (-β)) - 1 ≤ exp X * (exp (exp (-β)) - 1) := by
    have s := mul_le_mul_of_nonneg_right hX1 hEpos
    have e : (1 : Real) * (exp (exp (-β)) - 1) = exp (exp (-β)) - 1 := by mach_ring
    rw [e] at s
    exact s
  have hkey : -β ≤ exp X * (exp (exp (-β)) - 1) := le_trans (le_of_lt hE) hscale
  -- hence exp X − β ≤ exp (X + exp (−β))
  have hprod : exp X - β ≤ exp (X + exp (-β)) := by
    rw [exp_add]
    have e : exp X * exp (exp (-β)) = exp X + exp X * (exp (exp (-β)) - 1) := by
      mach_mpoly [exp X, exp (exp (-β))]
    rw [e]
    have s := add_le_add_wit (le_refl (exp X)) hkey
    have f : exp X + -β = exp X - β := by mach_ring
    rw [f] at s
    exact s
  -- monotone log, and log (exp ·) = ·
  rcases lt_total (exp X - β) 0 with hlt | heq | hgt
  · rw [log_nonpos (le_of_lt hlt)]
    have : (0 : Real) ≤ X + exp (-β) :=
      le_trans hX (le_of_lt (by
        have s := add_lt_add_left (exp_pos (-β)) X
        have e : X + 0 = X := by mach_ring
        rw [e] at s; exact s))
    exact this
  · rw [heq, log_nonpos (le_refl (0 : Real))]
    have : (0 : Real) ≤ X + exp (-β) :=
      le_trans hX (le_of_lt (by
        have s := add_lt_add_left (exp_pos (-β)) X
        have e : X + 0 = X := by mach_ring
        rw [e] at s; exact s))
    exact this
  · have hl := log_le_log hgt hprod
    rw [log_exp] at hl
    exact hl

-- ▸ Inequality bookkeeping helpers (this corpus has no `linarith`).

theorem mul_lt_mul_pos_left_wit {a b c : Real} (h : a < b) (hc : 0 < c) : c * a < c * b := by
  have s := mul_lt_mul_of_pos_right h hc
  have e1 : a * c = c * a := mul_comm a c
  have e2 : b * c = c * b := mul_comm b c
  rw [e1, e2] at s
  exact s

theorem sub_le_sub_left_wit {a b c : Real} (h : b ≤ c) : a - c ≤ a - b := by
  have s := add_le_add_left h (a - b - c)
  have e1 : a - b - c + b = a - c := by mach_mpoly [a, b, c]
  have e2 : a - b - c + c = a - b := by mach_mpoly [a, b, c]
  rw [e1, e2] at s
  exact s

theorem one_lt_sub_of_add_one_lt {p q : Real} (h : p + 1 < q) : 1 < q - p := by
  have s := add_lt_add_left h (-p)
  have e1 : -p + (p + 1) = (1 : Real) := by mach_mpoly [p]
  have e2 : -p + q = q - p := by mach_mpoly [p, q]
  rw [e1, e2] at s
  exact s

theorem four_lt_exp_two : ((1 : Real) + 1) * (1 + 1) < exp (1 + 1) := by
  have hp : (0 : Real) < 1 + 1 := add_pos one_pos one_pos
  have s1 : ((1 : Real) + 1) * (1 + 1) < exp 1 * (1 + 1) :=
    mul_lt_mul_of_pos_right two_lt_exp_one hp
  have s2 : exp 1 * ((1 : Real) + 1) < exp 1 * exp 1 :=
    mul_lt_mul_pos_left_wit two_lt_exp_one (exp_pos 1)
  have hsplit : exp ((1 : Real) + 1) = exp 1 * exp 1 := exp_add 1 1
  rw [hsplit]
  exact lt_trans_ax s1 s2

theorem lt_of_sub_pos_wit {a b : Real} (h : 0 < b - a) : a < b := by
  have s := add_lt_add_left h a
  have e1 : a + 0 = a := by mach_mpoly [a]
  have e2 : a + (b - a) = b := by mach_mpoly [a, b]
  rw [e1, e2] at s
  exact s

/-- # **`t1 = var`, `t2 = eml var (const b')` — the LAST of the six.**

With `u := exp (−log b')` and `X := u + 2`: `log_exp_sub_le` caps the child's log at `X + u`, and
`exp X = exp u · exp 2 > (1+u)·4 > X + u + 1` — so the tree's value exceeds `1`, while `1/X < 1`. -/
theorem depth2_var_evc_absurd {b' : Real}
    (h : ∀ y : Real, 0 < y →
      (EMLTree.eml EMLTree.var (EMLTree.eml EMLTree.var (EMLTree.const b'))).eval y = 1 / y) :
    False := by
  have hu : (0 : Real) < exp (-log b') := exp_pos _
  have h2 : (0 : Real) < 1 + 1 := add_pos one_pos one_pos
  have hX : (0 : Real) < exp (-log b') + (1 + 1) := add_pos hu h2
  have hXgt1 : (1 : Real) < exp (-log b') + (1 + 1) := by
    refine lt_of_sub_pos_wit ?_
    have e : exp (-log b') + (1 + 1) - 1 = exp (-log b') + 1 := by mach_mpoly [exp (-log b')]
    rw [e]
    exact add_pos hu one_pos
  -- exp X > (1+u)*4 > X + u + 1
  have hone_u : 1 + exp (-log b') < exp (exp (-log b')) :=
    exp_gt_one_plus_self (exp (-log b')) hu
  have hpos1u : (0 : Real) < 1 + exp (-log b') := add_pos one_pos hu
  have c1 : (1 + exp (-log b')) * (((1 : Real) + 1) * (1 + 1))
      < (1 + exp (-log b')) * exp (1 + 1) :=
    mul_lt_mul_pos_left_wit four_lt_exp_two hpos1u
  have c2 : (1 + exp (-log b')) * exp ((1 : Real) + 1)
      < exp (exp (-log b')) * exp (1 + 1) :=
    mul_lt_mul_of_pos_right hone_u (exp_pos (1 + 1))
  have hsplit : exp (exp (-log b') + (1 + 1)) = exp (exp (-log b')) * exp (1 + 1) :=
    exp_add _ _
  have cbig : (1 + exp (-log b')) * (((1 : Real) + 1) * (1 + 1))
      < exp (exp (-log b') + (1 + 1)) := by
    rw [hsplit]; exact lt_trans_ax c1 c2
  have hlin : exp (-log b') + (1 + 1) + exp (-log b') + 1
      < (1 + exp (-log b')) * (((1 : Real) + 1) * (1 + 1)) := by
    refine lt_of_sub_pos_wit ?_
    have e : (1 + exp (-log b')) * (((1 : Real) + 1) * (1 + 1))
        - (exp (-log b') + (1 + 1) + exp (-log b') + 1)
        = exp (-log b') + exp (-log b') + 1 := by mach_mpoly [exp (-log b')]
    rw [e]
    exact add_pos (add_pos hu hu) one_pos
  have hexpX : exp (-log b') + (1 + 1) + exp (-log b') + 1
      < exp (exp (-log b') + (1 + 1)) := lt_trans_ax hlin cbig
  -- the uniform log bound
  have hb := log_exp_sub_le (X := exp (-log b') + (1 + 1)) (β := log b') (le_of_lt hX)
  have hstep : exp (exp (-log b') + (1 + 1))
      - (exp (-log b') + (1 + 1) + exp (-log b'))
      ≤ exp (exp (-log b') + (1 + 1))
        - log (exp (exp (-log b') + (1 + 1)) - log b') := sub_le_sub_left_wit hb
  have hone : (1 : Real) < exp (exp (-log b') + (1 + 1))
      - (exp (-log b') + (1 + 1) + exp (-log b')) := one_lt_sub_of_add_one_lt hexpX
  have hgt1 : (1 : Real) < exp (exp (-log b') + (1 + 1))
      - log (exp (exp (-log b') + (1 + 1)) - log b') := lt_of_lt_of_le hone hstep
  -- but the value is 1/X < 1
  have he := h _ hX
  have hval : (EMLTree.eml EMLTree.var
      (EMLTree.eml EMLTree.var (EMLTree.const b'))).eval (exp (-log b') + (1 + 1))
      = exp (exp (-log b') + (1 + 1))
        - log (exp (exp (-log b') + (1 + 1)) - log b') := rfl
  rw [hval] at he
  rw [he] at hgt1
  exact lt_irrefl_ax 1 (lt_trans_ax hgt1 (div_lt_one_of_pos_lt hX hXgt1))

/-- # **`1/x` is not `eml t1 t2` for ANY LEAF `t1` and any depth-≤1 `t2`.**

The complement of case 9 on the left: all 12 such cells, in one statement. -/
theorem inv_x_not_depth2_left_leaf {t1 t2 : EMLTree}
    (ht1 : t1.depth = 0) (ht2 : t2.depth ≤ 1) :
    ¬ (∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x) := by
  intro h
  cases t1 with
  | eml p q => exfalso; simp only [EMLTree.depth] at ht1; omega
  | const c =>
      cases t2 with
      | const b =>
          exact inv_x_not_depth2_right_constval (t2 := EMLTree.const b) (V := b)
            (by simp only [EMLTree.depth]; omega) (fun _ => rfl) h
      | var => exact t2_var_left_const_absurd h
      | eml r s =>
          cases r with
          | const a' =>
              cases s with
              | const b' =>
                  exact inv_x_not_depth2_right_constval
                    (V := exp a' - log b') (by simp only [EMLTree.depth]; omega) (fun _ => rfl) h
              | var => exact depth2_const_ecv_absurd h
              | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
          | var =>
              cases s with
              | const b' => exact depth2_const_evc_absurd h
              | var => exact depth2_const_evv_absurd h
              | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
          | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
  | var =>
      cases t2 with
      | const b =>
          exact inv_x_not_depth2_right_constval (t2 := EMLTree.const b) (V := b)
            (by simp only [EMLTree.depth]; omega) (fun _ => rfl) h
      | var => exact t2_var_left_var_absurd h
      | eml r s =>
          cases r with
          | const a' =>
              cases s with
              | const b' =>
                  exact inv_x_not_depth2_right_constval
                    (V := exp a' - log b') (by simp only [EMLTree.depth]; omega) (fun _ => rfl) h
              | var => exact depth2_var_ecv_absurd h
              | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
          | var =>
              cases s with
              | const b' => exact depth2_var_evc_absurd h
              | var => exact depth2_var_evv_absurd h
              | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
          | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega

-- ===================================================================
-- ▸ ASSEMBLY: the arm's case-9 cells, in `x·f(x) = K` form, applied at K = 1
-- ===================================================================

/-- The adapter. Everything the arm proved about `x·f(x) = K` applies at `K = 1`. -/
theorem mulK_of_inv {T : EMLTree} (h : ∀ x : Real, 0 < x → T.eval x = 1 / x)
    {x : Real} (hx : 0 < x) : x * T.eval x = 1 := by
  rw [h x hx]
  exact mul_inv x (ne_of_gt hx)

theorem depth2_u4_w2_absurd {a' : Real}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
          (EMLTree.eml (EMLTree.const a') EMLTree.var)).eval x = 1 / x) : False :=
  u4_w2_absurd (mulK_of_inv h (exp_pos _)) (mulK_of_inv h (exp_pos _))

theorem depth2_u4_w4_absurd
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
          (EMLTree.eml EMLTree.var EMLTree.var)).eval x = 1 / x) : False :=
  u4_w4_absurd (mulK_of_inv h one_pos) (mulK_of_inv h (exp_pos 1))

theorem depth2_u4_w3_absurd {c' : Real}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
          (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval x = 1 / x) : False := by
  have hp2 : (0 : Real) < 1 + 1 := add_pos one_pos one_pos
  have hp3 : (0 : Real) < 1 + 1 + 1 := add_pos hp2 one_pos
  rcases lt_total (exp 1) (log c') with hbig | heq | hsmall
  · -- big branch: the second sample point is `log (log c')`, which is positive here
    have h1e : (1 : Real) < exp 1 := lt_trans_ax one_lt_one_plus_one_local two_lt_exp_one
    have h1 : (1 : Real) < log c' := lt_trans_ax h1e hbig
    have hpos : (0 : Real) < log (log c') := by
      have t := log_lt_log one_pos h1
      rw [log_one] at t; exact t
    exact u4_w3_big_absurd hbig (mulK_of_inv h one_pos) (mulK_of_inv h hpos)
  · exact u4_w3_small_absurd (le_of_eq heq.symm) (mulK_of_inv h one_pos)
      (mulK_of_inv h hp2) (mulK_of_inv h hp3)
  · exact u4_w3_small_absurd (le_of_lt hsmall) (mulK_of_inv h one_pos)
      (mulK_of_inv h hp2) (mulK_of_inv h hp3)

theorem loglog_pos_of_one_lt {c' : Real} (h1 : (1 : Real) < log c') : 0 < log (log c') := by
  have t := log_lt_log one_pos h1
  rw [log_one] at t; exact t

theorem one_lt_exp_one_wit : (1 : Real) < exp 1 :=
  lt_trans_ax one_lt_one_plus_one_local two_lt_exp_one

-- ▸ u1 row: left child `eml (const c₁) (const c₂)`
theorem depth2_u1_w2_absurd {c₁ c₂ a' : Real}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
          (EMLTree.eml (EMLTree.const a') EMLTree.var)).eval x = 1 / x) : False :=
  u1_w2_absurd (mulK_of_inv h (exp_pos _)) (mulK_of_inv h (exp_pos _))

theorem depth2_u1_w4_absurd {c₁ c₂ : Real}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
          (EMLTree.eml EMLTree.var EMLTree.var)).eval x = 1 / x) : False :=
  u1_w4_absurd (mulK_of_inv h one_pos)
    (mulK_of_inv h (add_pos one_pos one_pos))
    (mulK_of_inv h (add_pos (add_pos one_pos one_pos) one_pos))

theorem depth2_u1_w3_absurd {c₁ c₂ c' : Real}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
          (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval x = 1 / x) : False := by
  rcases lt_total (exp 1) (log c') with hbig | heq | hsmall
  · exact u1_w3_big_absurd hbig (mulK_of_inv h one_pos)
      (mulK_of_inv h (loglog_pos_of_one_lt (lt_trans_ax one_lt_exp_one_wit hbig)))
  · exact u1_w3_small_absurd (le_of_eq heq.symm)
      (mulK_of_inv h (add_pos (add_pos (add_pos (exp_pos _) (exp_pos _)) one_pos) one_pos))
  · exact u1_w3_small_absurd (le_of_lt hsmall)
      (mulK_of_inv h (add_pos (add_pos (add_pos (exp_pos _) (exp_pos _)) one_pos) one_pos))

-- ▸ u2 row: left child `eml (const a) var`; its cells conclude `1 < K`
theorem depth2_u2_w2_absurd {a a' : Real}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var)
          (EMLTree.eml (EMLTree.const a') EMLTree.var)).eval x = 1 / x) : False :=
  lt_irrefl_ax 1 (u2_w2_K_gt_one (mulK_of_inv h (exp_pos _)))

theorem depth2_u2_w4_absurd {a : Real}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var)
          (EMLTree.eml EMLTree.var EMLTree.var)).eval x = 1 / x) : False :=
  u2_w4_absurd (mulK_of_inv h one_pos) (mulK_of_inv h (exp_pos 1))

theorem depth2_u2_w3_absurd {a c' : Real}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var)
          (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval x = 1 / x) : False := by
  rcases lt_total (1 : Real) (log c') with hbig | heq | hsmall
  · exact lt_irrefl_ax 1
      (u2_w3_big_K_gt_one hbig (mulK_of_inv h (loglog_pos_of_one_lt hbig)))
  · exact u2_w3_small_absurd (le_of_eq heq.symm) (mulK_of_inv h one_pos)
      (mulK_of_inv h (add_pos one_pos one_pos))
  · exact u2_w3_small_absurd (le_of_lt hsmall) (mulK_of_inv h one_pos)
      (mulK_of_inv h (add_pos one_pos one_pos))

-- ▸ u3 row: left child `eml var (const c₂)`
theorem depth2_u3_w2_absurd {c₂ a' : Real}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c₂))
          (EMLTree.eml (EMLTree.const a') EMLTree.var)).eval x = 1 / x) : False :=
  u3_w2_absurd (mulK_of_inv h (exp_pos _)) (mulK_of_inv h (exp_pos _))

theorem depth2_u3_w4_absurd {c₂ : Real}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c₂))
          (EMLTree.eml EMLTree.var EMLTree.var)).eval x = 1 / x) : False :=
  u3_w4_absurd (mulK_of_inv h (u3Point_pos (log c₂) 1))

theorem depth2_u3_w3_absurd {c₂ c' : Real}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c₂))
          (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval x = 1 / x) : False := by
  rcases lt_total (exp 1) (log c') with hbig | heq | hsmall
  · exact u3_w3_big_absurd hbig (mulK_of_inv h one_pos)
      (mulK_of_inv h (loglog_pos_of_one_lt (lt_trans_ax one_lt_exp_one_wit hbig)))
  · exact u3_w3_small_absurd (le_of_eq heq.symm)
      (mulK_of_inv h (u3PointS_pos (log c₂) 1 (-log c')))
  · exact u3_w3_small_absurd (le_of_lt hsmall)
      (mulK_of_inv h (u3PointS_pos (log c₂) 1 (-log c')))

-- ===================================================================
-- ▸ THE DEPTH-2 THEOREM
-- ===================================================================

/-- Depth-0 trees: `const c` and `var` are not `1/x`. -/
theorem depth0_absurd {t : EMLTree} (ht : t.depth = 0)
    (h : ∀ x : Real, 0 < x → t.eval x = 1 / x) : False := by
  have hp2 : (0 : Real) < 1 + 1 := add_pos one_pos one_pos
  have hlt : (1 : Real) / (1 + 1) < 1 := div_lt_one_of_pos_lt hp2 one_lt_one_plus_one_local
  cases t with
  | eml p q => exfalso; simp only [EMLTree.depth] at ht; omega
  | const c =>
      have h1 := h 1 one_pos
      have h2 := h (1 + 1) hp2
      have e1 : (EMLTree.const c).eval (1 : Real) = c := rfl
      have e2 : (EMLTree.const c).eval ((1 : Real) + 1) = c := rfl
      rw [e1, one_div_one] at h1
      rw [e2, h1] at h2
      rw [← h2] at hlt
      exact lt_irrefl_ax 1 hlt
  | var =>
      have h2 := h (1 + 1) hp2
      have e2 : (EMLTree.var).eval ((1 : Real) + 1) = 1 + 1 := rfl
      rw [e2] at h2
      rw [← h2] at hlt
      exact lt_irrefl_ax 1 (lt_trans_ax one_lt_one_plus_one_local hlt)

/-- Left child `eml`-rooted (case 9) — the arm's table, assembled. -/
theorem depth2_left_eml_absurd {p q t2 : EMLTree}
    (hp : p.depth = 0) (hq : q.depth = 0) (ht2 : t2.depth ≤ 1)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml p q) t2).eval x = 1 / x) : False := by
  have hcv : ∀ V : Real, (∀ x : Real, t2.eval x = V) → False := fun V hV =>
    inv_x_not_depth2_right_constval (t1 := EMLTree.eml p q) (V := V)
      (by simp only [EMLTree.depth] at hp hq ⊢; omega) hV h
  cases t2 with
  | const b => exact hcv b (fun _ => rfl)
  | var =>
      exact inv_x_not_depth2_right_var (EMLTree.eml p q)
        (by simp only [EMLTree.depth] at hp hq ⊢; omega) h
  | eml r sq =>
      cases p with
      | eml _ _ => exfalso; simp only [EMLTree.depth] at hp; omega
      | const c₁ =>
          cases q with
          | eml _ _ => exfalso; simp only [EMLTree.depth] at hq; omega
          | const c₂ =>
              cases r with
              | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
              | const a' =>
                  cases sq with
                  | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
                  | const b' => exact hcv (exp a' - log b') (fun _ => rfl)
                  | var => exact depth2_u1_w2_absurd h
              | var =>
                  cases sq with
                  | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
                  | const c' => exact depth2_u1_w3_absurd h
                  | var => exact depth2_u1_w4_absurd h
          | var =>
              cases r with
              | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
              | const a' =>
                  cases sq with
                  | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
                  | const b' => exact hcv (exp a' - log b') (fun _ => rfl)
                  | var => exact depth2_u2_w2_absurd h
              | var =>
                  cases sq with
                  | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
                  | const c' => exact depth2_u2_w3_absurd h
                  | var => exact depth2_u2_w4_absurd h
      | var =>
          cases q with
          | eml _ _ => exfalso; simp only [EMLTree.depth] at hq; omega
          | const c₂ =>
              cases r with
              | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
              | const a' =>
                  cases sq with
                  | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
                  | const b' => exact hcv (exp a' - log b') (fun _ => rfl)
                  | var => exact depth2_u3_w2_absurd h
              | var =>
                  cases sq with
                  | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
                  | const c' => exact depth2_u3_w3_absurd h
                  | var => exact depth2_u3_w4_absurd h
          | var =>
              cases r with
              | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
              | const a' =>
                  cases sq with
                  | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
                  | const b' => exact hcv (exp a' - log b') (fun _ => rfl)
                  | var => exact depth2_u4_w2_absurd h
              | var =>
                  cases sq with
                  | eml _ _ => exfalso; simp only [EMLTree.depth] at ht2; omega
                  | const c' => exact depth2_u4_w3_absurd h
                  | var => exact depth2_u4_w4_absurd h

/-- # **`1/x ∉ EML₂`.** No tree of depth ≤ 2 realises `1/x` on the positive reals. -/
theorem inv_x_not_in_eml_depth_le_2 (t : EMLTree) (ht : t.depth ≤ 2) :
    ¬ (∀ x : Real, 0 < x → t.eval x = 1 / x) := by
  intro h
  cases t with
  | const c => exact depth0_absurd (t := EMLTree.const c) rfl h
  | var => exact depth0_absurd (t := EMLTree.var) rfl h
  | eml t1 t2 =>
      have h1 : t1.depth ≤ 1 := by simp only [EMLTree.depth] at ht; omega
      have h2 : t2.depth ≤ 1 := by simp only [EMLTree.depth] at ht; omega
      cases t1 with
      | const c => exact inv_x_not_depth2_left_leaf (t1 := EMLTree.const c) rfl h2 h
      | var => exact inv_x_not_depth2_left_leaf (t1 := EMLTree.var) rfl h2 h
      | eml p q =>
          have hp : p.depth = 0 := by simp only [EMLTree.depth] at h1; omega
          have hq : q.depth = 0 := by simp only [EMLTree.depth] at h1; omega
          exact depth2_left_eml_absurd hp hq h2 h

-- ===================================================================
-- ▸ DEPTH-FREE: the reduction never needed the left child to be shallow
--
-- `left_child_mul` used `eml (const a) var`; nothing in it depended on the
-- `const`. With an ARBITRARY subtree `u` in that slot the identity still holds,
-- and it constrains the right child at EVERY depth.
-- ===================================================================

/-- `x · exp((eml u var).eval x) = exp (exp (u.eval x))` — exactly, for any `u`, any depth. -/
theorem left_eml_var_mul {u : EMLTree} {x : Real} (hx : 0 < x) :
    x * exp ((EMLTree.eml u EMLTree.var).eval x) = exp (exp (u.eval x)) := by
  have hv : (EMLTree.var).eval x = x := rfl
  have hval : (EMLTree.eml u EMLTree.var).eval x = exp (u.eval x) - log x := by
    show exp (u.eval x) - log ((EMLTree.var).eval x) = _
    rw [hv]
  have hxne : x ≠ 0 := ne_of_gt hx
  rw [hval, sub_def, exp_add, exp_neg_inv, exp_log hx]
  have step : x * (exp (exp (u.eval x)) * (1 / x))
      = exp (exp (u.eval x)) * (x * (1 / x)) := by
    mach_mpoly [x, exp (exp (u.eval x)), 1 / x]
  rw [step, mul_inv x hxne]
  mach_ring

/-- **The reduction, at any depth.** -/
theorem reduce_left_eml_var {u t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml u EMLTree.var) t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) :
    exp (exp (u.eval x)) - x * log (t2.eval x) = 1 := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have he : exp ((EMLTree.eml u EMLTree.var).eval x) - log (t2.eval x) = 1 / x := h x hx
  have hmul : x * (exp ((EMLTree.eml u EMLTree.var).eval x) - log (t2.eval x))
      = x * (1 / x) := by rw [he]
  rw [mul_inv x hxne] at hmul
  have hd : x * (exp ((EMLTree.eml u EMLTree.var).eval x) - log (t2.eval x))
      = x * exp ((EMLTree.eml u EMLTree.var).eval x) - x * log (t2.eval x) := by
    mach_mpoly [x, exp ((EMLTree.eml u EMLTree.var).eval x), log (t2.eval x)]
  rw [hd, left_eml_var_mul hx] at hmul
  exact hmul

/-- # **A depth-free structural constraint.**

If the left child has the shape `eml u var` — for **any** subtree `u`, at **any** depth — then a tree
realising `1/x` forces its RIGHT child to exceed `1` at every positive point.

Because `exp (exp (u x)) > 1` always, the reduction gives `x · log (t2 x) > 0`, hence `t2 x > 1`. -/
theorem right_child_gt_one_of_left_eml_var {u t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml u EMLTree.var) t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) : 1 < t2.eval x := by
  have hr := reduce_left_eml_var h x hx
  have hgt : 1 < exp (exp (u.eval x)) := one_lt_exp_exp (u.eval x)
  have hxl : 0 < x * log (t2.eval x) := by
    have t : (exp (exp (u.eval x)) - x * log (t2.eval x)) + (x * log (t2.eval x) - 1)
        = 1 + (x * log (t2.eval x) - 1) := by rw [hr]
    have l : (exp (exp (u.eval x)) - x * log (t2.eval x)) + (x * log (t2.eval x) - 1)
        = exp (exp (u.eval x)) - 1 := by
      mach_mpoly [x, exp (exp (u.eval x)), log (t2.eval x)]
    have r : (1 : Real) + (x * log (t2.eval x) - 1) = x * log (t2.eval x) := by
      mach_mpoly [x, log (t2.eval x)]
    rw [l, r] at t
    rw [← t]
    exact sub_pos_of_lt hgt
  -- so log (t2 x) > 0, i.e. t2 x > 1
  have hlog : 0 < log (t2.eval x) := by
    rcases lt_total 0 (log (t2.eval x)) with hp | hz | hn
    · exact hp
    · exfalso; rw [← hz] at hxl
      have e : x * (0 : Real) = 0 := by mach_ring
      rw [e] at hxl; exact lt_irrefl_ax 0 hxl
    · exfalso
      have := mul_lt_mul_pos_left_wit hn hx
      have e : x * (0 : Real) = 0 := by mach_ring
      rw [e] at this
      exact lt_irrefl_ax 0 (lt_trans_ax hxl this)
  have hpos : 0 < t2.eval x := by
    rcases lt_total 0 (t2.eval x) with hp | hz | hn
    · exact hp
    · exfalso; rw [← hz, log_nonpos (le_refl (0:Real))] at hlog; exact lt_irrefl_ax 0 hlog
    · exfalso; rw [log_nonpos (le_of_lt hn)] at hlog; exact lt_irrefl_ax 0 hlog
  rcases lt_total 1 (t2.eval x) with hg | he1 | hl
  · exact hg
  · exfalso; rw [← he1, log_one] at hlog; exact lt_irrefl_ax 0 hlog
  · exfalso
    have := log_le_log hpos (le_of_lt hl)
    rw [log_one] at this
    exact lt_irrefl_ax 0 (lt_of_lt_of_le hlog this)

end MachLib
