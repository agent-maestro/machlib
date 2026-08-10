import MachLib.EMLDepthCost
import MachLib.EMLSizeCost

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

/-- **`x · log (t2 x) = exp (exp (u x)) − 1`** — the reduction, solved for the right child. -/
theorem right_child_log_eq {u t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml u EMLTree.var) t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) :
    x * log (t2.eval x) = exp (exp (u.eval x)) - 1 := by
  have hr := reduce_left_eml_var h x hx
  have t : (exp (exp (u.eval x)) - x * log (t2.eval x)) + (x * log (t2.eval x) - 1)
      = 1 + (x * log (t2.eval x) - 1) := by rw [hr]
  have l : (exp (exp (u.eval x)) - x * log (t2.eval x)) + (x * log (t2.eval x) - 1)
      = exp (exp (u.eval x)) - 1 := by
    mach_mpoly [x, exp (exp (u.eval x)), log (t2.eval x)]
  have r : (1 : Real) + (x * log (t2.eval x) - 1) = x * log (t2.eval x) := by
    mach_mpoly [x, log (t2.eval x)]
  rw [l, r] at t
  exact t.symm

/-- # **The right child is DETERMINED by the left.**

For left child `eml u var` — any `u`, any depth — a tree realising `1/x` forces

```
t2 x = exp ((exp (exp (u x)) − 1) / x)
```

**pointwise on `(0,∞)`.** There is no freedom left in `t2` at all: choosing `u` chooses `t2`. -/
theorem right_child_determined {u t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml u EMLTree.var) t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) :
    t2.eval x = exp ((exp (exp (u.eval x)) - 1) / x) := by
  have hgt := right_child_gt_one_of_left_eml_var h x hx
  have hpos : 0 < t2.eval x := lt_trans_ax one_pos hgt
  have hlog := right_child_log_eq h x hx
  have hxne : x ≠ 0 := ne_of_gt hx
  -- log (t2 x) = (E − 1)/x
  have hdiv : log (t2.eval x) = (exp (exp (u.eval x)) - 1) / x := by
    rw [div_def _ _ hxne, ← hlog]
    have e : x * log (t2.eval x) * (1 / x) = log (t2.eval x) * (x * (1 / x)) := by
      mach_mpoly [x, log (t2.eval x), 1 / x]
    rw [e, mul_inv x hxne]
    mach_ring
  rw [← hdiv, exp_log hpos]

-- ===================================================================
-- ▸ THE GENERAL MASTER EQUATION — all left-child shapes, all depths
--
-- `left_eml_var_mul` worked because `log (var) = log x` cancels the `x`.
-- Without that cancellation the identity is still exact, just with `w` in it.
-- ===================================================================

/-- **Master equation, `w` positive.** For left child `eml u w` at any depth:
`x · exp (exp (u x)) = w x · (1 + x · log (t2 x))`. -/
theorem master_eq_pos {u w t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml u w) t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) (hw : 0 < w.eval x) :
    x * exp (exp (u.eval x)) = w.eval x * (1 + x * log (t2.eval x)) := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hlv : (EMLTree.eml u w).eval x = exp (u.eval x) - log (w.eval x) := rfl
  have hexp : exp ((EMLTree.eml u w).eval x) = exp (exp (u.eval x)) * (1 / w.eval x) := by
    rw [hlv, sub_def, exp_add, exp_neg_inv, exp_log hw]
  have he : exp ((EMLTree.eml u w).eval x) - log (t2.eval x) = 1 / x := h x hx
  rw [hexp] at he
  -- multiply by x * w
  have hmul : (x * w.eval x) * (exp (exp (u.eval x)) * (1 / w.eval x) - log (t2.eval x))
      = (x * w.eval x) * (1 / x) := by rw [he]
  have hL : (x * w.eval x) * (exp (exp (u.eval x)) * (1 / w.eval x) - log (t2.eval x))
      = x * exp (exp (u.eval x)) * (w.eval x * (1 / w.eval x))
        - w.eval x * (x * log (t2.eval x)) := by
    mach_mpoly [x, w.eval x, exp (exp (u.eval x)), log (t2.eval x), 1 / w.eval x]
  have hR : (x * w.eval x) * (1 / x) = w.eval x * (x * (1 / x)) := by
    mach_mpoly [x, w.eval x, 1 / x]
  rw [hL, hR, mul_inv x hxne, mul_inv (w.eval x) (ne_of_gt hw)] at hmul
  have e1 : x * exp (exp (u.eval x)) * 1 - w.eval x * (x * log (t2.eval x))
      = x * exp (exp (u.eval x)) - w.eval x * (x * log (t2.eval x)) := by
    mach_mpoly [x, w.eval x, exp (exp (u.eval x)), log (t2.eval x)]
  rw [e1] at hmul
  -- hmul : x·E − w·(x·L) = w·1
  have final : x * exp (exp (u.eval x))
      = w.eval x * (1 + x * log (t2.eval x)) := by
    have t : (x * exp (exp (u.eval x)) - w.eval x * (x * log (t2.eval x)))
        + w.eval x * (x * log (t2.eval x))
        = w.eval x * 1 + w.eval x * (x * log (t2.eval x)) := by rw [hmul]
    have l : (x * exp (exp (u.eval x)) - w.eval x * (x * log (t2.eval x)))
        + w.eval x * (x * log (t2.eval x)) = x * exp (exp (u.eval x)) := by
      mach_mpoly [x, w.eval x, exp (exp (u.eval x)), log (t2.eval x)]
    have r : w.eval x * 1 + w.eval x * (x * log (t2.eval x))
        = w.eval x * (1 + x * log (t2.eval x)) := by
      mach_mpoly [x, w.eval x, log (t2.eval x)]
    rw [l, r] at t
    exact t
  exact final

/-- **Master equation, `w` clamped.** Where `w x ≤ 0` the totalised `log` gives `0`, and the
equation is `x · exp (exp (u x)) − x · log (t2 x) = 1`. -/
theorem master_eq_clamped {u w t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml u w) t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) (hw : w.eval x ≤ 0) :
    x * exp (exp (u.eval x)) - x * log (t2.eval x) = 1 := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hlv : (EMLTree.eml u w).eval x = exp (u.eval x) - log (w.eval x) := rfl
  have hexp : exp ((EMLTree.eml u w).eval x) = exp (exp (u.eval x)) := by
    rw [hlv, log_nonpos hw]
    have e : exp (u.eval x) - (0 : Real) = exp (u.eval x) := by mach_ring
    rw [e]
  have he : exp ((EMLTree.eml u w).eval x) - log (t2.eval x) = 1 / x := h x hx
  rw [hexp] at he
  have hmul : x * (exp (exp (u.eval x)) - log (t2.eval x)) = x * (1 / x) := by rw [he]
  rw [mul_inv x hxne] at hmul
  have hd : x * (exp (exp (u.eval x)) - log (t2.eval x))
      = x * exp (exp (u.eval x)) - x * log (t2.eval x) := by
    mach_mpoly [x, exp (exp (u.eval x)), log (t2.eval x)]
  rw [hd] at hmul
  exact hmul

/-- **Depth-free constraint for EVERY left-child shape** (where `w` is positive):
`x · log (t2 x) > −1`. Because the left side of the master equation is strictly positive. -/
theorem right_child_log_gt_neg_one {u w t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.eml u w) t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) (hw : 0 < w.eval x) :
    -1 < x * log (t2.eval x) := by
  have hm := master_eq_pos h x hx hw
  have hlhs : 0 < x * exp (exp (u.eval x)) := mul_pos hx (exp_pos _)
  rw [hm] at hlhs
  -- 0 < w · (1 + x·L) with w > 0 forces 0 < 1 + x·L
  have hfac : 0 < 1 + x * log (t2.eval x) := by
    rcases lt_total 0 (1 + x * log (t2.eval x)) with hp | hz | hn
    · exact hp
    · exfalso
      rw [← hz] at hlhs
      have e : w.eval x * (0 : Real) = 0 := by mach_ring
      rw [e] at hlhs; exact lt_irrefl_ax 0 hlhs
    · exfalso
      have := mul_lt_mul_pos_left_wit hn hw
      have e : w.eval x * (0 : Real) = 0 := by mach_ring
      rw [e] at this
      exact lt_irrefl_ax 0 (lt_trans_ax hlhs this)
  have s := add_lt_add_left hfac (-1 : Real)
  have e1 : (-1 : Real) + 0 = -1 := by mach_ring
  have e2 : (-1 : Real) + (1 + x * log (t2.eval x)) = x * log (t2.eval x) := by
    mach_mpoly [x, log (t2.eval x)]
  rw [e1, e2] at s
  exact s

-- ===================================================================
-- ▸ A DEPTH-4 WITNESS FOR `1/x` — the master equation, read forwards
--
-- `right_child_determined` says the right child must be `exp(c/x)`-shaped.
-- That is CHEAP: `e/x` is depth 2, so `exp(e/x)` is depth 3, so the whole tree
-- is depth 4. The depth-6 chain went the long way round.
-- ===================================================================

/-- `x · exp (A − log x) = exp A`, for any real `A` and `x > 0`. -/
theorem mul_exp_sub_log {A x : Real} (hx : 0 < x) : x * exp (A - log x) = exp A := by
  have hxne : x ≠ 0 := ne_of_gt hx
  rw [sub_def, exp_add, exp_neg_inv, exp_log hx]
  have e : x * (exp A * (1 / x)) = exp A * (x * (1 / x)) := by
    mach_mpoly [x, exp A, 1 / x]
  rw [e, mul_inv x hxne]
  mach_ring

theorem eq_inv_of_mul_eq_one {v x : Real} (hx : 0 < x) (h : x * v = 1) : v = 1 / x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have e : v * (x * (1 / x)) = (x * v) * (1 / x) := by mach_mpoly [x, v, 1 / x]
  rw [mul_inv x hxne, h] at e
  have e2 : v * (1 : Real) = v := by mach_ring
  have e3 : (1 : Real) * (1 / x) = 1 / x := by mach_ring
  rw [e2, e3] at e
  exact e

/-- **The depth-4 witness.** `c := log (log (1 + exp 1))`, so `exp (exp c) = 1 + exp 1`. -/
noncomputable def invX4 : EMLTree :=
  EMLTree.eml
    (EMLTree.eml (EMLTree.const (log (log (1 + exp 1)))) EMLTree.var)
    (EMLTree.eml (EMLTree.eml (EMLTree.eml (EMLTree.const 0) EMLTree.var) (EMLTree.const 1))
      (EMLTree.const 1))

theorem invX4_depth : invX4.depth = 4 := by rfl

theorem invX4_eval : ∀ x : Real, 0 < x → invX4.eval x = 1 / x := by
  intro x hx
  have h1e : (0 : Real) < 1 + exp 1 := add_pos one_pos (exp_pos 1)
  have hlog1 : (0 : Real) < log (1 + exp 1) := by
    have s : log 1 < log (1 + exp 1) := by
      refine log_lt_log one_pos ?_
      have t := add_lt_add_left (exp_pos 1) (1 : Real)
      have e : (1 : Real) + 0 = 1 := by mach_ring
      rw [e] at t; exact t
    rw [log_one] at s; exact s
  have hc : exp (exp (log (log (1 + exp 1)))) = 1 + exp 1 := by
    rw [exp_log hlog1, exp_log h1e]
  -- the right child's log is `exp (1 − log x)`
  have hW : (EMLTree.eml (EMLTree.eml (EMLTree.const 0) EMLTree.var) (EMLTree.const 1)).eval x
      = exp (1 - log x) := by
    show exp ((EMLTree.eml (EMLTree.const (0 : Real)) EMLTree.var).eval x)
        - log ((EMLTree.const (1 : Real)).eval x) = _
    show exp (exp (0 : Real) - log x) - log (1 : Real) = _
    rw [exp_zero, log_one]
    mach_mpoly [exp (1 - log x)]
  have hR : log ((EMLTree.eml (EMLTree.eml (EMLTree.eml (EMLTree.const 0) EMLTree.var)
        (EMLTree.const 1)) (EMLTree.const 1)).eval x) = exp (1 - log x) := by
    show log (exp ((EMLTree.eml (EMLTree.eml (EMLTree.const (0:Real)) EMLTree.var)
          (EMLTree.const 1)).eval x) - log ((EMLTree.const (1:Real)).eval x)) = _
    rw [hW]
    show log (exp (exp (1 - log x)) - log (1 : Real)) = _
    rw [log_one]
    have e : exp (exp (1 - log x)) - (0 : Real) = exp (exp (1 - log x)) := by mach_ring
    rw [e, log_exp]
  -- value
  have hval : invX4.eval x
      = exp (exp (log (log (1 + exp 1))) - log x) - exp (1 - log x) := by
    show exp ((EMLTree.eml (EMLTree.const (log (log (1 + exp 1)))) EMLTree.var).eval x)
        - log ((EMLTree.eml (EMLTree.eml (EMLTree.eml (EMLTree.const 0) EMLTree.var)
            (EMLTree.const 1)) (EMLTree.const 1)).eval x) = _
    rw [hR]
    rfl
  refine eq_inv_of_mul_eq_one hx ?_
  rw [hval]
  have hd : x * (exp (exp (log (log (1 + exp 1))) - log x) - exp (1 - log x))
      = x * exp (exp (log (log (1 + exp 1))) - log x) - x * exp (1 - log x) := by
    mach_mpoly [x, exp (exp (log (log (1 + exp 1))) - log x), exp (1 - log x)]
  rw [hd, mul_exp_sub_log hx, mul_exp_sub_log hx, hc]
  mach_ring

/-- # **`1/x ∈ EML₄`** — and with `inv_x_not_in_eml_depth_le_2`, **`d(1/x) ∈ {3, 4}`.** -/
theorem inv_x_mem_EML_depth_four :
    ∃ t : EMLTree, t.depth = 4 ∧ ∀ x : Real, 0 < x → t.eval x = 1 / x :=
  ⟨invX4, invX4_depth, invX4_eval⟩

-- ===================================================================
-- ▸ TOWARD DEPTH 3: how big can a shallow tree be near `0`?
--
-- `right_child_determined` forces the right child to be `exp(K/x)` — a
-- super-exponential blow-up at `0`. Shallow trees cannot do that, and the
-- reusable reason is that every depth-≤1 tree is at most `M − log x`.
-- ===================================================================

/-- **Every depth-≤1 tree is `≤ M − log x` on `(0,1]`**, for a constant `M` depending only on the
tree. The `−log x` is the fastest growth available that shallow. -/
theorem depth_le_one_upper_bound (T : EMLTree) (hT : T.depth ≤ 1) :
    ∃ M : Real, ∀ x : Real, 0 < x → x ≤ 1 → T.eval x ≤ M - log x := by
  have key : ∀ (M : Real) (x : Real), 0 < x → x ≤ 1 → M ≤ M - log x := by
    intro M x hx h1
    have hl : log x ≤ 0 := log_nonpos_of_le_one hx h1
    have s := add_le_add_wit (le_refl M) (by
      have t := add_le_add_left hl (-log x)
      have e1 : -log x + log x = (0 : Real) := by mach_ring
      have e2 : -log x + 0 = -log x := by mach_ring
      rw [e1, e2] at t
      exact t : (0 : Real) ≤ -log x)
    have e1 : M + 0 = M := by mach_ring
    have e2 : M + -log x = M - log x := by mach_ring
    rw [e1, e2] at s
    exact s
  cases T with
  | const c => exact ⟨c, fun x hx h1 => key c x hx h1⟩
  | var =>
      refine ⟨1, fun x hx h1 => ?_⟩
      show x ≤ 1 - log x
      exact le_trans h1 (key 1 x hx h1)
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd hT (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hT (by simp only [EMLTree.depth]; omega)
          | const q => exact ⟨exp p - log q, fun x hx h1 => key _ x hx h1⟩
          | var =>
              refine ⟨exp p, fun x hx h1 => ?_⟩
              show exp p - log x ≤ exp p - log x
              exact le_refl _
      | var =>
          cases b with
          | eml _ _ => exact absurd hT (by simp only [EMLTree.depth]; omega)
          | const q =>
              refine ⟨exp 1 - log q, fun x hx h1 => ?_⟩
              show exp x - log q ≤ exp 1 - log q - log x
              have he : exp x ≤ exp 1 := exp_monotone h1
              have s := add_le_add_wit he (le_refl (-log q))
              have e1 : exp x + -log q = exp x - log q := by mach_ring
              have e2 : exp 1 + -log q = exp 1 - log q := by mach_ring
              rw [e1, e2] at s
              exact le_trans s (key (exp 1 - log q) x hx h1)
          | var =>
              refine ⟨exp 1, fun x hx h1 => ?_⟩
              show exp x - log x ≤ exp 1 - log x
              have he : exp x ≤ exp 1 := exp_monotone h1
              have s := add_le_add_wit he (le_refl (-log x))
              have e1 : exp x + -log x = exp x - log x := by mach_ring
              have e2 : exp 1 + -log x = exp 1 - log x := by mach_ring
              rw [e1, e2] at s
              exact s

/-- `L·exp(−L−1) ≤ 1` for `L > 0`, from `L < exp (L+1)`. A division-free way to pick a cutoff
below both `1` and `L`. -/
theorem shrink_le_one {L : Real} (hL : 0 < L) : L * exp (-L - 1) ≤ 1 := by
  have hlt : L < exp (L + 1) := by
    have h1 : L < exp L := exp_grows_strictly_thm L
    have h2 : exp L < exp (L + 1) := by
      refine exp_lt ?_
      have s := add_lt_add_left one_pos L
      have e : L + 0 = L := by mach_ring
      rw [e] at s; exact s
    exact lt_trans_ax h1 h2
  -- L * exp(-L-1) ≤ 1  ⟸  L ≤ exp(L+1)
  have hinv : exp (-L - 1) = 1 / exp (L + 1) := by
    have e : -L - 1 = -(L + 1) := by mach_ring
    rw [e, exp_neg_inv]
  rw [hinv]
  have hpos : 0 < exp (L + 1) := exp_pos _
  have hd : L * (1 / exp (L + 1)) = L / exp (L + 1) :=
    (div_def L (exp (L + 1)) (ne_of_gt hpos)).symm
  rw [hd]
  exact le_of_lt (div_lt_one_of_pos_lt hpos hlt)

theorem shrink_pos {L : Real} (hL : 0 < L) : 0 < L * exp (-L - 1) := mul_pos hL (exp_pos _)

theorem shrink_lt {L : Real} (hL : 0 < L) : L * exp (-L - 1) < L := by
  have h1 : exp (-L - 1) < 1 := by
    have hneg : -L - 1 < 0 := by
      have hm1 : (-1 : Real) < 0 := by
        have t := add_lt_add_left zero_lt_one_ax (-1 : Real)
        have f1 : (-1 : Real) + 0 = -1 := by mach_ring
        have f2 : (-1 : Real) + 1 = 0 := by mach_ring
        rw [f1, f2] at t; exact t
      have s := add_lt_add_left hL (-L - 1)
      have e1 : -L - 1 + 0 = -L - 1 := by mach_ring
      have e2 : -L - 1 + L = -1 := by mach_ring
      rw [e1, e2] at s
      exact lt_trans_ax s hm1
    have hlt : exp (-L - 1) < exp 0 := exp_lt hneg
    rw [exp_zero] at hlt; exact hlt
  have s := mul_lt_mul_pos_left_wit h1 hL
  have e : L * (1 : Real) = L := by mach_ring
  rw [e] at s
  exact s

theorem neg_le_neg_wit {a b : Real} (h : a ≤ b) : -b ≤ -a := by
  have s := add_le_add_left h (-a - b)
  have e1 : -a - b + a = -b := by mach_mpoly [a, b]
  have e2 : -a - b + b = -a := by mach_mpoly [a, b]
  rw [e1, e2] at s
  exact s

theorem le_sub_log_of_le_one (M : Real) {x : Real} (hx : 0 < x) (h1 : x ≤ 1) :
    M ≤ M - log x := by
  have hl : log x ≤ 0 := log_nonpos_of_le_one hx h1
  have s := add_le_add_wit (le_refl M) (neg_le_neg_wit hl)
  have e1 : M + -(0 : Real) = M := by mach_ring
  have e2 : M + -log x = M - log x := by mach_ring
  rw [e1, e2] at s
  exact s

/-- `−log v ≤ −log w` when `0 < w ≤ v`. -/
theorem neg_log_le_of_ge {v w : Real} (hw : 0 < w) (h : w ≤ v) : -log v ≤ -log w :=
  neg_le_neg_wit (log_le_log hw h)

/-- **The companion bound, in its cutoff form.** For every depth-≤1 tree there are `N` and a cutoff
`δ ∈ (0,1]` with `−log (T x) ≤ N − log x` on `(0, δ]`. The cutoff is unavoidable: `eml var (const q)`
has a zero inside `(0,1]` when `log q ∈ (1, e)`. -/
theorem depth_le_one_neglog_bound (T : EMLTree) (hT : T.depth ≤ 1) :
    ∃ N δ : Real, 0 < δ ∧ δ ≤ 1 ∧
      ∀ x : Real, 0 < x → x ≤ δ → -log (T.eval x) ≤ N - log x := by
  cases T with
  | const c =>
      exact ⟨-log c, 1, one_pos, le_refl 1, fun x hx h1 => le_sub_log_of_le_one _ hx h1⟩
  | var =>
      refine ⟨0, 1, one_pos, le_refl 1, fun x hx h1 => ?_⟩
      show -log x ≤ 0 - log x
      have e : (0 : Real) - log x = -log x := by mach_ring
      rw [e]
      exact le_refl _
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd hT (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hT (by simp only [EMLTree.depth]; omega)
          | const q =>
              exact ⟨-log (exp p - log q), 1, one_pos, le_refl 1,
                fun x hx h1 => le_sub_log_of_le_one _ hx h1⟩
          | var =>
              refine ⟨-p, 1, one_pos, le_refl 1, fun x hx h1 => ?_⟩
              show -log (exp p - log x) ≤ -p - log x
              have hge : exp p ≤ exp p - log x := by
                have hl : log x ≤ 0 := log_nonpos_of_le_one hx h1
                have s := add_le_add_wit (le_refl (exp p)) (neg_le_neg_wit hl)
                have e1 : exp p + -(0 : Real) = exp p := by mach_ring
                have e2 : exp p + -log x = exp p - log x := by mach_ring
                rw [e1, e2] at s; exact s
              have hb := neg_log_le_of_ge (exp_pos p) hge
              rw [log_exp] at hb
              exact le_trans hb (le_sub_log_of_le_one (-p) hx h1)
      | var =>
          cases b with
          | eml _ _ => exact absurd hT (by simp only [EMLTree.depth]; omega)
          | var =>
              refine ⟨0, 1, one_pos, le_refl 1, fun x hx h1 => ?_⟩
              show -log (exp x - log x) ≤ 0 - log x
              have hone : (1 : Real) ≤ exp x - log x := by
                have hex : (1 : Real) ≤ exp x := one_le_exp (le_of_lt hx)
                have hl : log x ≤ 0 := log_nonpos_of_le_one hx h1
                have s := add_le_add_wit hex (neg_le_neg_wit hl)
                have e1 : (1 : Real) + -(0 : Real) = 1 := by mach_ring
                have e2 : exp x + -log x = exp x - log x := by mach_ring
                rw [e1, e2] at s; exact s
              have hb := neg_log_le_of_ge one_pos hone
              rw [log_one] at hb
              have e : -(0 : Real) = 0 := by mach_ring
              rw [e] at hb
              exact le_trans hb (le_sub_log_of_le_one 0 hx h1)
          | const q =>
              rcases lt_total (log q) 1 with hsm | heq | hbg
              · -- log q < 1 : value ≥ 1 − log q > 0 everywhere
                refine ⟨-log (1 - log q), 1, one_pos, le_refl 1, fun x hx h1 => ?_⟩
                show -log (exp x - log q) ≤ -log (1 - log q) - log x
                have hpos : (0 : Real) < 1 - log q := by
                  refine lt_of_sub_pos_wit ?_
                  have e : (1 : Real) - log q - 0 = 1 - log q := by mach_ring
                  rw [e]
                  refine lt_of_sub_pos_wit ?_
                  have e2 : (1 : Real) - log q - 0 = 1 - log q := by mach_ring
                  rw [e2]
                  have s := add_lt_add_left hsm (-log q)
                  have f1 : -log q + log q = (0 : Real) := by mach_ring
                  have f2 : -log q + 1 = 1 - log q := by mach_ring
                  rw [f1, f2] at s; exact s
                have hge : (1 : Real) - log q ≤ exp x - log q := by
                  have hex : (1 : Real) ≤ exp x := one_le_exp (le_of_lt hx)
                  have s := add_le_add_wit hex (le_refl (-log q))
                  have e1 : (1 : Real) + -log q = 1 - log q := by mach_ring
                  have e2 : exp x + -log q = exp x - log q := by mach_ring
                  rw [e1, e2] at s; exact s
                exact le_trans (neg_log_le_of_ge hpos hge)
                  (le_sub_log_of_le_one _ hx h1)
              · -- log q = 1 : value = exp x − 1 ≥ x
                refine ⟨0, 1, one_pos, le_refl 1, fun x hx h1 => ?_⟩
                show -log (exp x - log q) ≤ 0 - log x
                have hge : x ≤ exp x - log q := by
                  rw [heq]
                  have hb := exp_gt_one_plus_self x hx
                  have s := add_lt_add_left hb (-1 : Real)
                  have e1 : (-1 : Real) + (1 + x) = x := by mach_ring
                  have e2 : (-1 : Real) + exp x = exp x - 1 := by mach_ring
                  rw [e1, e2] at s
                  exact le_of_lt s
                have hb := neg_log_le_of_ge hx hge
                have e : (0 : Real) - log x = -log x := by mach_ring
                rw [e]
                exact hb
              · -- log q > 1 : below the cutoff the value is NEGATIVE and log clamps to 0
                have hL : (0 : Real) < log (log q) := by
                  have hq : (0 : Real) < log q := lt_trans_ax one_pos hbg
                  have t := log_lt_log one_pos hbg
                  rw [log_one] at t; exact t
                refine ⟨0, log (log q) * exp (-log (log q) - 1), shrink_pos hL,
                  shrink_le_one hL, fun x hx hd => ?_⟩
                show -log (exp x - log q) ≤ 0 - log x
                have hq : (0 : Real) < log q := lt_trans_ax one_pos hbg
                have hxL : x < log (log q) := lt_of_le_of_lt hd (shrink_lt hL)
                have hneg : exp x - log q ≤ 0 := by
                  have s : exp x < exp (log (log q)) := exp_lt hxL
                  rw [exp_log hq] at s
                  have t := add_lt_add_left s (-log q)
                  have e1 : -log q + exp x = exp x - log q := by mach_ring
                  have e2 : -log q + log q = (0 : Real) := by mach_ring
                  rw [e1, e2] at t
                  exact le_of_lt t
                rw [log_nonpos hneg]
                have e1 : -(0 : Real) = 0 := by mach_ring
                have e2 : (0 : Real) - log x = -log x := by mach_ring
                rw [e1, e2]
                have hl : log x ≤ 0 := log_nonpos_of_le_one hx
                  (le_trans hd (shrink_le_one hL))
                have hh := neg_le_neg_wit hl
                have e3 : -(0 : Real) = 0 := by mach_ring
                rw [e3] at hh
                exact hh

theorem log_lt_self {y : Real} (hy : 0 < y) : log y < y := by
  have h := exp_grows_strictly_thm (log y)
  rw [exp_log hy] at h
  exact h

theorem log_one_div {x : Real} (hx : 0 < x) : log (1 / x) = -log x := by
  have hinv : (0 : Real) < 1 / x := one_div_pos_of_pos hx
  have hm : log ((1 / x) * x) = log (1 / x) + log x := log_mul hinv hx
  have e : (1 / x) * x = 1 := by
    have h := mul_inv x (ne_of_gt hx)
    have c : (1 / x) * x = x * (1 / x) := mul_comm (1 / x) x
    rw [c, h]
  rw [e, log_one] at hm
  -- hm : 0 = log (1/x) + log x
  have t : (0 : Real) - log x = log (1 / x) + log x - log x := by rw [← hm]
  have l : log (1 / x) + log x - log x = log (1 / x) := by mach_mpoly [log (1 / x), log x]
  have r : (0 : Real) - log x = -log x := by mach_ring
  rw [l, r] at t
  exact t.symm

/-- `−x·log x ≤ 1` on `(0,∞)`, from `log y < y` at `y = 1/x`. -/
theorem neg_x_log_x_le_one {x : Real} (hx : 0 < x) : x * -log x ≤ 1 := by
  have hinv : (0 : Real) < 1 / x := one_div_pos_of_pos hx
  have h := log_lt_self hinv
  rw [log_one_div hx] at h
  have s := mul_lt_mul_pos_left_wit h hx
  rw [mul_inv x (ne_of_gt hx)] at s
  exact le_of_lt s

/-- `x · M ≤ exp M` for `0 < x ≤ 1` — the three sign cases of `M`. -/
theorem mul_le_exp_of_le_one {x M : Real} (hx : 0 < x) (h1 : x ≤ 1) : x * M ≤ exp M := by
  rcases lt_total 0 M with hp | hz | hn
  · have t := mul_le_mul_of_nonneg_right h1 (le_of_lt hp)
    have e : (1 : Real) * M = M := by mach_ring
    rw [e] at t
    exact le_trans t (le_of_lt (exp_grows_strictly_thm M))
  · rw [← hz]
    have e : x * (0 : Real) = 0 := by mach_ring
    rw [e]
    exact le_of_lt (exp_pos 0)
  · have t := mul_le_mul_of_nonneg_left (le_of_lt hn) (le_of_lt hx)
    have e : x * (0 : Real) = 0 := by mach_ring
    rw [e] at t
    exact le_trans t (le_of_lt (exp_pos M))

/-- **The depth-≤2 growth ceiling.** `x · T x ≤ C` near `0` — a depth-≤2 tree cannot outgrow `C/x`. -/
theorem depth_le_two_growth_ceiling (T : EMLTree) (hT : T.depth ≤ 2) :
    ∃ C δ : Real, 0 < δ ∧ δ ≤ 1 ∧ ∀ x : Real, 0 < x → x ≤ δ → x * T.eval x ≤ C := by
  have fromUpper : ∀ (S : EMLTree) (M : Real),
      (∀ x : Real, 0 < x → x ≤ 1 → S.eval x ≤ M - log x) →
      ∀ x : Real, 0 < x → x ≤ 1 → x * S.eval x ≤ exp M + 1 := by
    intro S M hM x hx h1
    have h2 : x * S.eval x ≤ x * (M - log x) :=
      mul_le_mul_of_nonneg_left (hM x hx h1) (le_of_lt hx)
    have hsplit : x * (M - log x) = x * M + x * -log x := by mach_mpoly [x, M, log x]
    rw [hsplit] at h2
    exact le_trans h2 (add_le_add_wit (mul_le_exp_of_le_one hx h1) (neg_x_log_x_le_one hx))
  cases Nat.lt_or_ge T.depth 2 with
  | inl hlt =>
      obtain ⟨M, hM⟩ := depth_le_one_upper_bound T (by omega)
      exact ⟨exp M + 1, 1, one_pos, le_refl 1, fun x hx h1 => fromUpper T M hM x hx h1⟩
  | inr hge =>
      cases T with
      | const c => exact absurd hge (by simp only [EMLTree.depth]; omega)
      | var => exact absurd hge (by simp only [EMLTree.depth]; omega)
      | eml A B =>
          have hA : A.depth ≤ 1 := by simp only [EMLTree.depth] at hT; omega
          have hB : B.depth ≤ 1 := by simp only [EMLTree.depth] at hT; omega
          obtain ⟨MA, hMA⟩ := depth_le_one_upper_bound A hA
          obtain ⟨NB, d, hd0, hd1, hNB⟩ := depth_le_one_neglog_bound B hB
          refine ⟨exp MA + (exp NB + 1), d, hd0, hd1, fun x hx hxd => ?_⟩
          have hx1 : x ≤ 1 := le_trans hxd hd1
          show x * (exp (A.eval x) - log (B.eval x)) ≤ _
          have hsplit : x * (exp (A.eval x) - log (B.eval x))
              = x * exp (A.eval x) + x * -log (B.eval x) := by
            mach_mpoly [x, exp (A.eval x), log (B.eval x)]
          rw [hsplit]
          have hL : x * exp (A.eval x) ≤ exp MA := by
            have he : exp (A.eval x) ≤ exp (MA - log x) := exp_monotone (hMA x hx hx1)
            have hm := mul_le_mul_of_nonneg_left he (le_of_lt hx)
            rw [mul_exp_sub_log hx] at hm
            exact hm
          have hR : x * -log (B.eval x) ≤ exp NB + 1 := by
            have hm := mul_le_mul_of_nonneg_left (hNB x hx hxd) (le_of_lt hx)
            have hs : x * (NB - log x) = x * NB + x * -log x := by mach_mpoly [x, NB, log x]
            rw [hs] at hm
            exact le_trans hm
              (add_le_add_wit (mul_le_exp_of_le_one hx hx1) (neg_x_log_x_le_one hx))
          exact add_le_add_wit hL hR

/-- `exp t ≥ t + t` for `t ≥ 1`, from `exp t = e·exp(t−1) ≥ e·t` and `e > 2`. -/
theorem exp_ge_two_mul {t : Real} (ht : 1 ≤ t) : t + t ≤ exp t := by
  have hsplit : exp t = exp 1 * exp (t - 1) := by
    rw [← exp_add]
    have e : (1 : Real) + (t - 1) = t := by mach_ring
    rw [e]
  have h1 : (1 : Real) + (t - 1) ≤ exp (t - 1) := by
    rcases (le_iff_lt_or_eq (1 : Real) t).mp ht with hlt | heq
    · have hp : (0 : Real) < t - 1 := by
        refine lt_of_sub_pos_wit ?_
        have e : t - 1 - 0 = t - 1 := by mach_ring
        rw [e]
        refine lt_of_sub_pos_wit ?_
        have e2 : t - 1 - 0 = t - 1 := by mach_ring
        rw [e2]
        have s := add_lt_add_left hlt (-1 : Real)
        have f1 : (-1 : Real) + 1 = 0 := by mach_ring
        have f2 : (-1 : Real) + t = t - 1 := by mach_ring
        rw [f1, f2] at s; exact s
      exact le_of_lt (exp_gt_one_plus_self (t - 1) hp)
    · rw [← heq]
      have e : (1 : Real) + (1 - 1) = 1 := by mach_ring
      have e2 : (1 : Real) - 1 = 0 := by mach_ring
      rw [e, e2, exp_zero]
      exact le_refl 1
  have ht0 : (0 : Real) < t := lt_of_lt_of_le one_pos ht
  have h2 : t + t ≤ exp 1 * t := by
    have hs : ((1 : Real) + 1) * t ≤ exp 1 * t :=
      mul_le_mul_of_nonneg_right (le_of_lt two_lt_exp_one) (le_of_lt ht0)
    have e : ((1 : Real) + 1) * t = t + t := by mach_mpoly [t]
    rw [e] at hs; exact hs
  have h3 : exp 1 * t ≤ exp 1 * exp (t - 1) := by
    have e : (1 : Real) + (t - 1) = t := by mach_ring
    rw [e] at h1
    exact mul_le_mul_of_nonneg_left h1 (le_of_lt (exp_pos 1))
  rw [hsplit]
  exact le_trans h2 h3

-- ▸ Small helpers for the depth-3 separation, each verified before use.

theorem mul_exp_neg_eq {K T : Real} (hK : 0 < K) : K * exp (-T) = exp (log K - T) := by
  rw [sub_def, exp_add, exp_log hK]

theorem sub_le_of_sub_le {a b c : Real} (h : a - c ≤ b) : a - b ≤ c := by
  have s := add_le_add_left h (c - b)
  have e1 : c - b + (a - c) = a - b := by mach_mpoly [a, b, c]
  have e2 : c - b + b = c := by mach_mpoly [b, c]
  rw [e1, e2] at s
  exact s

/-- `exp (-T) · L = 1 → L = exp T`. -/
theorem eq_exp_of_exp_neg_mul {T L : Real} (h : exp (-T) * L = 1) : L = exp T := by
  have hne : exp (-T) ≠ 0 := ne_of_gt (exp_pos _)
  have hmul : exp (-T) * L = exp (-T) * exp T := by
    rw [h, ← exp_add]
    have e : -T + T = (0 : Real) := by mach_ring
    rw [e, exp_zero]
  exact mul_left_cancel hne hmul

/-- `C < K · exp (exp T − T)` whenever `K > 0` and `T ≥ 1` and `T > log C − log K`. -/
theorem beats_const {K C T : Real} (hK : 0 < K) (hT1 : 1 ≤ T)
    (hTC : log C - log K < T) : C < K * exp (exp T - T) := by
  have hstep : exp T ≤ exp (exp T - T) := by
    refine exp_monotone ?_
    have h2 := exp_ge_two_mul hT1
    have s := add_le_add_left h2 (-T)
    have e1 : -T + (T + T) = T := by mach_mpoly [T]
    have e2 : -T + exp T = exp T - T := by mach_ring
    rw [e1, e2] at s
    exact s
  have hKexp : K * exp T ≤ K * exp (exp T - T) := mul_le_mul_of_nonneg_left hstep (le_of_lt hK)
  have hform : K * exp T = exp (log K + T) := by rw [exp_add, exp_log hK]
  rcases lt_total 0 C with hCp | hCz | hCn
  · have hlt : log C < log K + T := by
      have s := add_lt_add_left hTC (log K)
      have e1 : log K + (log C - log K) = log C := by mach_mpoly [log C, log K]
      rw [e1] at s
      exact s
    have hex : exp (log C) < exp (log K + T) := exp_lt hlt
    rw [exp_log hCp] at hex
    rw [hform] at hKexp
    exact lt_of_lt_of_le hex hKexp
  · rw [← hCz]
    exact lt_of_lt_of_le (mul_pos hK (exp_pos _)) (le_refl _)
  · exact lt_of_lt_of_le hCn (le_of_lt (mul_pos hK (exp_pos _)))

/-- The algebraic core of the depth-3 separation, with the sample point `K·exp(−T)` supplied. -/
theorem depth3_sep_core {c : Real} {t2 : EMLTree} {C T : Real}
    (hT1 : 1 ≤ T) (hTC : log C - log (exp (exp c) - 1) < T)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml (EMLTree.const c) EMLTree.var) t2).eval x = 1 / x)
    (hceil : ((exp (exp c) - 1) * exp (-T))
      * t2.eval ((exp (exp c) - 1) * exp (-T)) ≤ C) : False := by
  have hK : (0 : Real) < exp (exp c) - 1 := sub_pos_of_lt (one_lt_exp_exp c)
  have hX0 : (0 : Real) < (exp (exp c) - 1) * exp (-T) := mul_pos hK (exp_pos _)
  -- the pin, at this point
  have hpin := right_child_log_eq h _ hX0
  have hcv : (EMLTree.const c).eval ((exp (exp c) - 1) * exp (-T)) = c := rfl
  rw [hcv] at hpin
  -- cancel K
  have hcancel : exp (-T) * log (t2.eval ((exp (exp c) - 1) * exp (-T))) = 1 := by
    refine mul_left_cancel (ne_of_gt hK) ?_
    have e1 : (exp (exp c) - 1)
        * (exp (-T) * log (t2.eval ((exp (exp c) - 1) * exp (-T))))
        = ((exp (exp c) - 1) * exp (-T))
          * log (t2.eval ((exp (exp c) - 1) * exp (-T))) := by
      mach_mpoly [exp (exp c), exp (-T), log (t2.eval ((exp (exp c) - 1) * exp (-T)))]
    have e2 : (exp (exp c) - 1) * (1 : Real) = exp (exp c) - 1 := by mach_ring
    rw [e1, e2, hpin]
  have hL : log (t2.eval ((exp (exp c) - 1) * exp (-T))) = exp T :=
    eq_exp_of_exp_neg_mul hcancel
  -- so the right child is exp (exp T)
  have hgt1 := right_child_gt_one_of_left_eml_var h _ hX0
  have hval : t2.eval ((exp (exp c) - 1) * exp (-T)) = exp (exp T) := by
    rw [← hL, exp_log (lt_trans_ax one_pos hgt1)]
  -- and the product is K · exp (exp T − T)
  have hprod : ((exp (exp c) - 1) * exp (-T))
      * t2.eval ((exp (exp c) - 1) * exp (-T))
      = (exp (exp c) - 1) * exp (exp T - T) := by
    rw [hval]
    have e1 : ((exp (exp c) - 1) * exp (-T)) * exp (exp T)
        = (exp (exp c) - 1) * (exp (-T) * exp (exp T)) := by
      mach_mpoly [exp (exp c), exp (-T), exp (exp T)]
    rw [e1, ← exp_add]
    have e2 : -T + exp T = exp T - T := by mach_ring
    rw [e2]
  rw [hprod] at hceil
  exact lt_irrefl_ax C (lt_of_lt_of_le (beats_const hK hT1 hTC) hceil)

/-- # **Depth 3, branch `t1 = eml (const c) var`: IMPOSSIBLE.**

The determination forces the right child to be `exp(exp T)` at `K·exp(−T)`, so the product is
`K·exp(exp T − T)` — which outgrows the depth-≤2 ceiling. `T` is chosen so that **both** demands
(beat `C`, stay under the cutoff `d`) hold at once; they are co-monotone, so no `min` is needed. -/
theorem depth3_left_const_var_absurd {c : Real} {t2 : EMLTree} (ht2 : t2.depth ≤ 2)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml (EMLTree.const c) EMLTree.var) t2).eval x = 1 / x) : False := by
  obtain ⟨C, d, hd0, hd1, hC⟩ := depth_le_two_growth_ceiling t2 ht2
  have hK : (0 : Real) < exp (exp c) - 1 := sub_pos_of_lt (one_lt_exp_exp c)
  have hA : (0 : Real) < exp (log C - log (exp (exp c) - 1)) := exp_pos _
  have hB : (0 : Real) < exp (log (exp (exp c) - 1) - log d) := exp_pos _
  refine depth3_sep_core (C := C) (T := 1 + exp (log C - log (exp (exp c) - 1))
      + exp (log (exp (exp c) - 1) - log d)) ?_ ?_ h ?_
  · -- 1 ≤ T
    have s := add_le_add_wit (add_le_add_wit (le_refl (1 : Real)) (le_of_lt hA)) (le_of_lt hB)
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at s; exact s
  · -- log C − log K < T
    have h1 := exp_grows_strictly_thm (log C - log (exp (exp c) - 1))
    have s := add_le_add_wit (add_le_add_wit (le_of_lt one_pos)
      (le_refl (exp (log C - log (exp (exp c) - 1))))) (le_of_lt hB)
    have e : (0 : Real) + exp (log C - log (exp (exp c) - 1)) + 0
        = exp (log C - log (exp (exp c) - 1)) := by mach_ring
    rw [e] at s
    exact lt_of_lt_of_le h1 s
  · -- the ceiling applies at this point
    refine hC _ (mul_pos hK (exp_pos _)) ?_
    rw [mul_exp_neg_eq hK]
    -- log K − log d ≤ T
    have hTd : log (exp (exp c) - 1) - log d
        ≤ 1 + exp (log C - log (exp (exp c) - 1))
          + exp (log (exp (exp c) - 1) - log d) := by
      have h1 := exp_grows_strictly_thm (log (exp (exp c) - 1) - log d)
      have s := add_le_add_wit (add_le_add_wit (le_of_lt one_pos) (le_of_lt hA))
        (le_refl (exp (log (exp (exp c) - 1) - log d)))
      have e : (0 : Real) + 0 + exp (log (exp (exp c) - 1) - log d)
          = exp (log (exp (exp c) - 1) - log d) := by mach_ring
      rw [e] at s
      exact le_of_lt (lt_of_lt_of_le h1 s)
    have hmono := exp_monotone (sub_le_of_sub_le hTd)
    rw [exp_log hd0] at hmono
    exact hmono

/-- **Every depth-≤1 tree is bounded BELOW by a constant on `(0,1]`.** No cutoff needed here — the
`−log x` that made the upper bound grow only helps a lower bound. -/
theorem depth_le_one_lower_bound (T : EMLTree) (hT : T.depth ≤ 1) :
    ∃ m : Real, ∀ x : Real, 0 < x → x ≤ 1 → m ≤ T.eval x := by
  have hnl : ∀ x : Real, 0 < x → x ≤ 1 → (0 : Real) ≤ -log x := by
    intro x hx h1
    have hh := neg_le_neg_wit (log_nonpos_of_le_one hx h1)
    have e : -(0 : Real) = 0 := by mach_ring
    rw [e] at hh; exact hh
  cases T with
  | const c => exact ⟨c, fun x hx h1 => le_refl c⟩
  | var => exact ⟨0, fun x hx h1 => le_of_lt hx⟩
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd hT (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hT (by simp only [EMLTree.depth]; omega)
          | const q => exact ⟨exp p - log q, fun x hx h1 => le_refl _⟩
          | var =>
              refine ⟨exp p, fun x hx h1 => ?_⟩
              show exp p ≤ exp p - log x
              have s := add_le_add_wit (le_refl (exp p)) (hnl x hx h1)
              have e1 : exp p + 0 = exp p := by mach_ring
              have e2 : exp p + -log x = exp p - log x := by mach_ring
              rw [e1, e2] at s; exact s
      | var =>
          cases b with
          | eml _ _ => exact absurd hT (by simp only [EMLTree.depth]; omega)
          | const q =>
              refine ⟨1 - log q, fun x hx h1 => ?_⟩
              show (1 : Real) - log q ≤ exp x - log q
              have s := add_le_add_wit (one_le_exp (le_of_lt hx)) (le_refl (-log q))
              have e1 : (1 : Real) + -log q = 1 - log q := by mach_ring
              have e2 : exp x + -log q = exp x - log q := by mach_ring
              rw [e1, e2] at s; exact s
          | var =>
              refine ⟨1, fun x hx h1 => ?_⟩
              show (1 : Real) ≤ exp x - log x
              have s := add_le_add_wit (one_le_exp (le_of_lt hx)) (hnl x hx h1)
              have e1 : (1 : Real) + 0 = 1 := by mach_ring
              have e2 : exp x + -log x = exp x - log x := by mach_ring
              rw [e1, e2] at s; exact s

theorem one_le_of_mul_ge {K u : Real} (hK : 0 < K) (h : K ≤ K * u) : 1 ≤ u := by
  rcases lt_total u 1 with hlt | heq | hgt
  · exfalso
    have s := mul_lt_mul_pos_left_wit hlt hK
    have e : K * (1 : Real) = K := by mach_ring
    rw [e] at s
    exact lt_irrefl_ax K (lt_of_le_of_lt h s)
  · rw [heq]
    exact le_refl 1
  · exact le_of_lt hgt

theorem exp_le_of_exp_neg_mul_ge {T L : Real} (h : 1 ≤ exp (-T) * L) : exp T ≤ L := by
  have hm := mul_le_mul_of_nonneg_left h (le_of_lt (exp_pos T))
  have e1 : exp T * (1 : Real) = exp T := by mach_ring
  have e2 : exp T * (exp (-T) * L) = (exp T * exp (-T)) * L := by
    mach_mpoly [exp T, exp (-T), L]
  rw [e1, e2, ← exp_add] at hm
  have e3 : T + -T = (0 : Real) := by mach_ring
  rw [e3, exp_zero] at hm
  have e4 : (1 : Real) * L = L := by mach_ring
  rw [e4] at hm
  exact hm

/-- The separation core in **inequality** form — the pin only needs to be a lower bound. -/
theorem depth3_sep_core_ge {t2 : EMLTree} {C T K : Real} (hK : 0 < K)
    (hT1 : 1 ≤ T) (hTC : log C - log K < T)
    (hpin : K ≤ (K * exp (-T)) * log (t2.eval (K * exp (-T))))
    (hgt : 0 < t2.eval (K * exp (-T)))
    (hceil : (K * exp (-T)) * t2.eval (K * exp (-T)) ≤ C) : False := by
  have hassoc : (K * exp (-T)) * log (t2.eval (K * exp (-T)))
      = K * (exp (-T) * log (t2.eval (K * exp (-T)))) := by
    mach_mpoly [K, exp (-T), log (t2.eval (K * exp (-T)))]
  rw [hassoc] at hpin
  have hL := exp_le_of_exp_neg_mul_ge (one_le_of_mul_ge hK hpin)
  have hval : exp (exp T) ≤ t2.eval (K * exp (-T)) := by
    have hm := exp_monotone hL
    rw [exp_log hgt] at hm
    exact hm
  have hX0 : (0 : Real) < K * exp (-T) := mul_pos hK (exp_pos _)
  have hprod : K * exp (exp T - T) ≤ (K * exp (-T)) * t2.eval (K * exp (-T)) := by
    have hm := mul_le_mul_of_nonneg_left hval (le_of_lt hX0)
    have e1 : (K * exp (-T)) * exp (exp T) = K * (exp (-T) * exp (exp T)) := by
      mach_mpoly [K, exp (-T), exp (exp T)]
    rw [e1, ← exp_add] at hm
    have e2 : -T + exp T = exp T - T := by mach_ring
    rw [e2] at hm
    exact hm
  exact lt_irrefl_ax C (lt_of_lt_of_le (beats_const hK hT1 hTC) (le_trans hprod hceil))

/-- # **Depth 3: NO left child of shape `eml a var` works — for ANY depth-≤1 `a`.**

Generalises `depth3_left_const_var_absurd`. The lower bound on `a` makes the pin an inequality,
which is all the separation core needs. -/
theorem depth3_left_eml_var_absurd {a t2 : EMLTree} (ha : a.depth ≤ 1) (ht2 : t2.depth ≤ 2)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml a EMLTree.var) t2).eval x = 1 / x) : False := by
  obtain ⟨m, hm⟩ := depth_le_one_lower_bound a ha
  obtain ⟨C, d, hd0, hd1, hC⟩ := depth_le_two_growth_ceiling t2 ht2
  have hK : (0 : Real) < exp (exp m) - 1 := sub_pos_of_lt (one_lt_exp_exp m)
  have hA : (0 : Real) < exp (log C - log (exp (exp m) - 1)) := exp_pos _
  have hB : (0 : Real) < exp (log (exp (exp m) - 1) - log d) := exp_pos _
  -- the point sits under the cutoff
  have hXd : (exp (exp m) - 1)
      * exp (-(1 + exp (log C - log (exp (exp m) - 1))
        + exp (log (exp (exp m) - 1) - log d))) ≤ d := by
    rw [mul_exp_neg_eq hK]
    have hTd : log (exp (exp m) - 1) - log d
        ≤ 1 + exp (log C - log (exp (exp m) - 1))
          + exp (log (exp (exp m) - 1) - log d) := by
      have h1 := exp_grows_strictly_thm (log (exp (exp m) - 1) - log d)
      have s := add_le_add_wit (add_le_add_wit (le_of_lt one_pos) (le_of_lt hA))
        (le_refl (exp (log (exp (exp m) - 1) - log d)))
      have e : (0 : Real) + 0 + exp (log (exp (exp m) - 1) - log d)
          = exp (log (exp (exp m) - 1) - log d) := by mach_ring
      rw [e] at s
      exact le_of_lt (lt_of_lt_of_le h1 s)
    have hmono := exp_monotone (sub_le_of_sub_le hTd)
    rw [exp_log hd0] at hmono
    exact hmono
  have hX0 : (0 : Real) < (exp (exp m) - 1)
      * exp (-(1 + exp (log C - log (exp (exp m) - 1))
        + exp (log (exp (exp m) - 1) - log d))) := mul_pos hK (exp_pos _)
  have hX1 : (exp (exp m) - 1)
      * exp (-(1 + exp (log C - log (exp (exp m) - 1))
        + exp (log (exp (exp m) - 1) - log d))) ≤ 1 := le_trans hXd hd1
  refine depth3_sep_core_ge (C := C) hK ?_ ?_ ?_ ?_ (hC _ hX0 hXd)
  · have s := add_le_add_wit (add_le_add_wit (le_refl (1 : Real)) (le_of_lt hA)) (le_of_lt hB)
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at s; exact s
  · have h1 := exp_grows_strictly_thm (log C - log (exp (exp m) - 1))
    have s := add_le_add_wit (add_le_add_wit (le_of_lt one_pos)
      (le_refl (exp (log C - log (exp (exp m) - 1))))) (le_of_lt hB)
    have e : (0 : Real) + exp (log C - log (exp (exp m) - 1)) + 0
        = exp (log C - log (exp (exp m) - 1)) := by mach_ring
    rw [e] at s
    exact lt_of_lt_of_le h1 s
  · -- the pin, as a lower bound
    have hpin := right_child_log_eq h _ hX0
    rw [hpin]
    have hge : exp (exp m) ≤ exp (exp (a.eval ((exp (exp m) - 1)
        * exp (-(1 + exp (log C - log (exp (exp m) - 1))
          + exp (log (exp (exp m) - 1) - log d)))))) :=
      exp_monotone (exp_monotone (hm ((exp (exp m) - 1)
        * exp (-(1 + exp (log C - log (exp (exp m) - 1))
          + exp (log (exp (exp m) - 1) - log d)))) hX0 hX1))
    have s := add_le_add_wit hge (le_refl (-1 : Real))
    have e1 : exp (exp m) + -1 = exp (exp m) - 1 := by mach_ring
    have e2 : exp (exp (a.eval ((exp (exp m) - 1)
        * exp (-(1 + exp (log C - log (exp (exp m) - 1))
          + exp (log (exp (exp m) - 1) - log d)))))) + -1
        = exp (exp (a.eval ((exp (exp m) - 1)
        * exp (-(1 + exp (log C - log (exp (exp m) - 1))
          + exp (log (exp (exp m) - 1) - log d)))))) - 1 := by mach_ring
    rw [e1, e2] at s
    exact s
  · exact lt_trans_ax one_pos (right_child_gt_one_of_left_eml_var h _ hX0)

/-- **Pin for a LEAF left child.** `t1 = const c` forces `x · log (t2 x) = x·exp c − 1` — so
`x · log (t2 x) → −1`, whereas any *bounded-below* right child would give `→ 0`. -/
theorem leaf_const_pin {c : Real} {t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.const c) t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) : x * log (t2.eval x) = x * exp c - 1 := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have he : exp c - log (t2.eval x) = 1 / x := h x hx
  have hmul : x * (exp c - log (t2.eval x)) = x * (1 / x) := by rw [he]
  rw [mul_inv x hxne] at hmul
  have hd : x * (exp c - log (t2.eval x)) = x * exp c - x * log (t2.eval x) := by
    mach_mpoly [x, exp c, log (t2.eval x)]
  rw [hd] at hmul
  -- x·exp c − x·L = 1  ⟹  x·L = x·exp c − 1
  have t : (x * exp c - x * log (t2.eval x)) + (x * log (t2.eval x) - 1)
      = 1 + (x * log (t2.eval x) - 1) := by rw [hmul]
  have l : (x * exp c - x * log (t2.eval x)) + (x * log (t2.eval x) - 1)
      = x * exp c - 1 := by mach_mpoly [x, exp c, log (t2.eval x)]
  have r : (1 : Real) + (x * log (t2.eval x) - 1) = x * log (t2.eval x) := by
    mach_mpoly [x, log (t2.eval x)]
  rw [l, r] at t
  exact t.symm

/-- Same for `t1 = var`: `x · log (t2 x) = x·exp x − 1`. -/
theorem leaf_var_pin {t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) : x * log (t2.eval x) = x * exp x - 1 := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have he : exp x - log (t2.eval x) = 1 / x := h x hx
  have hmul : x * (exp x - log (t2.eval x)) = x * (1 / x) := by rw [he]
  rw [mul_inv x hxne] at hmul
  have hd : x * (exp x - log (t2.eval x)) = x * exp x - x * log (t2.eval x) := by
    mach_mpoly [x, exp x, log (t2.eval x)]
  rw [hd] at hmul
  have t : (x * exp x - x * log (t2.eval x)) + (x * log (t2.eval x) - 1)
      = 1 + (x * log (t2.eval x) - 1) := by rw [hmul]
  have l : (x * exp x - x * log (t2.eval x)) + (x * log (t2.eval x) - 1)
      = x * exp x - 1 := by mach_mpoly [x, exp x, log (t2.eval x)]
  have r : (1 : Real) + (x * log (t2.eval x) - 1) = x * log (t2.eval x) := by
    mach_mpoly [x, log (t2.eval x)]
  rw [l, r] at t
  exact t.symm

/-- **The leaf branch forces the right child BELOW `1` near `0`** — indeed `log (t2 x) < 0`
whenever `x·exp c < 1`. This is the opposite of `right_child_gt_one_of_left_eml_var`, and it is why
the small-point criterion cannot reach this branch. -/
theorem leaf_const_forces_small {c : Real} {t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.const c) t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) (hsm : x * exp c < 1) : x * log (t2.eval x) < 0 := by
  rw [leaf_const_pin h x hx]
  refine lt_of_sub_pos_wit ?_
  have e : (0 : Real) - (x * exp c - 1) = 1 - x * exp c := by mach_mpoly [x, exp c]
  rw [e]
  refine lt_of_sub_pos_wit ?_
  have e2 : (1 : Real) - x * exp c - 0 = 1 - x * exp c := by mach_mpoly [x, exp c]
  rw [e2]
  have s := add_lt_add_left hsm (-(x * exp c))
  have f1 : -(x * exp c) + x * exp c = (0 : Real) := by mach_mpoly [x, exp c]
  have f2 : -(x * exp c) + 1 = 1 - x * exp c := by mach_mpoly [x, exp c]
  rw [f1, f2] at s
  exact s

/-- **The DUAL ceiling at depth ≤ 1**: `x · log (T x) ≥ −C` near `0`. No depth-≤1 tree is as small
as `exp(−c/x)`. This follows from the companion bound; the depth-≤2 case does **not**. -/
theorem depth_le_one_dual_ceiling (T : EMLTree) (hT : T.depth ≤ 1) :
    ∃ C δ : Real, 0 < δ ∧ δ ≤ 1 ∧
      ∀ x : Real, 0 < x → x ≤ δ → -C ≤ x * log (T.eval x) := by
  obtain ⟨N, d, hd0, hd1, hN⟩ := depth_le_one_neglog_bound T hT
  refine ⟨exp N + 1, d, hd0, hd1, fun x hx hxd => ?_⟩
  have hx1 : x ≤ 1 := le_trans hxd hd1
  -- x·(−log (T x)) ≤ exp N + 1
  have hm := mul_le_mul_of_nonneg_left (hN x hx hxd) (le_of_lt hx)
  have hs : x * (N - log x) = x * N + x * -log x := by mach_mpoly [x, N, log x]
  rw [hs] at hm
  have hub : x * -log (T.eval x) ≤ exp N + 1 :=
    le_trans hm (add_le_add_wit (mul_le_exp_of_le_one hx hx1) (neg_x_log_x_le_one hx))
  -- rewrite as a lower bound on x·log (T x)
  have he : x * -log (T.eval x) = -(x * log (T.eval x)) := by
    mach_mpoly [x, log (T.eval x)]
  rw [he] at hub
  have s := neg_le_neg_wit hub
  have e : -(-(x * log (T.eval x))) = x * log (T.eval x) := by
    mach_mpoly [x, log (T.eval x)]
  rw [e] at s
  exact s

/-- **The tangent bound for `log`, on `[1,∞)`:** `log y ≤ y − 1`.

⚠ **The `0 < y < 1` half is NOT derivable here.** It needs `1 + z ≤ exp z` for **negative** `z`, and
the corpus only has the positive-argument form (`exp_gt_one_plus_self`, `exp_tangent_line_strict`).
Every route from the positive version back to the negative one goes through the statement itself. -/
theorem log_le_sub_one_of_one_le {y : Real} (hy : 1 ≤ y) : log y ≤ y - 1 := by
  rcases (le_iff_lt_or_eq (1 : Real) y).mp hy with hlt | heq
  · have hp : (0 : Real) < y - 1 := by
      refine lt_of_sub_pos_wit ?_
      have e : y - 1 - 0 = y - 1 := by mach_ring
      rw [e]
      have s := add_lt_add_left hlt (-1 : Real)
      have f1 : (-1 : Real) + 1 = 0 := by mach_ring
      have f2 : (-1 : Real) + y = y - 1 := by mach_ring
      rw [f1, f2] at s
      exact s
    have h := exp_gt_one_plus_self (y - 1) hp
    have e : (1 : Real) + (y - 1) = y := by mach_ring
    rw [e] at h
    have hl := log_le_log (lt_of_lt_of_le one_pos hy) (le_of_lt h)
    rw [log_exp] at hl
    exact hl
  · rw [← heq, log_one]
    have e : (1 : Real) - 1 = 0 := by mach_ring
    rw [e]
    exact le_refl 0

theorem one_lt_of_log_pos {y : Real} (h : 0 < log y) : 1 < y := by
  rcases lt_total 1 y with hg | he | hl
  · exact hg
  · exfalso; rw [← he, log_one] at h; exact lt_irrefl_ax 0 h
  · exfalso
    rcases lt_total 0 y with hp | hz | hn
    · have hle := log_le_log hp (le_of_lt hl)
      rw [log_one] at hle
      exact lt_irrefl_ax 0 (lt_of_lt_of_le h hle)
    · rw [← hz, log_nonpos (le_refl (0 : Real))] at h; exact lt_irrefl_ax 0 h
    · rw [log_nonpos (le_of_lt hn)] at h; exact lt_irrefl_ax 0 h

/-- # **The axiom gap was illusory.**

Wherever a depth-2 tree `eml A B` VANISHES, its right operand exceeds `1`:
`log (B x) = exp (A x) > 0` forces `B x > 1`.

**So the delicate case never needs the tangent bound below `1`** — the very condition that defines
it (`exp (A x) = log (B x)`, i.e. the tree vanishing) puts `B` in exactly the region where
`log_le_sub_one_of_one_le` applies. -/
theorem vanishing_forces_right_gt_one {A B : EMLTree} {x : Real}
    (hzero : exp (A.eval x) - log (B.eval x) = 0) : 1 < B.eval x := by
  have hlog : log (B.eval x) = exp (A.eval x) := by
    have t : exp (A.eval x) - log (B.eval x) + log (B.eval x)
        = 0 + log (B.eval x) := by rw [hzero]
    have l : exp (A.eval x) - log (B.eval x) + log (B.eval x) = exp (A.eval x) := by
      mach_mpoly [exp (A.eval x), log (B.eval x)]
    have r : (0 : Real) + log (B.eval x) = log (B.eval x) := by mach_ring
    rw [l, r] at t
    exact t.symm
  have hpos : (0 : Real) < log (B.eval x) := by rw [hlog]; exact exp_pos _
  exact one_lt_of_log_pos hpos

theorem mul_ge_neg_exp_of_le_one {x M : Real} (hx : 0 < x) (h1 : x ≤ 1) :
    -exp (-M) ≤ x * M := by
  have hMe : -exp (-M) ≤ M := by
    have hh := neg_le_neg_wit (le_of_lt (exp_grows_strictly_thm (-M)))
    have e : -(-M) = M := by mach_ring
    rw [e] at hh
    exact hh
  have hzero : -exp (-M) ≤ 0 := by
    have hh := neg_le_neg_wit (le_of_lt (exp_pos (-M)))
    have e : -(0 : Real) = 0 := by mach_ring
    rw [e] at hh
    exact hh
  rcases lt_total M 0 with hn | hz | hp
  · have hx1 : x - 1 ≤ 0 := by
      have s := add_le_add_left h1 (-1 : Real)
      have e1 : (-1 : Real) + x = x - 1 := by mach_ring
      have e2 : (-1 : Real) + 1 = 0 := by mach_ring
      rw [e1, e2] at s; exact s
    have hA : (0 : Real) ≤ -(x - 1) := by
      have hh := neg_le_neg_wit hx1
      have e : -(0 : Real) = 0 := by mach_ring
      rw [e] at hh; exact hh
    have hB : (0 : Real) ≤ -M := by
      have hh := neg_le_neg_wit (le_of_lt hn)
      have e : -(0 : Real) = 0 := by mach_ring
      rw [e] at hh; exact hh
    have hnn : (0 : Real) ≤ (x - 1) * M := by
      have hp2 := mul_nonneg hA hB
      have e : -(x - 1) * -M = (x - 1) * M := by mach_mpoly [x, M]
      rw [e] at hp2; exact hp2
    have s3 := add_le_add_left hnn M
    have e7 : M + 0 = M := by mach_ring
    have e8 : M + (x - 1) * M = x * M := by mach_mpoly [x, M]
    rw [e7, e8] at s3
    exact le_trans hMe s3
  · rw [hz]
    have e : x * (0 : Real) = 0 := by mach_ring
    have e2 : -(0 : Real) = 0 := by mach_ring
    rw [e, e2]
    have hh := neg_le_neg_wit (le_of_lt (exp_pos (0 : Real)))
    rw [e2] at hh
    exact hh
  · exact le_trans hzero (le_of_lt (mul_pos hx hp))

/-- # **Linear vanishing is enough.** If `T x ≥ K·x` near `0` then the dual ceiling holds.

This is why the delicate case is finishable: the cancellation in `exp(A x) − log(B x)` is at worst
**polynomial**, and even the crudest polynomial rate — linear — already bounds `x · log (T x)`. -/
theorem dual_bound_of_linear_lower {T : EMLTree} {K : Real} (hK : 0 < K)
    (h : ∀ x : Real, 0 < x → x ≤ 1 → K * x ≤ T.eval x) :
    ∀ x : Real, 0 < x → x ≤ 1 → -(exp (-log K) + 1) ≤ x * log (T.eval x) := by
  intro x hx h1
  have hKx : (0 : Real) < K * x := mul_pos hK hx
  have hlog : log (K * x) ≤ log (T.eval x) := log_le_log hKx (h x hx h1)
  rw [log_mul hK hx] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog (le_of_lt hx)
  have hsplit : x * (log K + log x) = x * log K + x * log x := by
    mach_mpoly [x, log K, log x]
  rw [hsplit] at hm
  have hA : -exp (-log K) ≤ x * log K := mul_ge_neg_exp_of_le_one hx h1
  have hB : (-1 : Real) ≤ x * log x := by
    have hh := neg_le_neg_wit (neg_x_log_x_le_one hx)
    have e : -(x * -log x) = x * log x := by mach_mpoly [x, log x]
    rw [e] at hh
    exact hh
  have hsum := add_le_add_wit hA hB
  have e : -exp (-log K) + -1 = -(exp (-log K) + 1) := by mach_ring
  rw [e] at hsum
  exact le_trans hsum hm

theorem log_nonpos_of_le_one' {y : Real} (hy : y ≤ 1) : log y ≤ 0 := by
  rcases lt_total 0 y with hp | hz | hn
  · have h := log_le_log hp hy
    rw [log_one] at h; exact h
  · rw [← hz, log_nonpos (le_refl (0 : Real))]
    exact le_refl 0
  · rw [log_nonpos (le_of_lt hn)]
    exact le_refl 0

/-- **Dual ceiling, regime 1: the right operand is `≤ 1`.** Then `−log (B x) ≥ 0`, so the tree is at
least `exp (A x) ≥ exp m`, and the bound is immediate. -/
theorem dual_bound_regime_one {A B : EMLTree} {m x : Real}
    (hx : 0 < x) (h1 : x ≤ 1) (hmA : m ≤ A.eval x) (hB : B.eval x ≤ 1) :
    -exp (-m) ≤ x * log ((EMLTree.eml A B).eval x) := by
  have hval : (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) := rfl
  have hlogB : log (B.eval x) ≤ 0 := log_nonpos_of_le_one' hB
  have hge : exp m ≤ (EMLTree.eml A B).eval x := by
    rw [hval]
    have s := add_le_add_wit (exp_monotone hmA) (neg_le_neg_wit hlogB)
    have e1 : exp m + -(0 : Real) = exp m := by mach_ring
    have e2 : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by
      mach_ring
    rw [e1, e2] at s
    exact s
  have hpos : (0 : Real) < (EMLTree.eml A B).eval x := lt_of_lt_of_le (exp_pos m) hge
  have hlog : m ≤ log ((EMLTree.eml A B).eval x) := by
    have h := log_le_log (exp_pos m) hge
    rw [log_exp] at h
    exact h
  have hm := mul_le_mul_of_nonneg_left hlog (le_of_lt hx)
  exact le_trans (mul_ge_neg_exp_of_le_one hx h1) hm

/-- **Dual ceiling, regime 2: the tree is `≤ 0`.** Totalisation clamps its log to `0`. -/
theorem dual_bound_regime_two {A B : EMLTree} {x : Real}
    (hT : (EMLTree.eml A B).eval x ≤ 0) :
    (0 : Real) ≤ x * log ((EMLTree.eml A B).eval x) := by
  rw [log_nonpos hT]
  have e : x * (0 : Real) = 0 := by mach_ring
  rw [e]
  exact le_refl 0

/-- # **A regime-3 floor, in the hardest representative case.**

`A = var`, `B = eml var (const c')` with the coincidence `log c' = 1 − e`, so the tree is
`exp x − log (exp x − 1 + e)` — both terms growing, nearly cancelling, value `→ 0` at `0`.

Factoring `exp x − 1 + e = e·(1 + (exp x − 1)·e⁻¹)` and applying `log y ≤ y − 1` (**the derivable
half**, since the factor is `≥ 1`) gives a clean **linear** floor. -/
theorem regime3_floor_var_expvar {x : Real} (hx : 0 < x) :
    (1 - exp (-1)) * x ≤ exp x - log (exp x - 1 + exp 1) := by
  have hem : exp 1 * exp (-1) = 1 := by
    rw [← exp_add]
    have e : (1 : Real) + -1 = 0 := by mach_ring
    rw [e, exp_zero]
  have hxg : (1 : Real) + x < exp x := exp_gt_one_plus_self x hx
  have hu1 : (1 : Real) ≤ 1 + (exp x - 1) * exp (-1) := by
    have hp : (0 : Real) ≤ (exp x - 1) * exp (-1) := by
      refine le_of_lt (mul_pos ?_ (exp_pos _))
      refine lt_of_sub_pos_wit ?_
      have e : exp x - 1 - 0 = exp x - 1 := by mach_ring
      rw [e]
      refine lt_of_sub_pos_wit ?_
      have e2 : exp x - 1 - 0 = exp x - 1 := by mach_ring
      rw [e2]
      have s := add_lt_add_left (lt_trans_ax (by
        have t := add_lt_add_left hx (1 : Real)
        have f : (1 : Real) + 0 = 1 := by mach_ring
        rw [f] at t; exact t) hxg) (-1 : Real)
      have f1 : (-1 : Real) + 1 = 0 := by mach_ring
      have f2 : (-1 : Real) + exp x = exp x - 1 := by mach_ring
      rw [f1, f2] at s
      exact s
    have s := add_le_add_wit (le_refl (1 : Real)) hp
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at s
    exact s
  have hfac : exp x - 1 + exp 1 = exp 1 * (1 + (exp x - 1) * exp (-1)) := by
    have e : exp 1 * (1 + (exp x - 1) * exp (-1))
        = exp 1 + (exp x - 1) * (exp 1 * exp (-1)) := by
      mach_mpoly [exp 1, exp x, exp (-1)]
    rw [e, hem]
    mach_mpoly [exp 1, exp x]
  have hupper : log (exp x - 1 + exp 1) ≤ 1 + (exp x - 1) * exp (-1) := by
    rw [hfac, log_mul (exp_pos 1) (lt_of_lt_of_le one_pos hu1), log_exp]
    have hl := log_le_sub_one_of_one_le hu1
    have e : (1 : Real) + (1 + (exp x - 1) * exp (-1)) - 1
        = 1 + (exp x - 1) * exp (-1) := by mach_mpoly [exp x, exp (-1)]
    have s := add_le_add_wit (le_refl (1 : Real)) hl
    have e2 : (1 : Real) + ((1 + (exp x - 1) * exp (-1)) - 1)
        = 1 + (exp x - 1) * exp (-1) := by mach_mpoly [exp x, exp (-1)]
    rw [e2] at s
    exact s
  -- exp x − log(...) ≥ (exp x − 1)(1 − exp(−1)) ≥ (1 − exp(−1))·x
  have hstep : (exp x - 1) * (1 - exp (-1)) ≤ exp x - log (exp x - 1 + exp 1) := by
    have s := sub_le_sub_left_wit (a := exp x) hupper
    have e : exp x - (1 + (exp x - 1) * exp (-1)) = (exp x - 1) * (1 - exp (-1)) := by
      mach_mpoly [exp x, exp (-1)]
    rw [e] at s
    exact s
  have hK : (0 : Real) ≤ 1 - exp (-1) := by
    refine le_of_lt (lt_of_sub_pos_wit ?_)
    have e : (1 : Real) - exp (-1) - 0 = 1 - exp (-1) := by mach_ring
    rw [e]
    refine lt_of_sub_pos_wit ?_
    have e2 : (1 : Real) - exp (-1) - 0 = 1 - exp (-1) := by mach_ring
    rw [e2]
    have hlt : exp (-1 : Real) < 1 := by
      have hn : (-1 : Real) < 0 := by
        have t := add_lt_add_left zero_lt_one_ax (-1 : Real)
        have f1 : (-1 : Real) + 0 = -1 := by mach_ring
        have f2 : (-1 : Real) + 1 = 0 := by mach_ring
        rw [f1, f2] at t; exact t
      have h := exp_lt hn
      rw [exp_zero] at h; exact h
    have s := add_lt_add_left hlt (-exp (-1 : Real))
    have f1 : -exp (-1 : Real) + exp (-1) = (0 : Real) := by mach_ring
    have f2 : -exp (-1 : Real) + 1 = 1 - exp (-1) := by mach_ring
    rw [f1, f2] at s
    exact s
  have hxle : x ≤ exp x - 1 := by
    have s := add_lt_add_left hxg (-1 : Real)
    have f1 : (-1 : Real) + (1 + x) = x := by mach_ring
    have f2 : (-1 : Real) + exp x = exp x - 1 := by mach_ring
    rw [f1, f2] at s
    exact le_of_lt s
  have hmul : (1 - exp (-1)) * x ≤ (exp x - 1) * (1 - exp (-1)) := by
    have s := mul_le_mul_of_nonneg_left hxle hK
    have e : (1 - exp (-1)) * (exp x - 1) = (exp x - 1) * (1 - exp (-1)) := by
      mach_mpoly [exp x, exp (-1)]
    rw [e] at s
    exact s
  exact le_trans hmul hstep

/-- Regime-3 floor, case `A = var`, `B` constant (coincidence forces `log β = 1`). -/
theorem regime3_floor_var_const {x : Real} (hx : 0 < x) : x ≤ exp x - 1 := by
  have h := exp_gt_one_plus_self x hx
  have s := add_lt_add_left h (-1 : Real)
  have f1 : (-1 : Real) + (1 + x) = x := by mach_ring
  have f2 : (-1 : Real) + exp x = exp x - 1 := by mach_ring
  rw [f1, f2] at s
  exact le_of_lt s

/-- Regime-3 floor, case `A = eml var (const q)`, `B` constant. Coincidence forces
`log β = exp (1 − q)`, and the tree factors as `exp(1−q)·(exp(exp x − 1) − 1)`. -/
theorem regime3_floor_expvar_const {q x : Real} (hx : 0 < x) :
    exp (1 - q) * x ≤ exp (exp x - q) - exp (1 - q) := by
  have hw : (0 : Real) < exp x - 1 := lt_of_lt_of_le hx (regime3_floor_var_const hx)
  have hsplit : exp (exp x - q) = exp (1 - q) * exp (exp x - 1) := by
    rw [← exp_add]
    have e : (1 - q) + (exp x - 1) = exp x - q := by mach_ring
    rw [e]
  have hinner : exp x - 1 ≤ exp (exp x - 1) - 1 := by
    have h := exp_gt_one_plus_self (exp x - 1) hw
    have s := add_lt_add_left h (-1 : Real)
    have f1 : (-1 : Real) + (1 + (exp x - 1)) = exp x - 1 := by mach_ring
    have f2 : (-1 : Real) + exp (exp x - 1) = exp (exp x - 1) - 1 := by mach_ring
    rw [f1, f2] at s
    exact le_of_lt s
  have hchain : x ≤ exp (exp x - 1) - 1 := le_trans (regime3_floor_var_const hx) hinner
  have hm := mul_le_mul_of_nonneg_left hchain (le_of_lt (exp_pos (1 - q)))
  have e : exp (1 - q) * (exp (exp x - 1) - 1) = exp (1 - q) * exp (exp x - 1) - exp (1 - q) := by
    mach_mpoly [exp (1 - q), exp (exp x - 1)]
  rw [e, ← hsplit] at hm
  exact hm

/-- **Quadratic vanishing is also enough.** The boundary sub-case of the last shape pair vanishes to
second order; a `K·x²` floor still bounds `x · log (T x)`. -/
theorem dual_bound_of_quadratic_lower {T : EMLTree} {K : Real} (hK : 0 < K)
    (h : ∀ x : Real, 0 < x → x ≤ 1 → K * (x * x) ≤ T.eval x) :
    ∀ x : Real, 0 < x → x ≤ 1 → -(exp (-log K) + 1 + 1) ≤ x * log (T.eval x) := by
  intro x hx h1
  have hxx : (0 : Real) < x * x := mul_pos hx hx
  have hKxx : (0 : Real) < K * (x * x) := mul_pos hK hxx
  have hlog : log (K * (x * x)) ≤ log (T.eval x) := log_le_log hKxx (h x hx h1)
  rw [log_mul hK hxx, log_mul hx hx] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog (le_of_lt hx)
  have hsplit : x * (log K + (log x + log x)) = x * log K + (x * log x + x * log x) := by
    mach_mpoly [x, log K, log x]
  rw [hsplit] at hm
  have hA : -exp (-log K) ≤ x * log K := mul_ge_neg_exp_of_le_one hx h1
  have hB : (-1 : Real) ≤ x * log x := by
    have hh := neg_le_neg_wit (neg_x_log_x_le_one hx)
    have e : -(x * -log x) = x * log x := by mach_mpoly [x, log x]
    rw [e] at hh
    exact hh
  have hsum := add_le_add_wit hA (add_le_add_wit hB hB)
  have e : -exp (-log K) + (-1 + -1) = -(exp (-log K) + 1 + 1) := by mach_ring
  rw [e] at hsum
  exact le_trans hsum hm

/-- # **Regime-3 bound for the LAST shape pair — and it subsumes case v.**

`A = eml var (const q)`, `B = eml var (const r)` with the coincidence forcing
`1 − r = exp c`, `c := exp (1 − q)`. Stated with `exp x − 1` on the left so it holds
**unconditionally in the sign of `c − exp (−c)`**; the linear floor follows when that is `≥ 0`. -/
theorem regime3_expvar_expvar_bound {q x : Real} (hx : 0 < x) :
    (exp (1 - q) - exp (-exp (1 - q))) * (exp x - 1)
      ≤ exp (exp x - q) - log (exp x - 1 + exp (exp (1 - q))) := by
  have hc : (0 : Real) < exp (1 - q) := exp_pos _
  have hw : (0 : Real) < exp x - 1 := lt_of_lt_of_le hx (regime3_floor_var_const hx)
  have hem : exp (exp (1 - q)) * exp (-exp (1 - q)) = 1 := by
    rw [← exp_add]
    have e : exp (1 - q) + -exp (1 - q) = (0 : Real) := by mach_ring
    rw [e, exp_zero]
  -- left term: exp (exp x − q) ≥ c · exp x
  have hsplit : exp (exp x - q) = exp (1 - q) * exp (exp x - 1) := by
    rw [← exp_add]
    have e : (1 - q) + (exp x - 1) = exp x - q := by mach_ring
    rw [e]
  have hge1 : exp x ≤ exp (exp x - 1) := by
    have h := exp_gt_one_plus_self (exp x - 1) hw
    have e : (1 : Real) + (exp x - 1) = exp x := by mach_ring
    rw [e] at h
    exact le_of_lt h
  have hL : exp (1 - q) * exp x ≤ exp (exp x - q) := by
    rw [hsplit]
    exact mul_le_mul_of_nonneg_left hge1 (le_of_lt hc)
  -- right term: log (exp x − 1 + exp c) ≤ c + (exp x − 1)·exp(−c)
  have hu1 : (1 : Real) ≤ 1 + (exp x - 1) * exp (-exp (1 - q)) := by
    have hp := le_of_lt (mul_pos hw (exp_pos (-exp (1 - q))))
    have s := add_le_add_wit (le_refl (1 : Real)) hp
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at s
    exact s
  have hfac : exp x - 1 + exp (exp (1 - q))
      = exp (exp (1 - q)) * (1 + (exp x - 1) * exp (-exp (1 - q))) := by
    have e : exp (exp (1 - q)) * (1 + (exp x - 1) * exp (-exp (1 - q)))
        = exp (exp (1 - q))
          + (exp x - 1) * (exp (exp (1 - q)) * exp (-exp (1 - q))) := by
      mach_mpoly [exp (exp (1 - q)), exp x, exp (-exp (1 - q))]
    rw [e, hem]
    mach_mpoly [exp (exp (1 - q)), exp x]
  have hupper : log (exp x - 1 + exp (exp (1 - q)))
      ≤ exp (1 - q) + (exp x - 1) * exp (-exp (1 - q)) := by
    rw [hfac, log_mul (exp_pos _) (lt_of_lt_of_le one_pos hu1), log_exp]
    have hl := log_le_sub_one_of_one_le hu1
    have s := add_le_add_wit (le_refl (exp (1 - q))) hl
    have e : exp (1 - q) + ((1 + (exp x - 1) * exp (-exp (1 - q))) - 1)
        = exp (1 - q) + (exp x - 1) * exp (-exp (1 - q)) := by
      mach_mpoly [exp (1 - q), exp x, exp (-exp (1 - q))]
    rw [e] at s
    exact s
  -- combine
  have hcomb := add_le_add_wit hL (neg_le_neg_wit hupper)
  have e1 : exp (1 - q) * exp x + -(exp (1 - q) + (exp x - 1) * exp (-exp (1 - q)))
      = (exp (1 - q) - exp (-exp (1 - q))) * (exp x - 1) := by
    mach_mpoly [exp (1 - q), exp x, exp (-exp (1 - q))]
  have e2 : exp (exp x - q) + -log (exp x - 1 + exp (exp (1 - q)))
      = exp (exp x - q) - log (exp x - 1 + exp (exp (1 - q))) := by mach_ring
  rw [e1, e2] at hcomb
  exact hcomb

/-- The linear floor for the last pair, when the coefficient is non-negative. (When it is negative
the tree DECREASES from `0`, so regime 3 is never entered — the case is vacuous, not unbounded.) -/
theorem regime3_floor_expvar_expvar {q x : Real} (hx : 0 < x)
    (hpos : 0 ≤ exp (1 - q) - exp (-exp (1 - q))) :
    (exp (1 - q) - exp (-exp (1 - q))) * x
      ≤ exp (exp x - q) - log (exp x - 1 + exp (exp (1 - q))) :=
  le_trans (mul_le_mul_of_nonneg_left (regime3_floor_var_const hx) hpos)
    (regime3_expvar_expvar_bound hx)

/-- # **The dual ceiling's residue is exactly `0 < T x < 1`.**

If the tree is `≤ 0` the totalised log clamps; if it is `≥ 1` its log is non-negative. **Either way
`x · log (T x) ≥ 0`, with no reference to the tree's shape, depth, or the value of `x`.** -/
theorem dual_ceiling_easy_cases {T : EMLTree} {x : Real} (hx : 0 < x)
    (hcase : T.eval x ≤ 0 ∨ 1 ≤ T.eval x) :
    (0 : Real) ≤ x * log (T.eval x) := by
  rcases hcase with hle | hge
  · rw [log_nonpos hle]
    have e : x * (0 : Real) = 0 := by mach_ring
    rw [e]
    exact le_refl 0
  · have hlog : (0 : Real) ≤ log (T.eval x) := by
      have h := log_le_log one_pos hge
      rw [log_one] at h
      exact h
    have hm := mul_le_mul_of_nonneg_left hlog (le_of_lt hx)
    have e : x * (0 : Real) = 0 := by mach_ring
    rw [e] at hm
    exact hm

/-- Regime 1 lands in the easy cases whenever `exp m ≥ 1`, i.e. `m ≥ 0`. -/
theorem dual_ceiling_regime_one_easy {A B : EMLTree} {m x : Real}
    (hx : 0 < x) (hm : 0 ≤ m) (hmA : m ≤ A.eval x) (hB : B.eval x ≤ 1) :
    (0 : Real) ≤ x * log ((EMLTree.eml A B).eval x) := by
  refine dual_ceiling_easy_cases hx (Or.inr ?_)
  have hval : (EMLTree.eml A B).eval x = exp (A.eval x) - log (B.eval x) := rfl
  have hlogB : log (B.eval x) ≤ 0 := log_nonpos_of_le_one' hB
  have hone : (1 : Real) ≤ exp (A.eval x) := one_le_exp (le_trans hm hmA)
  rw [hval]
  have s := add_le_add_wit hone (neg_le_neg_wit hlogB)
  have e1 : (1 : Real) + -(0 : Real) = 1 := by mach_ring
  have e2 : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by
    mach_ring
  rw [e1, e2] at s
  exact s

-- ===================================================================
-- ▸ CANONICAL-FORM MISMATCH (muse route): `exp(c/x)` is not `a + K/x`
--
-- Substituting `z = 1/x`, this is "`exp(cz)` is affine in `z` only if `c = 0`".
-- Three points and a second difference: `E³ − 2E² + E = E(E−1)² = 0`.
-- ===================================================================

theorem sq_eq_zero {y : Real} (h : y * y = 0) : y = 0 := by
  rcases lt_total 0 y with hp | hz | hn
  · exfalso
    have := mul_pos hp hp
    rw [h] at this
    exact lt_irrefl_ax 0 this
  · exact hz.symm
  · exfalso
    have hn' : (0 : Real) < -y := by
      have hh := neg_le_neg_wit (le_of_lt hn)
      have e : -(0 : Real) = 0 := by mach_ring
      rw [e] at hh
      rcases (le_iff_lt_or_eq (0 : Real) (-y)).mp hh with hlt | heq
      · exact hlt
      · exfalso
        have hy : y = 0 := by
          have t : -(-y) = -(0 : Real) := by rw [← heq]
          have e1 : -(-y) = y := by mach_ring
          have e2 : -(0 : Real) = 0 := by mach_ring
          rw [e1, e2] at t; exact t
        rw [hy] at hn; exact lt_irrefl_ax 0 hn
    have := mul_pos hn' hn'
    have e : -y * -y = y * y := by mach_mpoly [y]
    rw [e, h] at this
    exact lt_irrefl_ax 0 this

/-- **`exp` is not affine.** If `E := exp c` satisfies the three affine samples, then `c = 0`. -/
theorem exp_not_affine {c a K : Real}
    (h1 : exp c = a + K)
    (h2 : exp c * exp c = a + (K + K))
    (h3 : exp c * exp c * exp c = a + (K + K + K)) : c = 0 := by
  -- second difference vanishes: E³ − 2E² + E = 0
  have hsd : exp c * ((exp c - 1) * (exp c - 1)) = 0 := by
    have e : exp c * ((exp c - 1) * (exp c - 1))
        = (exp c * exp c * exp c - (a + (K + K + K)))
          - (exp c * exp c - (a + (K + K)))
          - ((exp c * exp c - (a + (K + K))) - (exp c - (a + K))) := by
      mach_mpoly [exp c, a, K]
    rw [e, h3, h2, h1]
    mach_mpoly [a, K]
  have hE : (exp c - 1) * (exp c - 1) = 0 := by
    refine mul_left_cancel (ne_of_gt (exp_pos c)) ?_
    have e : exp c * (0 : Real) = 0 := by mach_ring
    rw [hsd, e]
  have hE1 : exp c = 1 := by
    have h := sq_eq_zero hE
    have t : exp c - 1 + 1 = 0 + 1 := by rw [h]
    have e1 : exp c - 1 + 1 = exp c := by mach_ring
    have e2 : (0 : Real) + 1 = 1 := by mach_ring
    rw [e1, e2] at t
    exact t
  have h0 : exp c = exp 0 := by rw [hE1, exp_zero]
  exact exp_injective h0

-- ===================================================================
-- ▸ MUSE STEP 1: the depth-≤1 dichotomy
--   Every depth-≤1 tree is CONSTANT-valued or UNBOUNDED ABOVE on (0,∞).
--   This is the base of "bounded depth-≤2 ⟹ constant".
-- ===================================================================

theorem depth_le_one_const_or_unbounded (T : EMLTree) (hT : T.depth ≤ 1) :
    (∃ c : Real, ∀ x : Real, 0 < x → T.eval x = c)
    ∨ (∀ M : Real, ∃ x : Real, 0 < x ∧ M < T.eval x) := by
  cases T with
  | const c => exact Or.inl ⟨c, fun _ _ => rfl⟩
  | var =>
      refine Or.inr (fun M => ⟨exp M, exp_pos M, ?_⟩)
      exact exp_grows_strictly_thm M
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd hT (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hT (by simp only [EMLTree.depth]; omega)
          | const q => exact Or.inl ⟨exp p - log q, fun _ _ => rfl⟩
          | var =>
              -- exp p − log x, unbounded as x → 0⁺
              refine Or.inr (fun M => ⟨exp (exp p - M - 1), exp_pos _, ?_⟩)
              show M < exp p - log (exp (exp p - M - 1))
              rw [log_exp]
              refine lt_of_sub_pos_wit ?_
              have e : exp p - (exp p - M - 1) - M = 1 := by mach_ring
              rw [e]
              exact one_pos
      | var =>
          cases b with
          | eml _ _ => exact absurd hT (by simp only [EMLTree.depth]; omega)
          | const q =>
              -- exp x − log q, unbounded as x → ∞
              refine Or.inr (fun M => ⟨exp (M + log q), exp_pos _, ?_⟩)
              show M < exp (exp (M + log q)) - log q
              have h1 : M + log q < exp (M + log q) := exp_grows_strictly_thm _
              have h2 : exp (M + log q) < exp (exp (M + log q)) :=
                exp_grows_strictly_thm _
              have hchain : M + log q < exp (exp (M + log q)) := lt_trans_ax h1 h2
              refine lt_of_sub_pos_wit ?_
              have e : exp (exp (M + log q)) - log q - M
                  = exp (exp (M + log q)) - (M + log q) := by mach_ring
              rw [e]
              refine lt_of_sub_pos_wit ?_
              have e2 : exp (exp (M + log q)) - (M + log q) - 0
                  = exp (exp (M + log q)) - (M + log q) := by mach_ring
              rw [e2]
              have s := add_lt_add_left hchain (-(M + log q))
              have f1 : -(M + log q) + (M + log q) = (0 : Real) := by mach_ring
              have f2 : -(M + log q) + exp (exp (M + log q))
                  = exp (exp (M + log q)) - (M + log q) := by mach_ring
              rw [f1, f2] at s
              exact s
          | var =>
              -- exp x − log x, unbounded as x → ∞ (via exp x ≥ 2x and log x ≤ x − 1)
              refine Or.inr (fun M => ⟨exp M + 1, ?_, ?_⟩)
              · exact add_pos (exp_pos M) one_pos
              · show M < exp (exp M + 1) - log (exp M + 1)
                have hx1 : (1 : Real) ≤ exp M + 1 := by
                  have s := add_le_add_wit (le_of_lt (exp_pos M)) (le_refl (1 : Real))
                  have e : (0 : Real) + 1 = 1 := by mach_ring
                  rw [e] at s; exact s
                have hlog : log (exp M + 1) ≤ exp M + 1 - 1 :=
                  log_le_sub_one_of_one_le hx1
                have hexp : (exp M + 1) + (exp M + 1) ≤ exp (exp M + 1) :=
                  exp_ge_two_mul hx1
                -- exp X − log X ≥ 2X − (X−1) = X + 1 > M
                have hstep : exp M + 1 + 1 ≤ exp (exp M + 1) - log (exp M + 1) := by
                  have s := add_le_add_wit hexp (neg_le_neg_wit hlog)
                  have e1 : (exp M + 1) + (exp M + 1) + -(exp M + 1 - 1)
                      = exp M + 1 + 1 := by mach_ring
                  have e2 : exp (exp M + 1) + -log (exp M + 1)
                      = exp (exp M + 1) - log (exp M + 1) := by mach_ring
                  rw [e1, e2] at s
                  exact s
                have hM : M < exp M + 1 + 1 := by
                  have h := exp_grows_strictly_thm M
                  have s := add_lt_add_left h (1 + 1 : Real)
                  have f1 : (1 + 1 : Real) + M = M + (1 + 1) := by mach_ring
                  have f2 : (1 + 1 : Real) + exp M = exp M + 1 + 1 := by mach_ring
                  rw [f1, f2] at s
                  have hMlt : M < M + (1 + 1) := by
                    have t := add_lt_add_left (add_pos one_pos one_pos) M
                    have g : M + 0 = M := by mach_ring
                    rw [g] at t; exact t
                  exact lt_trans_ax hMlt s
                exact lt_of_lt_of_le hM hstep

/-- `y ≤ exp x · D` with `D ≥ 1` and `x ≥ 1` gives `log y ≤ x + log D` — including the clamped
branch, since `x + log D ≥ 1 > 0`. -/
theorem log_le_of_le_exp_mul {y x D : Real} (hx : 1 ≤ x) (hD : 1 ≤ D)
    (h : y ≤ exp x * D) : log y ≤ x + log D := by
  have hD0 : (0 : Real) < D := lt_of_lt_of_le one_pos hD
  have hlogD : (0 : Real) ≤ log D := by
    have t := log_le_log one_pos hD
    rw [log_one] at t; exact t
  have hsum : (0 : Real) ≤ x + log D := by
    have s := add_le_add_wit (le_of_lt (lt_of_lt_of_le one_pos hx)) hlogD
    have e : (0 : Real) + 0 = 0 := by mach_ring
    rw [e] at s; exact s
  rcases lt_total 0 y with hp | hz | hn
  · have hl := log_le_log hp h
    rw [log_mul (exp_pos x) hD0, log_exp] at hl
    exact hl
  · rw [← hz, log_nonpos (le_refl (0 : Real))]; exact hsum
  · rw [log_nonpos (le_of_lt hn)]; exact hsum

/-- **The `∞`-side companion bound:** every depth-≤1 tree has `log (B x) ≤ x + C` for `x ≥ 1`.
Together with the `0⁺` bounds this is what "bounded ⟹ constant" needs at both endpoints. -/
theorem depth_le_one_log_bound_at_infty (B : EMLTree) (hB : B.depth ≤ 1) :
    ∃ C : Real, ∀ x : Real, 1 ≤ x → log (B.eval x) ≤ x + C := by
  have hone : ∀ y x : Real, 1 ≤ x → y ≤ exp x * 1 → log y ≤ x + log 1 :=
    fun y x hx h => log_le_of_le_exp_mul hx (le_refl 1) h
  have hexp1 : ∀ x : Real, 1 ≤ x → (1 : Real) ≤ exp x :=
    fun x hx => one_le_exp (le_of_lt (lt_of_lt_of_le one_pos hx))
  cases B with
  | const c =>
      refine ⟨log (1 + exp c), fun x hx => ?_⟩
      refine log_le_of_le_exp_mul hx ?_ ?_
      · have s := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos c))
        have e : (1 : Real) + 0 = 1 := by mach_ring
        rw [e] at s; exact s
      · show c ≤ exp x * (1 + exp c)
        have h1 : c ≤ exp c := le_of_lt (exp_grows_strictly_thm c)
        have h2 : exp c ≤ exp x * (1 + exp c) := by
          have s := mul_le_mul_of_nonneg_right (hexp1 x hx) (le_of_lt (exp_pos c))
          have e : (1 : Real) * exp c = exp c := by mach_ring
          rw [e] at s
          have t := mul_le_mul_of_nonneg_left (by
            have u := add_le_add_wit (le_of_lt one_pos) (le_refl (exp c))
            have e2 : (0 : Real) + exp c = exp c := by mach_ring
            rw [e2] at u; exact u) (le_of_lt (exp_pos x))
          exact le_trans s t
        exact le_trans h1 h2
  | var =>
      refine ⟨0, fun x hx => ?_⟩
      show log x ≤ x + 0
      have h := log_le_sub_one_of_one_le hx
      have e : x - 1 ≤ x + 0 := by
        have s := add_le_add_wit (le_refl x) (neg_le_neg_wit (le_of_lt one_pos))
        have e1 : x + -(1 : Real) = x - 1 := by mach_ring
        have e2 : x + -(0 : Real) = x + 0 := by mach_ring
        rw [e1, e2] at s; exact s
      exact le_trans h e
  | eml a b =>
      -- every remaining shape is `≤ exp x · D` for an explicit `D ≥ 1`
      cases a with
      | eml _ _ => exact absurd hB (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hB (by simp only [EMLTree.depth]; omega)
          | const q =>
              refine ⟨log (1 + exp (exp p - log q)), fun x hx => ?_⟩
              refine log_le_of_le_exp_mul hx ?_ ?_
              · have s := add_le_add_wit (le_refl (1 : Real))
                  (le_of_lt (exp_pos (exp p - log q)))
                have e : (1 : Real) + 0 = 1 := by mach_ring
                rw [e] at s; exact s
              · show exp p - log q ≤ exp x * (1 + exp (exp p - log q))
                have h1 : exp p - log q ≤ exp (exp p - log q) :=
                  le_of_lt (exp_grows_strictly_thm _)
                have h2 : exp (exp p - log q) ≤ exp x * (1 + exp (exp p - log q)) := by
                  have s := mul_le_mul_of_nonneg_right (hexp1 x hx)
                    (le_of_lt (exp_pos (exp p - log q)))
                  have e : (1 : Real) * exp (exp p - log q) = exp (exp p - log q) := by
                    mach_ring
                  rw [e] at s
                  have t := mul_le_mul_of_nonneg_left (by
                    have u := add_le_add_wit (le_of_lt one_pos)
                      (le_refl (exp (exp p - log q)))
                    have e2 : (0 : Real) + exp (exp p - log q)
                        = exp (exp p - log q) := by mach_ring
                    rw [e2] at u; exact u) (le_of_lt (exp_pos x))
                  exact le_trans s t
                exact le_trans h1 h2
          | var =>
              refine ⟨log (1 + exp (exp p)), fun x hx => ?_⟩
              refine log_le_of_le_exp_mul hx ?_ ?_
              · have s := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos (exp p)))
                have e : (1 : Real) + 0 = 1 := by mach_ring
                rw [e] at s; exact s
              · show exp p - log x ≤ exp x * (1 + exp (exp p))
                have hlx : (0 : Real) ≤ log x := by
                  have t := log_le_log one_pos hx
                  rw [log_one] at t; exact t
                have hle : exp p - log x ≤ exp p := by
                  have s := add_le_add_wit (le_refl (exp p)) (neg_le_neg_wit hlx)
                  have e1 : exp p + -log x = exp p - log x := by mach_ring
                  have e2 : exp p + -(0 : Real) = exp p := by mach_ring
                  rw [e1, e2] at s; exact s
                have h2 : exp p ≤ exp x * (1 + exp (exp p)) := by
                  have hpe : exp p ≤ exp (exp p) := le_of_lt (exp_grows_strictly_thm _)
                  have s := mul_le_mul_of_nonneg_right (hexp1 x hx)
                    (le_of_lt (exp_pos (exp p)))
                  have e : (1 : Real) * exp (exp p) = exp (exp p) := by mach_ring
                  rw [e] at s
                  have t := mul_le_mul_of_nonneg_left (by
                    have u := add_le_add_wit (le_of_lt one_pos) (le_refl (exp (exp p)))
                    have e2 : (0 : Real) + exp (exp p) = exp (exp p) := by mach_ring
                    rw [e2] at u; exact u) (le_of_lt (exp_pos x))
                  exact le_trans hpe (le_trans s t)
                exact le_trans hle h2
      | var =>
          cases b with
          | eml _ _ => exact absurd hB (by simp only [EMLTree.depth]; omega)
          | const q =>
              refine ⟨log (1 + exp (-log q)), fun x hx => ?_⟩
              refine log_le_of_le_exp_mul hx ?_ ?_
              · have s := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos (-log q)))
                have e : (1 : Real) + 0 = 1 := by mach_ring
                rw [e] at s; exact s
              · show exp x - log q ≤ exp x * (1 + exp (-log q))
                have hq : -log q ≤ exp (-log q) := le_of_lt (exp_grows_strictly_thm _)
                have hstep : exp x - log q ≤ exp x + exp (-log q) := by
                  have s := add_le_add_wit (le_refl (exp x)) hq
                  have e : exp x + -log q = exp x - log q := by mach_ring
                  rw [e] at s; exact s
                have hstep2 : exp x + exp (-log q) ≤ exp x * (1 + exp (-log q)) := by
                  have e : exp x * (1 + exp (-log q)) = exp x + exp x * exp (-log q) := by
                    mach_mpoly [exp x, exp (-log q)]
                  rw [e]
                  have s := mul_le_mul_of_nonneg_right (hexp1 x hx)
                    (le_of_lt (exp_pos (-log q)))
                  have e2 : (1 : Real) * exp (-log q) = exp (-log q) := by mach_ring
                  rw [e2] at s
                  exact add_le_add_wit (le_refl (exp x)) s
                exact le_trans hstep hstep2
          | var =>
              refine ⟨0, fun x hx => ?_⟩
              show log (exp x - log x) ≤ x + 0
              have hlx : (0 : Real) ≤ log x := by
                have t := log_le_log one_pos hx
                rw [log_one] at t; exact t
              have hle : exp x - log x ≤ exp x * 1 := by
                have e : exp x * (1 : Real) = exp x := by mach_ring
                rw [e]
                have s := add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit hlx)
                have e1 : exp x + -log x = exp x - log x := by mach_ring
                have e2 : exp x + -(0 : Real) = exp x := by mach_ring
                rw [e1, e2] at s; exact s
              have h := log_le_of_le_exp_mul hx (le_refl (1 : Real)) hle
              rw [log_one] at h
              exact h

/-- Unboundedness passes through `log`: if `B` is unbounded above so is `log ∘ B`. -/
theorem unbounded_log_of_unbounded {B : EMLTree}
    (h : ∀ M : Real, ∃ x : Real, 0 < x ∧ M < B.eval x) :
    ∀ M : Real, ∃ x : Real, 0 < x ∧ M < log (B.eval x) := by
  intro M
  obtain ⟨x, hx, hgt⟩ := h (exp M)
  refine ⟨x, hx, ?_⟩
  have hl := log_lt_log (exp_pos M) hgt
  rw [log_exp] at hl
  exact hl

/-- # **Step 1, constant-left-child case.**

If the left child is constant-valued and the tree is bounded **below**, the tree is constant.
The dichotomy forces the right child to be constant too — otherwise `log (B x)` is unbounded above
and drags the tree to `−∞`. -/
theorem depth_two_const_left_bounded_const {A B : EMLTree} {α L : Real}
    (hA : ∀ x : Real, 0 < x → A.eval x = α) (hB : B.depth ≤ 1)
    (hbdd : ∀ x : Real, 0 < x → L ≤ (EMLTree.eml A B).eval x) :
    ∃ c : Real, ∀ x : Real, 0 < x → (EMLTree.eml A B).eval x = c := by
  rcases depth_le_one_const_or_unbounded B hB with hconst | hunb
  · obtain ⟨β, hβ⟩ := hconst
    refine ⟨exp α - log β, fun x hx => ?_⟩
    show exp (A.eval x) - log (B.eval x) = exp α - log β
    rw [hA x hx, hβ x hx]
  · exfalso
    obtain ⟨x, hx, hgt⟩ := unbounded_log_of_unbounded hunb (exp α - L)
    have hval : (EMLTree.eml A B).eval x = exp α - log (B.eval x) := by
      show exp (A.eval x) - log (B.eval x) = exp α - log (B.eval x)
      rw [hA x hx]
    have hT := hbdd x hx
    rw [hval] at hT
    -- L ≤ exp α − log (B x)  ⟹  log (B x) ≤ exp α − L, contradicting hgt
    have hle : log (B.eval x) ≤ exp α - L := by
      have s := add_le_add_left hT (log (B.eval x) - L)
      have e1 : log (B.eval x) - L + L = log (B.eval x) := by mach_ring
      have e2 : log (B.eval x) - L + (exp α - log (B.eval x)) = exp α - L := by
        mach_ring
      rw [e1, e2] at s
      exact s
    exact lt_irrefl_ax _ (lt_of_lt_of_le hgt hle)

/-- # **Step 1, unbounded-left case at `∞`.**

If the left child eventually dominates `x`, then `exp (A x) ≥ 2x` outruns the depth-1 linear log
bound `log (B x) ≤ x + C`, and the tree is unbounded above. -/
theorem depth_two_unbounded_of_left_ge_id {A B : EMLTree} (hB : B.depth ≤ 1)
    (hA : ∃ X₀ : Real, 1 ≤ X₀ ∧ ∀ x : Real, X₀ ≤ x → x ≤ A.eval x) :
    ∀ M : Real, ∃ x : Real, 0 < x ∧ M < (EMLTree.eml A B).eval x := by
  obtain ⟨C, hC⟩ := depth_le_one_log_bound_at_infty B hB
  obtain ⟨X₀, hX₀, hdom⟩ := hA
  intro M
  refine ⟨X₀ + exp (M + C), ?_, ?_⟩
  · exact add_pos (lt_of_lt_of_le one_pos hX₀) (exp_pos (M + C))
  · have hx1 : (1 : Real) ≤ X₀ + exp (M + C) := by
      have s := add_le_add_wit hX₀ (le_of_lt (exp_pos (M + C)))
      have e : (1 : Real) + 0 = 1 := by mach_ring
      rw [e] at s; exact s
    have hxX : X₀ ≤ X₀ + exp (M + C) := by
      have s := add_le_add_wit (le_refl X₀) (le_of_lt (exp_pos (M + C)))
      have e : X₀ + 0 = X₀ := by mach_ring
      rw [e] at s; exact s
    -- exp (A x) ≥ exp x ≥ 2x
    have hAx := hdom _ hxX
    have hexpA : exp (X₀ + exp (M + C)) ≤ exp (A.eval (X₀ + exp (M + C))) :=
      exp_monotone hAx
    have h2x : (X₀ + exp (M + C)) + (X₀ + exp (M + C)) ≤ exp (X₀ + exp (M + C)) :=
      exp_ge_two_mul hx1
    -- log (B x) ≤ x + C
    have hlogB := hC _ hx1
    -- combine
    have hlow : (X₀ + exp (M + C)) - C
        ≤ exp (A.eval (X₀ + exp (M + C))) - log (B.eval (X₀ + exp (M + C))) := by
      have s := add_le_add_wit (le_trans h2x hexpA) (neg_le_neg_wit hlogB)
      have e1 : (X₀ + exp (M + C)) + (X₀ + exp (M + C)) + -((X₀ + exp (M + C)) + C)
          = (X₀ + exp (M + C)) - C := by mach_ring
      have e2 : exp (A.eval (X₀ + exp (M + C))) + -log (B.eval (X₀ + exp (M + C)))
          = exp (A.eval (X₀ + exp (M + C))) - log (B.eval (X₀ + exp (M + C))) := by
        mach_ring
      rw [e1, e2] at s
      exact s
    have hgap : (0 : Real) < exp (M + C) - (M + C) := by
      have s := add_lt_add_left (exp_grows_strictly_thm (M + C)) (-(M + C))
      have f1 : -(M + C) + (M + C) = (0 : Real) := by mach_mpoly [M, C]
      have f2 : -(M + C) + exp (M + C) = exp (M + C) - (M + C) := by
        mach_mpoly [M, C, exp (M + C)]
      rw [f1, f2] at s
      exact s
    have hMlt : M < X₀ + exp (M + C) - C := by
      refine lt_of_sub_pos_wit ?_
      have e : X₀ + exp (M + C) - C - M = X₀ + (exp (M + C) - (M + C)) := by
        mach_mpoly [X₀, M, C, exp (M + C)]
      rw [e]
      exact add_pos (lt_of_lt_of_le one_pos hX₀) hgap
    exact lt_of_lt_of_le hMlt hlow

/-- `A = var` dominates `x` trivially, so any depth-2 tree with left child `var` is unbounded. -/
theorem depth_two_left_var_unbounded {B : EMLTree} (hB : B.depth ≤ 1) :
    ∀ M : Real, ∃ x : Real, 0 < x ∧ M < (EMLTree.eml EMLTree.var B).eval x :=
  depth_two_unbounded_of_left_ge_id hB ⟨1, le_refl 1, fun x _ => le_refl x⟩

/-- **The `0⁺` mirror of `depth_le_one_log_bound_at_infty`:** `log (B x) ≤ M − log x` near `0`.

The cutoff `exp (M − 2 − exp (M − 1))` sits below **both** `exp (M − 1)` (so that `M − log x ≥ 1`,
putting the tangent bound in its derivable range) and `1`. -/
theorem depth_le_one_log_upper_near_zero (B : EMLTree) (hB : B.depth ≤ 1) :
    ∃ N δ : Real, 0 < δ ∧ δ ≤ 1 ∧
      ∀ x : Real, 0 < x → x ≤ δ → log (B.eval x) ≤ N - log x := by
  obtain ⟨M, hM⟩ := depth_le_one_upper_bound B hB
  have hcut1 : M - (1 + 1) - exp (M - 1) ≤ M - 1 := by
    have hp : (0 : Real) < 1 + exp (M - 1) := add_pos one_pos (exp_pos _)
    have s := add_le_add_left (le_of_lt hp) (M - (1 + 1) - exp (M - 1))
    have e1 : M - (1 + 1) - exp (M - 1) + 0 = M - (1 + 1) - exp (M - 1) := by
      mach_mpoly [M, exp (M - 1)]
    have e2 : M - (1 + 1) - exp (M - 1) + (1 + exp (M - 1)) = M - 1 := by
      mach_mpoly [M, exp (M - 1)]
    rw [e1, e2] at s
    exact s
  have hcut0 : M - (1 + 1) - exp (M - 1) ≤ 0 := by
    have h := exp_grows_strictly_thm (M - 1)
    have s := add_lt_add_left h (-1 - exp (M - 1))
    have e1 : -1 - exp (M - 1) + (M - 1) = M - (1 + 1) - exp (M - 1) := by
      mach_mpoly [M, exp (M - 1)]
    have e2 : -1 - exp (M - 1) + exp (M - 1) = (-1 : Real) := by
      mach_mpoly [exp (M - 1)]
    rw [e1, e2] at s
    have hm1 : (-1 : Real) ≤ 0 := by
      have t := add_lt_add_left zero_lt_one_ax (-1 : Real)
      have f1 : (-1 : Real) + 0 = -1 := by mach_ring
      have f2 : (-1 : Real) + 1 = 0 := by mach_ring
      rw [f1, f2] at t; exact le_of_lt t
    exact le_trans (le_of_lt s) hm1
  refine ⟨M, exp (M - (1 + 1) - exp (M - 1)), exp_pos _, ?_, ?_⟩
  · have h := exp_monotone hcut0
    rw [exp_zero] at h
    exact h
  · intro x hx hxd
    have hx1 : x ≤ 1 := le_trans hxd (by
      have h := exp_monotone hcut0
      rw [exp_zero] at h
      exact h)
    have hlogx : log x ≤ M - 1 := by
      have h := log_le_log hx (le_trans hxd (exp_monotone hcut1))
      rw [log_exp] at h
      exact h
    have hge1 : (1 : Real) ≤ M - log x := by
      have s := add_le_add_wit (le_refl M) (neg_le_neg_wit hlogx)
      have e1 : M + -(M - 1) = (1 : Real) := by mach_mpoly [M]
      have e2 : M + -log x = M - log x := by mach_ring
      rw [e1, e2] at s
      exact s
    have hBle : B.eval x ≤ M - log x := hM x hx hx1
    rcases lt_total 0 (B.eval x) with hp | hz | hn
    · have h1 := log_le_log hp hBle
      have h2 := log_le_sub_one_of_one_le hge1
      have h3 : M - log x - 1 ≤ M - log x := by
        have s := add_le_add_wit (le_refl (M - log x)) (neg_le_neg_wit (le_of_lt one_pos))
        have e1 : M - log x + -(1 : Real) = M - log x - 1 := by mach_ring
        have e2 : M - log x + -(0 : Real) = M - log x := by mach_ring
        rw [e1, e2] at s
        exact s
      exact le_trans h1 (le_trans h2 h3)
    · rw [← hz, log_nonpos (le_refl (0 : Real))]
      exact le_trans (le_of_lt one_pos) hge1
    · rw [log_nonpos (le_of_lt hn)]
      exact le_trans (le_of_lt one_pos) hge1

/-- From a product lower bound at the sample point `exp (−t)`, read off a value lower bound.
`v ≥ exp t · (K − exp(−t)(N+t)) = K·exp t − (N+t) ≥ exp t − N − t ≥ t − N`. -/
theorem lower_from_product {v K N t : Real} (hK : 1 ≤ K) (ht1 : 1 ≤ t)
    (hprod : K - exp (-t) * (N + t) ≤ exp (-t) * v) : t - N ≤ v := by
  have hem : exp t * exp (-t) = 1 := by
    rw [← exp_add]
    have e : t + -t = (0 : Real) := by mach_ring
    rw [e, exp_zero]
  have hm := mul_le_mul_of_nonneg_left hprod (le_of_lt (exp_pos t))
  have eR : exp t * (exp (-t) * v) = (exp t * exp (-t)) * v := by
    mach_mpoly [exp t, exp (-t), v]
  have eL : exp t * (K - exp (-t) * (N + t))
      = K * exp t - (exp t * exp (-t)) * (N + t) := by
    mach_mpoly [exp t, exp (-t), K, N, t]
  rw [eL, eR, hem] at hm
  have e1 : (1 : Real) * v = v := by mach_ring
  have e2 : (1 : Real) * (N + t) = N + t := by mach_ring
  rw [e1, e2] at hm
  -- K·exp t − (N+t) ≥ exp t − (N+t) ≥ (t+t) − (N+t) = t − N
  have hKe : exp t ≤ K * exp t := by
    have s := mul_le_mul_of_nonneg_right hK (le_of_lt (exp_pos t))
    have e : (1 : Real) * exp t = exp t := by mach_ring
    rw [e] at s; exact s
  have h2t : t + t ≤ exp t := exp_ge_two_mul ht1
  have hchain : t - N ≤ K * exp t - (N + t) := by
    have s := add_le_add_wit (le_trans h2t hKe) (le_refl (-(N + t)))
    have e1 : t + t + -(N + t) = t - N := by mach_mpoly [t, N]
    have e2 : K * exp t + -(N + t) = K * exp t - (N + t) := by mach_ring
    rw [e1, e2] at s
    exact s
  exact le_trans hchain hm

/-- # **Step 1, unbounded-left case at `0⁺`.**

Left child `eml (const p) var`, so `x·exp(A x) = exp (exp p) =: K > 1` **exactly**. Since
`x·log(B x) → 0` for depth-≤1 `B`, the product `x·T x` stays near `K`, and `T x ≈ K/x` is unbounded.
Sampling at `x = exp(−t)` turns the whole argument into `T x ≥ K·exp t − N − t`. -/
theorem depth_two_left_const_var_unbounded {p : Real} {B : EMLTree} (hB : B.depth ≤ 1) :
    ∀ M : Real, ∃ x : Real, 0 < x ∧
      M < (EMLTree.eml (EMLTree.eml (EMLTree.const p) EMLTree.var) B).eval x := by
  obtain ⟨N, d, hd0, hd1, hN⟩ := depth_le_one_log_upper_near_zero B hB
  intro M
  -- the sample point
  refine ⟨exp (-(1 + exp (M + N) + exp (-log d))), exp_pos _, ?_⟩
  have ht1 : (1 : Real) ≤ 1 + exp (M + N) + exp (-log d) := by
    have s := add_le_add_wit (add_le_add_wit (le_refl (1 : Real))
      (le_of_lt (exp_pos (M + N)))) (le_of_lt (exp_pos (-log d)))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at s; exact s
  have hx0 : (0 : Real) < exp (-(1 + exp (M + N) + exp (-log d))) := exp_pos _
  have hxd : exp (-(1 + exp (M + N) + exp (-log d))) ≤ d := by
    have hstep : -(1 + exp (M + N) + exp (-log d)) ≤ log d := by
      have hge : -log d ≤ 1 + exp (M + N) + exp (-log d) := by
        have h1 := le_of_lt (exp_grows_strictly_thm (-log d))
        have s := add_le_add_wit (add_le_add_wit (le_of_lt one_pos)
          (le_of_lt (exp_pos (M + N)))) (le_refl (exp (-log d)))
        have e : (0 : Real) + 0 + exp (-log d) = exp (-log d) := by mach_ring
        rw [e] at s
        exact le_trans h1 s
      have s := neg_le_neg_wit hge
      have e : -(-log d) = log d := by mach_ring
      rw [e] at s
      exact s
    have h := exp_monotone hstep
    rw [exp_log hd0] at h
    exact h
  have hx1 : exp (-(1 + exp (M + N) + exp (-log d))) ≤ 1 := le_trans hxd hd1
  -- the exact product identity for the left child
  have hprodA : exp (-(1 + exp (M + N) + exp (-log d)))
      * exp ((EMLTree.eml (EMLTree.const p) EMLTree.var).eval
          (exp (-(1 + exp (M + N) + exp (-log d)))))
      = exp (exp p) := by
    have h := left_eml_var_mul (u := EMLTree.const p) hx0
    have e : (EMLTree.const p).eval (exp (-(1 + exp (M + N) + exp (-log d)))) = p := rfl
    rw [e] at h
    exact h
  -- log (B x) ≤ N + t, hence the product bound
  have hlogX : log (exp (-(1 + exp (M + N) + exp (-log d))))
      = -(1 + exp (M + N) + exp (-log d)) := log_exp _
  have hlogB : log (B.eval (exp (-(1 + exp (M + N) + exp (-log d)))))
      ≤ N + (1 + exp (M + N) + exp (-log d)) := by
    have h := hN _ hx0 hxd
    rw [hlogX] at h
    have e : N - -(1 + exp (M + N) + exp (-log d))
        = N + (1 + exp (M + N) + exp (-log d)) := by mach_ring
    rw [e] at h
    exact h
  have hprod : exp (exp p)
      - exp (-(1 + exp (M + N) + exp (-log d)))
        * (N + (1 + exp (M + N) + exp (-log d)))
      ≤ exp (-(1 + exp (M + N) + exp (-log d)))
        * (EMLTree.eml (EMLTree.eml (EMLTree.const p) EMLTree.var) B).eval
            (exp (-(1 + exp (M + N) + exp (-log d)))) := by
    show _ ≤ exp (-(1 + exp (M + N) + exp (-log d)))
      * (exp ((EMLTree.eml (EMLTree.const p) EMLTree.var).eval
          (exp (-(1 + exp (M + N) + exp (-log d))))) - log (B.eval _))
    have hsplit : exp (-(1 + exp (M + N) + exp (-log d)))
        * (exp ((EMLTree.eml (EMLTree.const p) EMLTree.var).eval
            (exp (-(1 + exp (M + N) + exp (-log d)))))
          - log (B.eval (exp (-(1 + exp (M + N) + exp (-log d))))))
        = exp (-(1 + exp (M + N) + exp (-log d)))
            * exp ((EMLTree.eml (EMLTree.const p) EMLTree.var).eval
              (exp (-(1 + exp (M + N) + exp (-log d)))))
          - exp (-(1 + exp (M + N) + exp (-log d)))
            * log (B.eval (exp (-(1 + exp (M + N) + exp (-log d))))) := by
      mach_mpoly [exp (-(1 + exp (M + N) + exp (-log d))),
        exp ((EMLTree.eml (EMLTree.const p) EMLTree.var).eval
          (exp (-(1 + exp (M + N) + exp (-log d))))),
        log (B.eval (exp (-(1 + exp (M + N) + exp (-log d)))))]
    rw [hsplit, hprodA]
    exact sub_le_sub_left_wit
      (mul_le_mul_of_nonneg_left hlogB (le_of_lt hx0))
  have hfin := lower_from_product (le_of_lt (one_lt_exp_exp p)) ht1 hprod
  -- t − N > M
  have hMt : M < (1 + exp (M + N) + exp (-log d)) - N := by
    refine lt_of_sub_pos_wit ?_
    have e : (1 + exp (M + N) + exp (-log d)) - N - M
        = 1 + (exp (M + N) - (M + N)) + exp (-log d) := by
      mach_mpoly [M, N, exp (M + N), exp (-log d)]
    rw [e]
    refine add_pos (add_pos one_pos ?_) (exp_pos _)
    have s := add_lt_add_left (exp_grows_strictly_thm (M + N)) (-(M + N))
    have f1 : -(M + N) + (M + N) = (0 : Real) := by mach_mpoly [M, N]
    have f2 : -(M + N) + exp (M + N) = exp (M + N) - (M + N) := by
      mach_mpoly [M, N, exp (M + N)]
    rw [f1, f2] at s
    exact s
  exact lt_of_lt_of_le hMt hfin

/-- # **MUSE STEP 1, COMPLETE: a bounded depth-2 tree is constant.**

Dispatch over the six left-child shapes. Two are constant-valued and use the **lower** bound; the
other four are unbounded above — at `∞` for the `var`-left shapes, at `0⁺` for `eml (const p) var` —
and contradict the **upper** bound. -/
theorem depth_two_bounded_const {A B : EMLTree} (hA : A.depth ≤ 1) (hB : B.depth ≤ 1)
    {L U : Real}
    (hlow : ∀ x : Real, 0 < x → L ≤ (EMLTree.eml A B).eval x)
    (hup : ∀ x : Real, 0 < x → (EMLTree.eml A B).eval x ≤ U) :
    ∃ c : Real, ∀ x : Real, 0 < x → (EMLTree.eml A B).eval x = c := by
  have contra : (∀ M : Real, ∃ x : Real, 0 < x ∧ M < (EMLTree.eml A B).eval x) → False := by
    intro h
    obtain ⟨x, hx, hgt⟩ := h U
    exact lt_irrefl_ax _ (lt_of_lt_of_le hgt (hup x hx))
  cases A with
  | const c =>
      exact depth_two_const_left_bounded_const (α := c) (fun _ _ => rfl) hB hlow
  | var =>
      exact absurd (depth_two_left_var_unbounded hB) contra
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
          | const q =>
              exact depth_two_const_left_bounded_const (α := exp p - log q)
                (fun _ _ => rfl) hB hlow
          | var => exact absurd (depth_two_left_const_var_unbounded hB) contra
      | var =>
          cases b with
          | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
          | const q =>
              refine absurd (depth_two_unbounded_of_left_ge_id hB
                ⟨1 + exp (log q), ?_, ?_⟩) contra
              · have s := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos (log q)))
                have e : (1 : Real) + 0 = 1 := by mach_ring
                rw [e] at s; exact s
              · intro x hxge
                show x ≤ exp x - log q
                have hx1 : (1 : Real) ≤ x := le_trans (by
                  have s := add_le_add_wit (le_refl (1 : Real))
                    (le_of_lt (exp_pos (log q)))
                  have e : (1 : Real) + 0 = 1 := by mach_ring
                  rw [e] at s; exact s) hxge
                have hq : log q ≤ x := le_trans (by
                  have h := le_of_lt (exp_grows_strictly_thm (log q))
                  have s := add_le_add_wit (le_of_lt one_pos) (le_refl (exp (log q)))
                  have e : (0 : Real) + exp (log q) = exp (log q) := by mach_ring
                  rw [e] at s
                  exact le_trans h s) hxge
                have h2x : x + x ≤ exp x := exp_ge_two_mul hx1
                have s := add_le_add_wit h2x (neg_le_neg_wit hq)
                have e1 : x + x + -x = x := by mach_mpoly [x]
                have e2 : exp x + -log q = exp x - log q := by mach_ring
                rw [e1, e2] at s
                exact s
          | var =>
              refine absurd (depth_two_unbounded_of_left_ge_id hB
                ⟨1, le_refl 1, ?_⟩) contra
              intro x hx1
              show x ≤ exp x - log x
              have h2x : x + x ≤ exp x := exp_ge_two_mul hx1
              have hlx : log x ≤ x - 1 := log_le_sub_one_of_one_le hx1
              have s := add_le_add_wit h2x (neg_le_neg_wit hlx)
              have e1 : x + x + -(x - 1) = x + 1 := by mach_mpoly [x]
              have e2 : exp x + -log x = exp x - log x := by mach_ring
              rw [e1, e2] at s
              have hxx : x ≤ x + 1 := by
                have t := add_le_add_wit (le_refl x) (le_of_lt one_pos)
                have e : x + 0 = x := by mach_ring
                rw [e] at t; exact t
              exact le_trans hxx s

-- ===================================================================
-- ▸ THE LEAF BRANCH CLOSES: its right child is BOUNDED, so step 1 bites
--
-- `leaf_const_pin` gives `x·log(t2 x) = x·exp c − 1`, i.e. `t2 x = exp(exp c)·exp(−1/x)`,
-- which lives in `(0, exp(exp c))`. A bounded depth-2 tree is constant — and a
-- constant right child contradicts the pin at two points.
-- ===================================================================

/-- A constant right child cannot satisfy the leaf pin: two points force `0 = −1`. -/
theorem leaf_pin_const_absurd {c k : Real}
    (h1 : (1 : Real) * log k = 1 * exp c - 1)
    (h2 : ((1 : Real) + 1) * log k = (1 + 1) * exp c - 1) : False := by
  have hlk : log k = exp c - 1 := by
    have e1 : (1 : Real) * log k = log k := by mach_ring
    have e2 : (1 : Real) * exp c - 1 = exp c - 1 := by mach_ring
    rw [e1, e2] at h1
    exact h1
  rw [hlk] at h2
  -- (1+1)(exp c − 1) = (1+1) exp c − 1  ⟹  0 = 1
  have hbad : (0 : Real) = 1 := by
    have e : ((1 : Real) + 1) * exp c - 1 - ((1 + 1) * (exp c - 1)) = 1 := by
      mach_mpoly [exp c]
    have t : ((1 : Real) + 1) * (exp c - 1) - ((1 + 1) * (exp c - 1)) = 1 := by
      rw [h2] at e ⊢
      exact e
    have e2 : ((1 : Real) + 1) * (exp c - 1) - ((1 + 1) * (exp c - 1)) = 0 := by
      mach_mpoly [exp c]
    rw [e2] at t
    exact t
  have h0 : (0 : Real) < 0 := by
    have t := one_pos
    rw [← hbad] at t
    exact t
  exact lt_irrefl_ax 0 h0

/-- The leaf pin bounds its right child **above** by `exp (exp c)`. -/
theorem leaf_pin_upper {c : Real} {t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.const c) t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) : t2.eval x ≤ exp (exp c) := by
  rcases lt_total 0 (t2.eval x) with hp | hz | hn
  · -- log (t2 x) = exp c − 1/x < exp c
    have hpin := leaf_const_pin h x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have hlog : log (t2.eval x) < exp c := by
      refine lt_of_sub_pos_wit ?_
      have hmul : x * (exp c - log (t2.eval x)) = 1 := by
        have e : x * (exp c - log (t2.eval x)) = x * exp c - x * log (t2.eval x) := by
          mach_mpoly [x, exp c, log (t2.eval x)]
        rw [e, hpin]
        mach_mpoly [x, exp c]
      rcases lt_total 0 (exp c - log (t2.eval x)) with hq | hr | hs
      · exact hq
      · exfalso
        rw [← hr] at hmul
        have e : x * (0 : Real) = 0 := by mach_ring
        rw [e] at hmul
        have h0 : (0 : Real) < 0 := by
          have t := one_pos
          rw [← hmul] at t
          exact t
        exact lt_irrefl_ax 0 h0
      · exfalso
        have hneg := mul_lt_mul_pos_left_wit hs hx
        have e : x * (0 : Real) = 0 := by mach_ring
        rw [e] at hneg
        rw [hmul] at hneg
        exact lt_irrefl_ax 0 (lt_trans_ax one_pos hneg)
    have hmono := exp_monotone (le_of_lt hlog)
    rw [exp_log hp] at hmono
    exact hmono
  · rw [← hz]; exact le_of_lt (exp_pos (exp c))
  · exact le_trans (le_of_lt hn) (le_of_lt (exp_pos (exp c)))

/-- The leaf pin bounds its right child **below**. `t2 x > 0` at every point except possibly
`x = exp (−c)`, where the totalised `log` may clamp — so one explicit constant covers everything. -/
theorem leaf_pin_lower {c : Real} {t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml (EMLTree.const c) t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) :
    -exp (-(t2.eval (exp (-c)))) - exp (t2.eval (exp (-c))) - 1 ≤ t2.eval x := by
  have hLneg : -exp (-(t2.eval (exp (-c)))) - exp (t2.eval (exp (-c))) - 1 < 0 := by
    refine lt_of_sub_pos_wit ?_
    have e : (0 : Real) - (-exp (-(t2.eval (exp (-c)))) - exp (t2.eval (exp (-c))) - 1)
        = exp (-(t2.eval (exp (-c)))) + exp (t2.eval (exp (-c))) + 1 := by
      mach_mpoly [exp (-(t2.eval (exp (-c)))), exp (t2.eval (exp (-c)))]
    rw [e]
    exact add_pos (add_pos (exp_pos _) (exp_pos _)) one_pos
  have hLv : -exp (-(t2.eval (exp (-c)))) - exp (t2.eval (exp (-c))) - 1
      ≤ t2.eval (exp (-c)) := by
    refine le_of_lt (lt_of_sub_pos_wit ?_)
    have e : t2.eval (exp (-c))
        - (-exp (-(t2.eval (exp (-c)))) - exp (t2.eval (exp (-c))) - 1)
        = (t2.eval (exp (-c)) + exp (-(t2.eval (exp (-c)))))
          + (exp (t2.eval (exp (-c))) + 1) := by
      mach_mpoly [t2.eval (exp (-c)), exp (-(t2.eval (exp (-c)))),
        exp (t2.eval (exp (-c)))]
    rw [e]
    refine add_pos ?_ (add_pos (exp_pos _) one_pos)
    have hg := exp_grows_strictly_thm (-(t2.eval (exp (-c))))
    have s := add_lt_add_left hg (t2.eval (exp (-c)))
    have f1 : t2.eval (exp (-c)) + -(t2.eval (exp (-c))) = (0 : Real) := by
      mach_mpoly [t2.eval (exp (-c))]
    rw [f1] at s
    exact s
  rcases lt_total 0 (t2.eval x) with hp | hz | hn
  · exact le_of_lt (lt_trans_ax hLneg hp)
  · rw [← hz]; exact le_of_lt hLneg
  · -- t2 x < 0 forces x = exp (−c)
    have hpin := leaf_const_pin h x hx
    rw [log_nonpos (le_of_lt hn)] at hpin
    have hxe : x = exp (-c) := by
      have e0 : x * (0 : Real) = 0 := by mach_ring
      rw [e0] at hpin
      -- 0 = x·exp c − 1, so x·exp c = 1
      have hxc : x * exp c = 1 := by
        have t : (0 : Real) + 1 = x * exp c - 1 + 1 := by rw [hpin]
        have e1 : (0 : Real) + 1 = 1 := by mach_ring
        have e2 : x * exp c - 1 + 1 = x * exp c := by mach_ring
        rw [e1, e2] at t
        exact t.symm
      have hem : exp c * exp (-c) = 1 := by
        rw [← exp_add]
        have e : c + -c = (0 : Real) := by mach_ring
        rw [e, exp_zero]
      have t : x * exp c * exp (-c) = 1 * exp (-c) := by rw [hxc]
      have e1 : x * exp c * exp (-c) = x * (exp c * exp (-c)) := by
        mach_mpoly [x, exp c, exp (-c)]
      have e2 : (1 : Real) * exp (-c) = exp (-c) := by mach_ring
      rw [e1, hem, e2] at t
      have e3 : x * (1 : Real) = x := by mach_ring
      rw [e3] at t
      exact t
    rw [hxe]
    exact hLv

/-- # **Depth 3, leaf-`const` branch: IMPOSSIBLE.**

The pin bounds the right child in `(L, exp(exp c))`; a bounded depth-2 tree is constant (step 1);
and a constant right child contradicts the pin at two points. -/
theorem depth3_leaf_const_absurd {c : Real} {t2 : EMLTree} (ht2 : t2.depth ≤ 2)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.const c) t2).eval x = 1 / x) : False := by
  have hconst : (∃ k : Real, ∀ x : Real, 0 < x → t2.eval x = k) → False := by
    intro hk
    obtain ⟨k, hk⟩ := hk
    refine leaf_pin_const_absurd (c := c) (k := k) ?_ ?_
    · have p1 := leaf_const_pin h 1 one_pos
      rw [hk 1 one_pos] at p1
      exact p1
    · have p2 := leaf_const_pin h (1 + 1) (add_pos one_pos one_pos)
      rw [hk (1 + 1) (add_pos one_pos one_pos)] at p2
      exact p2
  cases t2 with
  | const k => exact hconst ⟨k, fun _ _ => rfl⟩
  | var =>
      have hb := leaf_pin_upper h (exp (exp c) + 1) (add_pos (exp_pos _) one_pos)
      have hlt : exp (exp c) < exp (exp c) + 1 := by
        have t := add_lt_add_left one_pos (exp (exp c))
        have e : exp (exp c) + 0 = exp (exp c) := by mach_ring
        rw [e] at t; exact t
      exact lt_irrefl_ax _ (lt_of_lt_of_le hlt hb)
  | eml A B =>
      have hA : A.depth ≤ 1 := by simp only [EMLTree.depth] at ht2; omega
      have hB : B.depth ≤ 1 := by simp only [EMLTree.depth] at ht2; omega
      exact hconst (depth_two_bounded_const hA hB (leaf_pin_lower h) (leaf_pin_upper h))

theorem le_of_mul_le_mul_pos_left {x u v : Real} (hx : 0 < x) (h : x * u ≤ x * v) : u ≤ v := by
  rcases lt_total v u with hlt | heq | hgt
  · exfalso
    have s := mul_lt_mul_pos_left_wit hlt hx
    exact lt_irrefl_ax _ (lt_of_lt_of_le s h)
  · exact le_of_eq heq.symm
  · exact le_of_lt hgt

/-- # **The leaf-`var` branch does NOT yield to step 1.**

Its pin forces `t2 x ≥ exp (exp x − 1)` for `x ≥ 1`, so the right child is **unbounded above** —
unlike the leaf-`const` branch, where the pin bounded it inside `(0, exp(exp c))`.
`depth_two_bounded_const` is therefore unavailable here. -/
theorem leaf_var_pin_unbounded {t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x)
    (x : Real) (hx1 : 1 ≤ x) : exp (exp x - 1) ≤ t2.eval x := by
  have hx : (0 : Real) < x := lt_of_lt_of_le one_pos hx1
  have hpin := leaf_var_pin h x hx
  -- x·log (t2 x) = x·exp x − 1 ≥ x·(exp x − 1)
  have hge : x * (exp x - 1) ≤ x * log (t2.eval x) := by
    rw [hpin]
    have e : x * (exp x - 1) = x * exp x - x := by mach_mpoly [x, exp x]
    rw [e]
    exact sub_le_sub_left_wit hx1
  have hlog : exp x - 1 ≤ log (t2.eval x) := le_of_mul_le_mul_pos_left hx hge
  -- and log (t2 x) > 0, so t2 x > 0 and the exponential bound transfers
  have hpos : (0 : Real) < log (t2.eval x) := by
    have hgt : (0 : Real) < exp x - 1 := by
      refine lt_of_sub_pos_wit ?_
      have e : exp x - 1 - 0 = exp x - 1 := by mach_ring
      rw [e]
      have hlt : (1 : Real) < exp x := lt_of_lt_of_le (by
        have t := exp_lt (lt_of_lt_of_le one_pos hx1)
        rw [exp_zero] at t; exact t) (le_refl _)
      have s := add_lt_add_left hlt (-1 : Real)
      have f1 : (-1 : Real) + 1 = 0 := by mach_ring
      have f2 : (-1 : Real) + exp x = exp x - 1 := by mach_ring
      rw [f1, f2] at s
      exact s
    exact lt_of_lt_of_le hgt hlog
  have ht2pos : (0 : Real) < t2.eval x := lt_trans_ax one_pos (one_lt_of_log_pos hpos)
  have hm := exp_monotone hlog
  rw [exp_log ht2pos] at hm
  exact hm

/-- Leaf-`var` branch, right child `var`: one point kills it (`x = 1` forces `exp 1 = 1`). -/
theorem leaf_var_right_var_absurd
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var EMLTree.var).eval x = 1 / x) :
    False := by
  have hpin := leaf_var_pin (t2 := EMLTree.var) h 1 one_pos
  have hv : (EMLTree.var).eval (1 : Real) = 1 := rfl
  rw [hv, log_one] at hpin
  -- 1 * 0 = 1 * exp 1 − 1  ⟹  exp 1 = 1
  have he1 : exp 1 = 1 := by
    have e1 : (1 : Real) * 0 = 0 := by mach_ring
    rw [e1] at hpin
    have t : (0 : Real) + 1 = 1 * exp 1 - 1 + 1 := by rw [hpin]
    have e2 : (0 : Real) + 1 = 1 := by mach_ring
    have e3 : (1 : Real) * exp 1 - 1 + 1 = exp 1 := by mach_ring
    rw [e2, e3] at t
    exact t.symm
  have hlt : (1 : Real) < exp 1 := by
    have t := exp_lt zero_lt_one_ax
    rw [exp_zero] at t; exact t
  rw [he1] at hlt
  exact lt_irrefl_ax 1 hlt

/-- Leaf-`var` branch, right child constant: two points force `2·exp 2 − 2·exp 1 + 1 = 0`,
impossible since `exp 2 = exp 1 · exp 1 > exp 1`. -/
theorem leaf_var_right_const_absurd {k : Real}
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml EMLTree.var (EMLTree.const k)).eval x = 1 / x) : False := by
  have p1 := leaf_var_pin (t2 := EMLTree.const k) h 1 one_pos
  have p2 := leaf_var_pin (t2 := EMLTree.const k) h (1 + 1) (add_pos one_pos one_pos)
  have hc : ∀ y : Real, (EMLTree.const k).eval y = k := fun _ => rfl
  rw [hc] at p1 p2
  -- log k = exp 1 − 1, then substitute
  have hlk : log k = exp 1 - 1 := by
    have e1 : (1 : Real) * log k = log k := by mach_ring
    have e2 : (1 : Real) * exp 1 - 1 = exp 1 - 1 := by mach_ring
    rw [e1, e2] at p1
    exact p1
  rw [hlk] at p2
  -- (1+1)(exp 1 − 1) = (1+1) exp (1+1) − 1
  have hsplit : exp ((1 : Real) + 1) = exp 1 * exp 1 := exp_add 1 1
  rw [hsplit] at p2
  -- so (1+1)·exp 1·exp 1 − (1+1)·exp 1 + 1 = 0, but the left side is positive
  have hpos : (0 : Real) < (1 + 1) * (exp 1 * exp 1) - (1 + 1) * exp 1 + 1 := by
    have hgt : exp 1 < exp 1 * exp 1 := by
      have h1 : (1 : Real) < exp 1 := by
        have t := exp_lt zero_lt_one_ax
        rw [exp_zero] at t; exact t
      have s := mul_lt_mul_pos_left_wit h1 (exp_pos 1)
      have e : exp 1 * (1 : Real) = exp 1 := by mach_ring
      rw [e] at s
      exact s
    have hd : (0 : Real) < (1 + 1) * (exp 1 * exp 1) - (1 + 1) * exp 1 := by
      refine lt_of_sub_pos_wit ?_
      have e : (1 + 1) * (exp 1 * exp 1) - (1 + 1) * exp 1 - 0
          = (1 + 1) * (exp 1 * exp 1 - exp 1) := by
        mach_mpoly [exp 1]
      rw [e]
      refine mul_pos (add_pos one_pos one_pos) ?_
      refine lt_of_sub_pos_wit ?_
      have e2 : exp 1 * exp 1 - exp 1 - 0 = exp 1 * exp 1 - exp 1 := by
        mach_mpoly [exp 1]
      rw [e2]
      refine lt_of_sub_pos_wit ?_
      have e3 : exp 1 * exp 1 - exp 1 - 0 = exp 1 * exp 1 - exp 1 := by
        mach_mpoly [exp 1]
      rw [e3]
      have s := add_lt_add_left hgt (-exp 1)
      have f1 : -exp 1 + exp 1 = (0 : Real) := by mach_ring
      have f2 : -exp 1 + exp 1 * exp 1 = exp 1 * exp 1 - exp 1 := by
        mach_mpoly [exp 1]
      rw [f1, f2] at s
      exact s
    have s := add_lt_add_left one_pos ((1 + 1) * (exp 1 * exp 1) - (1 + 1) * exp 1)
    have e : (1 + 1) * (exp 1 * exp 1) - (1 + 1) * exp 1 + 0
        = (1 + 1) * (exp 1 * exp 1) - (1 + 1) * exp 1 := by mach_mpoly [exp 1]
    rw [e] at s
    exact lt_trans_ax hd s
  have hzero : (1 + 1) * (exp 1 * exp 1) - (1 + 1) * exp 1 + 1 = 0 := by
    have e : (1 + 1) * (exp 1 * exp 1) - (1 + 1) * exp 1 + 1
        = ((1 + 1) * (exp 1 * exp 1) - 1) - ((1 + 1) * (exp 1 - 1)) := by
      mach_mpoly [exp 1]
    rw [e, ← p2]
    mach_mpoly [exp 1]
  rw [hzero] at hpos
  exact lt_irrefl_ax 0 hpos

/-- The arithmetic core of the leaf-`var` kill, over bare reals.

⚠ **The floor's `L` depends on `t`** (`L = log K − t`), so the usable hypothesis is
`exp 1 − log K < t` — a condition on `t`. An earlier version took `L` free and required
`exp 1 − L < t`, which for `L = log K − t` degenerates to `exp 1 < log K`: **true, but never
satisfiable by the intended instantiation.**

Multiplying the pin by `exp t` linearises it to `v = w − exp t`; then `exp t ≤ exp 1 − log K + t`,
which `exp t ≥ t + t` contradicts once `t > exp 1 − log K`. -/
theorem leaf_var_arith {t v w Kl : Real} (ht1 : 1 ≤ t)
    (hpin : exp (-t) * v = exp (-t) * w - 1)
    (hLv : Kl - t ≤ v) (hw : w ≤ exp 1) (hbig : exp 1 - Kl < t) : False := by
  have hem : exp t * exp (-t) = 1 := by
    rw [← exp_add]
    have e : t + -t = (0 : Real) := by mach_ring
    rw [e, exp_zero]
  have hv : v = w - exp t := by
    have hmul : exp t * (exp (-t) * v) = exp t * (exp (-t) * w - 1) := by rw [hpin]
    have e1 : exp t * (exp (-t) * v) = (exp t * exp (-t)) * v := by
      mach_mpoly [exp t, exp (-t), v]
    have e2 : exp t * (exp (-t) * w - 1) = (exp t * exp (-t)) * w - exp t := by
      mach_mpoly [exp t, exp (-t), w]
    rw [e1, e2, hem] at hmul
    have e3 : (1 : Real) * v = v := by mach_ring
    have e4 : (1 : Real) * w = w := by mach_ring
    rw [e3, e4] at hmul
    exact hmul
  rw [hv] at hLv
  -- Kl − t ≤ w − exp t ≤ exp 1 − exp t  ⟹  exp t ≤ exp 1 − Kl + t
  have hstep : exp t ≤ exp 1 - Kl + t := by
    have s1 : Kl - t ≤ exp 1 - exp t := by
      have s := add_le_add_wit hw (le_refl (-exp t))
      have e1 : w + -exp t = w - exp t := by mach_ring
      have e2 : exp 1 + -exp t = exp 1 - exp t := by mach_ring
      rw [e1, e2] at s
      exact le_trans hLv s
    have s := add_le_add_left s1 (exp t - Kl + t)
    have e1 : exp t - Kl + t + (Kl - t) = exp t := by mach_mpoly [exp t, Kl, t]
    have e2 : exp t - Kl + t + (exp 1 - exp t) = exp 1 - Kl + t := by
      mach_mpoly [exp t, exp 1, Kl, t]
    rw [e1, e2] at s
    exact s
  -- exp t ≥ t + t forces t ≤ exp 1 − Kl
  have h2t : t + t ≤ exp t := exp_ge_two_mul ht1
  have hfin : t ≤ exp 1 - Kl := by
    have s := le_trans h2t hstep
    have u := add_le_add_left s (-t)
    have e1 : -t + (t + t) = t := by mach_mpoly [t]
    have e2 : -t + (exp 1 - Kl + t) = exp 1 - Kl := by mach_mpoly [exp 1, Kl, t]
    rw [e1, e2] at u
    exact u
  exact lt_irrefl_ax _ (lt_of_lt_of_le hbig hfin)

/-- # **Leaf-`var`: a linear floor on the right child is fatal.**

Instantiates `leaf_var_arith` at `x = exp(−t)` with `t := 1 + exp(exp 1 − log K) + exp(−log d)`,
which is simultaneously `≥ 1`, above `exp 1 − log K`, and small enough that `x ≤ d`. -/
theorem leaf_var_floor_absurd {t2 : EMLTree} {K d : Real} (hK : 0 < K)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hfloor : ∀ x : Real, 0 < x → x ≤ d → K * x ≤ t2.eval x)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  have ht1 : (1 : Real) ≤ 1 + exp (exp 1 - log K) + exp (-log d) := by
    have s := add_le_add_wit (add_le_add_wit (le_refl (1 : Real))
      (le_of_lt (exp_pos (exp 1 - log K)))) (le_of_lt (exp_pos (-log d)))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at s; exact s
  have hx0 : (0 : Real) < exp (-(1 + exp (exp 1 - log K) + exp (-log d))) := exp_pos _
  have hxd : exp (-(1 + exp (exp 1 - log K) + exp (-log d))) ≤ d := by
    have hge : -log d ≤ 1 + exp (exp 1 - log K) + exp (-log d) := by
      have h1 := le_of_lt (exp_grows_strictly_thm (-log d))
      have s := add_le_add_wit (add_le_add_wit (le_of_lt one_pos)
        (le_of_lt (exp_pos (exp 1 - log K)))) (le_refl (exp (-log d)))
      have e : (0 : Real) + 0 + exp (-log d) = exp (-log d) := by mach_ring
      rw [e] at s
      exact le_trans h1 s
    have hstep : -(1 + exp (exp 1 - log K) + exp (-log d)) ≤ log d := by
      have s := neg_le_neg_wit hge
      have e : -(-log d) = log d := by mach_ring
      rw [e] at s
      exact s
    have hh := exp_monotone hstep
    rw [exp_log hd] at hh
    exact hh
  have hx1 : exp (-(1 + exp (exp 1 - log K) + exp (-log d))) ≤ 1 := le_trans hxd hd1
  refine leaf_var_arith (t := 1 + exp (exp 1 - log K) + exp (-log d))
    (v := log (t2.eval (exp (-(1 + exp (exp 1 - log K) + exp (-log d))))))
    (w := exp (exp (-(1 + exp (exp 1 - log K) + exp (-log d)))))
    (Kl := log K) ht1 ?_ ?_ ?_ ?_
  · exact leaf_var_pin h _ hx0
  · -- the floor, pushed through log
    have hKx : (0 : Real) < K * exp (-(1 + exp (exp 1 - log K) + exp (-log d))) :=
      mul_pos hK hx0
    have hl := log_le_log hKx (hfloor _ hx0 hxd)
    rw [log_mul hK hx0, log_exp] at hl
    have e : log K + -(1 + exp (exp 1 - log K) + exp (-log d))
        = log K - (1 + exp (exp 1 - log K) + exp (-log d)) := by mach_ring
    rw [e] at hl
    exact hl
  · exact exp_monotone hx1
  · -- exp 1 − log K < t
    have h1 := exp_grows_strictly_thm (exp 1 - log K)
    have s := add_le_add_wit (add_le_add_wit (le_of_lt one_pos)
      (le_refl (exp (exp 1 - log K)))) (le_of_lt (exp_pos (-log d)))
    have e : (0 : Real) + exp (exp 1 - log K) + 0 = exp (exp 1 - log K) := by mach_ring
    rw [e] at s
    exact lt_of_lt_of_le h1 s

/-- # **Any CONSTANT-VALUED left child is impossible — not just `const c`.**

If `t1.eval x = C` on `(0,∞)` then `eml t1 t2` agrees pointwise with `eml (const C) t2` there, so
`depth3_leaf_const_absurd` applies verbatim. **No new proof, no duplicated machinery** — and the
left child may be of any depth. -/
theorem depth3_const_left_absurd {t1 t2 : EMLTree} {C : Real} (ht2 : t2.depth ≤ 2)
    (hC : ∀ x : Real, 0 < x → t1.eval x = C)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x) : False := by
  refine depth3_leaf_const_absurd (c := C) ht2 ?_
  intro x hx
  have e : (EMLTree.eml (EMLTree.const C) t2).eval x = (EMLTree.eml t1 t2).eval x := by
    show exp C - log (t2.eval x) = exp (t1.eval x) - log (t2.eval x)
    rw [hC x hx]
  rw [e]
  exact h x hx

/-- Third family, the constant-valued shape: `t1 = eml (const p) (const q)`. -/
theorem depth3_left_const_const_absurd {p q : Real} {t2 : EMLTree} (ht2 : t2.depth ≤ 2)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml (EMLTree.const p) (EMLTree.const q)) t2).eval x = 1 / x) :
    False :=
  depth3_const_left_absurd (C := exp p - log q) ht2 (fun _ _ => rfl) h

/-- # **The third family reduces to UNBOUNDED left children.**

A bounded depth-2 tree is constant (`depth_two_bounded_const`), and a constant-valued left child is
already impossible (`depth3_const_left_absurd`). So in `eml (eml A B) t2` **only an unbounded left
child can survive** — no case analysis on `A`, `B` at all. -/
theorem depth3_left_bounded_absurd {A B t2 : EMLTree} {L U : Real}
    (hA : A.depth ≤ 1) (hB : B.depth ≤ 1) (ht2 : t2.depth ≤ 2)
    (hlow : ∀ x : Real, 0 < x → L ≤ (EMLTree.eml A B).eval x)
    (hup : ∀ x : Real, 0 < x → (EMLTree.eml A B).eval x ≤ U)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml A B) t2).eval x = 1 / x) : False := by
  obtain ⟨C, hC⟩ := depth_two_bounded_const hA hB hlow hup
  exact depth3_const_left_absurd ht2 hC h

/-- **`∞`-side bound on the tree itself:** every depth-≤1 tree satisfies `A x ≤ exp x + C` for
`x ≥ 1`. Unlike the `log` bounds this needs **no cutoff** — every shape is dominated by `exp x`
plus a constant outright. -/
theorem depth_le_one_bound_at_infty (A : EMLTree) (hA : A.depth ≤ 1) :
    ∃ C : Real, ∀ x : Real, 1 ≤ x → A.eval x ≤ exp x + C := by
  have hnn : ∀ x : Real, 1 ≤ x → (0 : Real) ≤ log x := by
    intro x hx
    have t := log_le_log one_pos hx
    rw [log_one] at t; exact t
  have hadd : ∀ (v C x : Real), v ≤ C → (0 : Real) < exp x → v ≤ exp x + C := by
    intro v C x hv hx
    have s := add_le_add_wit (le_of_lt hx) hv
    have e : (0 : Real) + v = v := by mach_ring
    rw [e] at s; exact s
  cases A with
  | const c => exact ⟨c, fun x _ => hadd c c x (le_refl c) (exp_pos x)⟩
  | var =>
      refine ⟨0, fun x _ => ?_⟩
      show x ≤ exp x + 0
      have e : exp x + (0 : Real) = exp x := by mach_ring
      rw [e]
      exact le_of_lt (exp_grows_strictly_thm x)
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
          | const q =>
              exact ⟨exp p - log q, fun x _ =>
                hadd _ _ x (le_refl (exp p - log q)) (exp_pos x)⟩
          | var =>
              refine ⟨exp p, fun x hx => ?_⟩
              show exp p - log x ≤ exp x + exp p
              refine hadd _ _ x ?_ (exp_pos x)
              have s := add_le_add_wit (le_refl (exp p)) (neg_le_neg_wit (hnn x hx))
              have e1 : exp p + -log x = exp p - log x := by mach_ring
              have e2 : exp p + -(0 : Real) = exp p := by mach_ring
              rw [e1, e2] at s
              exact s
      | var =>
          cases b with
          | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
          | const q =>
              refine ⟨-log q, fun x _ => ?_⟩
              show exp x - log q ≤ exp x + -log q
              have e : exp x + -log q = exp x - log q := by mach_ring
              rw [e]
              exact le_refl _
          | var =>
              refine ⟨0, fun x hx => ?_⟩
              show exp x - log x ≤ exp x + 0
              have e : exp x + (0 : Real) = exp x := by mach_ring
              rw [e]
              have s := add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit (hnn x hx))
              have e1 : exp x + -log x = exp x - log x := by mach_ring
              have e2 : exp x + -(0 : Real) = exp x := by mach_ring
              rw [e1, e2] at s
              exact s

/-- # **The canonical reciprocal: `(size, depth) = (11, 4)`.**

`invX4` beats the original `invXTree` on **both** axes — and **size is the axis that is priced**
(`docs/cost_theory.md`, T38-NNP: *"composing operators is purely additive — no interface/depth
overhead"*). So this is the number a consumer wants.

⚠ **Best known, NOT proved optimal.** Optimality quantifies over every tree with `≤ 10` nodes —
which **includes depth-3 trees**, since a depth-3 reciprocal would sit at roughly 9 nodes and
strictly undercut this one. **`1/x ∉ EML₃` is therefore the lower-bound lemma protecting this
claim**, not the unrelated curiosity I had called it. -/
theorem invX4_size : invX4.size = 11 := by rfl

theorem invXTree_size : invXTree.size = 13 := by rfl

end MachLib
