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

/-! ### `invX4` is not isolated — it sits on a ONE-PARAMETER FAMILY

Found by the size-bounded search's **positive control**: asked to recover the known witness, the
optimiser returned machine-precision constants that were **not** the known ones. Working out why
gave the family below. A control that reproduces the answer exactly proves the optimiser can
memorise; one that finds a *different* exact answer proves it is searching. -/

/-- The depth-4 reciprocal with both free constants exposed. `invX4 = invX4gen (log (log (1+e))) 0`. -/
noncomputable def invX4gen (c0 c1 : Real) : EMLTree :=
  EMLTree.eml
    (EMLTree.eml (EMLTree.const c0) EMLTree.var)
    (EMLTree.eml (EMLTree.eml (EMLTree.eml (EMLTree.const c1) EMLTree.var) (EMLTree.const 1))
      (EMLTree.const 1))

theorem invX4_is_invX4gen : invX4 = invX4gen (log (log (1 + exp 1))) 0 := rfl

theorem invX4gen_size (c0 c1 : Real) : (invX4gen c0 c1).size = 11 := by rfl

theorem invX4gen_depth (c0 c1 : Real) : (invX4gen c0 c1).depth = 4 := by rfl

/-- **The whole family.** The two `const 1` leaves make their `log`s vanish, so the tree collapses
to `(exp(exp c0) − exp(exp c1))/x`. One equation on two constants ⟹ **a curve of witnesses.** -/
theorem invX4gen_eval {c0 c1 : Real} (hfam : exp (exp c0) - exp (exp c1) = 1) :
    ∀ x : Real, 0 < x → (invX4gen c0 c1).eval x = 1 / x := by
  intro x hx
  have hW : (EMLTree.eml (EMLTree.eml (EMLTree.const c1) EMLTree.var) (EMLTree.const 1)).eval x
      = exp (exp c1 - log x) := by
    show exp ((EMLTree.eml (EMLTree.const c1) EMLTree.var).eval x)
        - log ((EMLTree.const (1 : Real)).eval x) = _
    show exp (exp c1 - log x) - log (1 : Real) = _
    rw [log_one]; mach_mpoly [exp (exp c1 - log x)]
  have hR : log ((EMLTree.eml (EMLTree.eml (EMLTree.eml (EMLTree.const c1) EMLTree.var)
        (EMLTree.const 1)) (EMLTree.const 1)).eval x) = exp (exp c1 - log x) := by
    show log (exp ((EMLTree.eml (EMLTree.eml (EMLTree.const c1) EMLTree.var)
          (EMLTree.const 1)).eval x) - log ((EMLTree.const (1 : Real)).eval x)) = _
    rw [hW]
    show log (exp (exp (exp c1 - log x)) - log (1 : Real)) = _
    rw [log_one]
    have e : exp (exp (exp c1 - log x)) - (0 : Real) = exp (exp (exp c1 - log x)) := by mach_ring
    rw [e, log_exp]
  have hval : (invX4gen c0 c1).eval x = exp (exp c0 - log x) - exp (exp c1 - log x) := by
    show exp ((EMLTree.eml (EMLTree.const c0) EMLTree.var).eval x)
        - log ((EMLTree.eml (EMLTree.eml (EMLTree.eml (EMLTree.const c1) EMLTree.var)
            (EMLTree.const 1)) (EMLTree.const 1)).eval x) = _
    rw [hR]; rfl
  refine eq_inv_of_mul_eq_one hx ?_
  rw [hval]
  have hd : x * (exp (exp c0 - log x) - exp (exp c1 - log x))
      = x * exp (exp c0 - log x) - x * exp (exp c1 - log x) := by
    mach_mpoly [x, exp (exp c0 - log x), exp (exp c1 - log x)]
  rw [hd, mul_exp_sub_log hx, mul_exp_sub_log hx]
  exact hfam

/-- **`1/x` has a continuum of size-11 depth-4 realisations**, one for each `c1`: solve
`exp(exp c0) = 1 + exp(exp c1)`, which is always possible since the right side exceeds `1`. -/
theorem invX4gen_witness_for_any_c1 (c1 : Real) :
    ∃ c0 : Real, ∀ x : Real, 0 < x → (invX4gen c0 c1).eval x = 1 / x := by
  have h1 : (1 : Real) < 1 + exp (exp c1) := by
    have t := add_lt_add_left (exp_pos (exp c1)) (1 : Real)
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at t; exact t
  have hpos : (0 : Real) < 1 + exp (exp c1) := lt_of_lt_of_le one_pos (le_of_lt h1)
  have hlpos : (0 : Real) < log (1 + exp (exp c1)) := by
    have s : log 1 < log (1 + exp (exp c1)) := log_lt_log one_pos h1
    rw [log_one] at s; exact s
  refine ⟨log (log (1 + exp (exp c1))), invX4gen_eval ?_⟩
  rw [exp_log hlpos, exp_log hpos]
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

/-! ## ▸ **The size question, in the metric that is priced**

`docs/cost_theory.md` T38-NNP prices **size**, not depth. Everything above is stated in depth;
these two transfer it. -/

/-- **The first size LOWER bound on `1/x`: `s(1/x) ≥ 7`.**

`size ≤ 6` plus oddness gives `size ≤ 5`, then `2·depth + 1 ≤ 5` gives `depth ≤ 2`, and
`inv_x_not_in_eml_depth_le_2` closes it. So **two `eml` gates can never compute a reciprocal.** -/
theorem inv_x_size_ge_seven (t : EMLTree) (h : ∀ x : Real, 0 < x → t.eval x = 1 / x) :
    7 ≤ t.size := by
  obtain ⟨k, hk⟩ := size_odd t
  have hd := two_mul_depth_succ_le_size t
  rcases Nat.lt_or_ge t.size 7 with hlt | hge
  · exact absurd h (inv_x_not_in_eml_depth_le_2 t (by omega))
  · exact hge

/-- # **`s(1/x) ∈ {7, 9, 11}`** — proved.

A **minimal** EML reciprocal has size `7`, `9`, or `11`: at least `7` by `inv_x_size_ge_seven`, at
most `11` because `invX4` is a witness of that size, and `8`/`10` are impossible because
`size_odd` says sizes are always `2k+1`.

Three values, i.e. **three, four, or five `eml` gates.** (The numerical search over all 528
configurations at 3 and 4 gates found no witness — but that is evidence, not proof, so `7` and `9`
are not excluded here.) -/
theorem inv_x_min_size_seven_nine_or_eleven (t : EMLTree)
    (h : ∀ x : Real, 0 < x → t.eval x = 1 / x)
    (hmin : ∀ u : EMLTree, (∀ x : Real, 0 < x → u.eval x = 1 / x) → t.size ≤ u.size) :
    t.size = 7 ∨ t.size = 9 ∨ t.size = 11 := by
  have hlow := inv_x_size_ge_seven t h
  have hup : t.size ≤ 11 := by
    have h11 : invX4.size = 11 := by rfl
    have hle := hmin invX4 invX4_eval
    rwa [h11] at hle
  obtain ⟨k, hk⟩ := size_odd t
  omega

/-! ## ▸ The clamp, turned into a contradiction

The totalised `log` has been this arm's most persistent obstacle: wherever a tree goes non-positive,
`log` clamps to `0` and all information about the tree is destroyed. **In the leaf-`var` branch that
is backwards** — the pin says what the clamped value must *equal*, and it cannot. -/

/-- `exp (-1) < 1`. Reversal: if `exp(-1) ≥ 1` then `1 = exp(-1)·exp 1 ≥ exp 1 > 1`. -/
theorem exp_neg_one_lt_one : exp (-1) < 1 := by
  have hprod : exp (-1) * exp 1 = 1 := by
    rw [← exp_add]
    have e : (-1 : Real) + 1 = 0 := by mach_ring
    rw [e, exp_zero]
  rcases lt_total (exp (-1)) 1 with hgood | hz | hbad
  · exact hgood
  · exfalso
    rw [hz] at hprod
    have e : (1 : Real) * exp 1 = exp 1 := by mach_ring
    rw [e] at hprod
    exact (ne_of_lt (exp_grows_strictly_thm 1)) hprod.symm
  · exfalso
    have he1 : (1 : Real) < exp 1 := exp_grows_strictly_thm 1
    have s : 1 * exp 1 ≤ exp (-1) * exp 1 :=
      mul_le_mul_of_nonneg_right (le_of_lt hbad) (le_of_lt (exp_pos 1))
    rw [hprod] at s
    have e : (1 : Real) * exp 1 = exp 1 := by mach_ring
    rw [e] at s
    exact (ne_of_lt (lt_of_lt_of_le he1 s)) rfl

/-- **`x·exp x < 1` below `exp (-1)`.** Division-free: `x·exp x < exp(-1)·exp 1 = exp 0 = 1`. -/
theorem mul_exp_lt_one_of_lt_exp_neg_one {x : Real} (hx : 0 < x) (hlt : x < exp (-1)) :
    x * exp x < 1 := by
  have hprod : exp (-1) * exp 1 = 1 := by
    rw [← exp_add]
    have e : (-1 : Real) + 1 = 0 := by mach_ring
    rw [e, exp_zero]
  have hneg : (-1 : Real) < 0 := by
    have s := add_lt_add_left one_pos (-1 : Real)
    have l : (-1 : Real) + 0 = -1 := by mach_ring
    have r : (-1 : Real) + 1 = 0 := by mach_ring
    rw [l, r] at s; exact s
  have hx1 : x < 1 := lt_of_lt_of_le hlt (exp_le_one_of_nonpos (le_of_lt hneg))
  have s1 : x * exp x < exp (-1) * exp x := mul_lt_mul_of_pos_right hlt (exp_pos x)
  have s2 : exp (-1) * exp x < exp (-1) * exp 1 :=
    mul_lt_mul_pos_left (exp_lt hx1) (exp_pos (-1))
  rw [hprod] at s2
  exact lt_of_lt_of_le s1 (le_of_lt s2)

/-- **THE UNLOCK.** With a leaf-`var` left child the right child is **strictly positive** wherever
`x·exp x ≠ 1` — for **any** `t2`, at **any** depth.

If `t2 x ≤ 0` the totalised `log` clamps it to `0`, and `leaf_var_pin` then reads `0 = x·exp x − 1`.
So the clamp does not hide the tree here; it *pins* it, at the one point `x·exp x = 1`.

This discharges the two shape pairs that `RESULT_DUAL_CEILING.md` could only settle in prose
(*"vacuous — the tree is `≤ 0`, so regime 3 is unreachable"*). -/
theorem leaf_var_right_pos {t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x)
    {x : Real} (hx : 0 < x) (hlt : x * exp x < 1) : 0 < t2.eval x := by
  have key : t2.eval x ≤ 0 → False := by
    intro hle
    have hz : log (t2.eval x) = 0 := log_nonpos hle
    have hpin := leaf_var_pin h x hx
    rw [hz] at hpin
    have e : x * (0 : Real) = 0 := by mach_ring
    rw [e] at hpin
    have heq : x * exp x = 1 := by
      have s : (0 : Real) + 1 = (x * exp x - 1) + 1 := by rw [hpin]
      have l : (0 : Real) + 1 = 1 := by mach_ring
      have r : x * exp x - 1 + 1 = x * exp x := by mach_ring
      rw [l, r] at s; exact s.symm
    rw [heq] at hlt
    exact (ne_of_lt hlt) rfl
  rcases lt_total 0 (t2.eval x) with hgt | heq | hlt2
  · exact hgt
  · exact absurd (le_of_eq heq.symm) (fun hh => key hh)
  · exact absurd (le_of_lt hlt2) (fun hh => key hh)

/-- Packaged with the concrete cutoff. -/
theorem leaf_var_right_pos_near_zero {t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x)
    {x : Real} (hx : 0 < x) (hlt : x < exp (-1)) : 0 < t2.eval x :=
  leaf_var_right_pos h hx (mul_exp_lt_one_of_lt_exp_neg_one hx hlt)

/-! ## ▸ A reusable `min` surrogate

This corpus has no `min` and no `abs`. Three times already this arm has hand-rolled a bespoke
expression sitting under two bounds at once (`shrink_pos`/`shrink_lt`/`shrink_le_one`). **Here it is
once, in general.** -/

/-- `b·exp(-b) < 1` for `b > 0` — the whole content of the surrogate, from `b < exp b`. -/
theorem mul_exp_neg_lt_one {b : Real} (hb : 0 < b) : b * exp (-b) < 1 := by
  have hlt : b < exp b := exp_grows_strictly_thm b
  have s : b * exp (-b) < exp b * exp (-b) := mul_lt_mul_of_pos_right hlt (exp_pos (-b))
  have e : exp b * exp (-b) = 1 := by
    rw [← exp_add]
    have z : b + -b = 0 := by mach_ring
    rw [z, exp_zero]
  rw [e] at s; exact s

/-- **`min` surrogate.** `w a b := a·b·exp(-a-b)` is positive and **strictly below both** `a` and
`b`. Replaces every ad-hoc two-constraint cutoff in this arm. -/
theorem two_bound_witness {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    0 < a * b * exp (-a - b) ∧ a * b * exp (-a - b) < a ∧ a * b * exp (-a - b) < b := by
  have hea : exp (-a) ≤ 1 := by
    have hna : -a ≤ 0 := by
      have s := add_lt_add_left ha (-a)
      have l : -a + 0 = -a := by mach_ring
      have r : -a + a = 0 := by mach_ring
      rw [l, r] at s; exact le_of_lt s
    exact exp_le_one_of_nonpos hna
  have heb : exp (-b) ≤ 1 := by
    have hnb : -b ≤ 0 := by
      have s := add_lt_add_left hb (-b)
      have l : -b + 0 = -b := by mach_ring
      have r : -b + b = 0 := by mach_ring
      rw [l, r] at s; exact le_of_lt s
    exact exp_le_one_of_nonpos hnb
  have hsplit : exp (-a - b) = exp (-a) * exp (-b) := by
    rw [← exp_add]
    have z : -a + -b = -a - b := by mach_ring
    rw [z]
  refine ⟨?_, ?_, ?_⟩
  · exact mul_pos (mul_pos ha hb) (exp_pos _)
  · -- a·b·exp(-a-b) = a · (b·exp(-b) · exp(-a)) < a · 1
    have key : b * exp (-a - b) < 1 := by
      rw [hsplit]
      have e1 : b * (exp (-a) * exp (-b)) = (b * exp (-b)) * exp (-a) := by
        mach_mpoly [b, exp (-a), exp (-b)]
      rw [e1]
      have s1 : (b * exp (-b)) * exp (-a) < 1 * exp (-a) :=
        mul_lt_mul_of_pos_right (mul_exp_neg_lt_one hb) (exp_pos (-a))
      have e2 : (1 : Real) * exp (-a) = exp (-a) := by mach_ring
      rw [e2] at s1
      exact lt_of_lt_of_le s1 hea
    have s := mul_lt_mul_pos_left key ha
    have e3 : a * (b * exp (-a - b)) = a * b * exp (-a - b) := by
      mach_mpoly [a, b, exp (-a - b)]
    have e4 : a * (1 : Real) = a := by mach_ring
    rw [e3, e4] at s; exact s
  · have key : a * exp (-a - b) < 1 := by
      rw [hsplit]
      have e1 : a * (exp (-a) * exp (-b)) = (a * exp (-a)) * exp (-b) := by
        mach_mpoly [a, exp (-a), exp (-b)]
      rw [e1]
      have s1 : (a * exp (-a)) * exp (-b) < 1 * exp (-b) :=
        mul_lt_mul_of_pos_right (mul_exp_neg_lt_one ha) (exp_pos (-b))
      have e2 : (1 : Real) * exp (-b) = exp (-b) := by mach_ring
      rw [e2] at s1
      exact lt_of_lt_of_le s1 heb
    have s := mul_lt_mul_pos_left key hb
    have e3 : b * (a * exp (-a - b)) = a * b * exp (-a - b) := by
      mach_mpoly [a, b, exp (-a - b)]
    have e4 : b * (1 : Real) = b := by mach_ring
    rw [e3, e4] at s; exact s

/-! ## ▸ Two shape-free dispatchers into `leaf_var_floor_absurd` -/

/-- A **constant** positive floor near `0` is absurd. -/
theorem leaf_var_const_floor_absurd {t2 : EMLTree} {c d : Real}
    (hc : 0 < c) (hd : 0 < d) (hd1 : d ≤ 1)
    (hfl : ∀ x : Real, 0 < x → x ≤ d → c ≤ t2.eval x)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  refine leaf_var_floor_absurd hc hd hd1 (fun x hx hxd => ?_) h
  have hx1 : x ≤ 1 := le_trans hxd hd1
  have s : c * x ≤ c * 1 := mul_le_mul_of_nonneg_left hx1 (le_of_lt hc)
  have e : c * (1 : Real) = c := by mach_ring
  rw [e] at s
  exact le_trans s (hfl x hx hxd)

/-- An **affine** floor `γ + K·x` with `γ ≥ 0` and `K > 0` is absurd.

> **This is where the three-way pattern collapses to two.** The tangent bound `exp y ≥ 1 + y`
> supplies the linear term for free, so the *coincidence* case `γ = 0` needs no separate
> regime-3 floor — it is the same inequality with `γ` set to zero. -/
theorem leaf_var_affine_floor_absurd {t2 : EMLTree} {γ K : Real}
    (hK : 0 < K) (hγ : 0 ≤ γ)
    (hfl : ∀ x : Real, 0 < x → x ≤ 1 → γ + K * x ≤ t2.eval x)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  refine leaf_var_floor_absurd hK one_pos (le_refl 1) (fun x hx hx1 => ?_) h
  have s : K * x ≤ γ + K * x := by
    have t := add_le_add_wit hγ (le_refl (K * x))
    have e : (0 : Real) + K * x = K * x := by mach_ring
    rw [e] at t; exact t
  exact le_trans s (hfl x hx hx1)

/-- Strict monotonicity of the totalised `log` on the positives. Proved by *reversal*: if
`log y ≤ log x` then `y = exp(log y) ≤ exp(log x) = x`. -/
theorem log_lt_log_strict {x y : Real} (hx : 0 < x) (hxy : x < y) : log x < log y := by
  have hy : (0 : Real) < y := lt_of_lt_of_le hx (le_of_lt hxy)
  rcases lt_total (log x) (log y) with hp | hz | hn
  · exact hp
  · exfalso
    have ex := exp_log hx
    rw [hz, exp_log hy] at ex
    exact (ne_of_lt hxy) ex.symm
  · exfalso
    have s : exp (log y) ≤ exp (log x) := exp_monotone (le_of_lt hn)
    rw [exp_log hx, exp_log hy] at s
    exact (ne_of_lt (lt_of_lt_of_le hxy s)) rfl

theorem log_pos_of_one_lt {y : Real} (hy : 1 < y) : 0 < log y := by
  have t := log_lt_log_strict one_pos hy
  rwa [log_one] at t

/-- `∃`-form, so callers get a *name* for the witness instead of the expression. -/
theorem two_bound_witness' {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    ∃ w : Real, 0 < w ∧ w < a ∧ w < b :=
  ⟨_, two_bound_witness ha hb⟩

/-- Three constraints at once, by nesting `two_bound_witness`. -/
theorem three_bound_witness {a b c : Real} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ w : Real, 0 < w ∧ w < a ∧ w < b ∧ w < c := by
  obtain ⟨h1, h2, h3⟩ := two_bound_witness ha hb
  obtain ⟨g1, g2, g3⟩ := two_bound_witness h1 hc
  exact ⟨_, g1, lt_of_lt_of_le g2 (le_of_lt h2), lt_of_lt_of_le g2 (le_of_lt h3), g3⟩

/-- **The double tangent: `exp u ≥ e·u` for `u > 1`.**

One application of `1 + y < exp y` gives slope `1`. Peeling off a factor `exp 1` first and *then*
applying it gives slope `e` — and `e − 1 > 1` is exactly what lets an `exp`-of-a-diverging-argument
outrun a `log` of one. -/
theorem exp_e_mul_le {u : Real} (hu : 1 < u) : exp 1 * u ≤ exp u := by
  have hu1 : (0 : Real) < u - 1 := by
    have s := add_lt_add_left hu (-1 : Real)
    have l : (-1 : Real) + 1 = 0 := by mach_ring
    have r : (-1 : Real) + u = u - 1 := by mach_mpoly [u]
    rw [l, r] at s; exact s
  have ht := le_of_lt (exp_gt_one_plus_self (u - 1) hu1)
  have e1 : 1 + (u - 1) = u := by mach_mpoly [u]
  rw [e1] at ht
  have he : exp 1 * exp (u - 1) = exp u := by
    rw [← exp_add]
    have e : (1 : Real) + (u - 1) = u := by mach_mpoly [u]
    rw [e]
  have s : exp 1 * u ≤ exp 1 * exp (u - 1) :=
    mul_le_mul_of_nonneg_left ht (le_of_lt (exp_pos 1))
  rw [he] at s; exact s

/-! ## ▸ Two shape-free closures, powered by the unlock -/

/-- **Any constant-valued right child is absurd** — at any depth, any value.

No case split on the sign: `leaf_var_right_pos` *hands us* `γ > 0`, and the constant floor then
kills it. Compare `leaf_var_right_const_absurd`, which needed a two-point argument for the special
case `t2 = const k`. -/
theorem leaf_var_right_const_valued_absurd {t2 : EMLTree} {γ : Real}
    (hcv : ∀ x : Real, 0 < x → t2.eval x = γ)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  have hx0 : (0 : Real) < exp (-1 - 1) := exp_pos _
  have hlt : exp (-1 - 1) < exp (-1) := by
    refine exp_lt ?_
    have s := add_lt_add_left one_pos (-1 - 1 : Real)
    have l : (-1 - 1 : Real) + 0 = -1 - 1 := by mach_ring
    have r : (-1 - 1 : Real) + 1 = -1 := by mach_ring
    rw [l, r] at s; exact s
  have hp := leaf_var_right_pos_near_zero h hx0 hlt
  rw [hcv _ hx0] at hp
  exact leaf_var_const_floor_absurd hp one_pos (le_refl 1)
    (fun x hx _ => le_of_eq (hcv x hx).symm) h

/-- **A right child dominating `c₀ − log x` is absurd.** This is the *unbounded* branch: the two
depth-≤1 shapes whose value blows up at `0` (`exp p − log x` and `exp x − log x`) push their parent
above any constant below a cutoff, and `two_bound_witness` supplies a cutoff meeting both
constraints (`≤ 1` and small enough) with no `min`. -/
theorem leaf_var_dominates_neglog_cutoff_absurd {t2 : EMLTree} {c₀ d₀ : Real}
    (hd0 : 0 < d₀) (hd01 : d₀ ≤ 1)
    (hdom : ∀ x : Real, 0 < x → x ≤ d₀ → c₀ - log x ≤ t2.eval x)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  obtain ⟨hwpos, hw1, hwE⟩ := two_bound_witness hd0 (exp_pos (c₀ - 1))
  refine leaf_var_const_floor_absurd one_pos hwpos
    (le_trans (le_of_lt hw1) hd01) (fun x hx hxd => ?_) h
  have hx1 : x ≤ d₀ := le_trans hxd (le_of_lt hw1)
  have hlog : log x ≤ c₀ - 1 := by
    have s1 : log x ≤ log (d₀ * exp (c₀ - 1) * exp (-d₀ - exp (c₀ - 1))) := log_le_log hx hxd
    have s2 : log (d₀ * exp (c₀ - 1) * exp (-d₀ - exp (c₀ - 1))) ≤ log (exp (c₀ - 1)) :=
      log_le_log hwpos (le_of_lt hwE)
    rw [log_exp] at s2
    exact le_trans s1 s2
  have hge : (1 : Real) ≤ c₀ - log x := by
    have t := add_le_add_wit (le_refl c₀) (neg_le_neg_wit hlog)
    have l : c₀ + -(c₀ - 1) = 1 := by mach_ring
    have r : c₀ + -log x = c₀ - log x := by mach_ring
    rw [l, r] at t; exact t
  exact le_trans hge (hdom x hx hx1)

/-- The whole-interval special case. -/
theorem leaf_var_dominates_neglog_absurd {t2 : EMLTree} {c₀ : Real}
    (hdom : ∀ x : Real, 0 < x → x ≤ 1 → c₀ - log x ≤ t2.eval x)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False :=
  leaf_var_dominates_neglog_cutoff_absurd one_pos (le_refl 1) hdom h

/-- **A right child that is `≤ 0` anywhere below `exp (-1)` is absurd.** -/
theorem leaf_var_neg_point_absurd {t2 : EMLTree} {x₀ : Real}
    (hx0 : 0 < x₀) (hlt : x₀ < exp (-1)) (hneg : t2.eval x₀ ≤ 0)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False :=
  (ne_of_lt (lt_of_lt_of_le (leaf_var_right_pos_near_zero h hx0 hlt) hneg)) rfl

/-! ## ▸ **The first complete right-child-`eml` closure**

`t1 = var`, `t2 = eml A B` with `B` **constant-valued**. All six depth-≤1 shapes of `A`, no `min`,
no new axiom. Structure: the tangent bound `1 + y < exp y` turns every bounded `A` into an *affine*
lower bound `γ + K·x`; `γ ≥ 0` gives the floor and `γ < 0` gives a non-positive point, which
`leaf_var_right_pos` forbids.

> The **coincidence** case `γ = 0` — the one `RESULT_DUAL_CEILING.md` needed a bespoke regime-3
> floor for — is here just `γ ≥ 0` with `γ` set to zero. **The tangent bound supplies the linear
> term for free, so the three-way split collapses to two.** -/
theorem leaf_var_right_eml_const_absurd {A B : EMLTree} {β : Real}
    (hA : A.depth ≤ 1) (hB : ∀ x : Real, 0 < x → B.eval x = β)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml EMLTree.var (EMLTree.eml A B)).eval x = 1 / x) : False := by
  have hval : ∀ x : Real, 0 < x →
      (EMLTree.eml A B).eval x = exp (A.eval x) - log β := by
    intro x hx
    show exp (A.eval x) - log (B.eval x) = exp (A.eval x) - log β
    rw [hB x hx]
  -- `-log x ≥ 0` on `(0,1]`, reused by the two unbounded shapes
  have hnl : ∀ x : Real, 0 < x → x ≤ 1 → (0 : Real) ≤ -log x := by
    intro x hx h1
    have hh := neg_le_neg_wit (log_nonpos_of_le_one hx h1)
    have e : -(0 : Real) = 0 := by mach_ring
    rw [e] at hh; exact hh
  cases A with
  | const c =>
      exact leaf_var_right_const_valued_absurd
        (γ := exp c - log β) (fun x hx => hval x hx) h
  | var =>
      have hgood : (0 : Real) ≤ 1 - log β → False := by
        intro hγ
        refine leaf_var_affine_floor_absurd one_pos hγ (fun x hx hx1 => ?_) h
        rw [hval x hx]
        show 1 - log β + 1 * x ≤ exp x - log β
        have ht := le_of_lt (exp_gt_one_plus_self x hx)
        have s := add_le_add_wit ht (le_refl (-log β))
        have l : 1 + x + -log β = 1 - log β + 1 * x := by mach_mpoly [x, log β]
        have r : exp x + -log β = exp x - log β := by mach_mpoly [exp x, log β]
        rw [l, r] at s; exact s
      rcases lt_total (1 - log β) 0 with hneg | hz | hpos
      · have hLb : (1 : Real) < log β := by
          have s := add_lt_add_left hneg (log β)
          have l : log β + (1 - log β) = 1 := by mach_mpoly [log β]
          have r : log β + (0 : Real) = log β := by mach_ring
          rw [l, r] at s; exact s
        obtain ⟨hwpos, hw1, hwS⟩ :=
          two_bound_witness (exp_pos (-1)) (log_pos_of_one_lt hLb)
        refine leaf_var_neg_point_absurd hwpos hw1 ?_ h
        rw [hval _ hwpos]
        show exp _ - log β ≤ 0
        have hlt : exp (exp (-1) * log (log β) * exp (-exp (-1) - log (log β))) < log β := by
          have t := exp_lt hwS
          rwa [exp_log (lt_of_lt_of_le one_pos (le_of_lt hLb))] at t
        have s := add_lt_add_left hlt (-log β)
        have l : -log β + exp (exp (-1) * log (log β) * exp (-exp (-1) - log (log β)))
            = exp (exp (-1) * log (log β) * exp (-exp (-1) - log (log β))) - log β := by
          mach_mpoly [log β, exp (exp (-1) * log (log β) * exp (-exp (-1) - log (log β)))]
        have r : -log β + log β = 0 := by mach_ring
        rw [l, r] at s; exact le_of_lt s
      · exact hgood (le_of_eq hz.symm)
      · exact hgood (le_of_lt hpos)
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
          | const q =>
              exact leaf_var_right_const_valued_absurd
                (γ := exp (exp p - log q) - log β) (fun x hx => hval x hx) h
          | var =>
              -- A x = exp p − log x → ∞; parent dominates (1 + exp p − log β) − log x
              refine leaf_var_dominates_neglog_absurd
                (c₀ := 1 + exp p - log β) (fun x hx hx1 => ?_) h
              rw [hval x hx]
              show 1 + exp p - log β - log x ≤ exp (exp p - log x) - log β
              have harg : (0 : Real) < exp p - log x := by
                have t := add_le_add_wit (le_refl (exp p)) (hnl x hx hx1)
                have l : exp p + (0 : Real) = exp p := by mach_ring
                have r : exp p + -log x = exp p - log x := by mach_mpoly [exp p, log x]
                rw [l, r] at t
                exact lt_of_lt_of_le (exp_pos p) t
              have ht := le_of_lt (exp_gt_one_plus_self _ harg)
              have s := add_le_add_wit ht (le_refl (-log β))
              have l : 1 + (exp p - log x) + -log β = 1 + exp p - log β - log x := by
                mach_mpoly [exp p, log x, log β]
              have r : exp (exp p - log x) + -log β = exp (exp p - log x) - log β := by
                mach_mpoly [exp (exp p - log x), log β]
              rw [l, r] at s; exact s
      | var =>
          cases b with
          | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
          | const q =>
              have hgood : (0 : Real) ≤ exp (1 - log q) - log β → False := by
                intro hγ
                refine leaf_var_affine_floor_absurd (exp_pos (1 - log q)) hγ
                  (fun x hx hx1 => ?_) h
                rw [hval x hx]
                show exp (1 - log q) - log β + exp (1 - log q) * x
                    ≤ exp (exp x - log q) - log β
                have h1 : (1 - log q) + x ≤ exp x - log q := by
                  have t := le_of_lt (exp_gt_one_plus_self x hx)
                  have s := add_le_add_wit t (le_refl (-log q))
                  have l : 1 + x + -log q = 1 - log q + x := by mach_mpoly [x, log q]
                  have r : exp x + -log q = exp x - log q := by mach_mpoly [exp x, log q]
                  rw [l, r] at s; exact s
                have h2 : exp ((1 - log q) + x) ≤ exp (exp x - log q) := exp_monotone h1
                have h3 : exp (1 - log q) * (1 + x) ≤ exp ((1 - log q) + x) := by
                  rw [exp_add]
                  exact mul_le_mul_of_nonneg_left
                    (le_of_lt (exp_gt_one_plus_self x hx)) (le_of_lt (exp_pos _))
                have h4 := le_trans h3 h2
                have s := add_le_add_wit h4 (le_refl (-log β))
                have l : exp (1 - log q) * (1 + x) + -log β
                    = exp (1 - log q) - log β + exp (1 - log q) * x := by
                  mach_mpoly [exp (1 - log q), x, log β]
                have r : exp (exp x - log q) + -log β = exp (exp x - log q) - log β := by
                  mach_mpoly [exp (exp x - log q), log β]
                rw [l, r] at s; exact s
              rcases lt_total (exp (1 - log q) - log β) 0 with hneg | hz | hpos
              · have hlt1 : exp (1 - log q) < log β := by
                  have s := add_lt_add_left hneg (log β)
                  have l : log β + (exp (1 - log q) - log β) = exp (1 - log q) := by
                    mach_mpoly [log β, exp (1 - log q)]
                  have r : log β + (0 : Real) = log β := by mach_ring
                  rw [l, r] at s; exact s
                have hLbpos : (0 : Real) < log β :=
                  lt_of_lt_of_le (exp_pos (1 - log q)) (le_of_lt hlt1)
                have h2 : 1 - log q < log (log β) := by
                  have t := log_lt_log_strict (exp_pos (1 - log q)) hlt1
                  rwa [log_exp] at t
                have hS1 : (1 : Real) < log q + log (log β) := by
                  have s := add_lt_add_left h2 (log q)
                  have l : log q + (1 - log q) = 1 := by mach_mpoly [log q]
                  rw [l] at s; exact s
                obtain ⟨hwpos, hw1, hwS⟩ :=
                  two_bound_witness (exp_pos (-1)) (log_pos_of_one_lt hS1)
                refine leaf_var_neg_point_absurd hwpos hw1 ?_ h
                rw [hval _ hwpos]
                show exp (exp _ - log q) - log β ≤ 0
                have hx0 := exp_pos (-1)
                have hexp : exp (exp (-1) * log (log q + log (log β))
                    * exp (-exp (-1) - log (log q + log (log β))))
                    < log q + log (log β) := by
                  have t := exp_lt hwS
                  rwa [exp_log (lt_of_lt_of_le one_pos (le_of_lt hS1))] at t
                have hsub : exp (exp (-1) * log (log q + log (log β))
                    * exp (-exp (-1) - log (log q + log (log β)))) - log q < log (log β) := by
                  have s := add_lt_add_left hexp (-log q)
                  have l : -log q + (log q + log (log β)) = log (log β) := by
                    mach_mpoly [log q, log (log β)]
                  have r : -log q + exp (exp (-1) * log (log q + log (log β))
                      * exp (-exp (-1) - log (log q + log (log β))))
                      = exp (exp (-1) * log (log q + log (log β))
                      * exp (-exp (-1) - log (log q + log (log β)))) - log q := by
                    mach_mpoly [log q, exp (exp (-1) * log (log q + log (log β))
                      * exp (-exp (-1) - log (log q + log (log β))))]
                  rw [l, r] at s; exact s
                have hfin := exp_lt hsub
                rw [exp_log hLbpos] at hfin
                have s := add_lt_add_left hfin (-log β)
                have l : -log β + exp (exp (exp (-1) * log (log q + log (log β))
                    * exp (-exp (-1) - log (log q + log (log β)))) - log q)
                    = exp (exp (exp (-1) * log (log q + log (log β))
                    * exp (-exp (-1) - log (log q + log (log β)))) - log q) - log β := by
                  mach_mpoly [log β, exp (exp (exp (-1) * log (log q + log (log β))
                    * exp (-exp (-1) - log (log q + log (log β)))) - log q)]
                have r : -log β + log β = 0 := by mach_ring
                rw [l, r] at s; exact le_of_lt s
              · exact hgood (le_of_eq hz.symm)
              · exact hgood (le_of_lt hpos)
          | var =>
              -- A x = exp x − log x ≥ 1 − log x → ∞
              refine leaf_var_dominates_neglog_absurd
                (c₀ := 1 + 1 - log β) (fun x hx hx1 => ?_) h
              rw [hval x hx]
              show 1 + 1 - log β - log x ≤ exp (exp x - log x) - log β
              have hex1 : (1 : Real) ≤ exp x := one_le_exp (le_of_lt hx)
              have harg : (0 : Real) < exp x - log x := by
                have t := add_le_add_wit (le_refl (exp x)) (hnl x hx hx1)
                have l : exp x + (0 : Real) = exp x := by mach_ring
                have r : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
                rw [l, r] at t
                exact lt_of_lt_of_le (exp_pos x) t
              have ht := le_of_lt (exp_gt_one_plus_self _ harg)
              have hlow : 1 + 1 - log x ≤ 1 + (exp x - log x) := by
                have t := add_le_add_wit hex1 (le_refl (-log x))
                have l2 : (1 : Real) + -log x = 1 - log x := by mach_mpoly [log x]
                have r2 : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
                rw [l2, r2] at t
                have u := add_le_add_wit (le_refl (1 : Real)) t
                have l3 : (1 : Real) + (1 - log x) = 1 + 1 - log x := by mach_mpoly [log x]
                rw [l3] at u; exact u
              have hchain := le_trans hlow ht
              have s := add_le_add_wit hchain (le_refl (-log β))
              have l : 1 + 1 - log x + -log β = 1 + 1 - log β - log x := by
                mach_mpoly [log x, log β]
              have r : exp (exp x - log x) + -log β = exp (exp x - log x) - log β := by
                mach_mpoly [exp (exp x - log x), log β]
              rw [l, r] at s; exact s

/-! ## ▸ **Non-constant `B`: the two routes**

With `B x` blowing up like `−log x`, everything turns on whether `A` does too. -/

/-- **`A` bounded, `B` unbounded ⟹ the tree goes non-positive.** `exp(A x)` is capped by a constant
while `log(B x) → ∞`. -/
theorem eml_nonpos_of_bddA_unbddB {A B : EMLTree} {MA cB x₀ : Real}
    (hbig : exp (exp MA) ≤ cB - log x₀)
    (hMA : A.eval x₀ ≤ MA)
    (hlow : cB - log x₀ ≤ B.eval x₀) :
    (EMLTree.eml A B).eval x₀ ≤ 0 := by
  show exp (A.eval x₀) - log (B.eval x₀) ≤ 0
  have h1 : exp (A.eval x₀) ≤ exp MA := exp_monotone hMA
  have h2 : exp MA ≤ log (B.eval x₀) := by
    have s1 : log (exp (exp MA)) ≤ log (B.eval x₀) :=
      log_le_log (exp_pos (exp MA)) (le_trans hbig hlow)
    rwa [log_exp] at s1
  have hle := le_trans h1 h2
  have s := add_le_add_wit hle (le_refl (-log (B.eval x₀)))
  have l : exp (A.eval x₀) + -log (B.eval x₀) = exp (A.eval x₀) - log (B.eval x₀) := by
    mach_mpoly [exp (A.eval x₀), log (B.eval x₀)]
  have r : log (B.eval x₀) + -log (B.eval x₀) = 0 := by mach_ring
  rw [l, r] at s; exact s

theorem leaf_var_bddA_unbddB_absurd {A B : EMLTree} {MA cB : Real}
    (hMA : ∀ x : Real, 0 < x → x ≤ 1 → A.eval x ≤ MA)
    (hlow : ∀ x : Real, 0 < x → x ≤ 1 → cB - log x ≤ B.eval x)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml EMLTree.var (EMLTree.eml A B)).eval x = 1 / x) : False := by
  obtain ⟨w, hwpos, hwe, hwE⟩ :=
    two_bound_witness' (exp_pos (-1)) (exp_pos (cB - exp (exp MA)))
  have hw1 : w ≤ 1 := le_of_lt (lt_of_lt_of_le hwe (le_of_lt exp_neg_one_lt_one))
  have hl : log w ≤ cB - exp (exp MA) := by
    have t := log_le_log hwpos (le_of_lt hwE)
    rwa [log_exp] at t
  have hbig : exp (exp MA) ≤ cB - log w := by
    have t := add_le_add_wit (le_refl cB) (neg_le_neg_wit hl)
    have l2 : cB + -(cB - exp (exp MA)) = exp (exp MA) := by mach_mpoly [cB, exp (exp MA)]
    have r2 : cB + -log w = cB - log w := by mach_mpoly [cB, log w]
    rw [l2, r2] at t; exact t
  exact leaf_var_neg_point_absurd hwpos hwe
    (eml_nonpos_of_bddA_unbddB hbig (hMA w hwpos hw1) (hlow w hwpos hw1)) h

/-- **`A` unbounded, `B` unbounded ⟹ the tree dominates `c₀ − log x`.**

The double tangent gives `exp(A x) ≥ e·(cA − log x)` — slope `e` — while `log(B x)` has slope only
`1`. The surviving coefficient on `−log x` is `e − 1`, and `e > 2` (from the tangent bound at `1`)
makes it exceed `1`. -/
theorem leaf_var_unbddA_unbddB_absurd {A B : EMLTree} {cA cB : Real}
    (hcA : ∀ x : Real, 0 < x → x ≤ 1 → cA - log x ≤ A.eval x)
    (hcB : ∀ x : Real, 0 < x → x ≤ 1 → B.eval x ≤ cB - log x)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml EMLTree.var (EMLTree.eml A B)).eval x = 1 / x) : False := by
  obtain ⟨d, hdpos, hd1, hdA, hdB⟩ :=
    three_bound_witness one_pos (exp_pos (cA - 1)) (exp_pos (cB - 1))
  refine leaf_var_dominates_neglog_cutoff_absurd (c₀ := exp 1 * cA - cB + 1)
    hdpos (le_of_lt hd1) (fun x hx hxd => ?_) h
  have hx1 : x ≤ 1 := le_of_lt (lt_of_le_of_lt hxd hd1)
  have hnl : (0 : Real) ≤ -log x := by
    have hh := neg_le_neg_wit (log_nonpos_of_le_one hx hx1)
    have e : -(0 : Real) = 0 := by mach_ring
    rw [e] at hh; exact hh
  have hlA : log x < cA - 1 := by
    have t := log_lt_log_strict hx (lt_of_le_of_lt hxd hdA)
    rwa [log_exp] at t
  have hlB : log x ≤ cB - 1 := by
    have t := log_le_log hx (le_of_lt (lt_of_le_of_lt hxd hdB))
    rwa [log_exp] at t
  have hu : (1 : Real) < cA - log x := by
    have t := add_lt_add_left hlA (cA - log x - (cA - 1))
    have l2 : cA - log x - (cA - 1) + log x = 1 := by mach_mpoly [cA, log x]
    have r2 : cA - log x - (cA - 1) + (cA - 1) = cA - log x := by mach_mpoly [cA, log x]
    rw [l2, r2] at t; exact t
  have hone : (1 : Real) ≤ cB - log x := by
    have t := add_le_add_wit (le_refl (cB - log x - (cB - 1))) hlB
    have l2 : cB - log x - (cB - 1) + log x = 1 := by mach_mpoly [cB, log x]
    have r2 : cB - log x - (cB - 1) + (cB - 1) = cB - log x := by mach_mpoly [cB, log x]
    rw [l2, r2] at t; exact t
  have h1 : exp 1 * (cA - log x) ≤ exp (A.eval x) :=
    le_trans (exp_e_mul_le hu) (exp_monotone (hcA x hx hx1))
  have h2 : log (B.eval x) ≤ cB - log x - 1 := by
    have hz0 : (0 : Real) ≤ cB - log x - 1 := by
      have t := add_le_add_wit hone (le_refl (-1 : Real))
      have l2 : (1 : Real) + -1 = 0 := by mach_ring
      have r2 : cB - log x + -1 = cB - log x - 1 := by mach_mpoly [cB, log x]
      rw [l2, r2] at t; exact t
    rcases lt_total 0 (B.eval x) with hp | hz | hn
    · exact le_trans (log_le_log hp (hcB x hx hx1)) (log_le_sub_one_of_one_le hone)
    · rw [log_nonpos (le_of_eq hz.symm)]; exact hz0
    · rw [log_nonpos (le_of_lt hn)]; exact hz0
  have hsum := add_le_add_wit h1 (neg_le_neg_wit h2)
  have rr : exp (A.eval x) + -log (B.eval x) = (EMLTree.eml A B).eval x := by
    show exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x)
    mach_mpoly [exp (A.eval x), log (B.eval x)]
  rw [rr] at hsum
  have he2 : (0 : Real) ≤ exp 1 - 1 - 1 := by
    have t := le_of_lt (exp_gt_one_plus_self 1 one_pos)
    have s := add_le_add_wit t (le_refl (-(1 : Real) - 1))
    have l2 : (1 : Real) + 1 + (-1 - 1) = 0 := by mach_ring
    have r2 : exp 1 + (-1 - 1) = exp 1 - 1 - 1 := by mach_mpoly [exp 1]
    rw [l2, r2] at s; exact s
  have hp : (0 : Real) ≤ (exp 1 - 1 - 1) * (-log x) := by
    have t := mul_le_mul_of_nonneg_right he2 hnl
    have l2 : (0 : Real) * (-log x) = 0 := by mach_ring
    rw [l2] at t; exact t
  have hgoal : exp 1 * cA - cB + 1 - log x
      ≤ exp 1 * (cA - log x) + -(cB - log x - 1) := by
    have s := add_le_add_wit (le_refl (exp 1 * cA - cB + 1 - log x)) hp
    have l2 : exp 1 * cA - cB + 1 - log x + 0 = exp 1 * cA - cB + 1 - log x := by mach_ring
    have r2 : exp 1 * cA - cB + 1 - log x + (exp 1 - 1 - 1) * (-log x)
        = exp 1 * (cA - log x) + -(cB - log x - 1) := by
      mach_mpoly [exp 1, cA, cB, log x]
    rw [l2, r2] at s; exact s
  exact le_trans hgoal hsum

/-- Six `A`-shapes against an unbounded `B`: four bounded ones take the non-positive-point route,
the two that also blow up take the double-tangent route. -/
theorem leaf_var_unbddB_absurd {A B : EMLTree} {cBl cBu : Real}
    (hA : A.depth ≤ 1)
    (hlow : ∀ x : Real, 0 < x → x ≤ 1 → cBl - log x ≤ B.eval x)
    (hup : ∀ x : Real, 0 < x → x ≤ 1 → B.eval x ≤ cBu - log x)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml EMLTree.var (EMLTree.eml A B)).eval x = 1 / x) : False := by
  cases A with
  | const c =>
      exact leaf_var_bddA_unbddB_absurd (A := EMLTree.const c) (MA := c)
        (fun x _ _ => le_refl c) hlow h
  | var =>
      exact leaf_var_bddA_unbddB_absurd (A := EMLTree.var) (MA := 1)
        (fun x _ hx1 => hx1) hlow h
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
          | const q =>
              exact leaf_var_bddA_unbddB_absurd (MA := exp p - log q)
                (fun x _ _ => le_refl _) hlow h
          | var =>
              exact leaf_var_unbddA_unbddB_absurd (cA := exp p)
                (fun x _ _ => le_refl _) hup h
      | var =>
          cases b with
          | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
          | const q =>
              refine leaf_var_bddA_unbddB_absurd (MA := exp 1 - log q)
                (fun x hx hx1 => ?_) hlow h
              show exp x - log q ≤ exp 1 - log q
              have t := add_le_add_wit (exp_monotone hx1) (le_refl (-log q))
              have l2 : exp x + -log q = exp x - log q := by mach_mpoly [exp x, log q]
              have r2 : exp 1 + -log q = exp 1 - log q := by mach_mpoly [exp 1, log q]
              rw [l2, r2] at t; exact t
          | var =>
              refine leaf_var_unbddA_unbddB_absurd (cA := 1) (fun x hx hx1 => ?_) hup h
              show (1 : Real) - log x ≤ exp x - log x
              have t := add_le_add_wit (one_le_exp (le_of_lt hx)) (le_refl (-log x))
              have l2 : (1 : Real) + -log x = 1 - log x := by mach_mpoly [log x]
              have r2 : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
              rw [l2, r2] at t; exact t

/-! ## ▸ **The leaf-`var` branch, reduced to ONE shape** -/

/-- Every `t2 = eml A B` at depth ≤ 2 is absurd **except** `B = eml var (const q)`.

Four `B`-shapes close here: the two constant-valued ones via `leaf_var_right_eml_const_absurd`,
`B = var` because `log x → −∞` makes the parent dominate `−log x` with **no analysis of `A` at
all**, and the two that blow up via `leaf_var_unbddB_absurd`.

> `B = eml var (const q)` is the residue: `B x → 1 − log q`, **bounded** — the genuine
> divergent-cancellation case, where neither term runs away and the two nearly cancel. -/
theorem leaf_var_right_eml_absurd {A B : EMLTree} (hA : A.depth ≤ 1) (hB : B.depth ≤ 1)
    (hnot : ∀ q : Real, B ≠ EMLTree.eml EMLTree.var (EMLTree.const q))
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml EMLTree.var (EMLTree.eml A B)).eval x = 1 / x) : False := by
  cases B with
  | const q => exact leaf_var_right_eml_const_absurd (β := q) hA (fun x _ => rfl) h
  | var =>
      refine leaf_var_dominates_neglog_absurd (c₀ := 0) (fun x hx hx1 => ?_) h
      show (0 : Real) - log x ≤ exp (A.eval x) - log x
      have t := add_le_add_wit (le_of_lt (exp_pos (A.eval x))) (le_refl (-log x))
      have l2 : (0 : Real) + -log x = 0 - log x := by mach_mpoly [log x]
      have r2 : exp (A.eval x) + -log x = exp (A.eval x) - log x := by
        mach_mpoly [exp (A.eval x), log x]
      rw [l2, r2] at t; exact t
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd hB (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hB (by simp only [EMLTree.depth]; omega)
          | const q =>
              exact leaf_var_right_eml_const_absurd (β := exp p - log q) hA
                (fun x _ => rfl) h
          | var =>
              exact leaf_var_unbddB_absurd (cBl := exp p) (cBu := exp p) hA
                (fun x _ _ => le_refl _) (fun x _ _ => le_refl _) h
      | var =>
          cases b with
          | eml _ _ => exact absurd hB (by simp only [EMLTree.depth]; omega)
          | const q => exact absurd rfl (hnot q)
          | var =>
              refine leaf_var_unbddB_absurd (cBl := 1) (cBu := exp 1) hA
                (fun x hx hx1 => ?_) (fun x hx hx1 => ?_) h
              · show (1 : Real) - log x ≤ exp x - log x
                have t := add_le_add_wit (one_le_exp (le_of_lt hx)) (le_refl (-log x))
                have l2 : (1 : Real) + -log x = 1 - log x := by mach_mpoly [log x]
                have r2 : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
                rw [l2, r2] at t; exact t
              · show exp x - log x ≤ exp 1 - log x
                have t := add_le_add_wit (exp_monotone hx1) (le_refl (-log x))
                have l2 : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
                have r2 : exp 1 + -log x = exp 1 - log x := by mach_mpoly [exp 1, log x]
                rw [l2, r2] at t; exact t

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

/-! ## ▸ **The last shape of the leaf-`var` branch: `t2 = eml A (eml var (const q))`**

`B x = exp x − log q` is the **only** non-constant depth-≤1 right child that stays *bounded* at `0`.
Every other shape either runs to `+∞` (and `leaf_var_right_eml_absurd` kills it) or runs to `0`
(`B = var`, which hands the parent a free `−log x`). Here neither term runs away and the two nearly
cancel — the genuine divergent-cancellation case, which is why the previous two passes left it.

The new instrument is a **direction**, not a floor. Every closure in this arm so far read a *lower
bound* off the tree; the one fact that kills the shapes where the two terms cancel is that the pin
forces the right child to be **strictly increasing**. -/

/-- `0 < z ⟹ 0 < 1/z`, from `mul_inv` alone (this corpus has no ordered-field API for `/`). -/
theorem one_div_pos_of_pos {z : Real} (hz : 0 < z) : 0 < 1 / z := by
  rcases lt_total 0 (1 / z) with hp | hzz | hn
  · exact hp
  · exfalso
    have e : z * (1 / z) = 1 := mul_inv z (ne_of_gt hz)
    rw [← hzz] at e
    have e0 : z * (0 : Real) = 0 := by mach_ring
    rw [e0] at e
    exact (ne_of_lt one_pos) e
  · exfalso
    have s : z * (1 / z) < z * 0 := mul_lt_mul_pos_left_wit hn hz
    rw [mul_inv z (ne_of_gt hz)] at s
    have e0 : z * (0 : Real) = 0 := by mach_ring
    rw [e0] at s
    exact lt_irrefl_ax 0 (lt_trans_ax one_pos s)

/-- `0 < x < y ⟹ 1/y < 1/x`. Proved by *reversal*: `1/x ≤ 1/y` gives
`1 = x·(1/x) ≤ x·(1/y) < y·(1/y) = 1`. -/
theorem one_div_lt_one_div_of_lt {x y : Real} (hx : 0 < x) (hxy : x < y) :
    1 / y < 1 / x := by
  have hy : (0 : Real) < y := lt_trans_ax hx hxy
  have hbpos : (0 : Real) < 1 / y := one_div_pos_of_pos hy
  rcases lt_total (1 / y) (1 / x) with hp | hz | hn
  · exact hp
  · exfalso
    have s : x * (1 / y) < y * (1 / y) := mul_lt_mul_of_pos_right hxy hbpos
    rw [mul_inv y (ne_of_gt hy)] at s
    rw [hz] at s
    rw [mul_inv x (ne_of_gt hx)] at s
    exact lt_irrefl_ax 1 s
  · exfalso
    have s1 : x * (1 / x) ≤ x * (1 / y) :=
      mul_le_mul_of_nonneg_left (le_of_lt hn) (le_of_lt hx)
    have s2 : x * (1 / y) < y * (1 / y) := mul_lt_mul_of_pos_right hxy hbpos
    rw [mul_inv x (ne_of_gt hx)] at s1
    rw [mul_inv y (ne_of_gt hy)] at s2
    exact lt_irrefl_ax 1 (lt_of_le_of_lt s1 s2)

/-- # **The right child of a leaf-`var` reciprocal is STRICTLY INCREASING below the cutoff.**

Shape-free and depth-free, like `leaf_var_right_pos`. The equation gives
`log (t2 x) = exp x − 1/x` pointwise, and **both** terms of the right-hand side increase — `exp`
because it is `exp`, and `−1/x` because `x ↦ 1/x` decreases. So `log ∘ t2` is strictly increasing,
and `t2 > 0` (from `leaf_var_right_pos`) lets that be pulled back through `log`.

> Every earlier closure in this arm read a *floor* off the tree. This reads a **direction** — which
> is what the cancelling shapes need, because there the floor is `0` and carries no information. -/
theorem leaf_var_right_strict_mono {t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x)
    {x y : Real} (hx : 0 < x) (hxy : x < y) (hy : y < exp (-1)) :
    t2.eval x < t2.eval y := by
  have hyp : (0 : Real) < y := lt_trans_ax hx hxy
  have hxlt : x < exp (-1) := lt_trans_ax hxy hy
  have hpy : (0 : Real) < t2.eval y := leaf_var_right_pos_near_zero h hyp hy
  have ex : exp x - log (t2.eval x) = 1 / x := h x hx
  have ey : exp y - log (t2.eval y) = 1 / y := h y hyp
  have hE : exp x < exp y := exp_lt hxy
  have hI : 1 / y < 1 / x := one_div_lt_one_div_of_lt hx hxy
  -- `exp y − log(t2 y) < exp x − log(t2 x)`, then insert `exp x < exp y` on the left
  have s2 : exp y - log (t2.eval y) < exp x - log (t2.eval x) := by
    rw [ex, ey]; exact hI
  have s1 : -log (t2.eval y) + exp x < -log (t2.eval y) + exp y :=
    add_lt_add_left hE _
  have s1' : exp x - log (t2.eval y) < exp y - log (t2.eval y) := by
    have l : -log (t2.eval y) + exp x = exp x - log (t2.eval y) := by
      mach_mpoly [exp x, log (t2.eval y)]
    have r : -log (t2.eval y) + exp y = exp y - log (t2.eval y) := by
      mach_mpoly [exp y, log (t2.eval y)]
    rw [l, r] at s1; exact s1
  have s3 : exp x - log (t2.eval y) < exp x - log (t2.eval x) := lt_trans_ax s1' s2
  have hlog : log (t2.eval x) < log (t2.eval y) := by
    have s := add_lt_add_left s3 (log (t2.eval x) + log (t2.eval y) - exp x)
    have l : log (t2.eval x) + log (t2.eval y) - exp x + (exp x - log (t2.eval y))
        = log (t2.eval x) := by mach_mpoly [log (t2.eval x), log (t2.eval y), exp x]
    have r : log (t2.eval x) + log (t2.eval y) - exp x + (exp x - log (t2.eval x))
        = log (t2.eval y) := by mach_mpoly [log (t2.eval x), log (t2.eval y), exp x]
    rw [l, r] at s; exact s
  rcases lt_total (t2.eval x) (t2.eval y) with hp | hz | hn
  · exact hp
  · exfalso; rw [hz] at hlog; exact lt_irrefl_ax _ hlog
  · exfalso
    exact lt_irrefl_ax _ (lt_of_lt_of_le hlog (log_le_log hpy (le_of_lt hn)))

/-- **A right child that fails to increase anywhere below the cutoff is absurd.** The
contrapositive of `leaf_var_right_strict_mono`, in dispatcher form. -/
theorem leaf_var_nonincreasing_absurd {t2 : EMLTree} {x y : Real}
    (hx : 0 < x) (hxy : x < y) (hy : y < exp (-1))
    (hmono : t2.eval y ≤ t2.eval x)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False :=
  lt_irrefl_ax _ (lt_of_lt_of_le (leaf_var_right_strict_mono h hx hxy hy) hmono)

/-! ## ▸ **The direction lemma, in general form**

`leaf_var_right_strict_mono` above was stated for `t1 = var`, but **nothing in its proof uses that**.
The equation `exp(t1 x) − log(t2 x) = 1/x` gives `log(t2 x) = exp(t1 x) − 1/x` pointwise for *any*
`t1`, and `−1/x` rises on its own. So the left child only has to fail to *fall* for the right child
to be forced strictly up.

Stated once here, shape-free and depth-free, so it can be reached for deliberately rather than
rediscovered. The mechanism is **equational order reflection**: an equation pins the transformed
value, one side is strictly increasing, and `log` reflects order on its positive branch — so the
direction transfers back to the hidden subtree. Note this is *not* an appeal to piecewise
monotonicity of definable functions; it is elementary and gives a strict conclusion. -/

/-- **The general direction lemma.** If the left child does not decrease between two points, the
right child must strictly increase — for `t1`, `t2` of *any* shape and *any* depth. Only positivity
at the right-hand point is needed, and `leaf_var_right_pos` supplies that below the cutoff. -/
theorem depth3_right_strict_mono {t1 t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x)
    {x y : Real} (hx : 0 < x) (hxy : x < y)
    (hmono : t1.eval x ≤ t1.eval y) (hpy : 0 < t2.eval y) :
    t2.eval x < t2.eval y := by
  have hyp : (0 : Real) < y := lt_trans_ax hx hxy
  have ex : exp (t1.eval x) - log (t2.eval x) = 1 / x := h x hx
  have ey : exp (t1.eval y) - log (t2.eval y) = 1 / y := h y hyp
  have hE : exp (t1.eval x) ≤ exp (t1.eval y) := exp_monotone hmono
  have hI : 1 / y < 1 / x := one_div_lt_one_div_of_lt hx hxy
  have s2 : exp (t1.eval y) - log (t2.eval y) < exp (t1.eval x) - log (t2.eval x) := by
    rw [ex, ey]; exact hI
  have s1 : -log (t2.eval y) + exp (t1.eval x) ≤ -log (t2.eval y) + exp (t1.eval y) :=
    add_le_add_left hE _
  have s1' : exp (t1.eval x) - log (t2.eval y) ≤ exp (t1.eval y) - log (t2.eval y) := by
    have l : -log (t2.eval y) + exp (t1.eval x) = exp (t1.eval x) - log (t2.eval y) := by
      mach_mpoly [exp (t1.eval x), log (t2.eval y)]
    have r : -log (t2.eval y) + exp (t1.eval y) = exp (t1.eval y) - log (t2.eval y) := by
      mach_mpoly [exp (t1.eval y), log (t2.eval y)]
    rw [l, r] at s1; exact s1
  have s3 : exp (t1.eval x) - log (t2.eval y) < exp (t1.eval x) - log (t2.eval x) :=
    lt_of_le_of_lt s1' s2
  have hlog : log (t2.eval x) < log (t2.eval y) := by
    have s := add_lt_add_left s3 (log (t2.eval x) + log (t2.eval y) - exp (t1.eval x))
    have l : log (t2.eval x) + log (t2.eval y) - exp (t1.eval x)
          + (exp (t1.eval x) - log (t2.eval y)) = log (t2.eval x) := by
      mach_mpoly [log (t2.eval x), log (t2.eval y), exp (t1.eval x)]
    have r : log (t2.eval x) + log (t2.eval y) - exp (t1.eval x)
          + (exp (t1.eval x) - log (t2.eval x)) = log (t2.eval y) := by
      mach_mpoly [log (t2.eval x), log (t2.eval y), exp (t1.eval x)]
    rw [l, r] at s; exact s
  rcases lt_total (t2.eval x) (t2.eval y) with hp | hz | hn
  · exact hp
  · exfalso; rw [hz] at hlog; exact lt_irrefl_ax _ hlog
  · exfalso
    exact lt_irrefl_ax _ (lt_of_lt_of_le hlog (log_le_log hpy (le_of_lt hn)))

/-- **The eliminator.** Two points where the left child does not fall but the right child does not
rise kill the tree outright — no shape analysis, no depth bound, no parameter regimes. This is the
whole-family instrument: it prices a candidate by *behaviour* rather than by enumerating its
configurations. -/
theorem depth3_nonincreasing_absurd {t1 t2 : EMLTree} {x y : Real}
    (hx : 0 < x) (hxy : x < y) (hmono : t1.eval x ≤ t1.eval y) (hpy : 0 < t2.eval y)
    (hfail : t2.eval y ≤ t2.eval x)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x) : False :=
  lt_irrefl_ax _ (lt_of_lt_of_le (depth3_right_strict_mono h hx hxy hmono hpy) hfail)

/-- **The general clamp pin**, the analogue of `leaf_var_right_pos` for an arbitrary left child.
Where the right child is non-positive the totalised `log` collapses to `0`, and the equation then
pins the *left* child exactly: `x · exp(t1 x) = 1`. So a non-positive right child is not merely
awkward — it forces `t1 x = −log x` at that point, which for a fixed shallow `t1` can happen only on
the zero set of `t1 + log`. **This is the place where a zero-counting theorem would legitimately
apply** — counting solutions of an equation, which is what Khovanskii-type results are actually
about. -/
theorem depth3_left_pinned_of_right_nonpos {t1 t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x)
    {x : Real} (hx : 0 < x) (hle : t2.eval x ≤ 0) : x * exp (t1.eval x) = 1 := by
  have hz : log (t2.eval x) = 0 := log_nonpos hle
  have e : exp (t1.eval x) - log (t2.eval x) = 1 / x := h x hx
  rw [hz] at e
  have e2 : exp (t1.eval x) - (0 : Real) = exp (t1.eval x) := by mach_ring
  rw [e2] at e
  have hxne : x ≠ 0 := ne_of_gt hx
  rw [e, mul_inv x hxne]

/-! ### The `∞`-side rank ladder

The equation read at `∞` says `exp(t1 x) = 1/x + log(t2 x) ≤ 1 + log(t2 x)` for `x ≥ 1`. The left
side is `exp` of a depth-2 tree; the right is `log` of one. **Those sit two rungs apart**, so an
unbounded left child cannot be paid for. Making that precise needs three bounds, two of which
already exist (`depth_le_one_bound_at_infty`, `depth_le_one_log_bound_at_infty`) — the third is a
*lower* bound on `log`, i.e. a ceiling on `−log`, which no tool here had. -/

/-- `log_le_of_le_exp_mul` with the exponent free: the hypothesis `1 ≤ x` was only ever used to make
`x + log D` non-negative, which `0 ≤ z` does directly. Needed at `z := exp x`, one rung up. -/
theorem log_le_of_le_exp_mul' {y z D : Real} (hz : 0 ≤ z) (hD : 1 ≤ D)
    (h : y ≤ exp z * D) : log y ≤ z + log D := by
  have hD0 : (0 : Real) < D := lt_of_lt_of_le one_pos hD
  have hlogD : (0 : Real) ≤ log D := by
    have t := log_le_log one_pos hD
    rw [log_one] at t; exact t
  have hsum : (0 : Real) ≤ z + log D := by
    have s := add_le_add_wit hz hlogD
    have e : (0 : Real) + 0 = 0 := by mach_ring
    rw [e] at s; exact s
  rcases lt_total 0 y with hp | hzz | hn
  · have hl := log_le_log hp h
    rw [log_mul (exp_pos z) hD0, log_exp] at hl
    exact hl
  · rw [← hzz, log_nonpos (le_refl (0 : Real))]; exact hsum
  · rw [log_nonpos (le_of_lt hn)]; exact hsum

/-- **A ceiling on `−log` at `∞`.** Every depth-≤1 tree eventually keeps its `log` from running to
`−∞`: past an explicit threshold, `−log (D x) ≤ M`.

Why it is true shape by shape: a constant contributes a constant; `var` and the two shapes that grow
give `log ≥ 0`; and `exp p − log x`, which *falls* to `−∞`, is eventually **clamped** — so its `−log`
is `0`, not `+∞`. The totalised `log` is what makes the last case work, which is the third time in
this arm the clamp has helped rather than blocked. -/
theorem depth_le_one_neg_log_bound_at_infty (D : EMLTree) (hD : D.depth ≤ 1) :
    ∃ M x₁ : Real, 1 ≤ x₁ ∧ ∀ x : Real, x₁ ≤ x → -log (D.eval x) ≤ M := by
  -- `x ≥ 1 ⟹ log x ≥ 0 ⟹ −log x ≤ 0`, and `y ≥ 1 ⟹ −log y ≤ 0`
  have hnl : ∀ y : Real, 1 ≤ y → -log y ≤ 0 := by
    intro y hy
    have t := log_le_log one_pos hy
    rw [log_one] at t
    have s := neg_le_neg_wit t
    have e : -(0 : Real) = 0 := by mach_ring
    rw [e] at s; exact s
  cases D with
  | const c => exact ⟨-log c, 1, le_refl 1, fun _ _ => le_refl _⟩
  | var => exact ⟨0, 1, le_refl 1, fun x hx => hnl x hx⟩
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd hD (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hD (by simp only [EMLTree.depth]; omega)
          | const q => exact ⟨-log (exp p - log q), 1, le_refl 1, fun _ _ => le_refl _⟩
          | var =>
              -- `exp p − log x → −∞`: past `x = exp (exp p)` the log is CLAMPED to `0`
              refine ⟨0, 1 + exp (exp p), ?_, fun x hx => ?_⟩
              · have s := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos (exp p)))
                have e : (1 : Real) + 0 = 1 := by mach_ring
                rw [e] at s; exact s
              · show -log (exp p - log x) ≤ 0
                have hxpos : (0 : Real) < x :=
                  lt_of_lt_of_le (lt_of_lt_of_le one_pos
                    (by
                      have s := add_le_add_wit (le_refl (1 : Real))
                        (le_of_lt (exp_pos (exp p)))
                      have e : (1 : Real) + 0 = 1 := by mach_ring
                      rw [e] at s; exact s)) hx
                have hge : exp (exp p) ≤ x := by
                  have s := add_le_add_wit (le_of_lt one_pos) (le_refl (exp (exp p)))
                  have e : (0 : Real) + exp (exp p) = exp (exp p) := by mach_ring
                  rw [e] at s
                  exact le_trans s hx
                have hlog : exp p ≤ log x := by
                  have t := log_le_log (exp_pos (exp p)) hge
                  rwa [log_exp] at t
                have hnp : exp p - log x ≤ 0 := by
                  have s := add_le_add_wit hlog (le_refl (-log x))
                  have l : exp p + -log x = exp p - log x := by mach_mpoly [exp p, log x]
                  have r : log x + -log x = (0 : Real) := by mach_ring
                  rw [l, r] at s; exact s
                rw [log_nonpos hnp]
                have e : -(0 : Real) = 0 := by mach_ring
                rw [e]; exact le_refl _
      | var =>
          cases b with
          | eml _ _ => exact absurd hD (by simp only [EMLTree.depth]; omega)
          | const q =>
              -- `exp x − log q ≥ 1` once `exp x ≥ 1 + log q`
              refine ⟨0, 1 + exp (log q), ?_, fun x hx => ?_⟩
              · have s := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos (log q)))
                have e : (1 : Real) + 0 = 1 := by mach_ring
                rw [e] at s; exact s
              · show -log (exp x - log q) ≤ 0
                refine hnl _ ?_
                have h1 : 1 + exp (log q) < exp x :=
                  lt_of_lt_of_le (exp_grows_strictly_thm (1 + exp (log q))) (exp_monotone hx)
                have h2 : log q < exp (log q) := exp_grows_strictly_thm (log q)
                have hchain : 1 + log q ≤ exp x := by
                  have t : (1 : Real) + log q ≤ 1 + exp (log q) := by
                    have u := add_le_add_wit (le_refl (1 : Real)) (le_of_lt h2)
                    exact u
                  exact le_trans t (le_of_lt h1)
                have u := add_le_add_wit hchain (le_refl (-log q))
                have l : (1 : Real) + log q + -log q = 1 := by mach_mpoly [log q]
                have r : exp x + -log q = exp x - log q := by mach_mpoly [exp x, log q]
                rw [l, r] at u; exact u
          | var =>
              -- `exp x − log x ≥ 2 ≥ 1` for `x ≥ 1`, from `1 + x ≤ exp x` and `log x ≤ x − 1`
              refine ⟨0, 1, le_refl 1, fun x hx => ?_⟩
              show -log (exp x - log x) ≤ 0
              refine hnl _ ?_
              have hlogx : log x ≤ x - 1 := log_le_sub_one_of_one_le hx
              have hex : 1 + x ≤ exp x := one_add_le_exp x
              have s := add_le_add_wit hex (neg_le_neg_wit hlogx)
              have l : (1 : Real) + x + -(x - 1) = 1 + 1 := by mach_mpoly [x]
              have r : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
              rw [l, r] at s
              refine le_trans ?_ s
              have t := add_le_add_wit (le_refl (1 : Real)) (le_of_lt one_pos)
              have e : (1 : Real) + 0 = 1 := by mach_ring
              rw [e] at t; exact t

/-- **The depth-2 ceiling at `∞`:** `t x ≤ exp (exp x) · D` past a threshold. One rung above
`depth_le_one_bound_at_infty`, and the `−log` half is exactly what the ceiling above supplies. -/
theorem depth_le_two_bound_at_infty (t : EMLTree) (ht : t.depth ≤ 2) :
    ∃ D x₁ : Real, 1 ≤ x₁ ∧ 1 ≤ D ∧ ∀ x : Real, x₁ ≤ x → t.eval x ≤ exp (exp x) * D := by
  have hee : ∀ x : Real, 1 ≤ x → (1 : Real) ≤ exp (exp x) := by
    intro x hx
    exact one_le_exp (le_of_lt (exp_pos x))
  cases t with
  | const c =>
      refine ⟨1 + exp c, 1, le_refl 1, ?_, fun x hx => ?_⟩
      · have s := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos c))
        have e : (1 : Real) + 0 = 1 := by mach_ring
        rw [e] at s; exact s
      · show c ≤ exp (exp x) * (1 + exp c)
        have h1 : c ≤ 1 + exp c := by
          have s := add_le_add_wit (le_of_lt one_pos)
            (le_of_lt (exp_grows_strictly_thm c))
          have e : (0 : Real) + c = c := by mach_ring
          rw [e] at s; exact s
        have hpos : (0 : Real) ≤ 1 + exp c :=
          le_trans (le_of_lt one_pos) (by
            have s := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos c))
            have e : (1 : Real) + 0 = 1 := by mach_ring
            rw [e] at s; exact s)
        have s := mul_le_mul_of_nonneg_right (hee x hx) hpos
        have e : (1 : Real) * (1 + exp c) = 1 + exp c := by mach_mpoly [exp c]
        rw [e] at s
        exact le_trans h1 s
  | var =>
      refine ⟨1, 1, le_refl 1, le_refl 1, fun x hx => ?_⟩
      show x ≤ exp (exp x) * 1
      have e : exp (exp x) * (1 : Real) = exp (exp x) := by mach_mpoly [exp (exp x)]
      rw [e]
      exact le_of_lt (lt_trans_ax (exp_grows_strictly_thm x) (exp_grows_strictly_thm (exp x)))
  | eml C D' =>
      have hC : C.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_left C.depth D'.depth
        omega
      have hD' : D'.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_right C.depth D'.depth
        omega
      obtain ⟨K, hK⟩ := depth_le_one_bound_at_infty C hC
      obtain ⟨M, x₁, hx₁, hM⟩ := depth_le_one_neg_log_bound_at_infty D' hD'
      refine ⟨1 + exp K + exp M, x₁, hx₁, ?_, fun x hx => ?_⟩
      · have s := add_le_add_wit (add_le_add_wit (le_refl (1 : Real))
          (le_of_lt (exp_pos K))) (le_of_lt (exp_pos M))
        have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
        rw [e] at s; exact s
      · have hx1 : (1 : Real) ≤ x := le_trans hx₁ hx
        show exp (C.eval x) - log (D'.eval x) ≤ exp (exp x) * (1 + exp K + exp M)
        -- `exp (C x) ≤ exp (exp x) · exp K`
        have h1 : exp (C.eval x) ≤ exp (exp x) * exp K := by
          have s := exp_monotone (hK x hx1)
          rwa [exp_add] at s
        -- `−log (D' x) ≤ M ≤ exp M ≤ exp (exp x) · exp M`
        have h2 : -log (D'.eval x) ≤ exp (exp x) * exp M := by
          refine le_trans (hM x hx) (le_trans (le_of_lt (exp_grows_strictly_thm M)) ?_)
          have s := mul_le_mul_of_nonneg_right (hee x hx1) (le_of_lt (exp_pos M))
          have e : (1 : Real) * exp M = exp M := by mach_mpoly [exp M]
          rw [e] at s; exact s
        have s := add_le_add_wit h1 h2
        have l : exp (C.eval x) + -log (D'.eval x) = exp (C.eval x) - log (D'.eval x) := by
          mach_mpoly [exp (C.eval x), log (D'.eval x)]
        have r : exp (exp x) * exp K + exp (exp x) * exp M
            = exp (exp x) * (exp K + exp M) := by
          mach_mpoly [exp (exp x), exp K, exp M]
        rw [l, r] at s
        refine le_trans s ?_
        have hnn : (0 : Real) ≤ exp (exp x) := le_of_lt (exp_pos (exp x))
        have hle : exp K + exp M ≤ 1 + exp K + exp M := by
          have u := add_le_add_wit (le_of_lt one_pos) (le_refl (exp K + exp M))
          have e : (0 : Real) + (exp K + exp M) = exp K + exp M := by
            mach_mpoly [exp K, exp M]
          have e2 : (1 : Real) + (exp K + exp M) = 1 + exp K + exp M := by
            mach_mpoly [exp K, exp M]
          rw [e, e2] at u; exact u
        exact mul_le_mul_of_nonneg_left hle hnn

/-- **`exp` outruns every line, at a point we can name.** For `α ≥ 0` there is an explicit `x ≥ 1`
with `α·x + β < exp x`. Built from `exp_ge_three_mul`, so the only numeric input is `2 < e` squared.

This is the endgame of the `∞`-side argument: after both ceilings are applied the surviving
inequality is *exponential ≤ linear*, and this names the point where it fails. -/
theorem exp_beats_linear {α β : Real} (hα : 0 ≤ α) :
    ∃ x : Real, 1 ≤ x ∧ α * x + β < exp x := by
  -- Peel at `k := exp α`, big enough that `exp k ≥ 1 + α` absorbs the SLOPE, and evaluate at
  -- `x := 1 + exp α + exp R` with `R := β + (1+α)(exp α − 1)`, big enough to outrun the INTERCEPT.
  -- Every constraint is met by a sum of positive terms, so no `max` is needed.
  refine ⟨1 + exp α + exp (β + (1 + α) * (exp α - 1)), ?_, ?_⟩
  · have s := add_le_add_wit (add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos α)))
      (le_of_lt (exp_pos (β + (1 + α) * (exp α - 1))))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at s; exact s
  · have hpeel : exp (exp α) * (1 + (1 + exp α + exp (β + (1 + α) * (exp α - 1)) - exp α))
        ≤ exp (1 + exp α + exp (β + (1 + α) * (exp α - 1))) := by
      have h1 := one_add_le_exp (1 + exp α + exp (β + (1 + α) * (exp α - 1)) - exp α)
      have s := mul_le_mul_of_nonneg_left h1 (le_of_lt (exp_pos (exp α)))
      rw [← exp_add] at s
      have e : exp α + (1 + exp α + exp (β + (1 + α) * (exp α - 1)) - exp α)
          = 1 + exp α + exp (β + (1 + α) * (exp α - 1)) := by
        mach_mpoly [exp α, exp (β + (1 + α) * (exp α - 1))]
      rw [e] at s; exact s
    have hea : 1 + α ≤ exp (exp α) := by
      have h1 := one_add_le_exp (exp α)
      have h2 : (1 : Real) + α ≤ 1 + exp α :=
        add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_grows_strictly_thm α))
      exact le_trans h2 h1
    have hnn : (0 : Real)
        ≤ 1 + (1 + exp α + exp (β + (1 + α) * (exp α - 1)) - exp α) := by
      have s := add_le_add_wit (add_le_add_wit (le_of_lt one_pos) (le_of_lt one_pos))
        (le_of_lt (exp_pos (β + (1 + α) * (exp α - 1))))
      have l : (0 : Real) + 0 + 0 = 0 := by mach_ring
      have r : (1 : Real) + 1 + exp (β + (1 + α) * (exp α - 1))
          = 1 + (1 + exp α + exp (β + (1 + α) * (exp α - 1)) - exp α) := by
        mach_mpoly [exp α, exp (β + (1 + α) * (exp α - 1))]
      rw [l, r] at s; exact s
    have hmul : (1 + α) * (1 + (1 + exp α + exp (β + (1 + α) * (exp α - 1)) - exp α))
        ≤ exp (exp α) * (1 + (1 + exp α + exp (β + (1 + α) * (exp α - 1)) - exp α)) :=
      mul_le_mul_of_nonneg_right hea hnn
    have hgap : β + α * exp α - α - (1 + 1)
        < exp (β + (1 + α) * (exp α - 1)) := by
      have hlt : β + α * exp α - α - (1 + 1) < β + (1 + α) * (exp α - 1) := by
        have hpos : (0 : Real) < exp α + 1 := add_pos (exp_pos α) one_pos
        have s := add_lt_add_left hpos (β + α * exp α - α - (1 + 1))
        have l : β + α * exp α - α - (1 + 1) + 0 = β + α * exp α - α - (1 + 1) := by
          mach_mpoly [β, α, exp α]
        have r : β + α * exp α - α - (1 + 1) + (exp α + 1)
            = β + (1 + α) * (exp α - 1) := by mach_mpoly [β, α, exp α]
        rw [l, r] at s; exact s
      exact lt_trans_ax hlt (exp_grows_strictly_thm (β + (1 + α) * (exp α - 1)))
    have s := add_lt_add_left hgap
      ((1 + 1) * α + α * exp (β + (1 + α) * (exp α - 1)) + (1 + 1))
    have l : (1 + 1) * α + α * exp (β + (1 + α) * (exp α - 1)) + (1 + 1)
          + (β + α * exp α - α - (1 + 1))
        = α * (1 + exp α + exp (β + (1 + α) * (exp α - 1))) + β := by
      mach_mpoly [α, β, exp α, exp (β + (1 + α) * (exp α - 1))]
    have r : (1 + 1) * α + α * exp (β + (1 + α) * (exp α - 1)) + (1 + 1)
          + exp (β + (1 + α) * (exp α - 1))
        = (1 + α) * (1 + (1 + exp α + exp (β + (1 + α) * (exp α - 1)) - exp α)) := by
      mach_mpoly [α, exp α, exp (β + (1 + α) * (exp α - 1))]
    rw [l, r] at s
    exact lt_of_lt_of_le s (le_trans hmul hpeel)

/-- `exp_beats_linear` past an arbitrary threshold, by translating the variable: with `x = exp T + u`
the slope's contribution `α·exp T` folds into the intercept, and `exp T ≥ T` puts the point past the
threshold. -/
theorem exp_beats_linear_past {α β : Real} (hα : 0 ≤ α) (T : Real) :
    ∃ x : Real, T ≤ x ∧ 1 ≤ x ∧ α * x + β < exp x := by
  obtain ⟨u, hu1, hu⟩ := exp_beats_linear (α := α) (β := α * exp T + β) hα
  refine ⟨exp T + u, ?_, ?_, ?_⟩
  · have s := add_le_add_wit (le_of_lt (exp_grows_strictly_thm T))
      (le_of_lt (lt_of_lt_of_le one_pos hu1))
    have e : T + (0 : Real) = T := by mach_ring
    rw [e] at s; exact s
  · have s := add_le_add_wit (le_of_lt (exp_pos T)) hu1
    have e : (0 : Real) + 1 = 1 := by mach_ring
    rw [e] at s; exact s
  · -- `α·(exp T + u) + β = α·u + (α·exp T + β) < exp u ≤ exp (exp T + u)`
    have hup : exp u ≤ exp (exp T + u) := by
      rw [exp_add]
      have h1 : (1 : Real) ≤ exp (exp T) := one_le_exp (le_of_lt (exp_pos T))
      have s := mul_le_mul_of_nonneg_right h1 (le_of_lt (exp_pos u))
      have e : (1 : Real) * exp u = exp u := by mach_mpoly [exp u]
      rw [e] at s; exact s
    refine lt_of_lt_of_le ?_ hup
    have e : α * (exp T + u) + β = α * u + (α * exp T + β) := by
      mach_mpoly [α, β, exp T, u]
    rw [e]; exact hu

/-- # ▸ **The `∞`-side rank mismatch closes the unbounded-left-child family.**

`exp(t1 x) = 1/x + log(t2 x) ≤ 1 + log(t2 x)` for `x ≥ 1`. The left side is `exp` of a depth-2 tree;
the right is `log` of one. **Two rungs apart** — so once `A` pushes `t1` up at all (`A x ≥ x + c₀`,
which every `A` growing at `∞` satisfies), the left side is a double exponential and the right is a
single one, and no constants can reconcile them.

Every ingredient is a ceiling that already existed or was built for this: `depth_le_one_bound_at_infty`
and `depth_le_one_log_bound_at_infty` on the children, `depth_le_two_bound_at_infty` on `t2`, and
`exp_beats_linear_past` to name the point. **No configuration enumeration, and no parameter
regimes** — the argument never asks what the constants are. -/
theorem depth3_left_unbounded_absurd {A B t2 : EMLTree} {c₀ x₂ : Real}
    (hB : B.depth ≤ 1) (ht2 : t2.depth ≤ 2) (hx₂ : 1 ≤ x₂)
    (hAlow : ∀ x : Real, x₂ ≤ x → x + c₀ ≤ A.eval x)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml A B) t2).eval x = 1 / x) : False := by
  obtain ⟨CB, hCB⟩ := depth_le_one_log_bound_at_infty B hB
  obtain ⟨D, x₁', hx₁', hD1, hD'⟩ := depth_le_two_bound_at_infty t2 ht2
  -- both thresholds at once, without a `max`: their SUM dominates each, since both are `≥ 1 > 0`
  have hx₁ : (1 : Real) ≤ x₁' + x₂ := by
    have s := add_le_add_wit hx₁' (le_of_lt (lt_of_lt_of_le one_pos hx₂))
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at s; exact s
  have hge1 : x₁' ≤ x₁' + x₂ := by
    have s := add_le_add_wit (le_refl x₁') (le_of_lt (lt_of_lt_of_le one_pos hx₂))
    have e : x₁' + (0 : Real) = x₁' := by mach_mpoly [x₁']
    rw [e] at s; exact s
  have hge2 : x₂ ≤ x₁' + x₂ := by
    have s := add_le_add_wit (le_of_lt (lt_of_lt_of_le one_pos hx₁')) (le_refl x₂)
    have e : (0 : Real) + x₂ = x₂ := by mach_ring
    rw [e] at s; exact s
  have hD : ∀ x : Real, x₁' + x₂ ≤ x → t2.eval x ≤ exp (exp x) * D :=
    fun x hx => hD' x (le_trans hge1 hx)
  have hlogD : (0 : Real) ≤ log D := by
    have t := log_le_log one_pos hD1
    rw [log_one] at t; exact t
  have hE1 : (1 : Real) ≤ 1 + 1 + log D := by
    have s := add_le_add_wit (add_le_add_wit (le_refl (1 : Real)) (le_of_lt one_pos)) hlogD
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at s; exact s
  have hEpos : (0 : Real) < 1 + 1 + log D := lt_of_lt_of_le one_pos hE1
  -- the whole estimate, at every `x` past the threshold
  have hkey : ∀ x : Real, x₁' + x₂ ≤ x →
      exp (x + c₀) ≤ x + x + (CB + log (1 + 1 + log D)) := by
    intro x hx
    have hx1 : (1 : Real) ≤ x := le_trans hx₁ hx
    have hxpos : (0 : Real) < x := lt_of_lt_of_le one_pos hx1
    have hex1 : (1 : Real) ≤ exp x := one_le_exp (le_of_lt hxpos)
    -- `1/x ≤ 1`
    have hinv : 1 / x ≤ 1 := by
      rcases lt_total (1 / x) 1 with hp | hz | hn
      · exact le_of_lt hp
      · exact le_of_eq hz
      · exfalso
        have hipos : (0 : Real) < 1 / x := one_div_pos_of_pos hxpos
        have s : (1 : Real) * (1 / x) ≤ x * (1 / x) :=
          mul_le_mul_of_nonneg_right hx1 (le_of_lt hipos)
        rw [mul_inv x (ne_of_gt hxpos)] at s
        have e : (1 : Real) * (1 / x) = 1 / x := by mach_mpoly [(1 / x : Real)]
        rw [e] at s
        exact lt_irrefl_ax _ (lt_of_lt_of_le hn s)
    -- the equation, rearranged: `exp (t1 x) ≤ 1 + log (t2 x)`
    have heq := h x hxpos
    have hup1 : exp ((EMLTree.eml A B).eval x) ≤ 1 + log (t2.eval x) := by
      show exp (exp (A.eval x) - log (B.eval x)) ≤ 1 + log (t2.eval x)
      have hh : exp (exp (A.eval x) - log (B.eval x)) - log (t2.eval x) = 1 / x := heq
      have s := add_le_add_wit (le_of_eq hh) (le_refl (log (t2.eval x)))
      have l : exp (exp (A.eval x) - log (B.eval x)) - log (t2.eval x) + log (t2.eval x)
          = exp (exp (A.eval x) - log (B.eval x)) := by
        mach_mpoly [exp (exp (A.eval x) - log (B.eval x)), log (t2.eval x)]
      rw [l] at s
      refine le_trans s ?_
      have u := add_le_add_wit hinv (le_refl (log (t2.eval x)))
      exact u
    -- `log (t2 x) ≤ exp x + log D`, one rung up
    have hlt2 : log (t2.eval x) ≤ exp x + log D :=
      log_le_of_le_exp_mul' (le_of_lt (exp_pos x)) hD1 (hD x hx)
    -- `1 + exp x + log D ≤ exp x · E = exp (x + log E)`
    have hEmul : 1 + log (t2.eval x) ≤ exp (x + log (1 + 1 + log D)) := by
      have hstep : 1 + log (t2.eval x) ≤ exp x * (1 + 1 + log D) := by
        have s1 : 1 + log (t2.eval x) ≤ 1 + (exp x + log D) :=
          add_le_add_wit (le_refl (1 : Real)) hlt2
        refine le_trans s1 ?_
        have s2 : log D ≤ exp x * log D := by
          have t := mul_le_mul_of_nonneg_right hex1 hlogD
          have e : (1 : Real) * log D = log D := by mach_mpoly [log D]
          rw [e] at t; exact t
        have s3 := add_le_add_wit (add_le_add_wit hex1 (le_refl (exp x))) s2
        have l : (1 : Real) + exp x + log D = 1 + (exp x + log D) := by
          mach_mpoly [exp x, log D]
        have r : exp x + exp x + exp x * log D = exp x * (1 + 1 + log D) := by
          mach_mpoly [exp x, log D]
        rw [l, r] at s3; exact s3
      have e : exp (x + log (1 + 1 + log D)) = exp x * (1 + 1 + log D) := by
        rw [exp_add, exp_log hEpos]
      rw [e]; exact hstep
    -- reverse `exp`
    have hle : (EMLTree.eml A B).eval x ≤ x + log (1 + 1 + log D) := by
      have hchain : exp ((EMLTree.eml A B).eval x) ≤ exp (x + log (1 + 1 + log D)) :=
        le_trans hup1 hEmul
      rcases lt_total ((EMLTree.eml A B).eval x) (x + log (1 + 1 + log D)) with hp | hz | hn
      · exact le_of_lt hp
      · exact le_of_eq hz
      · exact absurd hchain (fun hc => lt_irrefl_ax _ (lt_of_lt_of_le (exp_lt hn) hc))
    -- and the lower bound on `t1`
    have hlow : exp (x + c₀) - (x + CB) ≤ (EMLTree.eml A B).eval x := by
      show exp (x + c₀) - (x + CB) ≤ exp (A.eval x) - log (B.eval x)
      have s := add_le_add_wit (exp_monotone (hAlow x (le_trans hge2 hx)))
        (neg_le_neg_wit (hCB x hx1))
      have l : exp (x + c₀) + -(x + CB) = exp (x + c₀) - (x + CB) := by
        mach_mpoly [exp (x + c₀), x, CB]
      have r : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by
        mach_mpoly [exp (A.eval x), log (B.eval x)]
      rw [l, r] at s; exact s
    have s := le_trans hlow hle
    have u := add_le_add_wit s (le_refl (x + CB))
    have l : exp (x + c₀) - (x + CB) + (x + CB) = exp (x + c₀) := by
      mach_mpoly [exp (x + c₀), x, CB]
    have r : x + log (1 + 1 + log D) + (x + CB)
        = x + x + (CB + log (1 + 1 + log D)) := by
      mach_mpoly [x, CB, log (1 + 1 + log D)]
    rw [l, r] at u; exact u
  -- name the point where the exponential wins
  obtain ⟨y, hyT, _, hy⟩ := exp_beats_linear_past
    (α := 1 + 1) (β := CB + log (1 + 1 + log D) - (c₀ + c₀))
    (le_of_lt (add_pos one_pos one_pos)) (x₁' + x₂ + c₀)
  have hxge : x₁' + x₂ ≤ y - c₀ := by
    have s := add_le_add_wit hyT (le_refl (-c₀))
    have l : x₁' + x₂ + c₀ + -c₀ = x₁' + x₂ := by mach_mpoly [x₁', x₂, c₀]
    have r : y + -c₀ = y - c₀ := by mach_mpoly [y, c₀]
    rw [l, r] at s; exact s
  have hk := hkey (y - c₀) hxge
  have e : y - c₀ + c₀ = y := by mach_mpoly [y, c₀]
  rw [e] at hk
  have hcontra : (1 + 1) * y + (CB + log (1 + 1 + log D) - (c₀ + c₀))
      = y - c₀ + (y - c₀) + (CB + log (1 + 1 + log D)) := by
    mach_mpoly [y, c₀, CB, log (1 + 1 + log D)]
  rw [hcontra] at hy
  exact lt_irrefl_ax _ (lt_of_lt_of_le hy hk)

/-- `y ≤ Y` and `1 ≤ Y` give `log y ≤ Y − 1` — **for the totalised `log`, with no case split at the
call site.** The clamp is handled inside: `y ≤ 1` (including `y ≤ 0`) gives `log y ≤ 0 ≤ Y − 1`. -/
theorem log_le_of_le_upper {y Y : Real} (hY : 1 ≤ Y) (hy : y ≤ Y) : log y ≤ Y - 1 := by
  have hY1 : (0 : Real) ≤ Y - 1 := sub_nonneg_of_le hY
  rcases lt_total 1 y with h1 | h1 | h1
  · have s := log_le_sub_one_of_one_le (le_of_lt h1)
    have t : y - 1 ≤ Y - 1 := by
      have u := add_le_add_wit hy (le_refl (-1 : Real))
      have l : y + -1 = y - 1 := by mach_ring
      have r : Y + -1 = Y - 1 := by mach_ring
      rw [l, r] at u; exact u
    exact le_trans s t
  · rw [← h1, log_one]; exact hY1
  · exact le_trans (log_nonpos_of_le_one' (le_of_lt h1)) hY1

/-- **A uniform ceiling for the residue's right child, with no `max` and no regime split.**

`log (exp x − L) ≤ exp (exp 1 − L)` on `(0,1]`. The trick is the choice `Y := 1 + exp (exp 1 − L)`,
which is `≥ 1` *by construction* — so the one hypothesis `log_le_of_le_upper` needs is free, and the
`L`-regimes (which decide whether `exp x − L` is positive at all) never have to be entered. -/
theorem exp_sub_const_log_ceiling {L x : Real} (hx1 : x ≤ 1) :
    log (exp x - L) ≤ exp (exp 1 - L) := by
  have hY : (1 : Real) ≤ 1 + exp (exp 1 - L) := by
    have s := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos (exp 1 - L)))
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at s; exact s
  have hy : exp x - L ≤ 1 + exp (exp 1 - L) := by
    have h1 : exp x - L ≤ exp 1 - L := by
      have s := add_le_add_wit (exp_monotone hx1) (le_refl (-L))
      have l : exp x + -L = exp x - L := by mach_mpoly [exp x, L]
      have r : exp 1 + -L = exp 1 - L := by mach_mpoly [exp 1, L]
      rw [l, r] at s; exact s
    have h2 : exp 1 - L < exp (exp 1 - L) := exp_grows_strictly_thm _
    have h3 : exp (exp 1 - L) ≤ 1 + exp (exp 1 - L) := by
      have s := add_le_add_wit (le_of_lt one_pos) (le_refl (exp (exp 1 - L)))
      have e : (0 : Real) + exp (exp 1 - L) = exp (exp 1 - L) := by mach_ring
      rw [e] at s; exact s
    exact le_trans h1 (le_trans (le_of_lt h2) h3)
  have s := log_le_of_le_upper hY hy
  have e : (1 : Real) + exp (exp 1 - L) - 1 = exp (exp 1 - L) := by
    mach_mpoly [exp (exp 1 - L)]
  rw [e] at s; exact s

/-- # **Constant-valued `A` — killed by direction alone, with no floor.**

`t2 x = K − log (exp x − L)` is **non-increasing**: `exp x − L` rises with `x`, so subtracting its
log can only pull `t2` down. But `leaf_var_right_strict_mono` says the right child must *rise*. Two
points settle it, and `K` is never inspected.

The only care is that the *totalised* `log` is not globally monotone (`log 0.5 < 0 = log (−1)`), so
both points must sit on the same side of the clamp boundary `x = log L`:

* `L ≤ 1` — `exp x − L > 0` for every `x > 0`, so the log is genuinely increasing; the fixed points
  `exp(−3) < exp(−2)` work.
* `1 < L` — put both points below `log L` (via `two_bound_witness`); there **both clamp to `0`**, so
  `t2` is outright *constant*, which is still not increasing. -/
theorem leaf_var_expvar_const_left_const_absurd {t2 : EMLTree} {K L : Real}
    (hval : ∀ x : Real, 0 < x → t2.eval x = K - log (exp x - L))
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  -- from `log (B x₁) ≤ log (B x₂)` to `t2 x₂ ≤ t2 x₁`
  have hstep : ∀ x y : Real, 0 < x → 0 < y →
      log (exp x - L) ≤ log (exp y - L) → t2.eval y ≤ t2.eval x := by
    intro x y hx hy hlog
    rw [hval x hx, hval y hy]
    have s := add_le_add_wit (le_refl K) (neg_le_neg_wit hlog)
    have l : K + -log (exp y - L) = K - log (exp y - L) := by
      mach_mpoly [K, log (exp y - L)]
    have r : K + -log (exp x - L) = K - log (exp x - L) := by
      mach_mpoly [K, log (exp x - L)]
    rw [l, r] at s; exact s
  -- `L ≤ 1`: no clamp anywhere on `(0,∞)`, so the log is genuinely increasing
  have hmain : L ≤ 1 → False := by
    intro hLle
    have hm32 : (-1 - 1 - 1 : Real) < -1 - 1 := by
      have s := add_lt_add_left one_pos (-1 - 1 - 1 : Real)
      have l : (-1 - 1 - 1 : Real) + 0 = -1 - 1 - 1 := by mach_ring
      have r : (-1 - 1 - 1 : Real) + 1 = -1 - 1 := by mach_ring
      rw [l, r] at s; exact s
    have hm21 : (-1 - 1 : Real) < -1 := by
      have s := add_lt_add_left one_pos (-1 - 1 : Real)
      have l : (-1 - 1 : Real) + 0 = -1 - 1 := by mach_ring
      have r : (-1 - 1 : Real) + 1 = -1 := by mach_ring
      rw [l, r] at s; exact s
    have hBpos : ∀ z : Real, 0 < z → 0 < exp z - L := by
      intro z hz
      have s : (1 : Real) < exp z := by
        have t := exp_lt hz; rwa [exp_zero] at t
      have u := add_lt_add_left (lt_of_le_of_lt hLle s) (-L)
      have l : -L + L = (0 : Real) := by mach_ring
      have r : -L + exp z = exp z - L := by mach_mpoly [L, exp z]
      rw [l, r] at u; exact u
    refine leaf_var_nonincreasing_absurd (exp_pos (-1 - 1 - 1))
      (exp_lt hm32) (exp_lt hm21) ?_ h
    refine hstep _ _ (exp_pos (-1 - 1 - 1)) (exp_pos (-1 - 1)) ?_
    refine log_le_log (hBpos _ (exp_pos _)) ?_
    have s := exp_monotone (le_of_lt (exp_lt hm32))
    have u := add_le_add_wit s (le_refl (-L))
    have l : exp (exp (-1 - 1 - 1)) + -L = exp (exp (-1 - 1 - 1)) - L := by
      mach_mpoly [exp (exp (-1 - 1 - 1)), L]
    have r : exp (exp (-1 - 1)) + -L = exp (exp (-1 - 1)) - L := by
      mach_mpoly [exp (exp (-1 - 1)), L]
    rw [l, r] at u; exact u
  rcases lt_total 1 L with hL | hL | hL
  · -- `1 < L`: both points below `log L`, where the clamp makes `t2` outright constant
    have hLpos : (0 : Real) < L := lt_trans_ax one_pos hL
    obtain ⟨w, hwpos, hw1, hwL⟩ := two_bound_witness' (exp_pos (-1)) (log_pos_of_one_lt hL)
    have hx1pos : (0 : Real) < w * exp (-1) := mul_pos hwpos (exp_pos (-1))
    have hlt12 : w * exp (-1) < w := by
      have s := mul_lt_mul_pos_left_wit exp_neg_one_lt_one hwpos
      have r : w * (1 : Real) = w := by mach_mpoly [w]
      rw [r] at s; exact s
    have hclamp : ∀ z : Real, z < log L → log (exp z - L) = 0 := by
      intro z hz
      refine log_nonpos ?_
      have s : exp z < L := by
        have t := exp_lt hz
        rwa [exp_log hLpos] at t
      have u := add_le_add_wit (le_of_lt s) (le_refl (-L))
      have l : exp z + -L = exp z - L := by mach_mpoly [exp z, L]
      have r : L + -L = (0 : Real) := by mach_ring
      rw [l, r] at u; exact u
    have hc1 := hclamp _ (lt_trans_ax hlt12 hwL)
    have hc2 := hclamp _ hwL
    refine leaf_var_nonincreasing_absurd hx1pos hlt12 hw1 ?_ h
    refine hstep _ _ hx1pos hwpos (le_of_eq ?_)
    rw [hc1, hc2]
  · exact hmain (le_of_eq hL.symm)
  · exact hmain (le_of_lt hL)

/-- # **Unbounded `A` — one dispatch, both shapes.**

`exp p − log x` and `exp x − log x` both dominate `c − log x`; the tangent bound lifts that through
`exp`, and `exp_sub_const_log_ceiling` caps the `log` term by a constant. So the parent dominates
`(1 + c − N) − log x` with `N := exp (exp 1 − L)`, and no `L`-regime is ever entered. -/
theorem leaf_var_expvar_const_unbdd_absurd {t2 : EMLTree} {Av : Real → Real} {c L : Real}
    (hval : ∀ x : Real, 0 < x → t2.eval x = exp (Av x) - log (exp x - L))
    (hdom : ∀ x : Real, 0 < x → x ≤ 1 → c - log x ≤ Av x)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  refine leaf_var_dominates_neglog_absurd (c₀ := 1 + c - exp (exp 1 - L))
    (fun x hx hx1 => ?_) h
  rw [hval x hx]
  have h1 : 1 + (c - log x) ≤ exp (Av x) :=
    le_trans (add_le_add_wit (le_refl (1 : Real)) (hdom x hx hx1)) (one_add_le_exp (Av x))
  have s := add_le_add_wit h1 (neg_le_neg_wit (exp_sub_const_log_ceiling (L := L) hx1))
  have l : 1 + (c - log x) + -exp (exp 1 - L) = 1 + c - exp (exp 1 - L) - log x := by
    mach_mpoly [c, log x, exp (exp 1 - L)]
  have r : exp (Av x) + -log (exp x - L) = exp (Av x) - log (exp x - L) := by
    mach_mpoly [exp (Av x), log (exp x - L)]
  rw [l, r] at s; exact s

/-! ### The bounded, non-constant shapes

`A = var` and `A = eml var (const q')` are the two that neither settle to a constant nor blow up.
Both are captured by a pair of bounds on `exp (A x)` around the same constant `G := exp (A 0⁺)`:

```
G · exp x  ≤  exp (A x)  ≤  G · exp (exp x − 1)
```

For `A = eml var (const q')` both hold with **equality** (`exp(exp x − log q') = G·exp(exp x − 1)`);
for `A = var` they are `exp x ≤ exp x` and `x ≤ exp x − 1`. Writing `u := exp x − 1`, the left bound
is `G·(1+u)` and the right is `G·exp u`. -/

/-- `L > 1`: below `log L` the log term is clamped to `0`, so the tree is just `exp (A x) ≥ G`. -/
theorem leaf_var_expvar_const_clamped_absurd {t2 : EMLTree} {Av : Real → Real} {G L : Real}
    (hG : 0 < G) (hL : 1 < L)
    (hval : ∀ x : Real, 0 < x → t2.eval x = exp (Av x) - log (exp x - L))
    (hlow : ∀ x : Real, 0 < x → G * exp x ≤ exp (Av x))
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  have hLpos : (0 : Real) < L := lt_trans_ax one_pos hL
  obtain ⟨w, hwpos, hw1, hwL⟩ := two_bound_witness' one_pos (log_pos_of_one_lt hL)
  refine leaf_var_const_floor_absurd hG hwpos (le_of_lt hw1) (fun x hx hxw => ?_) h
  rw [hval x hx]
  -- the clamp: `x ≤ w < log L` forces `exp x − L ≤ 0`
  have hclamp : log (exp x - L) = 0 := by
    refine log_nonpos ?_
    have s : exp x < L := by
      have t := exp_lt (lt_of_le_of_lt hxw hwL)
      rwa [exp_log hLpos] at t
    have u := add_le_add_wit (le_of_lt s) (le_refl (-L))
    have l : exp x + -L = exp x - L := by mach_mpoly [exp x, L]
    have r : L + -L = (0 : Real) := by mach_ring
    rw [l, r] at u; exact u
  rw [hclamp]
  have hge : G ≤ exp (Av x) := by
    refine le_trans ?_ (hlow x hx)
    have s := mul_le_mul_of_nonneg_left (one_le_exp (le_of_lt hx)) (le_of_lt hG)
    have e : G * (1 : Real) = G := by mach_mpoly [G]
    rw [e] at s; exact s
  have e : exp (Av x) - (0 : Real) = exp (Av x) := by mach_ring
  rw [e]; exact hge

/-- `exp x − 1 ≤ x · exp x`, from `1 − x ≤ exp (−x)`. The bound that turns the `L = 1` case's
`log (exp x − 1)` into `log x + 1`. -/
theorem exp_sub_one_le_mul_exp {x : Real} : exp x - 1 ≤ x * exp x := by
  have h1 : 1 + -x ≤ exp (-x) := one_add_le_exp (-x)
  have s := mul_le_mul_of_nonneg_left h1 (le_of_lt (exp_pos x))
  have l : exp x * (1 + -x) = exp x - x * exp x := by mach_mpoly [exp x, x]
  have r : exp x * exp (-x) = 1 := by
    rw [← exp_add]
    have e : x + -x = (0 : Real) := by mach_ring
    rw [e, exp_zero]
  rw [l, r] at s
  have u := add_le_add_wit s (le_refl (x * exp x - 1))
  have l2 : exp x - x * exp x + (x * exp x - 1) = exp x - 1 := by mach_mpoly [exp x, x]
  have r2 : (1 : Real) + (x * exp x - 1) = x * exp x := by mach_mpoly [x, exp x]
  rw [l2, r2] at u; exact u

/-- `L = 1`: the log argument is `exp x − 1`, which vanishes at `0`, so the tree runs to `+∞` —
`log (exp x − 1) ≤ log x + 1` on `(0,1]` turns it into domination of `(G − 1) − log x`. -/
theorem leaf_var_expvar_const_one_absurd {t2 : EMLTree} {Av : Real → Real} {G : Real}
    (hG : 0 < G)
    (hval : ∀ x : Real, 0 < x → t2.eval x = exp (Av x) - log (exp x - 1))
    (hlow : ∀ x : Real, 0 < x → G * exp x ≤ exp (Av x))
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  refine leaf_var_dominates_neglog_absurd (c₀ := G - 1) (fun x hx hx1 => ?_) h
  rw [hval x hx]
  -- `0 < exp x − 1 ≤ x · exp 1`
  have hupos : (0 : Real) < exp x - 1 := by
    have s : (1 : Real) < exp x := by
      have t := exp_lt hx; rwa [exp_zero] at t
    have u := add_lt_add_left s (-1 : Real)
    have l : (-1 : Real) + 1 = 0 := by mach_ring
    have r : (-1 : Real) + exp x = exp x - 1 := by mach_mpoly [exp x]
    rw [l, r] at u; exact u
  have hule : exp x - 1 ≤ x * exp 1 :=
    le_trans exp_sub_one_le_mul_exp
      (mul_le_mul_of_nonneg_left (exp_monotone hx1) (le_of_lt hx))
  -- `log (exp x − 1) ≤ log x + 1`
  have hlog : log (exp x - 1) ≤ log x + 1 := by
    have s := log_le_log hupos hule
    rwa [log_mul hx (exp_pos 1), log_exp] at s
  have hge : G ≤ exp (Av x) := by
    refine le_trans ?_ (hlow x hx)
    have s := mul_le_mul_of_nonneg_left (one_le_exp (le_of_lt hx)) (le_of_lt hG)
    have e : G * (1 : Real) = G := by mach_mpoly [G]
    rw [e] at s; exact s
  have s := add_le_add_wit hge (neg_le_neg_wit hlog)
  have l : G + -(log x + 1) = G - 1 - log x := by mach_mpoly [G, log x]
  have r : exp (Av x) + -log (exp x - 1) = exp (Av x) - log (exp x - 1) := by
    mach_mpoly [exp (Av x), log (exp x - 1)]
  rw [l, r] at s; exact s

/-- **The shifted tangent.** `log (exp g + u) ≤ g + u·exp(−g)` for `u ≥ 0` — the linear ceiling on
the log *at the point where the two terms cancel*, written division-free (`exp(−g)` for `1/M`).

Proof: put `v := log (exp g + u) − g`. Then `exp g · exp v = exp g + u`, so
`u = exp g · (exp v − 1) ≥ exp g · v` by the tangent bound, and multiplying by `exp(−g)` gives
`v ≤ u·exp(−g)`. Same peeling idea as `exp_e_mul_le`, applied to `log` instead of `exp`. -/
theorem log_shift_ceiling {g u : Real} (hu : 0 ≤ u) : log (exp g + u) ≤ g + u * exp (-g) := by
  have hpos : (0 : Real) < exp g + u := by
    have s := add_le_add_wit (le_refl (exp g)) hu
    have e : exp g + (0 : Real) = exp g := by mach_ring
    rw [e] at s
    exact lt_of_lt_of_le (exp_pos g) s
  have hemg : exp (-g) * exp g = 1 := exp_neg_self_mul g
  -- `exp g · exp v = exp g + u`
  have hsplit : exp g * exp (log (exp g + u) - g) = exp g + u := by
    rw [← exp_add]
    have e : g + (log (exp g + u) - g) = log (exp g + u) := by
      mach_mpoly [g, log (exp g + u)]
    rw [e, exp_log hpos]
  -- `exp g · v ≤ u`
  have hgv : exp g * (log (exp g + u) - g) ≤ u := by
    have ht := one_add_le_exp (log (exp g + u) - g)
    have s := mul_le_mul_of_nonneg_left ht (le_of_lt (exp_pos g))
    rw [hsplit] at s
    have l : exp g * (1 + (log (exp g + u) - g)) = exp g + exp g * (log (exp g + u) - g) := by
      mach_mpoly [exp g, log (exp g + u), g]
    rw [l] at s
    have u2 := add_le_add_wit s (le_refl (-exp g))
    have l2 : exp g + exp g * (log (exp g + u) - g) + -exp g
        = exp g * (log (exp g + u) - g) := by
      mach_mpoly [exp g, log (exp g + u), g]
    have r2 : exp g + u + -exp g = u := by mach_mpoly [exp g, u]
    rw [l2, r2] at u2; exact u2
  -- multiply by `exp(−g) > 0`
  have hv : log (exp g + u) - g ≤ u * exp (-g) := by
    have s := mul_le_mul_of_nonneg_left hgv (le_of_lt (exp_pos (-g)))
    have l : exp (-g) * (exp g * (log (exp g + u) - g))
        = (exp (-g) * exp g) * (log (exp g + u) - g) := by
      mach_mpoly [exp (-g), exp g, log (exp g + u), g]
    rw [l, hemg] at s
    have l2 : (1 : Real) * (log (exp g + u) - g) = log (exp g + u) - g := by
      mach_mpoly [log (exp g + u), g]
    have r2 : exp (-g) * u = u * exp (-g) := mul_comm _ _
    rw [l2, r2] at s; exact s
  have s := add_le_add_wit hv (le_refl g)
  have l : log (exp g + u) - g + g = log (exp g + u) := by
    mach_mpoly [log (exp g + u), g]
  have r : u * exp (-g) + g = g + u * exp (-g) := by mach_mpoly [u, exp (-g), g]
  rw [l, r] at s; exact s

/-- `L < 1`, `γ := G − log M > 0` (`M := 1 − L`): the tree has a positive constant floor. -/
theorem leaf_var_expvar_const_gamma_pos_absurd {t2 : EMLTree} {Av : Real → Real} {G L M : Real}
    (hG : 0 < G) (hM : 0 < M) (hLM : L = 1 - M) (hgam : log M < G)
    (hval : ∀ x : Real, 0 < x → t2.eval x = exp (Av x) - log (exp x - L))
    (hlow : ∀ x : Real, 0 < x → G * exp x ≤ exp (Av x))
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  have hBpos : ∀ z : Real, 0 < z → 0 < exp z - L := by
    intro z hz
    have s : (1 : Real) < exp z := by
      have t := exp_lt hz; rwa [exp_zero] at t
    have hu : (0 : Real) < exp z - 1 := by
      have u := add_lt_add_left s (-1 : Real)
      have l : (-1 : Real) + 1 = 0 := by mach_ring
      have r : (-1 : Real) + exp z = exp z - 1 := by mach_mpoly [exp z]
      rw [l, r] at u; exact u
    have hsum : (0 : Real) < (exp z - 1) + M := add_pos hu hM
    have e : (exp z - 1) + M = exp z - L := by rw [hLM]; mach_mpoly [exp z, M]
    rw [e] at hsum; exact hsum
  have hGle : ∀ z : Real, 0 < z → G ≤ exp (Av z) := by
    intro z hz
    refine le_trans ?_ (hlow z hz)
    have s := mul_le_mul_of_nonneg_left (one_le_exp (le_of_lt hz)) (le_of_lt hG)
    have e : G * (1 : Real) = G := by mach_mpoly [G]
    rw [e] at s; exact s
  have hMlt : M < exp G := by
    have s := exp_lt hgam
    rwa [exp_log hM] at s
  have hZ : (1 : Real) < exp G + L := by
    rw [hLM]
    have u := add_lt_add_left hMlt (1 - M)
    have l : (1 - M) + M = (1 : Real) := by mach_mpoly [M]
    have r : (1 - M) + exp G = exp G + (1 - M) := by mach_mpoly [M, exp G]
    rw [l, r] at u; exact u
  have hZpos : (0 : Real) < exp G + L := lt_trans_ax one_pos hZ
  obtain ⟨w, hwpos, hw1, hwZ⟩ := two_bound_witness' one_pos (log_pos_of_one_lt hZ)
  have hBwlt : exp w - L < exp G := by
    have s := exp_lt hwZ
    rw [exp_log hZpos] at s
    have u := add_lt_add_left s (-L)
    have l : -L + exp w = exp w - L := by mach_mpoly [exp w, L]
    have r : -L + (exp G + L) = exp G := by mach_mpoly [exp G, L]
    rw [l, r] at u; exact u
  have hlogw : log (exp w - L) < G := by
    have s := log_lt_log_strict (hBpos w hwpos) hBwlt
    rwa [log_exp] at s
  have hc : (0 : Real) < G - log (exp w - L) := by
    have u := add_lt_add_left hlogw (-log (exp w - L))
    have l : -log (exp w - L) + log (exp w - L) = (0 : Real) := by mach_ring
    have r : -log (exp w - L) + G = G - log (exp w - L) := by
      mach_mpoly [G, log (exp w - L)]
    rw [l, r] at u; exact u
  refine leaf_var_const_floor_absurd hc hwpos (le_of_lt hw1) (fun x hx hxw => ?_) h
  rw [hval x hx]
  have h2 : log (exp x - L) ≤ log (exp w - L) := by
    refine log_le_log (hBpos x hx) ?_
    have s := add_le_add_wit (exp_monotone hxw) (le_refl (-L))
    have l : exp x + -L = exp x - L := by mach_mpoly [exp x, L]
    have r : exp w + -L = exp w - L := by mach_mpoly [exp w, L]
    rw [l, r] at s; exact s
  have s := add_le_add_wit (hGle x hx) (neg_le_neg_wit h2)
  have l : G + -log (exp w - L) = G - log (exp w - L) := by
    mach_mpoly [G, log (exp w - L)]
  have r : exp (Av x) + -log (exp x - L) = exp (Av x) - log (exp x - L) := by
    mach_mpoly [exp (Av x), log (exp x - L)]
  rw [l, r] at s; exact s

/-- `L < 1`, `γ := G − log M < 0`: the tree is *negative* at a point below the cutoff, which
`leaf_var_right_pos` forbids. The point is found by taking logs — `u < log(log M) − log G` gives
`G·exp u < log M` — so no division is needed to locate it. -/
theorem leaf_var_expvar_const_gamma_neg_absurd {t2 : EMLTree} {Av : Real → Real} {G L M : Real}
    (hG : 0 < G) (hM : 0 < M) (hLM : L = 1 - M) (hgam : G < log M)
    (hval : ∀ x : Real, 0 < x → t2.eval x = exp (Av x) - log (exp x - L))
    (hupp : ∀ x : Real, 0 < x → exp (Av x) ≤ G * exp (exp x - 1))
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  have hlogMpos : (0 : Real) < log M := lt_trans_ax hG hgam
  have hS : log G < log (log M) := log_lt_log_strict hG hgam
  have hSpos : (0 : Real) < log (log M) - log G := by
    have u := add_lt_add_left hS (-log G)
    have l : -log G + log G = (0 : Real) := by mach_ring
    have r : -log G + log (log M) = log (log M) - log G := by
      mach_mpoly [log G, log (log M)]
    rw [l, r] at u; exact u
  have h1S : (1 : Real) < 1 + (log (log M) - log G) := by
    have u := add_lt_add_left hSpos (1 : Real)
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact u
  have h1Spos : (0 : Real) < 1 + (log (log M) - log G) := lt_trans_ax one_pos h1S
  obtain ⟨w, hwpos, hw1, hwS⟩ :=
    two_bound_witness' (exp_pos (-1)) (log_pos_of_one_lt h1S)
  have huS : exp w - 1 < log (log M) - log G := by
    have s := exp_lt hwS
    rw [exp_log h1Spos] at s
    have u := add_lt_add_left s (-1 : Real)
    have l : (-1 : Real) + exp w = exp w - 1 := by mach_mpoly [exp w]
    have r : (-1 : Real) + (1 + (log (log M) - log G)) = log (log M) - log G := by
      mach_mpoly [log (log M), log G]
    rw [l, r] at u; exact u
  have hkey : G * exp (exp w - 1) < log M := by
    have s : log G + (exp w - 1) < log (log M) := by
      have u := add_lt_add_left huS (log G)
      have l : log G + (log (log M) - log G) = log (log M) := by
        mach_mpoly [log G, log (log M)]
      rw [l] at u; exact u
    have t := exp_lt s
    rw [exp_add, exp_log hG, exp_log hlogMpos] at t
    exact t
  refine leaf_var_neg_point_absurd hwpos hw1 ?_ h
  rw [hval w hwpos]
  have hlogge : log M ≤ log (exp w - L) := by
    refine log_le_log hM ?_
    have s : (1 : Real) ≤ exp w := one_le_exp (le_of_lt hwpos)
    have u := add_le_add_wit s (le_refl (M - 1))
    have l : (1 : Real) + (M - 1) = M := by mach_mpoly [M]
    have r : exp w + (M - 1) = exp w - L := by rw [hLM]; mach_mpoly [exp w, M]
    rw [l, r] at u; exact u
  have hlt : exp (Av w) < log (exp w - L) :=
    lt_of_le_of_lt (hupp w hwpos) (lt_of_lt_of_le hkey hlogge)
  have u := add_lt_add_left hlt (-log (exp w - L))
  have l : -log (exp w - L) + exp (Av w) = exp (Av w) - log (exp w - L) := by
    mach_mpoly [exp (Av w), log (exp w - L)]
  have r : -log (exp w - L) + log (exp w - L) = (0 : Real) := by mach_ring
  rw [l, r] at u; exact le_of_lt u

/-! ### The coincidence `γ = 0`, i.e. `M = exp G`

`RESULT_LEAF_VAR_ASSEMBLY.md` found that for *constant-valued* `B` the coincidence needs nothing
extra: the tangent bound hands over a positive linear term whether or not `γ` is zero, so the
three-way split collapses to two. **That does not survive a moving `log`.** Here the linear
coefficient is `κ := G − exp(−G)`, and its sign is independent of `γ`:

| `κ` | tree near `0` | instrument |
|---|---|---|
| `> 0` | `≍ κ·x` | affine floor — the previous session's route |
| `< 0` | `≍ κ·x < 0` | a negative point |
| `= 0` | `≍ (G/4)·x²` | **a quadratic floor, which needs a new arithmetic core** |

`κ = 0` is `G·exp G = 1`, i.e. `G = Ω`, the omega constant — one transcendental parameter value,
and reachable, so it cannot be waved away. -/

/-- `γ = 0`, `κ > 0`: an affine floor, exactly as in the constant-`B` closure. -/
theorem leaf_var_expvar_const_gamma_zero_pos_absurd {t2 : EMLTree} {Av : Real → Real} {G L : Real}
    (hLM : L = 1 - exp G) (hkap : exp (-G) < G)
    (hval : ∀ x : Real, 0 < x → t2.eval x = exp (Av x) - log (exp x - L))
    (hlow : ∀ x : Real, 0 < x → G * exp x ≤ exp (Av x))
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  have hK : (0 : Real) < G - exp (-G) := by
    have u := add_lt_add_left hkap (-exp (-G))
    have l : -exp (-G) + exp (-G) = (0 : Real) := by mach_ring
    have r : -exp (-G) + G = G - exp (-G) := by mach_mpoly [G, exp (-G)]
    rw [l, r] at u; exact u
  refine leaf_var_affine_floor_absurd hK (le_refl (0 : Real)) (fun x hx _ => ?_) h
  rw [hval x hx]
  have hBeq : exp x - L = exp G + (exp x - 1) := by
    rw [hLM]; mach_mpoly [exp x, exp G]
  rw [hBeq]
  have hu0 : (0 : Real) ≤ exp x - 1 := by
    have s : (1 : Real) ≤ exp x := one_le_exp (le_of_lt hx)
    have u := add_le_add_wit s (le_refl (-1 : Real))
    have l : (1 : Real) + -1 = 0 := by mach_ring
    have r : exp x + -1 = exp x - 1 := by mach_mpoly [exp x]
    rw [l, r] at u; exact u
  have hceil := log_shift_ceiling (g := G) hu0
  have s := add_le_add_wit (hlow x hx) (neg_le_neg_wit hceil)
  -- `G·exp x − G − (exp x − 1)·exp(−G) = (exp x − 1)·(G − exp(−G))`
  have l : G * exp x + -(G + (exp x - 1) * exp (-G))
      = (exp x - 1) * (G - exp (-G)) := by
    mach_mpoly [G, exp x, exp (-G)]
  have r : exp (Av x) + -log (exp G + (exp x - 1))
      = exp (Av x) - log (exp G + (exp x - 1)) := by
    mach_mpoly [exp (Av x), log (exp G + (exp x - 1))]
  rw [l, r] at s
  refine le_trans ?_ s
  have hxu : x ≤ exp x - 1 := by
    have t := one_add_le_exp x
    have u := add_le_add_wit t (le_refl (-1 : Real))
    have l2 : (1 : Real) + x + -1 = x := by mach_mpoly [x]
    have r2 : exp x + -1 = exp x - 1 := by mach_mpoly [exp x]
    rw [l2, r2] at u; exact u
  have s2 := mul_le_mul_of_nonneg_right hxu (le_of_lt hK)
  have e : (0 : Real) + (G - exp (-G)) * x = x * (G - exp (-G)) := by
    mach_mpoly [G, exp (-G), x]
  rw [e]; exact s2

/-- **`3t ≤ exp t` for `t ≥ 4`** — the arithmetic a *quadratic* floor needs, and which
`exp_ge_two_mul` cannot supply (it gives exactly `2t`, which ties).

Peeling at `k = 2` instead of `k = 1`: `exp t = exp 2 · exp (t−2) ≥ exp 2 · (t−1) > 4(t−1) ≥ 3t`
once `t ≥ 4`. The only numeric input is `2 < e` squared — no sharper bound on `e` is needed, which
is why `t ≥ 4` rather than `t ≥ 2` is the threshold. -/
theorem exp_ge_three_mul {t : Real} (ht : (1 + 1 + 1 + 1 : Real) ≤ t) : t + t + t ≤ exp t := by
  have h14 : (1 : Real) ≤ 1 + 1 + 1 + 1 := by
    have s := add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl (1 : Real))
      (le_of_lt one_pos)) (le_of_lt one_pos)) (le_of_lt one_pos)
    have e : (1 : Real) + 0 + 0 + 0 = 1 := by mach_ring
    rw [e] at s; exact s
  have ht1 : (0 : Real) ≤ t - 1 := sub_nonneg_of_le (le_trans h14 ht)
  have hfour : ((1 : Real) + 1) * (1 + 1) < exp (1 + 1) := by
    have s1 : ((1 : Real) + 1) * (1 + 1) < exp 1 * (1 + 1) :=
      mul_lt_mul_of_pos_right two_lt_exp_one (add_pos one_pos one_pos)
    have s2 : exp 1 * ((1 : Real) + 1) < exp 1 * exp 1 :=
      mul_lt_mul_pos_left_wit two_lt_exp_one (exp_pos 1)
    have e : exp ((1 : Real) + 1) = exp 1 * exp 1 := exp_add 1 1
    rw [e]; exact lt_trans_ax s1 s2
  have hstep : exp ((1 : Real) + 1) * (t - 1) ≤ exp t := by
    have hlow : t - 1 ≤ exp (t - (1 + 1)) := by
      have s := one_add_le_exp (t - (1 + 1))
      have l : (1 : Real) + (t - (1 + 1)) = t - 1 := by mach_mpoly [t]
      rw [l] at s; exact s
    have s := mul_le_mul_of_nonneg_left hlow (le_of_lt (exp_pos (1 + 1)))
    rw [← exp_add] at s
    have e : ((1 : Real) + 1) + (t - (1 + 1)) = t := by mach_mpoly [t]
    rw [e] at s; exact s
  have hbig : ((1 : Real) + 1) * (1 + 1) * (t - 1) ≤ exp (1 + 1) * (t - 1) :=
    mul_le_mul_of_nonneg_right (le_of_lt hfour) ht1
  have hfin : t + t + t ≤ ((1 : Real) + 1) * (1 + 1) * (t - 1) := by
    have hd : (0 : Real) ≤ t - (1 + 1 + 1 + 1) := sub_nonneg_of_le ht
    have s := add_le_add_wit hd (le_refl (t + t + t))
    have l : (0 : Real) + (t + t + t) = t + t + t := by mach_mpoly [t]
    have r : (t - (1 + 1 + 1 + 1)) + (t + t + t) = ((1 : Real) + 1) * (1 + 1) * (t - 1) := by
      mach_mpoly [t]
    rw [l, r] at s; exact s
  exact le_trans hfin (le_trans hbig hstep)

/-- The arithmetic core for a **quadratic** floor. Identical in shape to `leaf_var_arith`, except
that `C·x²` contributes `t + t` where `K·x` contributed `t` — so the final absorption needs
`exp_ge_three_mul`, and `t` must be pushed past `4`. -/
theorem leaf_var_quad_arith {t v w Cl : Real} (ht4 : (1 + 1 + 1 + 1 : Real) ≤ t)
    (hpin : exp (-t) * v = exp (-t) * w - 1)
    (hLv : Cl - (t + t) ≤ v) (hw : w ≤ exp 1) (hbig : exp 1 - Cl < t) : False := by
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
  have hstep : exp t ≤ exp 1 - Cl + (t + t) := by
    have s1 : Cl - (t + t) ≤ exp 1 - exp t := by
      have s := add_le_add_wit hw (le_refl (-exp t))
      have e1 : w + -exp t = w - exp t := by mach_ring
      have e2 : exp 1 + -exp t = exp 1 - exp t := by mach_ring
      rw [e1, e2] at s
      exact le_trans hLv s
    have s := add_le_add_left s1 (exp t - Cl + (t + t))
    have e1 : exp t - Cl + (t + t) + (Cl - (t + t)) = exp t := by
      mach_mpoly [exp t, Cl, t]
    have e2 : exp t - Cl + (t + t) + (exp 1 - exp t) = exp 1 - Cl + (t + t) := by
      mach_mpoly [exp t, exp 1, Cl, t]
    rw [e1, e2] at s
    exact s
  have h3t : t + t + t ≤ exp t := exp_ge_three_mul ht4
  have hfin : t ≤ exp 1 - Cl := by
    have s := le_trans h3t hstep
    have u := add_le_add_left s (-(t + t))
    have e1 : -(t + t) + (t + t + t) = t := by mach_mpoly [t]
    have e2 : -(t + t) + (exp 1 - Cl + (t + t)) = exp 1 - Cl := by
      mach_mpoly [exp 1, Cl, t]
    rw [e1, e2] at u
    exact u
  exact lt_irrefl_ax _ (lt_of_lt_of_le hbig hfin)

/-- **A quadratic floor on the right child is fatal too.** `leaf_var_floor_absurd` with `C·x²` in
place of `K·x`, instantiated at `t := 4 + exp (exp 1 − log C) + exp (−log d)`. -/
theorem leaf_var_quad_floor_absurd {t2 : EMLTree} {C d : Real} (hC : 0 < C)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hfloor : ∀ x : Real, 0 < x → x ≤ d → C * (x * x) ≤ t2.eval x)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  have ht4 : (1 + 1 + 1 + 1 : Real)
      ≤ 1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d) := by
    have s := add_le_add_wit (add_le_add_wit (le_refl (1 + 1 + 1 + 1 : Real))
      (le_of_lt (exp_pos (exp 1 - log C)))) (le_of_lt (exp_pos (-log d)))
    have e : (1 + 1 + 1 + 1 : Real) + 0 + 0 = 1 + 1 + 1 + 1 := by mach_ring
    rw [e] at s; exact s
  have hx0 : (0 : Real)
      < exp (-(1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d))) := exp_pos _
  have hxd : exp (-(1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d))) ≤ d := by
    have hge : -log d ≤ 1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d) := by
      have h1 := le_of_lt (exp_grows_strictly_thm (-log d))
      have s := add_le_add_wit (add_le_add_wit
        (le_of_lt (add_pos (add_pos (add_pos one_pos one_pos) one_pos) one_pos))
        (le_of_lt (exp_pos (exp 1 - log C)))) (le_refl (exp (-log d)))
      have e : (0 : Real) + 0 + exp (-log d) = exp (-log d) := by mach_ring
      rw [e] at s
      exact le_trans h1 s
    have hstep : -(1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d)) ≤ log d := by
      have s := neg_le_neg_wit hge
      have e : -(-log d) = log d := by mach_ring
      rw [e] at s
      exact s
    have hh := exp_monotone hstep
    rw [exp_log hd] at hh
    exact hh
  have hx1 : exp (-(1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d))) ≤ 1 :=
    le_trans hxd hd1
  refine leaf_var_quad_arith
    (t := 1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d))
    (v := log (t2.eval (exp (-(1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d))))))
    (w := exp (exp (-(1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d)))))
    (Cl := log C) ht4 ?_ ?_ ?_ ?_
  · exact leaf_var_pin h _ hx0
  · -- the quadratic floor, pushed through `log`: `log (C·x·x) = log C − (t + t)`
    have hsq : (0 : Real)
        < exp (-(1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d)))
          * exp (-(1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d))) := mul_pos hx0 hx0
    have hCx : (0 : Real) < C * (exp (-(1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d)))
        * exp (-(1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d)))) := mul_pos hC hsq
    have hl := log_le_log hCx (hfloor _ hx0 hxd)
    rw [log_mul hC hsq, log_mul hx0 hx0, log_exp] at hl
    have e : log C + (-(1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d))
        + -(1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d)))
        = log C - ((1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d))
          + (1 + 1 + 1 + 1 + exp (exp 1 - log C) + exp (-log d))) := by
      mach_mpoly [log C, exp (exp 1 - log C), exp (-log d)]
    rw [e] at hl
    exact hl
  · exact exp_monotone hx1
  · have h1 := exp_grows_strictly_thm (exp 1 - log C)
    have s := add_le_add_wit (add_le_add_wit
      (le_of_lt (add_pos (add_pos (add_pos one_pos one_pos) one_pos) one_pos))
      (le_refl (exp (exp 1 - log C)))) (le_of_lt (exp_pos (-log d)))
    have e : (0 : Real) + exp (exp 1 - log C) + 0 = exp (exp 1 - log C) := by mach_ring
    rw [e] at s
    exact lt_of_lt_of_le h1 s

/-- `1/2 + 1/2 = 1`, from `mul_inv`. This corpus has no numeral `2`, so the halving that a
second-order tangent bound needs has to be built. -/
theorem half_add_half : (1 / (1 + 1) : Real) + 1 / (1 + 1) = 1 := by
  have h2 : (0 : Real) < 1 + 1 := add_pos one_pos one_pos
  have s := mul_inv (1 + 1 : Real) (ne_of_gt h2)
  have e : ((1 : Real) + 1) * (1 / (1 + 1)) = 1 / (1 + 1) + 1 / (1 + 1) := by
    mach_mpoly [(1 / (1 + 1) : Real)]
  rw [e] at s; exact s

/-- **The second-order tangent, by squaring the first.** `exp (s+s) = (exp s)² ≥ (1+s)²`. Stated in
`s` rather than in `u = s+s` precisely so that no division appears in the statement. -/
theorem exp_quad_lower {s : Real} (hs : 0 ≤ s) : 1 + (s + s) + s * s ≤ exp (s + s) := by
  have h1s : (0 : Real) ≤ 1 + s := by
    have t := add_le_add_wit (le_of_lt one_pos) hs
    have e : (0 : Real) + 0 = 0 := by mach_ring
    rw [e] at t; exact t
  have ht := one_add_le_exp s
  have s1 : (1 + s) * (1 + s) ≤ exp s * (1 + s) := mul_le_mul_of_nonneg_right ht h1s
  have s2 : exp s * (1 + s) ≤ exp s * exp s :=
    mul_le_mul_of_nonneg_left ht (le_of_lt (exp_pos s))
  have e : exp (s + s) = exp s * exp s := exp_add s s
  rw [e]
  have l : 1 + (s + s) + s * s = (1 + s) * (1 + s) := by mach_mpoly [s]
  rw [l]
  exact le_trans s1 s2

/-- `exp u − 1 − u ≥ (u/2)²` — the quadratic gap the coincidence lives in.

⚠ **`u ≥ 0` is load-bearing, not decoration.** The inequality is FALSE for `u ≲ −2.5`: at `u = −4`
the left side is `3.018` and the right is `4`. Every summary of the Ω argument must carry the
hypothesis with it. (At the call site `u = exp x − 1 ≥ 0` for `x > 0`, so the domain is genuinely
met — but the bound is not a two-sided Taylor fact and must not be quoted as one.) -/
theorem exp_sub_one_sub_self_ge_quad {u : Real} (hu : 0 ≤ u) :
    u * (1 / (1 + 1)) * (u * (1 / (1 + 1))) ≤ exp u - 1 - u := by
  have h2 : (0 : Real) < 1 + 1 := add_pos one_pos one_pos
  have hhpos : (0 : Real) < 1 / (1 + 1) := one_div_pos_of_pos h2
  have hs0 : (0 : Real) ≤ u * (1 / (1 + 1)) := mul_nonneg hu (le_of_lt hhpos)
  have hss : u * (1 / (1 + 1)) + u * (1 / (1 + 1)) = u := by
    have e : u * (1 / (1 + 1)) + u * (1 / (1 + 1)) = u * (1 / (1 + 1) + 1 / (1 + 1)) := by
      mach_mpoly [u, (1 / (1 + 1) : Real)]
    rw [e, half_add_half]; mach_mpoly [u]
  have hq := exp_quad_lower hs0
  rw [hss] at hq
  have s := add_le_add_wit hq (le_refl (-1 - u))
  have l : 1 + u + u * (1 / (1 + 1)) * (u * (1 / (1 + 1))) + (-1 - u)
      = u * (1 / (1 + 1)) * (u * (1 / (1 + 1))) := by
    mach_mpoly [u, (1 / (1 + 1) : Real)]
  have r : exp u + (-1 - u) = exp u - 1 - u := by mach_mpoly [exp u, u]
  rw [l, r] at s; exact s

/-- # **The Ω-point: `γ = 0` AND `κ = 0`.**

`G = exp(−G)`, i.e. `G·exp G = 1`, i.e. `G = Ω`. Both the constant and the linear term cancel
*exactly*, and what is left is second order: `t2 x ≥ G·(u/2)² ≥ (G/4)·x²`.

> This is where the previous session's lesson stops. There the tangent bound supplied a positive
> linear term for free; here the moving `log` cancels it, and only the **quadratic** gap survives —
> which is why `leaf_var_quad_floor_absurd` had to be built. -/
theorem leaf_var_expvar_const_gamma_zero_zero_absurd {t2 : EMLTree} {Av : Real → Real}
    {G L : Real} (hG : 0 < G) (hLM : L = 1 - exp G) (hkap : exp (-G) = G)
    (hval : ∀ x : Real, 0 < x → t2.eval x = exp (Av x) - log (exp x - L))
    (hexact : ∀ x : Real, 0 < x → exp (Av x) = G * exp (exp x - 1))
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  have h2 : (0 : Real) < 1 + 1 := add_pos one_pos one_pos
  have hhpos : (0 : Real) < 1 / (1 + 1) := one_div_pos_of_pos h2
  have hC : (0 : Real) < G * (1 / (1 + 1) * (1 / (1 + 1))) := mul_pos hG (mul_pos hhpos hhpos)
  refine leaf_var_quad_floor_absurd hC one_pos (le_refl 1) (fun x hx _ => ?_) h
  rw [hval x hx, hexact x hx]
  have hBeq : exp x - L = exp G + (exp x - 1) := by
    rw [hLM]; mach_mpoly [exp x, exp G]
  rw [hBeq]
  have hu0 : (0 : Real) ≤ exp x - 1 := by
    have s : (1 : Real) ≤ exp x := one_le_exp (le_of_lt hx)
    have u := add_le_add_wit s (le_refl (-1 : Real))
    have l : (1 : Real) + -1 = 0 := by mach_ring
    have r : exp x + -1 = exp x - 1 := by mach_mpoly [exp x]
    rw [l, r] at u; exact u
  have hxu : x ≤ exp x - 1 := by
    have t := one_add_le_exp x
    have u := add_le_add_wit t (le_refl (-1 : Real))
    have l : (1 : Real) + x + -1 = x := by mach_mpoly [x]
    have r : exp x + -1 = exp x - 1 := by mach_mpoly [exp x]
    rw [l, r] at u; exact u
  -- the quadratic gap, scaled by `G`
  have hgap := exp_sub_one_sub_self_ge_quad hu0
  have hGgap := mul_le_mul_of_nonneg_left hgap (le_of_lt hG)
  -- the log ceiling, with `exp(−G) = G`
  have hceil := log_shift_ceiling (g := G) hu0
  rw [hkap] at hceil
  -- `G·exp u − (G + u·G) = G·(exp u − 1 − u)`
  have s := add_le_add_wit (le_refl (G * exp (exp x - 1))) (neg_le_neg_wit hceil)
  have l : G * exp (exp x - 1) + -(G + (exp x - 1) * G)
      = G * (exp (exp x - 1) - 1 - (exp x - 1)) := by
    mach_mpoly [G, exp (exp x - 1), exp x]
  have r : G * exp (exp x - 1) + -log (exp G + (exp x - 1))
      = G * exp (exp x - 1) - log (exp G + (exp x - 1)) := by
    mach_mpoly [G, exp (exp x - 1), log (exp G + (exp x - 1))]
  rw [l, r] at s
  refine le_trans ?_ (le_trans hGgap s)
  -- `(x/2)² ≤ (u/2)²`, then multiply by `G`
  have hstep : x * (1 / (1 + 1)) * (x * (1 / (1 + 1)))
      ≤ (exp x - 1) * (1 / (1 + 1)) * ((exp x - 1) * (1 / (1 + 1))) := by
    have hx2 : x * (1 / (1 + 1)) ≤ (exp x - 1) * (1 / (1 + 1)) :=
      mul_le_mul_of_nonneg_right hxu (le_of_lt hhpos)
    have hxn : (0 : Real) ≤ x * (1 / (1 + 1)) := mul_nonneg (le_of_lt hx) (le_of_lt hhpos)
    have hun : (0 : Real) ≤ (exp x - 1) * (1 / (1 + 1)) := mul_nonneg hu0 (le_of_lt hhpos)
    exact le_trans (mul_le_mul_of_nonneg_right hx2 hxn)
      (mul_le_mul_of_nonneg_left hx2 hun)
  have hGstep := mul_le_mul_of_nonneg_left hstep (le_of_lt hG)
  have e : G * (1 / (1 + 1) * (1 / (1 + 1))) * (x * x)
      = G * (x * (1 / (1 + 1)) * (x * (1 / (1 + 1)))) := by
    mach_mpoly [G, x, (1 / (1 + 1) : Real)]
  rw [e]; exact hGstep

/-- The matching **floor** for `log_shift_ceiling`: `log (exp g + u) ≥ g + z − z²` with
`z := u·exp(−g)`. Both bounds come from the same two facts — `exp v − 1 ≤ v·exp v` gives
`z ≤ v·(1+z)`, and `log (1+z) ≤ z` gives `v ≤ z`; substituting the second into the first turns
`v ≥ z − v·z` into `v ≥ z − z²`, with no division. -/
theorem log_shift_floor {g u : Real} (hu : 0 ≤ u) :
    g + u * exp (-g) - u * exp (-g) * (u * exp (-g)) ≤ log (exp g + u) := by
  have hpos : (0 : Real) < exp g + u := by
    have s := add_le_add_wit (le_refl (exp g)) hu
    have e : exp g + (0 : Real) = exp g := by mach_ring
    rw [e] at s
    exact lt_of_lt_of_le (exp_pos g) s
  have hz0 : (0 : Real) ≤ u * exp (-g) := mul_nonneg hu (le_of_lt (exp_pos (-g)))
  -- `exp v = 1 + z` for `v := log (exp g + u) − g`
  have hev : exp (log (exp g + u) - g) = 1 + u * exp (-g) := by
    have esplit : log (exp g + u) - g = log (exp g + u) + -g := by mach_ring
    rw [esplit, exp_add, exp_log hpos]
    have e : (exp g + u) * exp (-g) = exp g * exp (-g) + u * exp (-g) := by
      mach_mpoly [exp g, u, exp (-g)]
    rw [e]
    have e2 : exp g * exp (-g) = 1 := by
      rw [← exp_add]
      have e3 : g + -g = (0 : Real) := by mach_ring
      rw [e3, exp_zero]
    rw [e2]
  -- `v ≤ z`
  have hvz : log (exp g + u) - g ≤ u * exp (-g) := by
    have hv := log_le_sub_one_of_one_le (y := 1 + u * exp (-g)) (by
      have s := add_le_add_wit (le_refl (1 : Real)) hz0
      have e : (1 : Real) + 0 = 1 := by mach_ring
      rw [e] at s; exact s)
    have e : log (1 + u * exp (-g)) = log (exp g + u) - g := by
      rw [← hev, log_exp]
    rw [e] at hv
    have e2 : (1 : Real) + u * exp (-g) - 1 = u * exp (-g) := by
      mach_mpoly [u, exp (-g)]
    rw [e2] at hv; exact hv
  -- `z ≤ v·(1+z)`
  have hzv : u * exp (-g) ≤ (log (exp g + u) - g) * (1 + u * exp (-g)) := by
    have s := exp_sub_one_le_mul_exp (x := log (exp g + u) - g)
    rw [hev] at s
    have e : (1 : Real) + u * exp (-g) - 1 = u * exp (-g) := by mach_mpoly [u, exp (-g)]
    rw [e] at s; exact s
  -- `v·z ≤ z·z`, so `v ≥ z − z²`
  have hvzz : (log (exp g + u) - g) * (u * exp (-g)) ≤ u * exp (-g) * (u * exp (-g)) :=
    mul_le_mul_of_nonneg_right hvz hz0
  have hfin : u * exp (-g) - u * exp (-g) * (u * exp (-g)) ≤ log (exp g + u) - g := by
    -- `z − v·z ≤ v`, from `z ≤ v·(1+z)`
    have step1 : u * exp (-g) - (log (exp g + u) - g) * (u * exp (-g))
        ≤ log (exp g + u) - g := by
      have s := add_le_add_wit hzv (le_refl (-((log (exp g + u) - g) * (u * exp (-g)))))
      have l : u * exp (-g) + -((log (exp g + u) - g) * (u * exp (-g)))
          = u * exp (-g) - (log (exp g + u) - g) * (u * exp (-g)) := by
        mach_mpoly [u, exp (-g), log (exp g + u), g]
      have r : (log (exp g + u) - g) * (1 + u * exp (-g))
            + -((log (exp g + u) - g) * (u * exp (-g)))
          = log (exp g + u) - g := by
        mach_mpoly [u, exp (-g), log (exp g + u), g]
      rw [l, r] at s; exact s
    -- `z − z² ≤ z − v·z`, from `v·z ≤ z²`
    have step2 : u * exp (-g) - u * exp (-g) * (u * exp (-g))
        ≤ u * exp (-g) - (log (exp g + u) - g) * (u * exp (-g)) := by
      have s := add_le_add_wit (le_refl (u * exp (-g))) (neg_le_neg_wit hvzz)
      have l : u * exp (-g) + -(u * exp (-g) * (u * exp (-g)))
          = u * exp (-g) - u * exp (-g) * (u * exp (-g)) := by
        mach_mpoly [u, exp (-g)]
      have r : u * exp (-g) + -((log (exp g + u) - g) * (u * exp (-g)))
          = u * exp (-g) - (log (exp g + u) - g) * (u * exp (-g)) := by
        mach_mpoly [u, exp (-g), log (exp g + u), g]
      rw [l, r] at s; exact s
    exact le_trans step2 step1
  have s := add_le_add_wit hfin (le_refl g)
  have l : u * exp (-g) - u * exp (-g) * (u * exp (-g)) + g
      = g + u * exp (-g) - u * exp (-g) * (u * exp (-g)) := by
    mach_mpoly [u, exp (-g), g]
  have r : log (exp g + u) - g + g = log (exp g + u) := by
    mach_mpoly [log (exp g + u), g]
  rw [l, r] at s; exact s

/-- `γ = 0`, `κ < 0`: the tree dips *below zero*. The linear term now points the wrong way, and the
quadratic correction `−z²` from `log_shift_floor` is small enough not to rescue it — provided the
point is chosen with `u·(G·e + exp(−G)²) < exp(−G) − G`, which `mul_exp_neg_lt_one` supplies
without division. -/
theorem leaf_var_expvar_const_gamma_zero_neg_absurd {t2 : EMLTree} {Av : Real → Real}
    {G L : Real} (hG : 0 < G) (hLM : L = 1 - exp G) (hkap : G < exp (-G))
    (hval : ∀ x : Real, 0 < x → t2.eval x = exp (Av x) - log (exp x - L))
    (hupp : ∀ x : Real, 0 < x → exp (Av x) ≤ G * exp (exp x - 1))
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  have hD : (0 : Real) < exp (-G) - G := by
    have u := add_lt_add_left hkap (-G)
    have l : -G + G = (0 : Real) := by mach_ring
    have r : -G + exp (-G) = exp (-G) - G := by mach_mpoly [G, exp (-G)]
    rw [l, r] at u; exact u
  have hb : (0 : Real) < G * exp 1 + exp (-G) * exp (-G) :=
    add_pos (mul_pos hG (exp_pos 1)) (mul_pos (exp_pos (-G)) (exp_pos (-G)))
  -- `u₀ < 1` and `u₀·b < D`
  obtain ⟨u₀, hu0pos, hu01, hu0D⟩ :=
    two_bound_witness' one_pos (mul_pos hD (exp_pos (-(G * exp 1 + exp (-G) * exp (-G)))))
  have hu0b : u₀ * (G * exp 1 + exp (-G) * exp (-G)) < exp (-G) - G := by
    have s := mul_lt_mul_of_pos_right hu0D hb
    have e : (exp (-G) - G) * exp (-(G * exp 1 + exp (-G) * exp (-G)))
          * (G * exp 1 + exp (-G) * exp (-G))
        = (exp (-G) - G) * ((G * exp 1 + exp (-G) * exp (-G))
          * exp (-(G * exp 1 + exp (-G) * exp (-G)))) := by
      mach_mpoly [exp (-G), G, exp 1, exp (-(G * exp 1 + exp (-G) * exp (-G)))]
    rw [e] at s
    have t := mul_lt_mul_pos_left_wit (mul_exp_neg_lt_one hb) hD
    have e2 : (exp (-G) - G) * (1 : Real) = exp (-G) - G := by mach_mpoly [exp (-G), G]
    rw [e2] at t
    exact lt_trans_ax s t
  -- the point `w`, small enough that `u := exp w − 1 ≤ u₀`
  obtain ⟨w, hwpos, hw1, hwu⟩ :=
    two_bound_witness' (exp_pos (-1)) (mul_pos hu0pos (exp_pos (-1)))
  have hwle1 : w ≤ 1 := le_of_lt (lt_trans_ax hw1 exp_neg_one_lt_one)
  have huu0 : exp w - 1 ≤ u₀ := by
    have s1 : exp w - 1 ≤ w * exp w := exp_sub_one_le_mul_exp
    have s2 : w * exp w ≤ w * exp 1 :=
      mul_le_mul_of_nonneg_left (exp_monotone hwle1) (le_of_lt hwpos)
    have s3 : w * exp 1 < u₀ * exp (-1) * exp 1 :=
      mul_lt_mul_of_pos_right hwu (exp_pos 1)
    have e : u₀ * exp (-1) * exp 1 = u₀ := by
      have e2 : u₀ * exp (-1) * exp 1 = u₀ * (exp (-1) * exp 1) := by
        mach_mpoly [u₀, exp (-1), exp 1]
      rw [e2, exp_neg_self_mul]
      mach_mpoly [u₀]
    rw [e] at s3
    exact le_trans s1 (le_trans s2 (le_of_lt s3))
  have hu0' : (0 : Real) ≤ exp w - 1 := by
    have s : (1 : Real) ≤ exp w := one_le_exp (le_of_lt hwpos)
    have u := add_le_add_wit s (le_refl (-1 : Real))
    have l : (1 : Real) + -1 = 0 := by mach_ring
    have r : exp w + -1 = exp w - 1 := by mach_mpoly [exp w]
    rw [l, r] at u; exact u
  refine leaf_var_neg_point_absurd hwpos hw1 ?_ h
  rw [hval w hwpos]
  have hBeq : exp w - L = exp G + (exp w - 1) := by
    rw [hLM]; mach_mpoly [exp w, exp G]
  rw [hBeq]
  -- upper bound on the tree: `G·exp u ≤ G + G·u·exp u₀`
  have hupper : exp (Av w) ≤ G + G * ((exp w - 1) * exp u₀) := by
    refine le_trans (hupp w hwpos) ?_
    have s1 : exp (exp w - 1) - 1 ≤ (exp w - 1) * exp (exp w - 1) := exp_sub_one_le_mul_exp
    have s2 : (exp w - 1) * exp (exp w - 1) ≤ (exp w - 1) * exp u₀ :=
      mul_le_mul_of_nonneg_left (exp_monotone huu0) hu0'
    have s3 : exp (exp w - 1) ≤ 1 + (exp w - 1) * exp u₀ := by
      have t := add_le_add_wit (le_trans s1 s2) (le_refl (1 : Real))
      have l : exp (exp w - 1) - 1 + 1 = exp (exp w - 1) := by
        mach_mpoly [exp (exp w - 1)]
      have r : (exp w - 1) * exp u₀ + 1 = 1 + (exp w - 1) * exp u₀ := by
        mach_mpoly [exp w, exp u₀]
      rw [l, r] at t; exact t
    have t := mul_le_mul_of_nonneg_left s3 (le_of_lt hG)
    have e : G * (1 + (exp w - 1) * exp u₀) = G + G * ((exp w - 1) * exp u₀) := by
      mach_mpoly [G, exp w, exp u₀]
    rw [e] at t; exact t
  have hfloor := log_shift_floor (g := G) hu0'
  have s := add_le_add_wit hupper (neg_le_neg_wit hfloor)
  have r : exp (Av w) + -log (exp G + (exp w - 1))
      = exp (Av w) - log (exp G + (exp w - 1)) := by
    mach_mpoly [exp (Av w), log (exp G + (exp w - 1))]
  have l : G + G * ((exp w - 1) * exp u₀)
        + -(G + (exp w - 1) * exp (-G)
          - (exp w - 1) * exp (-G) * ((exp w - 1) * exp (-G)))
      = (exp w - 1) * (G * exp u₀ - exp (-G)
          + (exp w - 1) * (exp (-G) * exp (-G))) := by
    mach_mpoly [G, exp w, exp u₀, exp (-G)]
  rw [l, r] at s
  refine le_trans s ?_
  -- the bracket is `≤ 0`
  have hbr : G * exp u₀ - exp (-G) + (exp w - 1) * (exp (-G) * exp (-G)) ≤ 0 := by
    have hexpu0 : exp u₀ - 1 ≤ u₀ * exp 1 :=
      le_trans exp_sub_one_le_mul_exp
        (mul_le_mul_of_nonneg_left (exp_monotone (le_of_lt hu01)) (le_of_lt hu0pos))
    have s1 : G * (exp u₀ - 1) ≤ G * (u₀ * exp 1) :=
      mul_le_mul_of_nonneg_left hexpu0 (le_of_lt hG)
    have s2 : (exp w - 1) * (exp (-G) * exp (-G)) ≤ u₀ * (exp (-G) * exp (-G)) :=
      mul_le_mul_of_nonneg_right huu0
        (le_of_lt (mul_pos (exp_pos (-G)) (exp_pos (-G))))
    have s3 := add_le_add_wit s1 s2
    have s4 : G * (u₀ * exp 1) + u₀ * (exp (-G) * exp (-G))
        = u₀ * (G * exp 1 + exp (-G) * exp (-G)) := by
      mach_mpoly [G, u₀, exp 1, exp (-G)]
    rw [s4] at s3
    have s5 := lt_of_le_of_lt s3 hu0b
    -- `G(exp u₀ − 1) + (exp w −1)·exp(−G)² < exp(−G) − G`
    have u := add_lt_add_left s5 (G - exp (-G))
    have l2 : G - exp (-G) + (G * (exp u₀ - 1) + (exp w - 1) * (exp (-G) * exp (-G)))
        = G * exp u₀ - exp (-G) + (exp w - 1) * (exp (-G) * exp (-G)) := by
      mach_mpoly [G, exp u₀, exp w, exp (-G)]
    have r2 : G - exp (-G) + (exp (-G) - G) = (0 : Real) := by
      mach_mpoly [G, exp (-G)]
    rw [l2, r2] at u
    exact le_of_lt u
  have t := mul_le_mul_of_nonneg_left hbr hu0'
  have e : (exp w - 1) * (0 : Real) = 0 := by mach_ring
  rw [e] at t; exact t

/-- **`A = eml var (const q')`, assembled.** The shape whose `exp (A x)` is *exactly* `G·exp u`.
Four regimes of `L`, and inside the last one three of `κ` — the full stratification, and every
boundary between them is transcendental. -/
theorem leaf_var_expvar_const_bdd_absurd {t2 : EMLTree} {Av : Real → Real} {G L : Real}
    (hG : 0 < G)
    (hval : ∀ x : Real, 0 < x → t2.eval x = exp (Av x) - log (exp x - L))
    (hexact : ∀ x : Real, 0 < x → exp (Av x) = G * exp (exp x - 1))
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  have hxu : ∀ x : Real, x ≤ exp x - 1 := by
    intro x
    have t := one_add_le_exp x
    have u := add_le_add_wit t (le_refl (-1 : Real))
    have l : (1 : Real) + x + -1 = x := by mach_mpoly [x]
    have r : exp x + -1 = exp x - 1 := by mach_mpoly [exp x]
    rw [l, r] at u; exact u
  have hlow : ∀ x : Real, 0 < x → G * exp x ≤ exp (Av x) := by
    intro x hx
    rw [hexact x hx]
    exact mul_le_mul_of_nonneg_left (exp_monotone (hxu x)) (le_of_lt hG)
  have hupp : ∀ x : Real, 0 < x → exp (Av x) ≤ G * exp (exp x - 1) :=
    fun x hx => le_of_eq (hexact x hx)
  rcases lt_total 1 L with hL | hL | hL
  · exact leaf_var_expvar_const_clamped_absurd hG hL hval hlow h
  · rw [← hL] at hval
    exact leaf_var_expvar_const_one_absurd hG hval hlow h
  · have hM : (0 : Real) < 1 - L := by
      have u := add_lt_add_left hL (-L)
      have l : -L + L = (0 : Real) := by mach_ring
      have r : -L + 1 = 1 - L := by mach_mpoly [L]
      rw [l, r] at u; exact u
    have hLM : L = 1 - (1 - L) := by mach_ring
    rcases lt_total (log (1 - L)) G with hg | hg | hg
    · exact leaf_var_expvar_const_gamma_pos_absurd hG hM hLM hg hval hlow h
    · have hMe : (1 : Real) - L = exp G := by rw [← hg]; exact (exp_log hM).symm
      have hLG : L = 1 - exp G := by rw [← hMe]; mach_ring
      rcases lt_total (exp (-G)) G with hk | hk | hk
      · exact leaf_var_expvar_const_gamma_zero_pos_absurd hLG hk hval hlow h
      · exact leaf_var_expvar_const_gamma_zero_zero_absurd hG hLG hk hval hexact h
      · exact leaf_var_expvar_const_gamma_zero_neg_absurd hG hLG hk hval hupp h
    · exact leaf_var_expvar_const_gamma_neg_absurd hG hM hLM hg hval hupp h

/-- **`A = var`, assembled.** Here `G = 1`, so the coincidence `γ = 0` forces `M = e` and then
`κ = 1 − e⁻¹ > 0`: **this shape can never reach the Ω-point.** That is why it needs no sharp lower
bound on `exp (A x)`, and why the quadratic core is only ever invoked by the other shape. -/
theorem leaf_var_expvar_const_left_var_absurd {t2 : EMLTree} {L : Real}
    (hval : ∀ x : Real, 0 < x → t2.eval x = exp x - log (exp x - L))
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  have hxu : ∀ x : Real, x ≤ exp x - 1 := by
    intro x
    have t := one_add_le_exp x
    have u := add_le_add_wit t (le_refl (-1 : Real))
    have l : (1 : Real) + x + -1 = x := by mach_mpoly [x]
    have r : exp x + -1 = exp x - 1 := by mach_mpoly [exp x]
    rw [l, r] at u; exact u
  have hlow : ∀ x : Real, 0 < x → (1 : Real) * exp x ≤ exp x := by
    intro x _
    have e : (1 : Real) * exp x = exp x := by mach_mpoly [exp x]
    rw [e]; exact le_refl _
  have hupp : ∀ x : Real, 0 < x → exp x ≤ (1 : Real) * exp (exp x - 1) := by
    intro x _
    have e : (1 : Real) * exp (exp x - 1) = exp (exp x - 1) := by
      mach_mpoly [exp (exp x - 1)]
    rw [e]
    exact exp_monotone (hxu x)
  rcases lt_total 1 L with hL | hL | hL
  · exact leaf_var_expvar_const_clamped_absurd (Av := fun x => x) (G := 1) one_pos hL
      hval hlow h
  · rw [← hL] at hval
    exact leaf_var_expvar_const_one_absurd (Av := fun x => x) (G := 1) one_pos hval hlow h
  · have hM : (0 : Real) < 1 - L := by
      have u := add_lt_add_left hL (-L)
      have l : -L + L = (0 : Real) := by mach_ring
      have r : -L + 1 = 1 - L := by mach_mpoly [L]
      rw [l, r] at u; exact u
    have hLM : L = 1 - (1 - L) := by mach_ring
    rcases lt_total (log (1 - L)) 1 with hg | hg | hg
    · exact leaf_var_expvar_const_gamma_pos_absurd (Av := fun x => x) (G := 1)
        one_pos hM hLM hg hval hlow h
    · -- `γ = 0` ⟹ `M = e`; and `κ = 1 − e⁻¹ > 0`, so the affine floor always suffices
      have hMe : (1 : Real) - L = exp 1 := by
        have t := exp_log hM
        rw [hg] at t
        exact t.symm
      have hLG : L = 1 - exp 1 := by rw [← hMe]; mach_ring
      exact leaf_var_expvar_const_gamma_zero_pos_absurd (Av := fun x => x) (G := 1)
        hLG exp_neg_one_lt_one hval hlow h
    · exact leaf_var_expvar_const_gamma_neg_absurd (Av := fun x => x) (G := 1)
        one_pos hM hLM hg hval hupp h

/-- # **The last shape of the leaf-`var` branch is impossible.**

`t2 = eml A (eml var (const q))`, `A` any depth-≤1 tree, `q` free. All six shapes of `A`:

| `A` | route |
|---|---|
| `const c`, `eml (const p) (const q')` | two-point **monotonicity** — no floor |
| `eml (const p) var`, `eml var var` | dominates `c₀ − log x` |
| `var` | `γ`-split; `κ > 0` always, so never reaches the Ω-point |
| `eml var (const q')` | `γ`-split **and** `κ`-split, including the quadratic Ω-point | -/
theorem leaf_var_right_eml_var_const_absurd {A : EMLTree} {q : Real} (hA : A.depth ≤ 1)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml EMLTree.var
        (EMLTree.eml A (EMLTree.eml EMLTree.var (EMLTree.const q)))).eval x = 1 / x) : False := by
  cases A with
  | const c =>
      exact leaf_var_expvar_const_left_const_absurd (K := exp c) (L := log q)
        (fun _ _ => rfl) h
  | var =>
      exact leaf_var_expvar_const_left_var_absurd (L := log q) (fun _ _ => rfl) h
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
          | const q' =>
              exact leaf_var_expvar_const_left_const_absurd (K := exp (exp p - log q'))
                (L := log q) (fun _ _ => rfl) h
          | var =>
              exact leaf_var_expvar_const_unbdd_absurd (Av := fun x => exp p - log x)
                (c := exp p) (L := log q) (fun _ _ => rfl) (fun _ _ _ => le_refl _) h
      | var =>
          cases b with
          | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
          | const q' =>
              refine leaf_var_expvar_const_bdd_absurd (Av := fun x => exp x - log q')
                (G := exp (1 - log q')) (L := log q) (exp_pos _)
                (fun _ _ => rfl) (fun x _ => ?_) h
              rw [← exp_add]
              have e : (1 - log q') + (exp x - 1) = exp x - log q' := by
                mach_mpoly [log q', exp x]
              rw [e]
          | var =>
              refine leaf_var_expvar_const_unbdd_absurd (Av := fun x => exp x - log x)
                (c := 1) (L := log q) (fun _ _ => rfl) (fun x hx _ => ?_) h
              have s := add_le_add_wit (one_le_exp (le_of_lt hx)) (le_refl (-log x))
              have l : (1 : Real) + -log x = 1 - log x := by mach_mpoly [log x]
              have r : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
              rw [l, r] at s; exact s

/-- # ▸ **`t1 = var` is CLOSED — the first complete family of the depth-3 arm.**

No depth-≤2 right child lets `eml var t2` be `1/x`. Assembled from `leaf_var_right_const_absurd`
(`t2` a constant), `leaf_var_right_var_absurd` (`t2 = var`), `leaf_var_right_eml_absurd` (every
`eml A B` with `B` not `eml var (const q)`), and the residue closed above.

**This does NOT move `d(1/x)`**, which stays `{3,4}`: the other depth-3 family — `t1 = eml a b`
with `b ≠ var` and an unbounded left child — is untouched, and either could still hold a witness. -/
theorem leaf_var_absurd {t2 : EMLTree} (ht2 : t2.depth ≤ 2)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml EMLTree.var t2).eval x = 1 / x) : False := by
  cases t2 with
  | const k => exact leaf_var_right_const_absurd h
  | var => exact leaf_var_right_var_absurd h
  | eml A B =>
      have hA : A.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht2
        have := Nat.le_max_left A.depth B.depth
        omega
      have hB : B.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht2
        have := Nat.le_max_right A.depth B.depth
        omega
      cases B with
      | const k =>
          exact leaf_var_right_eml_absurd hA hB (fun _ hc => EMLTree.noConfusion hc) h
      | var =>
          exact leaf_var_right_eml_absurd hA hB (fun _ hc => EMLTree.noConfusion hc) h
      | eml a b =>
          cases a with
          | const p =>
              refine leaf_var_right_eml_absurd hA hB (fun _ hc => ?_) h
              injection hc with h1 _
              exact EMLTree.noConfusion h1
          | eml _ _ =>
              refine leaf_var_right_eml_absurd hA hB (fun _ hc => ?_) h
              injection hc with h1 _
              exact EMLTree.noConfusion h1
          | var =>
              cases b with
              | const q => exact leaf_var_right_eml_var_const_absurd hA h
              | var =>
                  refine leaf_var_right_eml_absurd hA hB (fun _ hc => ?_) h
                  injection hc with _ h2
                  exact EMLTree.noConfusion h2
              | eml _ _ =>
                  refine leaf_var_right_eml_absurd hA hB (fun _ hc => ?_) h
                  injection hc with _ h2
                  exact EMLTree.noConfusion h2

/-- `t1 = eml var B` — the left child's own left child is `var`, so `A x = x` dominates itself. -/
theorem depth3_left_var_left_absurd {B t2 : EMLTree} (hB : B.depth ≤ 1) (ht2 : t2.depth ≤ 2)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml EMLTree.var B) t2).eval x = 1 / x) : False := by
  refine depth3_left_unbounded_absurd (c₀ := 0) (x₂ := 1) hB ht2 (le_refl 1) (fun x _ => ?_) h
  show x + 0 ≤ x
  have e : x + (0 : Real) = x := by mach_mpoly [x]
  rw [e]; exact le_refl _

/-- `t1 = eml (eml var b) B` — `A x = exp x − log (b x) ≥ x` past `4 + exp C_b`, since
`exp_ge_three_mul` pays for both the `−x` from the log ceiling and the `x` being dominated. -/
theorem depth3_left_eml_var_left_absurd {b B t2 : EMLTree} (hb : b.depth ≤ 1)
    (hB : B.depth ≤ 1) (ht2 : t2.depth ≤ 2)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml (EMLTree.eml EMLTree.var b) B) t2).eval x = 1 / x) :
    False := by
  obtain ⟨Cb, hCb⟩ := depth_le_one_log_bound_at_infty b hb
  have h14 : (1 : Real) ≤ 1 + 1 + 1 + 1 := by
    have t := add_le_add_wit (add_le_add_wit (add_le_add_wit (le_refl (1 : Real))
      (le_of_lt one_pos)) (le_of_lt one_pos)) (le_of_lt one_pos)
    have e : (1 : Real) + 0 + 0 + 0 = 1 := by mach_ring
    rw [e] at t; exact t
  have hthr : (1 : Real) ≤ 1 + 1 + 1 + 1 + exp Cb := by
    have s := add_le_add_wit h14 (le_of_lt (exp_pos Cb))
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at s; exact s
  refine depth3_left_unbounded_absurd (c₀ := 0) (x₂ := 1 + 1 + 1 + 1 + exp Cb)
    hB ht2 hthr (fun x hx => ?_) h
  show x + 0 ≤ exp x - log (b.eval x)
  have h4 : (1 + 1 + 1 + 1 : Real) ≤ x := by
    have s := add_le_add_wit (le_refl (1 + 1 + 1 + 1 : Real)) (le_of_lt (exp_pos Cb))
    have e : (1 + 1 + 1 + 1 : Real) + 0 = 1 + 1 + 1 + 1 := by mach_ring
    rw [e] at s
    exact le_trans s hx
  have hx1 : (1 : Real) ≤ x := le_trans h14 h4
  have hCbx : Cb ≤ x := by
    have s := add_le_add_wit (le_of_lt (lt_of_lt_of_le one_pos h14))
      (le_of_lt (exp_grows_strictly_thm Cb))
    have e : (0 : Real) + Cb = Cb := by mach_ring
    rw [e] at s
    exact le_trans s hx
  have h3 := exp_ge_three_mul h4
  -- `x + x + Cb ≤ x + x + x ≤ exp x`
  have hsum : x + x + Cb ≤ exp x := by
    have s := add_le_add_wit (le_refl (x + x)) hCbx
    exact le_trans s h3
  have s := add_le_add_wit hsum (neg_le_neg_wit (hCb x hx1))
  have l : x + x + Cb + -(x + Cb) = x + 0 := by mach_mpoly [x, Cb]
  have r : exp x + -log (b.eval x) = exp x - log (b.eval x) := by
    mach_mpoly [exp x, log (b.eval x)]
  rw [l, r] at s; exact s

/-- # ▸ **The `0⁺`-side rank mismatch: `t1 = eml (eml (const p) var) B`.**

The mirror of the `∞`-side argument. Here `A x = exp p − log x` blows **up** at `0`, so
`exp (A x) = exp(exp p)·(1/x)` and `t1` runs to `+∞` like `1/x`. Then `exp (t1 x)` is a double
exponential in `−log x` while `1/x + log (t2 x)` is a single one — two rungs apart again.

Substituting `x = exp(−t)` turns every `1/x` into `exp t` and every `−log x` into `t`, so the whole
argument runs **division-free** in `t`, and the endgame is the same `exp_beats_linear_past`. -/
theorem depth3_left_pole_at_zero_absurd {p : Real} {B t2 : EMLTree}
    (hB : B.depth ≤ 1) (ht2 : t2.depth ≤ 2)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml (EMLTree.eml (EMLTree.const p) EMLTree.var) B) t2).eval x
        = 1 / x) : False := by
  obtain ⟨N, δ₁, hδ₁0, hδ₁1, hN⟩ := depth_le_one_log_upper_near_zero B hB
  obtain ⟨C, δ₂, hδ₂0, hδ₂1, hC⟩ := depth_le_two_growth_ceiling t2 ht2
  have hC'1 : (1 : Real) ≤ 1 + exp C := by
    have s := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos C))
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at s; exact s
  have hlogC' : (0 : Real) ≤ log (1 + exp C) := by
    have t := log_le_log one_pos hC'1
    rw [log_one] at t; exact t
  have hE1 : (1 : Real) ≤ 1 + 1 + exp (log (1 + exp C)) := by
    have s := add_le_add_wit (add_le_add_wit (le_refl (1 : Real)) (le_of_lt one_pos))
      (le_of_lt (exp_pos (log (1 + exp C))))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at s; exact s
  have hEpos : (0 : Real) < 1 + 1 + exp (log (1 + exp C)) := lt_of_lt_of_le one_pos hE1
  -- the estimate, at every `t` past the threshold
  have hkey : ∀ t : Real, 1 + exp (-log δ₁) + exp (-log δ₂) ≤ t →
      exp (exp p + t)
        ≤ t + t + (N + log (1 + 1 + exp (log (1 + exp C)))) := by
    intro t ht
    have ht1 : (1 : Real) ≤ t := by
      have s := add_le_add_wit (add_le_add_wit (le_refl (1 : Real))
        (le_of_lt (exp_pos (-log δ₁)))) (le_of_lt (exp_pos (-log δ₂)))
      have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
      rw [e] at s
      exact le_trans s ht
    have ht0 : (0 : Real) ≤ t := le_trans (le_of_lt one_pos) ht1
    have hxpos : (0 : Real) < exp (-t) := exp_pos _
    have hlogx : log (exp (-t)) = -t := log_exp _
    -- `exp (−t) ≤ δᵢ`
    have hxd : ∀ δ : Real, 0 < δ → exp (-log δ) ≤ t → exp (-t) ≤ δ := by
      intro δ hδ hge
      have h1 : -log δ ≤ t := le_trans (le_of_lt (exp_grows_strictly_thm (-log δ))) hge
      have h2 : -t ≤ log δ := by
        have s := neg_le_neg_wit h1
        have e : -(-log δ) = log δ := by mach_ring
        rw [e] at s; exact s
      have hh := exp_monotone h2
      rwa [exp_log hδ] at hh
    have hx1' : exp (-log δ₁) ≤ t := by
      have s := add_le_add_wit (add_le_add_wit (le_of_lt one_pos)
        (le_refl (exp (-log δ₁)))) (le_of_lt (exp_pos (-log δ₂)))
      have e : (0 : Real) + exp (-log δ₁) + 0 = exp (-log δ₁) := by mach_ring
      rw [e] at s
      exact le_trans s ht
    have hx2' : exp (-log δ₂) ≤ t := by
      have s := add_le_add_wit (add_le_add_wit (le_of_lt one_pos)
        (le_of_lt (exp_pos (-log δ₁)))) (le_refl (exp (-log δ₂)))
      have e : (0 : Real) + 0 + exp (-log δ₂) = exp (-log δ₂) := by mach_ring
      rw [e] at s
      exact le_trans s ht
    have hxδ₁ : exp (-t) ≤ δ₁ := hxd δ₁ hδ₁0 hx1'
    have hxδ₂ : exp (-t) ≤ δ₂ := hxd δ₂ hδ₂0 hx2'
    -- `1 / exp (−t) = exp t`
    have hinv : (1 : Real) / exp (-t) = exp t := by
      have hm : exp t * exp (-t) = 1 := by
        rw [← exp_add]
        have e : t + -t = (0 : Real) := by mach_ring
        rw [e, exp_zero]
      have hmi := mul_inv (exp (-t)) (ne_of_gt hxpos)
      have s : exp t * (exp (-t) * (1 / exp (-t))) = exp t * 1 := by rw [hmi]
      have l : exp t * (exp (-t) * (1 / exp (-t)))
          = (exp t * exp (-t)) * (1 / exp (-t)) := by
        mach_mpoly [exp t, exp (-t), (1 / exp (-t) : Real)]
      rw [l, hm] at s
      have e1 : (1 : Real) * (1 / exp (-t)) = 1 / exp (-t) := by
        mach_mpoly [(1 / exp (-t) : Real)]
      have e2 : exp t * (1 : Real) = exp t := by mach_mpoly [exp t]
      rw [e1, e2] at s; exact s
    -- the equation at `x = exp (−t)`
    have heq := h (exp (-t)) hxpos
    rw [hinv] at heq
    -- the left child's value: `exp p − log x = exp p + t`
    have hAv : (EMLTree.eml (EMLTree.const p) EMLTree.var).eval (exp (-t)) = exp p + t := by
      show exp p - log (exp (-t)) = exp p + t
      rw [hlogx]
      mach_mpoly [exp p, t]
    -- `log (B x) ≤ N + t`
    have hBlog : log (B.eval (exp (-t))) ≤ N + t := by
      have s := hN (exp (-t)) hxpos hxδ₁
      rw [hlogx] at s
      have e : N - -t = N + t := by mach_mpoly [N, t]
      rw [e] at s; exact s
    -- `t2 x ≤ exp t · (1 + exp C)`
    have ht2up : t2.eval (exp (-t)) ≤ exp t * (1 + exp C) := by
      have s := hC (exp (-t)) hxpos hxδ₂
      have s2 := mul_le_mul_of_nonneg_left s (le_of_lt (exp_pos t))
      have l : exp t * (exp (-t) * t2.eval (exp (-t)))
          = (exp t * exp (-t)) * t2.eval (exp (-t)) := by
        mach_mpoly [exp t, exp (-t), t2.eval (exp (-t))]
      have hm : exp t * exp (-t) = 1 := by
        rw [← exp_add]
        have e : t + -t = (0 : Real) := by mach_ring
        rw [e, exp_zero]
      rw [l, hm] at s2
      have e1 : (1 : Real) * t2.eval (exp (-t)) = t2.eval (exp (-t)) := by
        mach_mpoly [t2.eval (exp (-t))]
      rw [e1] at s2
      refine le_trans s2 ?_
      have hCC : C ≤ 1 + exp C := by
        have u := add_le_add_wit (le_of_lt one_pos) (le_of_lt (exp_grows_strictly_thm C))
        have e : (0 : Real) + C = C := by mach_ring
        rw [e] at u; exact u
      exact mul_le_mul_of_nonneg_left hCC (le_of_lt (exp_pos t))
    have hlogt2 : log (t2.eval (exp (-t))) ≤ t + log (1 + exp C) :=
      log_le_of_le_exp_mul' ht0 hC'1 ht2up
    -- `exp (t1 x) = exp t + log (t2 x) ≤ exp (t + log E)`
    have hup : exp ((EMLTree.eml (EMLTree.eml (EMLTree.const p) EMLTree.var) B).eval (exp (-t)))
        ≤ exp (t + log (1 + 1 + exp (log (1 + exp C)))) := by
      have hh : exp ((EMLTree.eml (EMLTree.eml (EMLTree.const p) EMLTree.var) B).eval
          (exp (-t))) - log (t2.eval (exp (-t))) = exp t := heq
      have s := add_le_add_wit (le_of_eq hh) (le_refl (log (t2.eval (exp (-t)))))
      have l : exp ((EMLTree.eml (EMLTree.eml (EMLTree.const p) EMLTree.var) B).eval (exp (-t)))
            - log (t2.eval (exp (-t))) + log (t2.eval (exp (-t)))
          = exp ((EMLTree.eml (EMLTree.eml (EMLTree.const p) EMLTree.var) B).eval (exp (-t))) := by
        mach_mpoly [exp ((EMLTree.eml (EMLTree.eml (EMLTree.const p) EMLTree.var) B).eval
          (exp (-t))), log (t2.eval (exp (-t)))]
      rw [l] at s
      refine le_trans s ?_
      have s2 := add_le_add_wit (le_refl (exp t)) hlogt2
      refine le_trans s2 ?_
      -- `exp t + (t + log C') ≤ exp t · E = exp (t + log E)`
      have hstep : exp t + (t + log (1 + exp C))
          ≤ exp t * (1 + 1 + exp (log (1 + exp C))) := by
        have hex1 : (1 : Real) ≤ exp t := one_le_exp ht0
        have hte : t ≤ exp t := le_of_lt (exp_grows_strictly_thm t)
        have hlc : log (1 + exp C) ≤ exp t * exp (log (1 + exp C)) := by
          have u := mul_le_mul_of_nonneg_right hex1 (le_of_lt (exp_pos (log (1 + exp C))))
          have e : (1 : Real) * exp (log (1 + exp C)) = exp (log (1 + exp C)) := by
            mach_mpoly [exp (log (1 + exp C))]
          rw [e] at u
          exact le_trans (le_of_lt (exp_grows_strictly_thm (log (1 + exp C)))) u
        have s3 := add_le_add_wit (add_le_add_wit (le_refl (exp t)) hte) hlc
        have l2 : exp t + t + log (1 + exp C) = exp t + (t + log (1 + exp C)) := by
          mach_mpoly [exp t, t, log (1 + exp C)]
        have r2 : exp t + exp t + exp t * exp (log (1 + exp C))
            = exp t * (1 + 1 + exp (log (1 + exp C))) := by
          mach_mpoly [exp t, exp (log (1 + exp C))]
        rw [l2, r2] at s3; exact s3
      have e : exp (t + log (1 + 1 + exp (log (1 + exp C))))
          = exp t * (1 + 1 + exp (log (1 + exp C))) := by
        rw [exp_add, exp_log hEpos]
      rw [e]; exact hstep
    -- reverse `exp`, then insert the lower bound on `t1`
    have hle : (EMLTree.eml (EMLTree.eml (EMLTree.const p) EMLTree.var) B).eval (exp (-t))
        ≤ t + log (1 + 1 + exp (log (1 + exp C))) := by
      rcases lt_total ((EMLTree.eml (EMLTree.eml (EMLTree.const p) EMLTree.var) B).eval
        (exp (-t))) (t + log (1 + 1 + exp (log (1 + exp C)))) with hp | hz | hn
      · exact le_of_lt hp
      · exact le_of_eq hz
      · exact absurd hup (fun hc => lt_irrefl_ax _ (lt_of_lt_of_le (exp_lt hn) hc))
    have hlow : exp (exp p + t) - (N + t)
        ≤ (EMLTree.eml (EMLTree.eml (EMLTree.const p) EMLTree.var) B).eval (exp (-t)) := by
      show exp (exp p + t) - (N + t)
        ≤ exp ((EMLTree.eml (EMLTree.const p) EMLTree.var).eval (exp (-t)))
          - log (B.eval (exp (-t)))
      rw [hAv]
      have s := add_le_add_wit (le_refl (exp (exp p + t))) (neg_le_neg_wit hBlog)
      have l : exp (exp p + t) + -(N + t) = exp (exp p + t) - (N + t) := by
        mach_mpoly [exp (exp p + t), N, t]
      have r : exp (exp p + t) + -log (B.eval (exp (-t)))
          = exp (exp p + t) - log (B.eval (exp (-t))) := by
        mach_mpoly [exp (exp p + t), log (B.eval (exp (-t)))]
      rw [l, r] at s; exact s
    have s := le_trans hlow hle
    have u := add_le_add_wit s (le_refl (N + t))
    have l : exp (exp p + t) - (N + t) + (N + t) = exp (exp p + t) := by
      mach_mpoly [exp (exp p + t), N, t]
    have r : t + log (1 + 1 + exp (log (1 + exp C))) + (N + t)
        = t + t + (N + log (1 + 1 + exp (log (1 + exp C)))) := by
      mach_mpoly [t, N, log (1 + 1 + exp (log (1 + exp C)))]
    rw [l, r] at u; exact u
  -- name the point: `exp s ≤ 2s + const` fails
  obtain ⟨s, hsT, _, hs⟩ := exp_beats_linear_past
    (α := 1 + 1)
    (β := N + log (1 + 1 + exp (log (1 + exp C))) - (exp p + exp p))
    (le_of_lt (add_pos one_pos one_pos))
    (1 + exp (-log δ₁) + exp (-log δ₂) + exp p)
  have htge : 1 + exp (-log δ₁) + exp (-log δ₂) ≤ s - exp p := by
    have u := add_le_add_wit hsT (le_refl (-exp p))
    have l : 1 + exp (-log δ₁) + exp (-log δ₂) + exp p + -exp p
        = 1 + exp (-log δ₁) + exp (-log δ₂) := by
      mach_mpoly [exp (-log δ₁), exp (-log δ₂), exp p]
    have r : s + -exp p = s - exp p := by mach_mpoly [s, exp p]
    rw [l, r] at u; exact u
  have hk := hkey (s - exp p) htge
  have e : exp p + (s - exp p) = s := by mach_mpoly [s, exp p]
  rw [e] at hk
  have hrw : (1 + 1) * s + (N + log (1 + 1 + exp (log (1 + exp C))) - (exp p + exp p))
      = s - exp p + (s - exp p) + (N + log (1 + 1 + exp (log (1 + exp C)))) := by
    mach_mpoly [s, exp p, N, log (1 + 1 + exp (log (1 + exp C)))]
  rw [hrw] at hs
  exact lt_irrefl_ax _ (lt_of_lt_of_le hs hk)

/-! ## ▸ **The bounded-left-child core**

What is left of depth 3 is `t1 = eml A B` with `A` **constant-valued** — so `exp (A x)` is a
constant and `exp (t1 x) = exp(A x)/B(x)` is *bounded* wherever `B` stays away from `0`. That is
exactly the situation the leaf-`var` branch was in (`t1 = var` gives `exp (t1 x) ≤ e` on `(0,1]`),
and **every load-bearing lemma of that branch used only the bound, never the shape**.

So the core is generalised here rather than re-derived: `leaf_var_arith` is the `W = exp 1` instance
of `bounded_left_arith`, and `leaf_var_floor_absurd` the corresponding instance below. This is what
makes the remaining work a *port* of a finished argument rather than a fresh three-session arc. -/

/-- The pin for an arbitrary left child: `x · log (t2 x) = x · exp (t1 x) − 1`. -/
theorem depth3_pin {t1 t2 : EMLTree}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x)
    (x : Real) (hx : 0 < x) :
    x * log (t2.eval x) = x * exp (t1.eval x) - 1 := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have he : exp (t1.eval x) - log (t2.eval x) = 1 / x := h x hx
  have hmul : x * (exp (t1.eval x) - log (t2.eval x)) = x * (1 / x) := by rw [he]
  rw [mul_inv x hxne] at hmul
  have hd : x * (exp (t1.eval x) - log (t2.eval x))
      = x * exp (t1.eval x) - x * log (t2.eval x) := by
    mach_mpoly [x, exp (t1.eval x), log (t2.eval x)]
  rw [hd] at hmul
  have t : (x * exp (t1.eval x) - x * log (t2.eval x)) + (x * log (t2.eval x) - 1)
      = 1 + (x * log (t2.eval x) - 1) := by rw [hmul]
  have l : (x * exp (t1.eval x) - x * log (t2.eval x)) + (x * log (t2.eval x) - 1)
      = x * exp (t1.eval x) - 1 := by
    mach_mpoly [x, exp (t1.eval x), log (t2.eval x)]
  have r : (1 : Real) + (x * log (t2.eval x) - 1) = x * log (t2.eval x) := by
    mach_mpoly [x, log (t2.eval x)]
  rw [l, r] at t; exact t.symm

/-- `leaf_var_arith` with `exp 1` replaced by an arbitrary ceiling `W` on the left child. The proof
is unchanged — `exp 1` was only ever the bound on `exp (var x)` over `(0,1]`. -/
theorem bounded_left_arith {t v w Kl W : Real} (ht1 : 1 ≤ t)
    (hpin : exp (-t) * v = exp (-t) * w - 1)
    (hLv : Kl - t ≤ v) (hw : w ≤ W) (hbig : W - Kl < t) : False := by
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
  have hstep : exp t ≤ W - Kl + t := by
    have s1 : Kl - t ≤ W - exp t := by
      have s := add_le_add_wit hw (le_refl (-exp t))
      have e1 : w + -exp t = w - exp t := by mach_ring
      have e2 : W + -exp t = W - exp t := by mach_ring
      rw [e1, e2] at s
      exact le_trans hLv s
    have s := add_le_add_left s1 (exp t - Kl + t)
    have e1 : exp t - Kl + t + (Kl - t) = exp t := by mach_mpoly [exp t, Kl, t]
    have e2 : exp t - Kl + t + (W - exp t) = W - Kl + t := by
      mach_mpoly [exp t, W, Kl, t]
    rw [e1, e2] at s
    exact s
  have h2t : t + t ≤ exp t := exp_ge_two_mul ht1
  have hfin : t ≤ W - Kl := by
    have s := le_trans h2t hstep
    have u := add_le_add_left s (-t)
    have e1 : -t + (t + t) = t := by mach_mpoly [t]
    have e2 : -t + (W - Kl + t) = W - Kl := by mach_mpoly [W, Kl, t]
    rw [e1, e2] at u
    exact u
  exact lt_irrefl_ax _ (lt_of_lt_of_le hbig hfin)

/-- **A linear floor on the right child is fatal whenever the LEFT child is bounded.** The
generalisation of `leaf_var_floor_absurd`: the whole leaf-`var` floor apparatus turns out to need
only `exp (t1 x) ≤ W` on the cutoff interval. -/
theorem bounded_left_floor_absurd {t1 t2 : EMLTree} {K d W : Real} (hK : 0 < K)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hW : ∀ x : Real, 0 < x → x ≤ d → exp (t1.eval x) ≤ W)
    (hfloor : ∀ x : Real, 0 < x → x ≤ d → K * x ≤ t2.eval x)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x) : False := by
  have ht1 : (1 : Real) ≤ 1 + exp (W - log K) + exp (-log d) := by
    have s := add_le_add_wit (add_le_add_wit (le_refl (1 : Real))
      (le_of_lt (exp_pos (W - log K)))) (le_of_lt (exp_pos (-log d)))
    have e : (1 : Real) + 0 + 0 = 1 := by mach_ring
    rw [e] at s; exact s
  have hx0 : (0 : Real) < exp (-(1 + exp (W - log K) + exp (-log d))) := exp_pos _
  have hxd : exp (-(1 + exp (W - log K) + exp (-log d))) ≤ d := by
    have hge : -log d ≤ 1 + exp (W - log K) + exp (-log d) := by
      have h1 := le_of_lt (exp_grows_strictly_thm (-log d))
      have s := add_le_add_wit (add_le_add_wit (le_of_lt one_pos)
        (le_of_lt (exp_pos (W - log K)))) (le_refl (exp (-log d)))
      have e : (0 : Real) + 0 + exp (-log d) = exp (-log d) := by mach_ring
      rw [e] at s
      exact le_trans h1 s
    have hstep : -(1 + exp (W - log K) + exp (-log d)) ≤ log d := by
      have s := neg_le_neg_wit hge
      have e : -(-log d) = log d := by mach_ring
      rw [e] at s
      exact s
    have hh := exp_monotone hstep
    rw [exp_log hd] at hh
    exact hh
  refine bounded_left_arith (t := 1 + exp (W - log K) + exp (-log d))
    (v := log (t2.eval (exp (-(1 + exp (W - log K) + exp (-log d))))))
    (w := exp (t1.eval (exp (-(1 + exp (W - log K) + exp (-log d))))))
    (Kl := log K) (W := W) ht1 ?_ ?_ ?_ ?_
  · exact depth3_pin h _ hx0
  · have hKx : (0 : Real) < K * exp (-(1 + exp (W - log K) + exp (-log d))) :=
      mul_pos hK hx0
    have hl := log_le_log hKx (hfloor _ hx0 hxd)
    rw [log_mul hK hx0, log_exp] at hl
    have e : log K + -(1 + exp (W - log K) + exp (-log d))
        = log K - (1 + exp (W - log K) + exp (-log d)) := by mach_ring
    rw [e] at hl
    exact hl
  · exact hW _ hx0 hxd
  · have h1 := exp_grows_strictly_thm (W - log K)
    have s := add_le_add_wit (add_le_add_wit (le_of_lt one_pos)
      (le_refl (exp (W - log K)))) (le_of_lt (exp_pos (-log d)))
    have e : (0 : Real) + exp (W - log K) + 0 = exp (W - log K) := by mach_ring
    rw [e] at s
    exact lt_of_lt_of_le h1 s

/-! ### Discharging the bound for a constant-valued `A`

`t1 = eml A B` with `A` constant-valued gives `t1 x = exp α − log (B x)`, so `exp (t1 x)` is bounded
exactly when `B` is bounded **away from `0`** — either from above by a positive floor on `B`, or by
the clamp when `B` goes non-positive. Both are one line through `log`'s monotonicity, division-free.

Running the depth-≤1 shapes of `B` through these two gives a bound in every case **but one**:
`B = eml var (const q)` with `log q = 1`, where `B x = exp x − 1 → 0⁺` and `exp (t1 x) ≍ exp(α)/x`
runs away. One transcendental parameter value again. -/

/-- `B` bounded below by a positive constant ⟹ `exp (t1 x)` bounded. -/
theorem exp_const_left_bounded {α b₀ d : Real} {B : EMLTree}
    (hb₀ : 0 < b₀) (hB : ∀ x : Real, 0 < x → x ≤ d → b₀ ≤ B.eval x) :
    ∀ x : Real, 0 < x → x ≤ d →
      exp ((EMLTree.eml (EMLTree.const α) B).eval x) ≤ exp (exp α - log b₀) := by
  intro x hx hxd
  show exp (exp α - log (B.eval x)) ≤ exp (exp α - log b₀)
  refine exp_monotone ?_
  have hl : log b₀ ≤ log (B.eval x) := log_le_log hb₀ (hB x hx hxd)
  have s := add_le_add_wit (le_refl (exp α)) (neg_le_neg_wit hl)
  have l : exp α + -log (B.eval x) = exp α - log (B.eval x) := by
    mach_mpoly [exp α, log (B.eval x)]
  have r : exp α + -log b₀ = exp α - log b₀ := by mach_mpoly [exp α, log b₀]
  rw [l, r] at s; exact s

/-- `B` non-positive ⟹ the totalised `log` clamps and `exp (t1 x)` is the *constant* `exp (exp α)`.
The clamp bounding rather than blocking, for the fourth time in this arm. -/
theorem exp_const_left_bounded_clamped {α d : Real} {B : EMLTree}
    (hB : ∀ x : Real, 0 < x → x ≤ d → B.eval x ≤ 0) :
    ∀ x : Real, 0 < x → x ≤ d →
      exp ((EMLTree.eml (EMLTree.const α) B).eval x) ≤ exp (exp α) := by
  intro x hx hxd
  show exp (exp α - log (B.eval x)) ≤ exp (exp α)
  rw [log_nonpos (hB x hx hxd)]
  have e : exp α - (0 : Real) = exp α := by mach_ring
  rw [e]; exact le_refl _

/-- The quadratic core, likewise generalised: `leaf_var_quad_arith` is this at `W = exp 1`. Needed
because the leaf-`var` branch's coincidence loci (the Ω-point) admit only a **quadratic** floor, so a
port that carried the linear core alone would stall in exactly the hard cases. -/
theorem bounded_left_quad_arith {t v w Cl W : Real} (ht4 : (1 + 1 + 1 + 1 : Real) ≤ t)
    (hpin : exp (-t) * v = exp (-t) * w - 1)
    (hLv : Cl - (t + t) ≤ v) (hw : w ≤ W) (hbig : W - Cl < t) : False := by
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
  have hstep : exp t ≤ W - Cl + (t + t) := by
    have s1 : Cl - (t + t) ≤ W - exp t := by
      have s := add_le_add_wit hw (le_refl (-exp t))
      have e1 : w + -exp t = w - exp t := by mach_ring
      have e2 : W + -exp t = W - exp t := by mach_ring
      rw [e1, e2] at s
      exact le_trans hLv s
    have s := add_le_add_left s1 (exp t - Cl + (t + t))
    have e1 : exp t - Cl + (t + t) + (Cl - (t + t)) = exp t := by
      mach_mpoly [exp t, Cl, t]
    have e2 : exp t - Cl + (t + t) + (W - exp t) = W - Cl + (t + t) := by
      mach_mpoly [exp t, W, Cl, t]
    rw [e1, e2] at s
    exact s
  have h3t : t + t + t ≤ exp t := exp_ge_three_mul ht4
  have hfin : t ≤ W - Cl := by
    have s := le_trans h3t hstep
    have u := add_le_add_left s (-(t + t))
    have e1 : -(t + t) + (t + t + t) = t := by mach_mpoly [t]
    have e2 : -(t + t) + (W - Cl + (t + t)) = W - Cl := by mach_mpoly [W, Cl, t]
    rw [e1, e2] at u
    exact u
  exact lt_irrefl_ax _ (lt_of_lt_of_le hbig hfin)

/-- **A quadratic floor is fatal under a bounded left child too.** Completes the ported core: the
remaining depth-3 case now needs only the *shape* analysis of `t2`, with every arithmetic
obligation already discharged in the general form. -/
theorem bounded_left_quad_floor_absurd {t1 t2 : EMLTree} {C d W : Real} (hC : 0 < C)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hW : ∀ x : Real, 0 < x → x ≤ d → exp (t1.eval x) ≤ W)
    (hfloor : ∀ x : Real, 0 < x → x ≤ d → C * (x * x) ≤ t2.eval x)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x) : False := by
  have ht4 : (1 + 1 + 1 + 1 : Real)
      ≤ 1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d) := by
    have s := add_le_add_wit (add_le_add_wit (le_refl (1 + 1 + 1 + 1 : Real))
      (le_of_lt (exp_pos (W - log C)))) (le_of_lt (exp_pos (-log d)))
    have e : (1 + 1 + 1 + 1 : Real) + 0 + 0 = 1 + 1 + 1 + 1 := by mach_ring
    rw [e] at s; exact s
  have hx0 : (0 : Real)
      < exp (-(1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d))) := exp_pos _
  have hxd : exp (-(1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d))) ≤ d := by
    have hge : -log d ≤ 1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d) := by
      have h1 := le_of_lt (exp_grows_strictly_thm (-log d))
      have s := add_le_add_wit (add_le_add_wit
        (le_of_lt (add_pos (add_pos (add_pos one_pos one_pos) one_pos) one_pos))
        (le_of_lt (exp_pos (W - log C)))) (le_refl (exp (-log d)))
      have e : (0 : Real) + 0 + exp (-log d) = exp (-log d) := by mach_ring
      rw [e] at s
      exact le_trans h1 s
    have hstep : -(1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d)) ≤ log d := by
      have s := neg_le_neg_wit hge
      have e : -(-log d) = log d := by mach_ring
      rw [e] at s
      exact s
    have hh := exp_monotone hstep
    rw [exp_log hd] at hh
    exact hh
  refine bounded_left_quad_arith
    (t := 1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d))
    (v := log (t2.eval (exp (-(1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d))))))
    (w := exp (t1.eval (exp (-(1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d))))))
    (Cl := log C) (W := W) ht4 ?_ ?_ ?_ ?_
  · exact depth3_pin h _ hx0
  · have hsq : (0 : Real)
        < exp (-(1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d)))
          * exp (-(1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d))) := mul_pos hx0 hx0
    have hCx : (0 : Real) < C * (exp (-(1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d)))
        * exp (-(1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d)))) := mul_pos hC hsq
    have hl := log_le_log hCx (hfloor _ hx0 hxd)
    rw [log_mul hC hsq, log_mul hx0 hx0, log_exp] at hl
    have e : log C + (-(1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d))
        + -(1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d)))
        = log C - ((1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d))
          + (1 + 1 + 1 + 1 + exp (W - log C) + exp (-log d))) := by
      mach_mpoly [log C, exp (W - log C), exp (-log d)]
    rw [e] at hl
    exact hl
  · exact hW _ hx0 hxd
  · have h1 := exp_grows_strictly_thm (W - log C)
    have s := add_le_add_wit (add_le_add_wit
      (le_of_lt (add_pos (add_pos (add_pos one_pos one_pos) one_pos) one_pos))
      (le_refl (exp (W - log C)))) (le_of_lt (exp_pos (-log d)))
    have e : (0 : Real) + exp (W - log C) + 0 = exp (W - log C) := by mach_ring
    rw [e] at s
    exact lt_of_lt_of_le h1 s

/-! ## ▸ **Decay by depth, base case: a POSITIVE depth-≤1 tree has a linear floor**

The theorem family both open items point at. `LogSafe`'s removal wants *how fast can a positive
depth-≤j term approach 0*, and the last depth-3 case wants the same at depth 2. This is the rung-1
base, and it is sharp: the only shape whose value actually reaches `0` at the origin is
`eml var (const q)` at `log q = 1`, where `t x = exp x − 1 ≥ x` — **linear, and no quadratic
correction is needed at this depth.** The quadratic case appears only one rung up.

Positivity is a *hypothesis* here, not something derived from a pin — which is exactly what makes
the statement reusable, and what the leaf-`var` branch could not do because its floors were
entangled with its own equation. -/
theorem depth_le_one_positive_floor (t : EMLTree) (ht : t.depth ≤ 1) {d : Real}
    (hd : 0 < d) (hd1 : d ≤ 1) (hpos : ∀ x : Real, 0 < x → x ≤ d → 0 < t.eval x) :
    ∃ K d' : Real, 0 < K ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' → K * x ≤ t.eval x := by
  -- a constant-valued tree: its own value is the floor, since `x ≤ 1`
  have hconst : ∀ v : Real, 0 < v → ∀ x : Real, 0 < x → x ≤ d → v * x ≤ v := by
    intro v hv x _ hxd
    have hx1 : x ≤ 1 := le_trans hxd hd1
    have s := mul_le_mul_of_nonneg_left hx1 (le_of_lt hv)
    have e : v * (1 : Real) = v := by mach_mpoly [v]
    rw [e] at s; exact s
  -- `x ≤ exp x − 1`, the linear floor at the one shape that reaches `0`
  have hxu : ∀ x : Real, x ≤ exp x - 1 := by
    intro x
    have t := one_add_le_exp x
    have u := add_le_add_wit t (le_refl (-1 : Real))
    have l : (1 : Real) + x + -1 = x := by mach_mpoly [x]
    have r : exp x + -1 = exp x - 1 := by mach_mpoly [exp x]
    rw [l, r] at u; exact u
  have hnl : ∀ x : Real, 0 < x → x ≤ d → log x ≤ 0 := by
    intro x hx hxd
    exact log_nonpos_of_le_one hx (le_trans hxd hd1)
  cases t with
  | const c =>
      refine ⟨c, d, hpos d hd (le_refl d), hd, le_refl d, fun x hx hxd => ?_⟩
      exact hconst c (hpos d hd (le_refl d)) x hx hxd
  | var =>
      refine ⟨1, d, one_pos, hd, le_refl d, fun x _ _ => ?_⟩
      show (1 : Real) * x ≤ x
      have e : (1 : Real) * x = x := by mach_mpoly [x]
      rw [e]; exact le_refl _
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd ht (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd ht (by simp only [EMLTree.depth]; omega)
          | const q =>
              refine ⟨exp p - log q, d, hpos d hd (le_refl d), hd, le_refl d,
                fun x hx hxd => ?_⟩
              exact hconst _ (hpos d hd (le_refl d)) x hx hxd
          | var =>
              -- `exp p − log x ≥ exp p` on `(0,1]`, so the constant `exp p` is a floor
              refine ⟨exp p, d, exp_pos p, hd, le_refl d, fun x hx hxd => ?_⟩
              show exp p * x ≤ exp p - log x
              refine le_trans (hconst (exp p) (exp_pos p) x hx hxd) ?_
              have s := add_le_add_wit (le_refl (exp p)) (neg_le_neg_wit (hnl x hx hxd))
              have l : exp p + -(0 : Real) = exp p := by mach_ring
              have r : exp p + -log x = exp p - log x := by mach_mpoly [exp p, log x]
              rw [l, r] at s; exact s
      | var =>
          cases b with
          | eml _ _ => exact absurd ht (by simp only [EMLTree.depth]; omega)
          | const q =>
              -- `exp x − log q`: positivity forces `log q ≤ 1`, and then `≥ exp x − 1 ≥ x`
              have hL : log q ≤ 1 := by
                rcases lt_total (log q) 1 with hp | hz | hn
                · exact le_of_lt hp
                · exact le_of_eq hz
                · exfalso
                  obtain ⟨w, hwpos, hwd, hwL⟩ :=
                    two_bound_witness' hd (log_pos_of_one_lt hn)
                  have hlt : exp w < log q := by
                    have s := exp_lt hwL
                    rwa [exp_log (lt_trans_ax one_pos hn)] at s
                  have hneg : exp w - log q < 0 := by
                    have s := add_lt_add_left hlt (-log q)
                    have l : -log q + exp w = exp w - log q := by
                      mach_mpoly [exp w, log q]
                    have r : -log q + log q = (0 : Real) := by mach_ring
                    rw [l, r] at s; exact s
                  exact lt_irrefl_ax _
                    (lt_trans_ax (hpos w hwpos (le_of_lt hwd)) hneg)
              refine ⟨1, d, one_pos, hd, le_refl d, fun x _ _ => ?_⟩
              show (1 : Real) * x ≤ exp x - log q
              have e : (1 : Real) * x = x := by mach_mpoly [x]
              rw [e]
              refine le_trans (hxu x) ?_
              have s := add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit hL)
              have l : exp x + -(1 : Real) = exp x - 1 := by mach_mpoly [exp x]
              have r : exp x + -log q = exp x - log q := by mach_mpoly [exp x, log q]
              rw [l, r] at s; exact s
          | var =>
              -- `exp x − log x ≥ 2 ≥ x` on `(0,1]`
              refine ⟨1, d, one_pos, hd, le_refl d, fun x hx hxd => ?_⟩
              show (1 : Real) * x ≤ exp x - log x
              have e : (1 : Real) * x = x := by mach_mpoly [x]
              rw [e]
              have s := add_le_add_wit (le_of_lt (exp_grows_strictly_thm x))
                (neg_le_neg_wit (hnl x hx hxd))
              have l : x + -(0 : Real) = x := by mach_ring
              have r : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
              rw [l, r] at s; exact s

/-! ### The shifted base rung — clearing a constant, not just zero

`depth_le_one_positive_floor` asks the tree to clear `0`. Rung 2 needs it to clear a *constant*:
`t = eml A B` with `B` constant-valued is `exp (A x) − c_B`, positive exactly when `A x` clears
`log c_B`.

Two shapes need a **smaller cutoff** than the one they are handed, which the unshifted version did
not: `exp p − log x` and `exp x − log x` clear any constant, but only once `−log x` has grown past
it. That is why this returns its own `d'`. -/
theorem depth_le_one_shifted_floor (t : EMLTree) (ht : t.depth ≤ 1) (c : Real) {d : Real}
    (hd : 0 < d) (hd1 : d ≤ 1) (hpos : ∀ x : Real, 0 < x → x ≤ d → c < t.eval x) :
    ∃ K d' : Real, 0 < K ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' → K * x ≤ t.eval x - c := by
  have hconst : ∀ v : Real, 0 < v → ∀ x : Real, 0 < x → x ≤ d → v * x ≤ v := by
    intro v hv x _ hxd
    have s := mul_le_mul_of_nonneg_left (le_trans hxd hd1) (le_of_lt hv)
    have e : v * (1 : Real) = v := by mach_mpoly [v]
    rw [e] at s; exact s
  have hsub : ∀ v : Real, c < v → (0 : Real) < v - c := by
    intro v hv
    have s := add_lt_add_left hv (-c)
    have l : -c + c = (0 : Real) := by mach_ring
    have r : -c + v = v - c := by mach_mpoly [v, c]
    rw [l, r] at s; exact s
  -- "wait for `−log x` to grow past `z`": below `exp (−z)` it has
  have hlogbig : ∀ z w x : Real, 0 < x → x ≤ w → w < exp (-z) → z ≤ -log x := by
    intro z w x hx hxw hwz
    have h1 : x < exp (-z) := lt_of_le_of_lt hxw hwz
    have h2 : log x < -z := by
      have s := log_lt_log_strict hx h1
      rwa [log_exp] at s
    have s := add_lt_add_left h2 (-log x + z)
    have l : -log x + z + log x = z := by mach_mpoly [log x, z]
    have r : -log x + z + -z = -log x := by mach_mpoly [log x, z]
    rw [l, r] at s
    exact le_of_lt s
  cases t with
  | const v =>
      refine ⟨v - c, d, hsub v (hpos d hd (le_refl d)), hd, le_refl d, fun x hx hxd => ?_⟩
      exact hconst _ (hsub v (hpos d hd (le_refl d))) x hx hxd
  | var =>
      -- `c < x` on all of `(0,d]` forces `c ≤ 0`
      have hc : c ≤ 0 := by
        rcases lt_total c 0 with hp | hz | hn
        · exact le_of_lt hp
        · exact le_of_eq hz
        · exfalso
          obtain ⟨w, hwpos, hwd, hwc⟩ := two_bound_witness' hd hn
          exact lt_irrefl_ax _ (lt_trans_ax (hpos w hwpos (le_of_lt hwd)) hwc)
      refine ⟨1, d, one_pos, hd, le_refl d, fun x _ _ => ?_⟩
      show (1 : Real) * x ≤ x - c
      have s := add_le_add_wit (le_refl x) (neg_le_neg_wit hc)
      have l : x + -(0 : Real) = 1 * x := by mach_mpoly [x]
      have r : x + -c = x - c := by mach_mpoly [x, c]
      rw [l, r] at s; exact s
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd ht (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd ht (by simp only [EMLTree.depth]; omega)
          | const q =>
              refine ⟨exp p - log q - c, d, hsub _ (hpos d hd (le_refl d)), hd, le_refl d,
                fun x hx hxd => ?_⟩
              exact hconst _ (hsub _ (hpos d hd (le_refl d))) x hx hxd
          | var =>
              obtain ⟨w, hwpos, hwd, hwe⟩ :=
                two_bound_witness' hd (exp_pos (exp p - c - 1))
              refine ⟨1, w, one_pos, hwpos, le_of_lt hwd, fun x hx hxw => ?_⟩
              show (1 : Real) * x ≤ exp p - log x - c
              have hz : 1 + c - exp p ≤ -log x := by
                refine hlogbig _ w x hx hxw ?_
                have e : -(1 + c - exp p) = exp p - c - 1 := by mach_mpoly [c, exp p]
                rw [e]; exact hwe
              have hx1 : x ≤ 1 := le_trans hxw (le_trans (le_of_lt hwd) hd1)
              have hge : (1 : Real) ≤ exp p - log x - c := by
                have s := add_le_add_wit (le_refl (exp p - c)) hz
                have l : exp p - c + (1 + c - exp p) = 1 := by mach_mpoly [exp p, c]
                have r : exp p - c + -log x = exp p - log x - c := by
                  mach_mpoly [exp p, c, log x]
                rw [l, r] at s; exact s
              have e : (1 : Real) * x = x := by mach_mpoly [x]
              rw [e]
              exact le_trans hx1 hge
      | var =>
          cases b with
          | eml _ _ => exact absurd ht (by simp only [EMLTree.depth]; omega)
          | const q =>
              -- positivity forces `log q + c ≤ 1`, then `exp x − log q − c ≥ exp x − 1 ≥ x`
              have hL : log q + c ≤ 1 := by
                rcases lt_total (log q + c) 1 with hp | hz | hn
                · exact le_of_lt hp
                · exact le_of_eq hz
                · exfalso
                  obtain ⟨w, hwpos, hwd, hwL⟩ :=
                    two_bound_witness' hd (log_pos_of_one_lt hn)
                  have hlt : exp w < log q + c := by
                    have s := exp_lt hwL
                    rwa [exp_log (lt_trans_ax one_pos hn)] at s
                  have hcc : exp w - log q < c := by
                    have s := add_lt_add_left hlt (-log q)
                    have l : -log q + exp w = exp w - log q := by
                      mach_mpoly [exp w, log q]
                    have r : -log q + (log q + c) = c := by mach_mpoly [log q, c]
                    rw [l, r] at s; exact s
                  exact lt_irrefl_ax _
                    (lt_trans_ax (hpos w hwpos (le_of_lt hwd)) hcc)
              refine ⟨1, d, one_pos, hd, le_refl d, fun x _ _ => ?_⟩
              show (1 : Real) * x ≤ exp x - log q - c
              have e : (1 : Real) * x = x := by mach_mpoly [x]
              rw [e]
              have hxu : x ≤ exp x - 1 := by
                have tt := one_add_le_exp x
                have u := add_le_add_wit tt (le_refl (-1 : Real))
                have l : (1 : Real) + x + -1 = x := by mach_mpoly [x]
                have r : exp x + -1 = exp x - 1 := by mach_mpoly [exp x]
                rw [l, r] at u; exact u
              refine le_trans hxu ?_
              have s := add_le_add_wit (le_refl (exp x)) (neg_le_neg_wit hL)
              have l : exp x + -(1 : Real) = exp x - 1 := by mach_mpoly [exp x]
              have r : exp x + -(log q + c) = exp x - log q - c := by
                mach_mpoly [exp x, log q, c]
              rw [l, r] at s; exact s
          | var =>
              obtain ⟨w, hwpos, hwd, hwe⟩ := two_bound_witness' hd (exp_pos (-c))
              refine ⟨1, w, one_pos, hwpos, le_of_lt hwd, fun x hx hxw => ?_⟩
              show (1 : Real) * x ≤ exp x - log x - c
              have hz : c ≤ -log x := hlogbig _ w x hx hxw hwe
              have hx1 : x ≤ 1 := le_trans hxw (le_trans (le_of_lt hwd) hd1)
              have e : (1 : Real) * x = x := by mach_mpoly [x]
              rw [e]
              have s := add_le_add_wit (one_le_exp (le_of_lt hx)) hz
              have r : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
              rw [r] at s
              have u := add_le_add_wit s (le_refl (-c))
              have l2 : (1 : Real) + c + -c = 1 := by mach_mpoly [c]
              have r2 : exp x - log x + -c = exp x - log x - c := by
                mach_mpoly [exp x, log x, c]
              rw [l2, r2] at u
              exact le_trans hx1 u

/-- # ▸ **Rung 2 for a constant-valued right child: the floor is LINEAR.**

`t = eml A B` with `B ≡ β`. Positivity says `exp (A x)` clears `log β`, so the shifted base rung
gives `A x ≥ log (log β) + K·x`, and exponentiating turns that into
`exp (A x) ≥ log β · exp (K x) ≥ log β + (log β · K) · x`.

> **No quadratic correction appears.** That matches the leaf-`var` branch from the other side: the
> quadratic showed up only once the `log` term *moved*. A constant right child cannot produce the
> second-order cancellation, and this is the proof of that, not an observation about it. -/
theorem depth_le_two_const_right_floor {A B : EMLTree} {β d : Real}
    (hA : A.depth ≤ 1) (hβ : ∀ x : Real, 0 < x → B.eval x = β)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hpos : ∀ x : Real, 0 < x → x ≤ d → 0 < (EMLTree.eml A B).eval x) :
    ∃ K d' : Real, 0 < K ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' → K * x ≤ (EMLTree.eml A B).eval x := by
  have hval : ∀ x : Real, 0 < x → (EMLTree.eml A B).eval x = exp (A.eval x) - log β := by
    intro x hx
    show exp (A.eval x) - log (B.eval x) = exp (A.eval x) - log β
    rw [hβ x hx]
  rcases lt_total 0 (log β) with hb | hb | hb
  · -- `log β > 0`: the shifted rung applies at `c := log (log β)`
    have hclear : ∀ x : Real, 0 < x → x ≤ d → log (log β) < A.eval x := by
      intro x hx hxd
      have h1 : log β < exp (A.eval x) := by
        have s := hpos x hx hxd
        rw [hval x hx] at s
        have u := add_lt_add_left s (log β)
        have l : log β + (0 : Real) = log β := by mach_ring
        have r : log β + (exp (A.eval x) - log β) = exp (A.eval x) := by
          mach_mpoly [log β, exp (A.eval x)]
        rw [l, r] at u; exact u
      have s := log_lt_log_strict hb h1
      rwa [log_exp] at s
    obtain ⟨K, d', hK, hd'0, hd'd, hfl⟩ :=
      depth_le_one_shifted_floor A hA (log (log β)) hd hd1 hclear
    refine ⟨log β * K, d', mul_pos hb hK, hd'0, hd'd, fun x hx hxd => ?_⟩
    rw [hval x hx]
    -- `A x ≥ log (log β) + K x` ⟹ `exp (A x) ≥ log β · (1 + K x)`
    have hAx : log (log β) + K * x ≤ A.eval x := by
      have s := add_le_add_wit (hfl x hx hxd) (le_refl (log (log β)))
      have l : K * x + log (log β) = log (log β) + K * x := by
        mach_mpoly [K, x, log (log β)]
      have r : A.eval x - log (log β) + log (log β) = A.eval x := by
        mach_mpoly [A.eval x, log (log β)]
      rw [l, r] at s; exact s
    have hexp : exp (log (log β) + K * x) ≤ exp (A.eval x) := exp_monotone hAx
    have hsplit : exp (log (log β) + K * x) = log β * exp (K * x) := by
      rw [exp_add, exp_log hb]
    rw [hsplit] at hexp
    have hlin : log β * (1 + K * x) ≤ log β * exp (K * x) :=
      mul_le_mul_of_nonneg_left (one_add_le_exp (K * x)) (le_of_lt hb)
    have s := le_trans hlin hexp
    have u := add_le_add_wit s (le_refl (-log β))
    have l : log β * (1 + K * x) + -log β = log β * K * x := by
      mach_mpoly [log β, K, x]
    have r : exp (A.eval x) + -log β = exp (A.eval x) - log β := by
      mach_mpoly [exp (A.eval x), log β]
    rw [l, r] at u; exact u
  · -- `log β = 0`: the tree IS `exp (A x)`, bounded below by `exp m`
    obtain ⟨m, hm⟩ := depth_le_one_lower_bound A hA
    refine ⟨exp m, d, exp_pos m, hd, le_refl d, fun x hx hxd => ?_⟩
    rw [hval x hx, ← hb]
    have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
    rw [e]
    have hx1 : x ≤ 1 := le_trans hxd hd1
    have s := mul_le_mul_of_nonneg_left hx1 (le_of_lt (exp_pos m))
    have e2 : exp m * (1 : Real) = exp m := by mach_mpoly [exp m]
    rw [e2] at s
    exact le_trans s (exp_monotone (hm x hx hx1))
  · -- `log β < 0`: the subtracted term HELPS, so `exp m` is still a floor
    obtain ⟨m, hm⟩ := depth_le_one_lower_bound A hA
    refine ⟨exp m, d, exp_pos m, hd, le_refl d, fun x hx hxd => ?_⟩
    rw [hval x hx]
    have hx1 : x ≤ 1 := le_trans hxd hd1
    have s := mul_le_mul_of_nonneg_left hx1 (le_of_lt (exp_pos m))
    have e2 : exp m * (1 : Real) = exp m := by mach_mpoly [exp m]
    rw [e2] at s
    refine le_trans s (le_trans (exp_monotone (hm x hx hx1)) ?_)
    have u := add_le_add_wit (le_refl (exp (A.eval x))) (neg_le_neg_wit (le_of_lt hb))
    have l : exp (A.eval x) + -(0 : Real) = exp (A.eval x) := by mach_ring
    have r : exp (A.eval x) + -log β = exp (A.eval x) - log β := by
      mach_mpoly [exp (A.eval x), log β]
    rw [l, r] at u; exact u

/-- **`exp` clears any additive constant, eventually — on a whole ray, not at one point.**
`exp_beats_linear` names a single point; a *floor* needs the inequality to hold throughout, which is
what this supplies. `exp_ge_three_mul` does the work: past `4`, `exp v ≥ 3v = v + 2v`, and `2v`
outgrows a fixed `β` as soon as `v ≥ β`. -/
theorem exp_ge_add_const (β : Real) :
    ∀ v : Real, 1 + 1 + 1 + 1 + exp β ≤ v → v + β ≤ exp v := by
  intro v hv
  have h4 : (1 + 1 + 1 + 1 : Real) ≤ v := by
    have s := add_le_add_wit (le_refl (1 + 1 + 1 + 1 : Real)) (le_of_lt (exp_pos β))
    have e : (1 + 1 + 1 + 1 : Real) + 0 = 1 + 1 + 1 + 1 := by mach_ring
    rw [e] at s; exact le_trans s hv
  have hβv : β ≤ v := by
    have s := add_le_add_wit
      (le_of_lt (add_pos (add_pos (add_pos one_pos one_pos) one_pos) one_pos))
      (le_of_lt (exp_grows_strictly_thm β))
    have e : (0 : Real) + β = β := by mach_ring
    rw [e] at s
    exact le_trans s hv
  have h3 := exp_ge_three_mul h4
  refine le_trans ?_ h3
  have s := add_le_add_wit (le_refl (v + v)) hβv
  have l : v + v + β = v + β + v := by mach_mpoly [v, β]
  have r : v + v + v = v + v + v := rfl
  rw [l] at s
  -- `v + β ≤ v + β + v`? no: use `v + β + 0 ≤ v + β + v` via `0 ≤ v`
  have hv0 : (0 : Real) ≤ v := le_trans (le_of_lt (add_pos (add_pos (add_pos one_pos one_pos)
    one_pos) one_pos)) h4
  have u := add_le_add_wit (le_refl (v + β)) hv0
  have l2 : v + β + (0 : Real) = v + β := by mach_mpoly [v, β]
  rw [l2] at u
  exact le_trans u s

/-- **Rung 2, moving right child, the `B = var` shape.** `log (B x) = log x → −∞`, so the subtracted
term *adds* and the tree is above `1` past `exp (−1)` — a constant floor, and positivity is not even
needed. The easy end of the moving case. -/
theorem depth_le_two_var_right_floor {A : EMLTree} :
    ∀ x : Real, 0 < x → x ≤ exp (-1) →
      (1 : Real) * x ≤ (EMLTree.eml A EMLTree.var).eval x := by
  intro x hx hxd
  show (1 : Real) * x ≤ exp (A.eval x) - log x
  have hx1 : x ≤ 1 := le_trans hxd (le_of_lt exp_neg_one_lt_one)
  have e : (1 : Real) * x = x := by mach_mpoly [x]
  rw [e]
  -- `−log x ≥ 1` below `exp (−1)`
  have hlog : (1 : Real) ≤ -log x := by
    have h1 : log x ≤ -1 := by
      have s := log_le_log hx hxd
      rwa [log_exp] at s
    have s := neg_le_neg_wit h1
    have el : -(-1 : Real) = 1 := by mach_ring
    rw [el] at s; exact s
  have s := add_le_add_wit (le_of_lt (exp_pos (A.eval x))) hlog
  have l : (0 : Real) + 1 = 1 := by mach_ring
  have r : exp (A.eval x) + -log x = exp (A.eval x) - log x := by
    mach_mpoly [exp (A.eval x), log x]
  rw [l, r] at s
  exact le_trans hx1 s

/-- # ▸ **Rung 2 when the LEFT child diverges: a floor, for every right child at once.**

Setting out to close the "`B → +∞`" row showed the hypothesis that actually does the work is about
`A`, not `B`: once `A x ≥ c₀ − log x`, the `log` ceiling
(`depth_le_one_log_upper_near_zero`, valid for *any* depth-≤1 `B`) is outrun and the tree sits above
`1`. So this one theorem covers every right child, and the `B`-shape split is only needed when `A`
stays bounded.

In `u := −log x` the estimate is `exp (c₀ + u) − N − u ≥ 1`, which is exactly the ray form
`exp_ge_add_const` was built for — the point version would have given a contradiction, not a
floor. -/
theorem depth_le_two_diverging_left_floor {A B : EMLTree} {c₀ d : Real}
    (hB : B.depth ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (hAlow : ∀ x : Real, 0 < x → x ≤ d → c₀ - log x ≤ A.eval x) :
    ∃ K d' : Real, 0 < K ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' → K * x ≤ (EMLTree.eml A B).eval x := by
  obtain ⟨N, δ, hδ0, hδ1, hN⟩ := depth_le_one_log_upper_near_zero B hB
  -- cut below `d`, below `δ`, and far enough out that `exp` has cleared the constant
  obtain ⟨w, hwpos, hwd, hwδ⟩ := two_bound_witness' hd hδ0
  obtain ⟨w2, hw2pos, hw2w, hw2e⟩ :=
    two_bound_witness' hwpos
      (exp_pos (c₀ - (1 + 1 + 1 + 1) - exp (N + 1 - c₀)))
  refine ⟨1, w2, one_pos, hw2pos, le_trans (le_of_lt hw2w) (le_of_lt hwd),
    fun x hx hxw => ?_⟩
  have hxw' : x ≤ w := le_trans hxw (le_of_lt hw2w)
  have hxd : x ≤ d := le_trans hxw' (le_of_lt hwd)
  have hxδ : x ≤ δ := le_trans hxw' (le_of_lt hwδ)
  have hx1 : x ≤ 1 := le_trans hxd hd1
  -- `c₀ − log x` is past the ray's threshold
  have hfar : (1 + 1 + 1 + 1 : Real) + exp (N + 1 - c₀) ≤ c₀ - log x := by
    have hlt : x < exp (c₀ - (1 + 1 + 1 + 1) - exp (N + 1 - c₀)) :=
      lt_of_le_of_lt hxw hw2e
    have hlog : log x < c₀ - (1 + 1 + 1 + 1) - exp (N + 1 - c₀) := by
      have s := log_lt_log_strict hx hlt
      rwa [log_exp] at s
    have s := add_lt_add_left hlog ((1 + 1 + 1 + 1 : Real) + exp (N + 1 - c₀) - log x)
    have l : (1 + 1 + 1 + 1 : Real) + exp (N + 1 - c₀) - log x + log x
        = (1 + 1 + 1 + 1 : Real) + exp (N + 1 - c₀) := by
      mach_mpoly [exp (N + 1 - c₀), log x]
    have r : (1 + 1 + 1 + 1 : Real) + exp (N + 1 - c₀) - log x
          + (c₀ - (1 + 1 + 1 + 1) - exp (N + 1 - c₀))
        = c₀ - log x := by
      mach_mpoly [exp (N + 1 - c₀), log x, c₀]
    rw [l, r] at s
    exact le_of_lt s
  -- the ray bound, then the log ceiling
  have hray := exp_ge_add_const (N + 1 - c₀) (c₀ - log x) hfar
  have hAx : exp (c₀ - log x) ≤ exp (A.eval x) := exp_monotone (hAlow x hx hxd)
  have hlogB : log (B.eval x) ≤ N - log x := hN x hx hxδ
  have hge : (1 : Real) ≤ (EMLTree.eml A B).eval x := by
    show (1 : Real) ≤ exp (A.eval x) - log (B.eval x)
    have s := add_le_add_wit (le_trans hray hAx) (neg_le_neg_wit hlogB)
    have l : c₀ - log x + (N + 1 - c₀) + -(N - log x) = 1 := by
      mach_mpoly [c₀, log x, N]
    have r : exp (A.eval x) + -log (B.eval x) = exp (A.eval x) - log (B.eval x) := by
      mach_mpoly [exp (A.eval x), log (B.eval x)]
    rw [l, r] at s; exact s
  have e : (1 : Real) * x = x := by mach_mpoly [x]
  rw [e]
  exact le_trans hx1 hge

/-- `A = eml (const p) var` supplies the divergence hypothesis with `c₀ = exp p`, exactly. -/
theorem depth_le_two_const_var_left_floor {p d : Real} {B : EMLTree}
    (hB : B.depth ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ K d' : Real, 0 < K ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' →
        K * x ≤ (EMLTree.eml (EMLTree.eml (EMLTree.const p) EMLTree.var) B).eval x :=
  depth_le_two_diverging_left_floor (c₀ := exp p) hB hd hd1 (fun _ _ _ => le_refl _)

/-- `A = eml var var` supplies it with `c₀ = 1`, since `exp x ≥ 1` on the positives. -/
theorem depth_le_two_var_var_left_floor {d : Real} {B : EMLTree}
    (hB : B.depth ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ K d' : Real, 0 < K ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' →
        K * x ≤ (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) B).eval x := by
  refine depth_le_two_diverging_left_floor (c₀ := 1) hB hd hd1 (fun x hx _ => ?_)
  show (1 : Real) - log x ≤ exp x - log x
  have s := add_le_add_wit (one_le_exp (le_of_lt hx)) (le_refl (-log x))
  have l : (1 : Real) + -log x = 1 - log x := by mach_mpoly [log x]
  have r : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
  rw [l, r] at s; exact s

/-- **Rung 2's fourth row: a bounded left child cannot survive a diverging right child.**

If `exp (A x) ≤ W` while `B x ≥ −log x`, then `log (B x)` climbs past `W` and the tree goes
*negative* — so the positivity hypothesis is contradicted outright and no floor question arises.
The point where it happens is named: below `exp (−exp W)`, since there `−log x > exp W` and `log` of
that already exceeds `W`.

Note the double `log` in the threshold. `B` diverges only like `−log x`, so `log (B x)` diverges
like `log (−log x)` — the slowest divergence in this grammar, and the reason the cutoff is a tower
of two rather than one. -/
theorem depth_le_two_bounded_left_diverging_right_absurd {A B : EMLTree} {W d : Real}
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hW : ∀ x : Real, 0 < x → x ≤ d → exp (A.eval x) ≤ W)
    (hBlow : ∀ x : Real, 0 < x → x ≤ d → -log x ≤ B.eval x)
    (hpos : ∀ x : Real, 0 < x → x ≤ d → 0 < (EMLTree.eml A B).eval x) : False := by
  obtain ⟨w, hwpos, hwd, hwe⟩ := two_bound_witness' hd (exp_pos (-exp W))
  -- `−log w > exp W`
  have hlogw : exp W < -log w := by
    have hlt : w < exp (-exp W) := hwe
    have hlog : log w < -exp W := by
      have s := log_lt_log_strict hwpos hlt
      rwa [log_exp] at s
    have s := add_lt_add_left hlog (exp W - log w)
    have l : exp W - log w + log w = exp W := by mach_mpoly [exp W, log w]
    have r : exp W - log w + -exp W = -log w := by mach_mpoly [exp W, log w]
    rw [l, r] at s; exact s
  -- `W < log (B w)`
  have hWlt : W < log (B.eval w) := by
    have h1 : log (exp W) < log (-log w) :=
      log_lt_log_strict (exp_pos W) hlogw
    rw [log_exp] at h1
    have h2 : log (-log w) ≤ log (B.eval w) :=
      log_le_log (lt_trans_ax (exp_pos W) hlogw) (hBlow w hwpos (le_of_lt hwd))
    exact lt_of_lt_of_le h1 h2
  -- so the tree is negative at `w`
  have hneg : (EMLTree.eml A B).eval w < 0 := by
    show exp (A.eval w) - log (B.eval w) < 0
    have hle : exp (A.eval w) < log (B.eval w) :=
      lt_of_le_of_lt (hW w hwpos (le_of_lt hwd)) hWlt
    have s := add_lt_add_left hle (-log (B.eval w))
    have l : -log (B.eval w) + exp (A.eval w) = exp (A.eval w) - log (B.eval w) := by
      mach_mpoly [exp (A.eval w), log (B.eval w)]
    have r : -log (B.eval w) + log (B.eval w) = (0 : Real) := by mach_ring
    rw [l, r] at s; exact s
  exact lt_irrefl_ax _ (lt_trans_ax (hpos w hwpos (le_of_lt hwd)) hneg)

/-- `B = eml (const p) var` diverges at least as fast as `−log x`. -/
theorem eml_const_var_ge_neg_log {p : Real} :
    ∀ x : Real, 0 < x → -log x ≤ (EMLTree.eml (EMLTree.const p) EMLTree.var).eval x := by
  intro x _
  show -log x ≤ exp p - log x
  have s := add_le_add_wit (le_of_lt (exp_pos p)) (le_refl (-log x))
  have l : (0 : Real) + -log x = -log x := by mach_ring
  have r : exp p + -log x = exp p - log x := by mach_mpoly [exp p, log x]
  rw [l, r] at s; exact s

/-- `B = eml var var` likewise. -/
theorem eml_var_var_ge_neg_log :
    ∀ x : Real, 0 < x → -log x ≤ (EMLTree.eml EMLTree.var EMLTree.var).eval x := by
  intro x _
  show -log x ≤ exp x - log x
  have s := add_le_add_wit (le_of_lt (exp_pos x)) (le_refl (-log x))
  have l : (0 : Real) + -log x = -log x := by mach_ring
  have r : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
  rw [l, r] at s; exact s

/-- The `L ≤ 1` half: no clamp on `(0,d]`, so `x ↦ exp α − log (exp x − L)` is **non-increasing**
and its value at the right endpoint floors the whole interval. -/
theorem const_left_expvar_right_floor_nolclamp {A B : EMLTree} {α L d : Real}
    (hA : ∀ x : Real, 0 < x → A.eval x = α)
    (hB : ∀ x : Real, 0 < x → B.eval x = exp x - L)
    (hd : 0 < d) (hd1 : d ≤ 1) (hL : L ≤ 1)
    (hpos : ∀ x : Real, 0 < x → x ≤ d → 0 < (EMLTree.eml A B).eval x) :
    ∃ K d' : Real, 0 < K ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' → K * x ≤ (EMLTree.eml A B).eval x := by
  have hval : ∀ x : Real, 0 < x →
      (EMLTree.eml A B).eval x = exp α - log (exp x - L) := by
    intro x hx
    show exp (A.eval x) - log (B.eval x) = exp α - log (exp x - L)
    rw [hA x hx, hB x hx]
  -- `exp x − L > 0` on the positives, since `exp x > 1 ≥ L`
  have hBpos : ∀ x : Real, 0 < x → 0 < exp x - L := by
    intro x hx
    have h1 : (1 : Real) < exp x := by
      have t := exp_lt hx; rwa [exp_zero] at t
    have u := add_lt_add_left (lt_of_le_of_lt hL h1) (-L)
    have l : -L + L = (0 : Real) := by mach_ring
    have r : -L + exp x = exp x - L := by mach_mpoly [L, exp x]
    rw [l, r] at u; exact u
  refine ⟨(EMLTree.eml A B).eval d, d, hpos d hd (le_refl d), hd, le_refl d,
    fun x hx hxd => ?_⟩
  -- monotone: `log (exp x − L) ≤ log (exp d − L)`
  have hmono : (EMLTree.eml A B).eval d ≤ (EMLTree.eml A B).eval x := by
    rw [hval x hx, hval d hd]
    have hlog : log (exp x - L) ≤ log (exp d - L) := by
      refine log_le_log (hBpos x hx) ?_
      have s := add_le_add_wit (exp_monotone hxd) (le_refl (-L))
      have l : exp x + -L = exp x - L := by mach_mpoly [exp x, L]
      have r : exp d + -L = exp d - L := by mach_mpoly [exp d, L]
      rw [l, r] at s; exact s
    have s := add_le_add_wit (le_refl (exp α)) (neg_le_neg_wit hlog)
    have l : exp α + -log (exp d - L) = exp α - log (exp d - L) := by
      mach_mpoly [exp α, log (exp d - L)]
    have r : exp α + -log (exp x - L) = exp α - log (exp x - L) := by
      mach_mpoly [exp α, log (exp x - L)]
    rw [l, r] at s; exact s
  refine le_trans ?_ hmono
  have hx1 : x ≤ 1 := le_trans hxd hd1
  have s := mul_le_mul_of_nonneg_left hx1 (le_of_lt (hpos d hd (le_refl d)))
  have e : (EMLTree.eml A B).eval d * (1 : Real) = (EMLTree.eml A B).eval d := by
    mach_mpoly [(EMLTree.eml A B).eval d]
  rw [e] at s; exact s

/-- # ▸ **The last row, first sub-case: a constant-valued left child needs no `γ/κ` analysis.**

`t x = exp α − log (exp x − L)` is **non-increasing** — the right child rises, so subtracting its
log can only pull the tree down. Positivity at the *right endpoint* therefore floors the whole
interval, and the coincidence analysis never starts.

The clamp splits it and helps on both sides: for `L ≤ 1` there is no clamp and monotonicity runs;
for `L > 1` the tree is **outright constant** `exp α` below `log L`, which is a better floor still.
The same observation that closed the constant-`A` shapes of the leaf-`var` branch — there against
the pin's *increasing* direction, here against positivity. -/
theorem depth_le_two_const_left_expvar_right_floor {A B : EMLTree} {α L d : Real}
    (hA : ∀ x : Real, 0 < x → A.eval x = α)
    (hB : ∀ x : Real, 0 < x → B.eval x = exp x - L)
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hpos : ∀ x : Real, 0 < x → x ≤ d → 0 < (EMLTree.eml A B).eval x) :
    ∃ K d' : Real, 0 < K ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' → K * x ≤ (EMLTree.eml A B).eval x := by
  rcases lt_total 1 L with hL | hL | hL
  · -- `L > 1`: below `log L` the log is clamped and the tree is the constant `exp α`
    have hLpos : (0 : Real) < L := lt_trans_ax one_pos hL
    obtain ⟨w, hwpos, hwd, hwL⟩ := two_bound_witness' hd (log_pos_of_one_lt hL)
    refine ⟨exp α, w, exp_pos α, hwpos, le_of_lt hwd, fun x hx hxw => ?_⟩
    have hclamp : log (B.eval x) = 0 := by
      refine log_nonpos ?_
      rw [hB x hx]
      have hlt : exp x < L := by
        have s := exp_lt (lt_of_le_of_lt hxw hwL)
        rwa [exp_log hLpos] at s
      have u := add_le_add_wit (le_of_lt hlt) (le_refl (-L))
      have l : exp x + -L = exp x - L := by mach_mpoly [exp x, L]
      have r : L + -L = (0 : Real) := by mach_ring
      rw [l, r] at u; exact u
    show exp α * x ≤ exp (A.eval x) - log (B.eval x)
    rw [hA x hx, hclamp]
    have e : exp α - (0 : Real) = exp α := by mach_ring
    rw [e]
    have hx1 : x ≤ 1 := le_trans hxw (le_trans (le_of_lt hwd) hd1)
    have s := mul_le_mul_of_nonneg_left hx1 (le_of_lt (exp_pos α))
    have e2 : exp α * (1 : Real) = exp α := by mach_mpoly [exp α]
    rw [e2] at s; exact s
  · exact const_left_expvar_right_floor_nolclamp hA hB hd hd1 (le_of_eq hL.symm) hpos
  · exact const_left_expvar_right_floor_nolclamp hA hB hd hd1 (le_of_lt hL) hpos

/-! ### The last row's `L ≥ 1` regimes: constant floors, no `γ` needed

With `B x = exp x − L`, the parameter `L` decides whether the right child is bounded away from `0`
at the origin. Only `L < 1` leaves it bounded and *positive* — the divergent-cancellation regime
where `γ/κ` is unavoidable. The other two regimes give constant floors outright, and are recorded
here so the residue is exactly `L < 1`. -/

/-- `L > 1`: the right child is `≤ 0` below `log L`, the log clamps, and the tree is just
`exp (A x) ≥ G`. -/
theorem depth_le_two_expvar_right_clamped_floor {A B : EMLTree} {G L d : Real}
    (hG : 0 < G) (hL : 1 < L)
    (hB : ∀ x : Real, 0 < x → B.eval x = exp x - L)
    (hlow : ∀ x : Real, 0 < x → G * exp x ≤ exp (A.eval x))
    (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ K d' : Real, 0 < K ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' → K * x ≤ (EMLTree.eml A B).eval x := by
  have hLpos : (0 : Real) < L := lt_trans_ax one_pos hL
  obtain ⟨w, hwpos, hwd, hwL⟩ := two_bound_witness' hd (log_pos_of_one_lt hL)
  refine ⟨G, w, hG, hwpos, le_of_lt hwd, fun x hx hxw => ?_⟩
  have hclamp : log (B.eval x) = 0 := by
    refine log_nonpos ?_
    rw [hB x hx]
    have hlt : exp x < L := by
      have s := exp_lt (lt_of_le_of_lt hxw hwL)
      rwa [exp_log hLpos] at s
    have u := add_le_add_wit (le_of_lt hlt) (le_refl (-L))
    have l : exp x + -L = exp x - L := by mach_mpoly [exp x, L]
    have r : L + -L = (0 : Real) := by mach_ring
    rw [l, r] at u; exact u
  show G * x ≤ exp (A.eval x) - log (B.eval x)
  rw [hclamp]
  have e : exp (A.eval x) - (0 : Real) = exp (A.eval x) := by mach_ring
  rw [e]
  have hx1 : x ≤ 1 := le_trans hxw (le_trans (le_of_lt hwd) hd1)
  have s := mul_le_mul_of_nonneg_left hx1 (le_of_lt hG)
  have e2 : G * (1 : Real) = G := by mach_mpoly [G]
  rw [e2] at s
  refine le_trans s (le_trans ?_ (hlow x hx))
  have t := mul_le_mul_of_nonneg_left (one_le_exp (le_of_lt hx)) (le_of_lt hG)
  have e3 : G * (1 : Real) = G := by mach_mpoly [G]
  rw [e3] at t; exact t

/-- `L = 1`: the right child is `exp x − 1 → 0⁺`, so its log runs to `−∞` and the tree runs **up**.
`exp x − 1 ≤ x·e` turns that into `t x ≥ G − 1 − log x`, and past `exp (G − 2)` that clears `1`. -/
theorem depth_le_two_expvar_right_one_floor {A B : EMLTree} {G d : Real}
    (hG : 0 < G)
    (hB : ∀ x : Real, 0 < x → B.eval x = exp x - 1)
    (hlow : ∀ x : Real, 0 < x → G * exp x ≤ exp (A.eval x))
    (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ K d' : Real, 0 < K ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' → K * x ≤ (EMLTree.eml A B).eval x := by
  obtain ⟨w, hwpos, hwd, hwe⟩ := two_bound_witness' hd (exp_pos (G - (1 + 1)))
  refine ⟨1, w, one_pos, hwpos, le_of_lt hwd, fun x hx hxw => ?_⟩
  have hx1 : x ≤ 1 := le_trans hxw (le_trans (le_of_lt hwd) hd1)
  -- `log (exp x − 1) ≤ log x + 1`
  have hupos : (0 : Real) < exp x - 1 := by
    have s : (1 : Real) < exp x := by
      have t := exp_lt hx; rwa [exp_zero] at t
    have u := add_lt_add_left s (-1 : Real)
    have l : (-1 : Real) + 1 = 0 := by mach_ring
    have r : (-1 : Real) + exp x = exp x - 1 := by mach_mpoly [exp x]
    rw [l, r] at u; exact u
  have hlogu : log (exp x - 1) ≤ log x + 1 := by
    have hule : exp x - 1 ≤ x * exp 1 :=
      le_trans exp_sub_one_le_mul_exp
        (mul_le_mul_of_nonneg_left (exp_monotone hx1) (le_of_lt hx))
    have s := log_le_log hupos hule
    rwa [log_mul hx (exp_pos 1), log_exp] at s
  -- `−log x ≥ 2 − G` below `exp (G − 2)`
  have hlogx : (1 + 1 : Real) - G ≤ -log x := by
    have hlt : x < exp (G - (1 + 1)) := lt_of_le_of_lt hxw hwe
    have hl : log x < G - (1 + 1) := by
      have s := log_lt_log_strict hx hlt
      rwa [log_exp] at s
    have s := add_lt_add_left hl ((1 + 1 : Real) - G - log x)
    have l : (1 + 1 : Real) - G - log x + log x = 1 + 1 - G := by
      mach_mpoly [G, log x]
    have r : (1 + 1 : Real) - G - log x + (G - (1 + 1)) = -log x := by
      mach_mpoly [G, log x]
    rw [l, r] at s
    exact le_of_lt s
  have hGle : G ≤ exp (A.eval x) := by
    refine le_trans ?_ (hlow x hx)
    have t := mul_le_mul_of_nonneg_left (one_le_exp (le_of_lt hx)) (le_of_lt hG)
    have e : G * (1 : Real) = G := by mach_mpoly [G]
    rw [e] at t; exact t
  show (1 : Real) * x ≤ exp (A.eval x) - log (B.eval x)
  rw [hB x hx]
  have e : (1 : Real) * x = x := by mach_mpoly [x]
  rw [e]
  have hge : (1 : Real) ≤ exp (A.eval x) - log (exp x - 1) := by
    have s := add_le_add_wit hGle (neg_le_neg_wit hlogu)
    have l : G + -(log x + 1) = G - 1 - log x := by mach_mpoly [G, log x]
    have r : exp (A.eval x) + -log (exp x - 1)
        = exp (A.eval x) - log (exp x - 1) := by
      mach_mpoly [exp (A.eval x), log (exp x - 1)]
    rw [l, r] at s
    refine le_trans ?_ s
    have u := add_le_add_wit (le_refl (G - 1)) hlogx
    have l2 : G - 1 + (1 + 1 - G) = 1 := by mach_mpoly [G]
    have r2 : G - 1 + -log x = G - 1 - log x := by mach_mpoly [G, log x]
    rw [l2, r2] at u; exact u
  exact le_trans hx1 hge

/-! ### The `L < 1` regime: `γ ≠ 0` ports to floors, leaving only the coincidence

Write `M := 1 − L > 0`, so the right child is `M + (exp x − 1)` and `γ := G − log M` is the tree's
value in the limit at `0`. The two `γ ≠ 0` cases are the bulk of the parameter space and both port
from the leaf-`var` proofs directly — keeping their floor derivations, which never used the pin, and
replacing the branch that called `leaf_var_neg_point_absurd` with the positivity hypothesis, which
refutes exactly that branch. -/

/-- `γ > 0`: the tree settles above a positive constant, so a constant floor works. -/
theorem depth_le_two_cancel_gamma_pos_floor {A B : EMLTree} {G L M d : Real}
    (hG : 0 < G) (hM : 0 < M) (hLM : L = 1 - M) (hgam : log M < G)
    (hB : ∀ x : Real, 0 < x → B.eval x = exp x - L)
    (hlow : ∀ x : Real, 0 < x → G * exp x ≤ exp (A.eval x))
    (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ K d' : Real, 0 < K ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' → K * (x * x) ≤ (EMLTree.eml A B).eval x := by
  have hBpos : ∀ z : Real, 0 < z → 0 < exp z - L := by
    intro z hz
    have s : (1 : Real) < exp z := by
      have t := exp_lt hz; rwa [exp_zero] at t
    have hu : (0 : Real) < exp z - 1 := by
      have u := add_lt_add_left s (-1 : Real)
      have l : (-1 : Real) + 1 = 0 := by mach_ring
      have r : (-1 : Real) + exp z = exp z - 1 := by mach_mpoly [exp z]
      rw [l, r] at u; exact u
    have hsum : (0 : Real) < (exp z - 1) + M := add_pos hu hM
    have e : (exp z - 1) + M = exp z - L := by rw [hLM]; mach_mpoly [exp z, M]
    rw [e] at hsum; exact hsum
  have hGle : ∀ x : Real, 0 < x → G ≤ exp (A.eval x) := by
    intro x hx
    refine le_trans ?_ (hlow x hx)
    have s := mul_le_mul_of_nonneg_left (one_le_exp (le_of_lt hx)) (le_of_lt hG)
    have e : G * (1 : Real) = G := by mach_mpoly [G]
    rw [e] at s; exact s
  have hMlt : M < exp G := by
    have s := exp_lt hgam
    rwa [exp_log hM] at s
  have hZ : (1 : Real) < exp G + L := by
    rw [hLM]
    have u := add_lt_add_left hMlt (1 - M)
    have l : (1 - M) + M = (1 : Real) := by mach_mpoly [M]
    have r : (1 - M) + exp G = exp G + (1 - M) := by mach_mpoly [M, exp G]
    rw [l, r] at u; exact u
  have hZpos : (0 : Real) < exp G + L := lt_trans_ax one_pos hZ
  obtain ⟨w, hwpos, hwd, hwZ⟩ := two_bound_witness' hd (log_pos_of_one_lt hZ)
  have hBwlt : exp w - L < exp G := by
    have s := exp_lt hwZ
    rw [exp_log hZpos] at s
    have u := add_lt_add_left s (-L)
    have l : -L + exp w = exp w - L := by mach_mpoly [exp w, L]
    have r : -L + (exp G + L) = exp G := by mach_mpoly [exp G, L]
    rw [l, r] at u; exact u
  have hlogw : log (exp w - L) < G := by
    have s := log_lt_log_strict (hBpos w hwpos) hBwlt
    rwa [log_exp] at s
  have hc : (0 : Real) < G - log (exp w - L) := by
    have u := add_lt_add_left hlogw (-log (exp w - L))
    have l : -log (exp w - L) + log (exp w - L) = (0 : Real) := by mach_ring
    have r : -log (exp w - L) + G = G - log (exp w - L) := by
      mach_mpoly [G, log (exp w - L)]
    rw [l, r] at u; exact u
  refine ⟨G - log (exp w - L), w, hc, hwpos, le_of_lt hwd, fun x hx hxw => ?_⟩
  have hx1 : x ≤ 1 := le_trans hxw (le_trans (le_of_lt hwd) hd1)
  show (G - log (exp w - L)) * (x * x) ≤ exp (A.eval x) - log (B.eval x)
  rw [hB x hx]
  -- the constant floor
  have hfloor : G - log (exp w - L) ≤ exp (A.eval x) - log (exp x - L) := by
    have h2 : log (exp x - L) ≤ log (exp w - L) := by
      refine log_le_log (hBpos x hx) ?_
      have s := add_le_add_wit (exp_monotone hxw) (le_refl (-L))
      have l : exp x + -L = exp x - L := by mach_mpoly [exp x, L]
      have r : exp w + -L = exp w - L := by mach_mpoly [exp w, L]
      rw [l, r] at s; exact s
    have s := add_le_add_wit (hGle x hx) (neg_le_neg_wit h2)
    have l : G + -log (exp w - L) = G - log (exp w - L) := by
      mach_mpoly [G, log (exp w - L)]
    have r : exp (A.eval x) + -log (exp x - L) = exp (A.eval x) - log (exp x - L) := by
      mach_mpoly [exp (A.eval x), log (exp x - L)]
    rw [l, r] at s; exact s
  refine le_trans ?_ hfloor
  -- `c·(x·x) ≤ c` since `x·x ≤ 1`
  have hxx : x * x ≤ 1 := by
    have s := mul_le_mul_of_nonneg_right hx1 (le_of_lt hx)
    have e : (1 : Real) * x = x := by mach_mpoly [x]
    rw [e] at s
    exact le_trans s hx1
  have s := mul_le_mul_of_nonneg_left hxx (le_of_lt hc)
  have e : (G - log (exp w - L)) * (1 : Real) = G - log (exp w - L) := by
    mach_mpoly [G, log (exp w - L)]
  rw [e] at s; exact s

/-- `γ < 0`: the tree dips **below zero**, so the positivity hypothesis is refuted — the same point
construction as `leaf_var_expvar_const_gamma_neg_absurd`, with `hpos` in place of the pin. -/
theorem depth_le_two_cancel_gamma_neg_absurd {A B : EMLTree} {G L M d : Real}
    (hG : 0 < G) (hM : 0 < M) (hLM : L = 1 - M) (hgam : G < log M)
    (hB : ∀ x : Real, 0 < x → B.eval x = exp x - L)
    (hupp : ∀ x : Real, 0 < x → exp (A.eval x) ≤ G * exp (exp x - 1))
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hpos : ∀ x : Real, 0 < x → x ≤ d → 0 < (EMLTree.eml A B).eval x) : False := by
  have hlogMpos : (0 : Real) < log M := lt_trans_ax hG hgam
  have hS : log G < log (log M) := log_lt_log_strict hG hgam
  have hSpos : (0 : Real) < log (log M) - log G := by
    have u := add_lt_add_left hS (-log G)
    have l : -log G + log G = (0 : Real) := by mach_ring
    have r : -log G + log (log M) = log (log M) - log G := by
      mach_mpoly [log G, log (log M)]
    rw [l, r] at u; exact u
  have h1S : (1 : Real) < 1 + (log (log M) - log G) := by
    have u := add_lt_add_left hSpos (1 : Real)
    have l : (1 : Real) + 0 = 1 := by mach_ring
    rw [l] at u; exact u
  have h1Spos : (0 : Real) < 1 + (log (log M) - log G) := lt_trans_ax one_pos h1S
  obtain ⟨w, hwpos, hwd, hwS⟩ := two_bound_witness' hd (log_pos_of_one_lt h1S)
  have huS : exp w - 1 < log (log M) - log G := by
    have s := exp_lt hwS
    rw [exp_log h1Spos] at s
    have u := add_lt_add_left s (-1 : Real)
    have l : (-1 : Real) + exp w = exp w - 1 := by mach_mpoly [exp w]
    have r : (-1 : Real) + (1 + (log (log M) - log G)) = log (log M) - log G := by
      mach_mpoly [log (log M), log G]
    rw [l, r] at u; exact u
  have hkey : G * exp (exp w - 1) < log M := by
    have s : log G + (exp w - 1) < log (log M) := by
      have u := add_lt_add_left huS (log G)
      have l : log G + (log (log M) - log G) = log (log M) := by
        mach_mpoly [log G, log (log M)]
      rw [l] at u; exact u
    have t := exp_lt s
    rw [exp_add, exp_log hG, exp_log hlogMpos] at t
    exact t
  have hlogge : log M ≤ log (B.eval w) := by
    refine log_le_log hM ?_
    rw [hB w hwpos]
    have s : (1 : Real) ≤ exp w := one_le_exp (le_of_lt hwpos)
    have u := add_le_add_wit s (le_refl (M - 1))
    have l : (1 : Real) + (M - 1) = M := by mach_mpoly [M]
    have r : exp w + (M - 1) = exp w - L := by rw [hLM]; mach_mpoly [exp w, M]
    rw [l, r] at u; exact u
  have hneg : (EMLTree.eml A B).eval w < 0 := by
    show exp (A.eval w) - log (B.eval w) < 0
    have hlt : exp (A.eval w) < log (B.eval w) :=
      lt_of_le_of_lt (hupp w hwpos) (lt_of_lt_of_le hkey hlogge)
    have s := add_lt_add_left hlt (-log (B.eval w))
    have l : -log (B.eval w) + exp (A.eval w) = exp (A.eval w) - log (B.eval w) := by
      mach_mpoly [exp (A.eval w), log (B.eval w)]
    have r : -log (B.eval w) + log (B.eval w) = (0 : Real) := by mach_ring
    rw [l, r] at s; exact s
  exact lt_irrefl_ax _ (lt_trans_ax (hpos w hwpos (le_of_lt hwd)) hneg)

/-! ### On the coincidence locus `γ = 0`: the `κ` split, ported

`M = exp G`, so the constant terms cancel exactly and the tree's leading behaviour is decided by
`κ := G − exp(−G)`. All three ports keep the leaf-`var` floor derivations verbatim and swap the
pin for positivity. `A = var` has `G = 1` and therefore `κ = 1 − e⁻¹ > 0`, so it never reaches the
`κ ≤ 0` branches — which is why only those need the exact form of `exp (A x)`. -/

/-- `κ > 0`: a **linear** floor `(exp x − 1)·κ ≥ x·κ`. -/
theorem depth_le_two_cancel_kappa_pos_floor {A B : EMLTree} {G L d : Real}
    (hLM : L = 1 - exp G) (hkap : exp (-G) < G)
    (hB : ∀ x : Real, 0 < x → B.eval x = exp x - L)
    (hlow : ∀ x : Real, 0 < x → G * exp x ≤ exp (A.eval x))
    (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ K d' : Real, 0 < K ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' → K * (x * x) ≤ (EMLTree.eml A B).eval x := by
  have hK : (0 : Real) < G - exp (-G) := by
    have u := add_lt_add_left hkap (-exp (-G))
    have l : -exp (-G) + exp (-G) = (0 : Real) := by mach_ring
    have r : -exp (-G) + G = G - exp (-G) := by mach_mpoly [G, exp (-G)]
    rw [l, r] at u; exact u
  refine ⟨G - exp (-G), d, hK, hd, le_refl d, fun x hx hxd => ?_⟩
  have hx1 : x ≤ 1 := le_trans hxd hd1
  show (G - exp (-G)) * (x * x) ≤ exp (A.eval x) - log (B.eval x)
  rw [hB x hx]
  have hBeq : exp x - L = exp G + (exp x - 1) := by
    rw [hLM]; mach_mpoly [exp x, exp G]
  rw [hBeq]
  have hu0 : (0 : Real) ≤ exp x - 1 := by
    have s : (1 : Real) ≤ exp x := one_le_exp (le_of_lt hx)
    have u := add_le_add_wit s (le_refl (-1 : Real))
    have l : (1 : Real) + -1 = 0 := by mach_ring
    have r : exp x + -1 = exp x - 1 := by mach_mpoly [exp x]
    rw [l, r] at u; exact u
  have hxu : x ≤ exp x - 1 := by
    have t := one_add_le_exp x
    have u := add_le_add_wit t (le_refl (-1 : Real))
    have l : (1 : Real) + x + -1 = x := by mach_mpoly [x]
    have r : exp x + -1 = exp x - 1 := by mach_mpoly [exp x]
    rw [l, r] at u; exact u
  have hceil := log_shift_ceiling (g := G) hu0
  have s := add_le_add_wit (hlow x hx) (neg_le_neg_wit hceil)
  have l : G * exp x + -(G + (exp x - 1) * exp (-G))
      = (exp x - 1) * (G - exp (-G)) := by
    mach_mpoly [G, exp x, exp (-G)]
  have r : exp (A.eval x) + -log (exp G + (exp x - 1))
      = exp (A.eval x) - log (exp G + (exp x - 1)) := by
    mach_mpoly [exp (A.eval x), log (exp G + (exp x - 1))]
  rw [l, r] at s
  refine le_trans ?_ s
  -- `K·(x·x) ≤ K·x ≤ (exp x − 1)·K`
  have h1 : (G - exp (-G)) * (x * x) ≤ (G - exp (-G)) * x := by
    have hxx : x * x ≤ x := by
      have t := mul_le_mul_of_nonneg_left hx1 (le_of_lt hx)
      have e : x * (1 : Real) = x := by mach_mpoly [x]
      rw [e] at t; exact t
    exact mul_le_mul_of_nonneg_left hxx (le_of_lt hK)
  have h2 : (G - exp (-G)) * x ≤ (exp x - 1) * (G - exp (-G)) := by
    have t := mul_le_mul_of_nonneg_right hxu (le_of_lt hK)
    have e : (G - exp (-G)) * x = x * (G - exp (-G)) := mul_comm _ _
    rw [e]; exact t
  exact le_trans h1 h2

/-- `κ < 0`: the tree dips **below zero**, refuting positivity. The point construction is
`leaf_var_expvar_const_gamma_zero_neg_absurd`'s, with the cutoff taken against `d` instead of
`exp (−1)` and `hpos` in place of the pin. -/
theorem depth_le_two_cancel_kappa_neg_absurd {A B : EMLTree} {G L d : Real}
    (hG : 0 < G) (hLM : L = 1 - exp G) (hkap : G < exp (-G))
    (hB : ∀ x : Real, 0 < x → B.eval x = exp x - L)
    (hupp : ∀ x : Real, 0 < x → exp (A.eval x) ≤ G * exp (exp x - 1))
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hpos : ∀ x : Real, 0 < x → x ≤ d → 0 < (EMLTree.eml A B).eval x) : False := by
  have hD : (0 : Real) < exp (-G) - G := by
    have u := add_lt_add_left hkap (-G)
    have l : -G + G = (0 : Real) := by mach_ring
    have r : -G + exp (-G) = exp (-G) - G := by mach_mpoly [G, exp (-G)]
    rw [l, r] at u; exact u
  have hb : (0 : Real) < G * exp 1 + exp (-G) * exp (-G) :=
    add_pos (mul_pos hG (exp_pos 1)) (mul_pos (exp_pos (-G)) (exp_pos (-G)))
  obtain ⟨u₀, hu0pos, hu01, hu0D⟩ :=
    two_bound_witness' one_pos
      (mul_pos hD (exp_pos (-(G * exp 1 + exp (-G) * exp (-G)))))
  have hu0b : u₀ * (G * exp 1 + exp (-G) * exp (-G)) < exp (-G) - G := by
    have s := mul_lt_mul_of_pos_right hu0D hb
    have e : (exp (-G) - G) * exp (-(G * exp 1 + exp (-G) * exp (-G)))
          * (G * exp 1 + exp (-G) * exp (-G))
        = (exp (-G) - G) * ((G * exp 1 + exp (-G) * exp (-G))
          * exp (-(G * exp 1 + exp (-G) * exp (-G)))) := by
      mach_mpoly [exp (-G), G, exp 1, exp (-(G * exp 1 + exp (-G) * exp (-G)))]
    rw [e] at s
    have t := mul_lt_mul_pos_left_wit (mul_exp_neg_lt_one hb) hD
    have e2 : (exp (-G) - G) * (1 : Real) = exp (-G) - G := by
      mach_mpoly [exp (-G), G]
    rw [e2] at t
    exact lt_trans_ax s t
  obtain ⟨w, hwpos, hwd, hwu⟩ :=
    two_bound_witness' hd (mul_pos hu0pos (exp_pos (-1)))
  have hwle1 : w ≤ 1 := le_trans (le_of_lt hwd) hd1
  have huu0 : exp w - 1 ≤ u₀ := by
    have s1 : exp w - 1 ≤ w * exp w := exp_sub_one_le_mul_exp
    have s2 : w * exp w ≤ w * exp 1 :=
      mul_le_mul_of_nonneg_left (exp_monotone hwle1) (le_of_lt hwpos)
    have s3 : w * exp 1 < u₀ * exp (-1) * exp 1 :=
      mul_lt_mul_of_pos_right hwu (exp_pos 1)
    have e : u₀ * exp (-1) * exp 1 = u₀ := by
      have e2 : u₀ * exp (-1) * exp 1 = u₀ * (exp (-1) * exp 1) := by
        mach_mpoly [u₀, exp (-1), exp 1]
      rw [e2, exp_neg_self_mul]
      mach_mpoly [u₀]
    rw [e] at s3
    exact le_trans s1 (le_trans s2 (le_of_lt s3))
  have hu0' : (0 : Real) ≤ exp w - 1 := by
    have s : (1 : Real) ≤ exp w := one_le_exp (le_of_lt hwpos)
    have u := add_le_add_wit s (le_refl (-1 : Real))
    have l : (1 : Real) + -1 = 0 := by mach_ring
    have r : exp w + -1 = exp w - 1 := by mach_mpoly [exp w]
    rw [l, r] at u; exact u
  have hneg : (EMLTree.eml A B).eval w ≤ 0 := by
    show exp (A.eval w) - log (B.eval w) ≤ 0
    rw [hB w hwpos]
    have hBeq : exp w - L = exp G + (exp w - 1) := by
      rw [hLM]; mach_mpoly [exp w, exp G]
    rw [hBeq]
    have hupper : exp (A.eval w) ≤ G + G * ((exp w - 1) * exp u₀) := by
      refine le_trans (hupp w hwpos) ?_
      have s1 : exp (exp w - 1) - 1 ≤ (exp w - 1) * exp (exp w - 1) :=
        exp_sub_one_le_mul_exp
      have s2 : (exp w - 1) * exp (exp w - 1) ≤ (exp w - 1) * exp u₀ :=
        mul_le_mul_of_nonneg_left (exp_monotone huu0) hu0'
      have s3 : exp (exp w - 1) ≤ 1 + (exp w - 1) * exp u₀ := by
        have t := add_le_add_wit (le_trans s1 s2) (le_refl (1 : Real))
        have l : exp (exp w - 1) - 1 + 1 = exp (exp w - 1) := by
          mach_mpoly [exp (exp w - 1)]
        have r : (exp w - 1) * exp u₀ + 1 = 1 + (exp w - 1) * exp u₀ := by
          mach_mpoly [exp w, exp u₀]
        rw [l, r] at t; exact t
      have t := mul_le_mul_of_nonneg_left s3 (le_of_lt hG)
      have e : G * (1 + (exp w - 1) * exp u₀) = G + G * ((exp w - 1) * exp u₀) := by
        mach_mpoly [G, exp w, exp u₀]
      rw [e] at t; exact t
    have hfloor := log_shift_floor (g := G) hu0'
    have s := add_le_add_wit hupper (neg_le_neg_wit hfloor)
    have r : exp (A.eval w) + -log (exp G + (exp w - 1))
        = exp (A.eval w) - log (exp G + (exp w - 1)) := by
      mach_mpoly [exp (A.eval w), log (exp G + (exp w - 1))]
    have l : G + G * ((exp w - 1) * exp u₀)
          + -(G + (exp w - 1) * exp (-G)
            - (exp w - 1) * exp (-G) * ((exp w - 1) * exp (-G)))
        = (exp w - 1) * (G * exp u₀ - exp (-G)
            + (exp w - 1) * (exp (-G) * exp (-G))) := by
      mach_mpoly [G, exp w, exp u₀, exp (-G)]
    rw [l, r] at s
    refine le_trans s ?_
    have hbr : G * exp u₀ - exp (-G) + (exp w - 1) * (exp (-G) * exp (-G)) ≤ 0 := by
      have hexpu0 : exp u₀ - 1 ≤ u₀ * exp 1 :=
        le_trans exp_sub_one_le_mul_exp
          (mul_le_mul_of_nonneg_left (exp_monotone (le_of_lt hu01)) (le_of_lt hu0pos))
      have s1 : G * (exp u₀ - 1) ≤ G * (u₀ * exp 1) :=
        mul_le_mul_of_nonneg_left hexpu0 (le_of_lt hG)
      have s2 : (exp w - 1) * (exp (-G) * exp (-G)) ≤ u₀ * (exp (-G) * exp (-G)) :=
        mul_le_mul_of_nonneg_right huu0
          (le_of_lt (mul_pos (exp_pos (-G)) (exp_pos (-G))))
      have s3 := add_le_add_wit s1 s2
      have s4 : G * (u₀ * exp 1) + u₀ * (exp (-G) * exp (-G))
          = u₀ * (G * exp 1 + exp (-G) * exp (-G)) := by
        mach_mpoly [G, u₀, exp 1, exp (-G)]
      rw [s4] at s3
      have s5 := lt_of_le_of_lt s3 hu0b
      have u := add_lt_add_left s5 (G - exp (-G))
      have l2 : G - exp (-G) + (G * (exp u₀ - 1) + (exp w - 1) * (exp (-G) * exp (-G)))
          = G * exp u₀ - exp (-G) + (exp w - 1) * (exp (-G) * exp (-G)) := by
        mach_mpoly [G, exp u₀, exp w, exp (-G)]
      have r2 : G - exp (-G) + (exp (-G) - G) = (0 : Real) := by
        mach_mpoly [G, exp (-G)]
      rw [l2, r2] at u
      exact le_of_lt u
    have t := mul_le_mul_of_nonneg_left hbr hu0'
    have e : (exp w - 1) * (0 : Real) = 0 := by mach_ring
    rw [e] at t; exact t
  exact lt_irrefl_ax _ (lt_of_lt_of_le (hpos w hwpos (le_of_lt hwd)) hneg)

/-- # ▸ **The Ω-point: `γ = 0` and `κ = 0`, where the floor is QUADRATIC.**

`G·exp G = 1`. **The constant and first-order terms vanish exactly, so the leading contribution is
second order**: `G·(exp u − 1 − u) ≥ G·(u/2)² ≥ (G/4)·x²`, on `u := exp x − 1 ≥ 0`. This is the last
case of rung 2 and the only one in the ladder whose leading term is quadratic — which is why
`exp_quad_lower` had to be built at all.

> The quadratic floor is **forced, not a technical strengthening**. `γ = 0` kills the constant term
> and `κ = 0` kills the linear one, so the proof architecture mirrors the expression's own Taylor
> structure rather than working around an automation limit.

⚠ `exp u − 1 − u ≥ (u/2)²` **requires `u ≥ 0`** — it fails for `u ≲ −2.5`. Here `u = exp x − 1 ≥ 0`
for `x > 0`, so the domain is met, but the bound is not two-sided and must not be summarised as if
it were.

The derivation is `leaf_var_expvar_const_gamma_zero_zero_absurd`'s, kept whole; only its ending
changes, from feeding `leaf_var_quad_floor_absurd` to simply *being* the floor. -/
theorem depth_le_two_cancel_kappa_zero_floor {A B : EMLTree} {G L d : Real}
    (hG : 0 < G) (hLM : L = 1 - exp G) (hkap : exp (-G) = G)
    (hB : ∀ x : Real, 0 < x → B.eval x = exp x - L)
    (hexact : ∀ x : Real, 0 < x → exp (A.eval x) = G * exp (exp x - 1))
    (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ K d' : Real, 0 < K ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' → K * (x * x) ≤ (EMLTree.eml A B).eval x := by
  have h2 : (0 : Real) < 1 + 1 := add_pos one_pos one_pos
  have hhpos : (0 : Real) < 1 / (1 + 1) := one_div_pos_of_pos h2
  refine ⟨G * (1 / (1 + 1) * (1 / (1 + 1))), d,
    mul_pos hG (mul_pos hhpos hhpos), hd, le_refl d, fun x hx hxd => ?_⟩
  show G * (1 / (1 + 1) * (1 / (1 + 1))) * (x * x)
      ≤ exp (A.eval x) - log (B.eval x)
  rw [hB x hx, hexact x hx]
  have hBeq : exp x - L = exp G + (exp x - 1) := by
    rw [hLM]; mach_mpoly [exp x, exp G]
  rw [hBeq]
  have hu0 : (0 : Real) ≤ exp x - 1 := by
    have s : (1 : Real) ≤ exp x := one_le_exp (le_of_lt hx)
    have u := add_le_add_wit s (le_refl (-1 : Real))
    have l : (1 : Real) + -1 = 0 := by mach_ring
    have r : exp x + -1 = exp x - 1 := by mach_mpoly [exp x]
    rw [l, r] at u; exact u
  have hxu : x ≤ exp x - 1 := by
    have t := one_add_le_exp x
    have u := add_le_add_wit t (le_refl (-1 : Real))
    have l : (1 : Real) + x + -1 = x := by mach_mpoly [x]
    have r : exp x + -1 = exp x - 1 := by mach_mpoly [exp x]
    rw [l, r] at u; exact u
  have hgap := exp_sub_one_sub_self_ge_quad hu0
  have hGgap := mul_le_mul_of_nonneg_left hgap (le_of_lt hG)
  have hceil := log_shift_ceiling (g := G) hu0
  rw [hkap] at hceil
  have s := add_le_add_wit (le_refl (G * exp (exp x - 1))) (neg_le_neg_wit hceil)
  have l : G * exp (exp x - 1) + -(G + (exp x - 1) * G)
      = G * (exp (exp x - 1) - 1 - (exp x - 1)) := by
    mach_mpoly [G, exp (exp x - 1), exp x]
  have r : G * exp (exp x - 1) + -log (exp G + (exp x - 1))
      = G * exp (exp x - 1) - log (exp G + (exp x - 1)) := by
    mach_mpoly [G, exp (exp x - 1), log (exp G + (exp x - 1))]
  rw [l, r] at s
  refine le_trans ?_ (le_trans hGgap s)
  have hstep : x * (1 / (1 + 1)) * (x * (1 / (1 + 1)))
      ≤ (exp x - 1) * (1 / (1 + 1)) * ((exp x - 1) * (1 / (1 + 1))) := by
    have hx2 : x * (1 / (1 + 1)) ≤ (exp x - 1) * (1 / (1 + 1)) :=
      mul_le_mul_of_nonneg_right hxu (le_of_lt hhpos)
    have hxn : (0 : Real) ≤ x * (1 / (1 + 1)) := mul_nonneg (le_of_lt hx) (le_of_lt hhpos)
    have hun : (0 : Real) ≤ (exp x - 1) * (1 / (1 + 1)) := mul_nonneg hu0 (le_of_lt hhpos)
    exact le_trans (mul_le_mul_of_nonneg_right hx2 hxn)
      (mul_le_mul_of_nonneg_left hx2 hun)
  have hGstep := mul_le_mul_of_nonneg_left hstep (le_of_lt hG)
  have e : G * (1 / (1 + 1) * (1 / (1 + 1))) * (x * x)
      = G * (x * (1 / (1 + 1)) * (x * (1 / (1 + 1)))) := by
    mach_mpoly [G, x, (1 / (1 + 1) : Real)]
  rw [e]; exact hGstep

/-- A linear floor is a quadratic one on `(0,1]`, since `x·x ≤ x` there. Lets the rung-2 rows that
produce constant or linear certificates be stated in the single output shape the classification
uses. -/
theorem linear_floor_to_quad {t : EMLTree} {K d : Real} (hK : 0 < K) (hd1 : d ≤ 1)
    (h : ∀ x : Real, 0 < x → x ≤ d → K * x ≤ t.eval x) :
    ∀ x : Real, 0 < x → x ≤ d → K * (x * x) ≤ t.eval x := by
  intro x hx hxd
  have hx1 : x ≤ 1 := le_trans hxd hd1
  have hxx : x * x ≤ x := by
    have s := mul_le_mul_of_nonneg_left hx1 (le_of_lt hx)
    have e : x * (1 : Real) = x := by mach_mpoly [x]
    rw [e] at s; exact s
  exact le_trans (mul_le_mul_of_nonneg_left hxx (le_of_lt hK)) (h x hx hxd)

/-- # ▸ **Rung 2's hardest row, as ONE classification.**

Every configuration of `t = eml A B` with `B x = exp x − L` either **carries a certified quadratic
floor** or **cannot stay positive** — and which, is decided by three parameters:

| | condition | certificate |
|---|---|---|
| `L > 1` | the log clamps | constant floor |
| `L = 1` | the log runs to `−∞` | constant floor |
| `L < 1`, `γ > 0` | tree settles above `0` | constant floor |
| `L < 1`, `γ < 0` | tree settles below `0` | **positivity refuted** |
| `L < 1`, `γ = 0`, `κ > 0` | first order survives | linear floor |
| `L < 1`, `γ = 0`, `κ < 0` | first order is negative | **positivity refuted** |
| `L < 1`, `γ = 0`, `κ = 0` | `G = Ω`; first two orders vanish | **quadratic floor** |

`γ := G − log(1−L)` is the tree's limiting value at `0`; `κ := G − exp(−G)` is its first-order
coefficient once `γ` vanishes. So the ladder *constant → linear → quadratic → impossible* is indexed
by how many leading Taylor coefficients cancel, which is what makes this a classification rather
than a case list.

`hnec` asks for the exact form of `exp (A x)` **only when `κ = 0`**, because that is the only branch
needing it — and `A = var`, which cannot supply it, has `G = 1` and therefore `κ = 1 − e⁻¹ > 0`, so
it discharges the hypothesis vacuously. -/
theorem rung2_expvar_right_floor {A B : EMLTree} {G L d : Real}
    (hG : 0 < G)
    (hB : ∀ x : Real, 0 < x → B.eval x = exp x - L)
    (hlow : ∀ x : Real, 0 < x → G * exp x ≤ exp (A.eval x))
    (hupp : ∀ x : Real, 0 < x → exp (A.eval x) ≤ G * exp (exp x - 1))
    (hnec : exp (-G) = G → ∀ x : Real, 0 < x → exp (A.eval x) = G * exp (exp x - 1))
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hpos : ∀ x : Real, 0 < x → x ≤ d → 0 < (EMLTree.eml A B).eval x) :
    ∃ K d' : Real, 0 < K ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' → K * (x * x) ≤ (EMLTree.eml A B).eval x := by
  rcases lt_total 1 L with hL | hL | hL
  · obtain ⟨K, d', hK, hd'0, hd'd, hfl⟩ :=
      depth_le_two_expvar_right_clamped_floor hG hL hB hlow hd hd1
    exact ⟨K, d', hK, hd'0, hd'd, linear_floor_to_quad hK (le_trans hd'd hd1) hfl⟩
  · obtain ⟨K, d', hK, hd'0, hd'd, hfl⟩ :=
      depth_le_two_expvar_right_one_floor hG (fun x hx => by
        have h := hB x hx
        rw [← hL] at h
        exact h) hlow hd hd1
    exact ⟨K, d', hK, hd'0, hd'd, linear_floor_to_quad hK (le_trans hd'd hd1) hfl⟩
  · have hM : (0 : Real) < 1 - L := by
      have u := add_lt_add_left hL (-L)
      have l : -L + L = (0 : Real) := by mach_ring
      have r : -L + 1 = 1 - L := by mach_mpoly [L]
      rw [l, r] at u; exact u
    have hLM : L = 1 - (1 - L) := by mach_ring
    rcases lt_total (log (1 - L)) G with hg | hg | hg
    · exact depth_le_two_cancel_gamma_pos_floor hG hM hLM hg hB hlow hd hd1
    · -- `γ = 0`, so `1 − L = exp G`
      have hMe : (1 : Real) - L = exp G := by
        have t := exp_log hM
        rw [hg] at t
        exact t.symm
      have hLG : L = 1 - exp G := by rw [← hMe]; mach_ring
      rcases lt_total (exp (-G)) G with hk | hk | hk
      · exact depth_le_two_cancel_kappa_pos_floor hLG hk hB hlow hd hd1
      · exact depth_le_two_cancel_kappa_zero_floor hG hLG hk hB (hnec hk) hd hd1
      · exact (depth_le_two_cancel_kappa_neg_absurd hG hLG hk hB hupp hd hd1 hpos).elim
    · exact (depth_le_two_cancel_gamma_neg_absurd hG hM hLM hg hB hupp hd hd1 hpos).elim

/-! ## ▸ **The lift: rung 2 ⟹ the depth-3 bounded-left case**

Rather than continue case-by-case, this makes the *architecture* explicit. Two connectives turn a
completed rung 2 into a depth-3 elimination:

1. a bounded left child forces the right child **positive** near `0` (below), and
2. a positive depth-≤2 right child has a **quadratic floor** (rung 2), which
   `bounded_left_quad_floor_absurd` then kills.

So the remaining depth-3 work is not a case analysis at all — it is exactly the assembly of rung 2
over depth-≤2 trees, and `depth3_bounded_left_of_rung2` below states that reduction as a theorem
rather than as a plan. -/

/-- **A bounded left child forces the right child positive near `0`.**

`depth3_left_pinned_of_right_nonpos` says a non-positive right child pins `x·exp (t1 x) = 1`. With
`exp (t1 x) ≤ W` that forces `x·W ≥ 1`, so below `1/W` the right child cannot be non-positive. The
cutoff is written `exp (−log W)` to keep it division-free. -/
theorem depth3_right_pos_of_bounded_left {t1 t2 : EMLTree} {W d : Real}
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x)
    (hd : 0 < d) (hW : ∀ x : Real, 0 < x → x ≤ d → exp (t1.eval x) ≤ W) :
    ∃ d' : Real, 0 < d' ∧ d' ≤ d ∧ ∀ x : Real, 0 < x → x ≤ d' → 0 < t2.eval x := by
  -- `W` is positive: it dominates an `exp`
  have hWpos : (0 : Real) < W :=
    lt_of_lt_of_le (exp_pos (t1.eval d)) (hW d hd (le_refl d))
  obtain ⟨w, hwpos, hwd, hwe⟩ := two_bound_witness' hd (exp_pos (-log W))
  refine ⟨w, hwpos, le_of_lt hwd, fun x hx hxw => ?_⟩
  rcases lt_total 0 (t2.eval x) with hp | hz | hn
  · exact hp
  · exfalso
    exact absurd (depth3_left_pinned_of_right_nonpos h hx (le_of_eq hz.symm))
      (by
        intro hpin
        -- `x·W < 1` below the cutoff, contradicting `x·exp (t1 x) = 1 ≤ x·W`
        have hxW : x * W < 1 := by
          have hlt : x < exp (-log W) := lt_of_le_of_lt hxw hwe
          have hlog : log x < -log W := by
            have s := log_lt_log_strict hx hlt
            rwa [log_exp] at s
          have hsum : log (x * W) < 0 := by
            rw [log_mul hx hWpos]
            have s := add_lt_add_left hlog (log W)
            have l : log W + -log W = (0 : Real) := by mach_ring
            have r : log W + log x = log x + log W := by mach_mpoly [log W, log x]
            rw [l, r] at s; exact s
          have t := exp_lt hsum
          rw [exp_log (mul_pos hx hWpos), exp_zero] at t
          exact t
        have hge : (1 : Real) ≤ x * W := by
          have s := mul_le_mul_of_nonneg_left (hW x hx (le_trans hxw (le_of_lt hwd)))
            (le_of_lt hx)
          rw [hpin] at s
          exact s
        exact lt_irrefl_ax _ (lt_of_lt_of_le hxW hge))
  · exfalso
    have hpin := depth3_left_pinned_of_right_nonpos h hx (le_of_lt hn)
    have hxW : x * W < 1 := by
      have hlt : x < exp (-log W) := lt_of_le_of_lt hxw hwe
      have hlog : log x < -log W := by
        have s := log_lt_log_strict hx hlt
        rwa [log_exp] at s
      have hsum : log (x * W) < 0 := by
        rw [log_mul hx hWpos]
        have s := add_lt_add_left hlog (log W)
        have l : log W + -log W = (0 : Real) := by mach_ring
        have r : log W + log x = log x + log W := by mach_mpoly [log W, log x]
        rw [l, r] at s; exact s
      have t := exp_lt hsum
      rw [exp_log (mul_pos hx hWpos), exp_zero] at t
      exact t
    have hge : (1 : Real) ≤ x * W := by
      have s := mul_le_mul_of_nonneg_left (hW x hx (le_trans hxw (le_of_lt hwd)))
        (le_of_lt hx)
      rw [hpin] at s
      exact s
    exact lt_irrefl_ax _ (lt_of_lt_of_le hxW hge)

/-- # ▸ **THE LIFT.** A completed rung 2 eliminates the depth-3 bounded-left case.

`hrung2` is exactly the rung-2 statement for `t2` — *positive near `0` implies a quadratic floor*.
Given it, a bounded left child is impossible, with no further case analysis: positivity comes from
the clamp pin, the floor comes from rung 2, and `bounded_left_quad_floor_absurd` closes.

**This is the reduction, stated as a theorem rather than as a plan.** What remains of depth 3 is now
literally the assembly of rung 2 over depth-≤2 trees — nothing else. -/
theorem depth3_bounded_left_of_rung2 {t1 t2 : EMLTree} {W d : Real}
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hW : ∀ x : Real, 0 < x → x ≤ d → exp (t1.eval x) ≤ W)
    (hrung2 : ∀ d₀ : Real, 0 < d₀ → d₀ ≤ d →
      (∀ x : Real, 0 < x → x ≤ d₀ → 0 < t2.eval x) →
      ∃ C d' : Real, 0 < C ∧ 0 < d' ∧ d' ≤ d₀ ∧
        ∀ x : Real, 0 < x → x ≤ d' → C * (x * x) ≤ t2.eval x)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x) : False := by
  obtain ⟨d₀, hd₀0, hd₀d, hposr⟩ := depth3_right_pos_of_bounded_left h hd hW
  obtain ⟨C, d', hC, hd'0, hd'd₀, hfl⟩ := hrung2 d₀ hd₀0 hd₀d hposr
  have hd'd : d' ≤ d := le_trans hd'd₀ hd₀d
  exact bounded_left_quad_floor_absurd hC hd'0 (le_trans hd'd hd1)
    (fun x hx hxd => hW x hx (le_trans hxd hd'd)) hfl h

/-! ## ▸ Classifying the children once, instead of 36 nested branches

The rung-2 assembly needs `A` and `B` dispatched by *behaviour*, not by constructor. Classifying
each side once turns a 6×6 constructor match into 1 + 4 + 4 dispatches — and the classifications
are reusable in their own right. -/

/-- **Every depth-≤1 tree is one of three things at `0`:** it diverges like `−log x`, it is
constant-valued, or it is one of the two shapes that stay bounded while moving — for which the
whole `G`-parameterisation (`hlow`/`hupp`, and `hexact` exactly when `κ = 0` needs it) is available.

`A = var` discharges the `hnec` implication vacuously, since `exp (−1) < 1 = G`. -/
theorem depth_le_one_trichotomy (A : EMLTree) (hA : A.depth ≤ 1) :
    (∃ c₀ : Real, ∀ x : Real, 0 < x → x ≤ 1 → c₀ - log x ≤ A.eval x)
    ∨ (∃ α : Real, ∀ x : Real, 0 < x → A.eval x = α)
    ∨ (∃ G : Real, 0 < G ∧ (∀ x : Real, 0 < x → G * exp x ≤ exp (A.eval x))
        ∧ (∀ x : Real, 0 < x → exp (A.eval x) ≤ G * exp (exp x - 1))
        ∧ (exp (-G) = G → ∀ x : Real, 0 < x → exp (A.eval x) = G * exp (exp x - 1))) := by
  have hxu : ∀ x : Real, x ≤ exp x - 1 := by
    intro x
    have t := one_add_le_exp x
    have u := add_le_add_wit t (le_refl (-1 : Real))
    have l : (1 : Real) + x + -1 = x := by mach_mpoly [x]
    have r : exp x + -1 = exp x - 1 := by mach_mpoly [exp x]
    rw [l, r] at u; exact u
  cases A with
  | const c => exact Or.inr (Or.inl ⟨c, fun _ _ => rfl⟩)
  | var =>
      refine Or.inr (Or.inr ⟨1, one_pos, ?_, ?_, ?_⟩)
      · intro x _
        show (1 : Real) * exp x ≤ exp x
        have e : (1 : Real) * exp x = exp x := by mach_mpoly [exp x]
        rw [e]; exact le_refl _
      · intro x _
        show exp x ≤ (1 : Real) * exp (exp x - 1)
        have e : (1 : Real) * exp (exp x - 1) = exp (exp x - 1) := by
          mach_mpoly [exp (exp x - 1)]
        rw [e]; exact exp_monotone (hxu x)
      · intro hc
        exact absurd hc (fun he => lt_irrefl_ax _
          (lt_of_lt_of_le exp_neg_one_lt_one (le_of_eq he.symm)))
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
          | const q => exact Or.inr (Or.inl ⟨exp p - log q, fun _ _ => rfl⟩)
          | var => exact Or.inl ⟨exp p, fun _ _ _ => le_refl _⟩
      | var =>
          cases b with
          | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
          | const q =>
              -- `exp (exp x − log q) = exp (1 − log q) · exp (exp x − 1)`, exactly
              have hex : ∀ x : Real, 0 < x →
                  exp ((EMLTree.eml EMLTree.var (EMLTree.const q)).eval x)
                    = exp (1 - log q) * exp (exp x - 1) := by
                intro x _
                show exp (exp x - log q) = exp (1 - log q) * exp (exp x - 1)
                rw [← exp_add]
                have e : (1 - log q) + (exp x - 1) = exp x - log q := by
                  mach_mpoly [log q, exp x]
                rw [e]
              refine Or.inr (Or.inr ⟨exp (1 - log q), exp_pos _, ?_, ?_, fun _ => hex⟩)
              · intro x hx
                rw [hex x hx]
                exact mul_le_mul_of_nonneg_left (exp_monotone (hxu x))
                  (le_of_lt (exp_pos _))
              · intro x hx
                rw [hex x hx]; exact le_refl _
          | var =>
              refine Or.inl ⟨1, fun x hx _ => ?_⟩
              show (1 : Real) - log x ≤ exp x - log x
              have s := add_le_add_wit (one_le_exp (le_of_lt hx)) (le_refl (-log x))
              have l : (1 : Real) + -log x = 1 - log x := by mach_mpoly [log x]
              have r : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
              rw [l, r] at s; exact s

/-- **Every depth-≤1 right child is one of four things at `0`:** constant-valued, `var` itself,
divergent (`≥ −log x`), or the one bounded-but-moving shape `exp x − L`. -/
theorem depth_le_one_right_tetrachotomy (B : EMLTree) (hB : B.depth ≤ 1) :
    (∃ β : Real, ∀ x : Real, 0 < x → B.eval x = β)
    ∨ (∀ x : Real, 0 < x → B.eval x = x)
    ∨ (∀ x : Real, 0 < x → -log x ≤ B.eval x)
    ∨ (∃ L : Real, ∀ x : Real, 0 < x → B.eval x = exp x - L) := by
  cases B with
  | const q => exact Or.inl ⟨q, fun _ _ => rfl⟩
  | var => exact Or.inr (Or.inl (fun _ _ => rfl))
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd hB (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hB (by simp only [EMLTree.depth]; omega)
          | const q => exact Or.inl ⟨exp p - log q, fun _ _ => rfl⟩
          | var => exact Or.inr (Or.inr (Or.inl (fun x hx => eml_const_var_ge_neg_log x hx)))
      | var =>
          cases b with
          | eml _ _ => exact absurd hB (by simp only [EMLTree.depth]; omega)
          | const q => exact Or.inr (Or.inr (Or.inr ⟨log q, fun _ _ => rfl⟩))
          | var => exact Or.inr (Or.inr (Or.inl (fun x hx => eml_var_var_ge_neg_log x hx)))

/-- # ▸▸ **RUNG 2, ASSEMBLED: a positive depth-≤2 tree has a quadratic floor near `0`.**

The decay-by-depth ladder at depth 2. Every positive depth-≤2 tree is bounded below by `C·x²` on
some `(0,d']` — so nothing in this grammar can be positive and decay faster than quadratically at
depth 2, and in particular nothing can imitate `exp(−1/x)`.

Assembled from the classifications: `A` diverging covers every `B` at once; otherwise the four
`B`-behaviours dispatch, with the bounded-and-moving corner going to `rung2_expvar_right_floor`,
whose own eleven-way split is where the Ω-point lives. -/
theorem rung2_positive_floor (t : EMLTree) (ht : t.depth ≤ 2) {d : Real}
    (hd : 0 < d) (hd1 : d ≤ 1)
    (hpos : ∀ x : Real, 0 < x → x ≤ d → 0 < t.eval x) :
    ∃ C d' : Real, 0 < C ∧ 0 < d' ∧ d' ≤ d ∧
      ∀ x : Real, 0 < x → x ≤ d' → C * (x * x) ≤ t.eval x := by
  have hxx1 : ∀ x : Real, 0 < x → x ≤ 1 → x * x ≤ 1 := by
    intro x hx hx1
    have s := mul_le_mul_of_nonneg_right hx1 (le_of_lt hx)
    have e : (1 : Real) * x = x := by mach_mpoly [x]
    rw [e] at s; exact le_trans s hx1
  -- the `B = var` corner, needed under two of the three `A`-classes
  have hvarfloor : ∀ A' B' : EMLTree, (∀ x : Real, 0 < x → B'.eval x = x) →
      ∃ C d' : Real, 0 < C ∧ 0 < d' ∧ d' ≤ d ∧
        ∀ x : Real, 0 < x → x ≤ d' → C * (x * x) ≤ (EMLTree.eml A' B').eval x := by
    intro A' B' hBv
    obtain ⟨w, hwpos, hwd, hwe⟩ := two_bound_witness' hd (exp_pos (-1))
    refine ⟨1, w, one_pos, hwpos, le_of_lt hwd, fun x hx hxw => ?_⟩
    show (1 : Real) * (x * x) ≤ exp (A'.eval x) - log (B'.eval x)
    rw [hBv x hx]
    have hx1 : x ≤ 1 := le_trans hxw (le_trans (le_of_lt hwd) hd1)
    have hlog : (1 : Real) ≤ -log x := by
      have hlt : x < exp (-1) := lt_of_le_of_lt hxw hwe
      have h1 : log x < -1 := by
        have s := log_lt_log_strict hx hlt
        rwa [log_exp] at s
      have s := add_lt_add_left h1 (-log x + 1)
      have l : -log x + 1 + log x = 1 := by mach_mpoly [log x]
      have r : -log x + 1 + -1 = -log x := by mach_mpoly [log x]
      rw [l, r] at s; exact le_of_lt s
    have s := add_le_add_wit (le_of_lt (exp_pos (A'.eval x))) hlog
    have l : (0 : Real) + 1 = 1 := by mach_ring
    have r : exp (A'.eval x) + -log x = exp (A'.eval x) - log x := by
      mach_mpoly [exp (A'.eval x), log x]
    rw [l, r] at s
    have e : (1 : Real) * (x * x) = x * x := by mach_mpoly [x]
    rw [e]
    exact le_trans (hxx1 x hx hx1) s
  cases t with
  | const c =>
      have hc : (0 : Real) < c := hpos d hd (le_refl d)
      refine ⟨c, d, hc, hd, le_refl d, fun x hx hxd => ?_⟩
      show c * (x * x) ≤ c
      have s := mul_le_mul_of_nonneg_left (hxx1 x hx (le_trans hxd hd1)) (le_of_lt hc)
      have e : c * (1 : Real) = c := by mach_mpoly [c]
      rw [e] at s; exact s
  | var =>
      refine ⟨1, d, one_pos, hd, le_refl d, fun x hx hxd => ?_⟩
      show (1 : Real) * (x * x) ≤ x
      have e : (1 : Real) * (x * x) = x * x := by mach_mpoly [x]
      rw [e]
      have s := mul_le_mul_of_nonneg_left (le_trans hxd hd1) (le_of_lt hx)
      have e2 : x * (1 : Real) = x := by mach_mpoly [x]
      rw [e2] at s; exact s
  | eml A B =>
      have hA : A.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_left A.depth B.depth
        omega
      have hB : B.depth ≤ 1 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_right A.depth B.depth
        omega
      rcases depth_le_one_trichotomy A hA with ⟨c₀, hc₀⟩ | ⟨α, hα⟩ | ⟨G, hG, hlow, hupp, hnec⟩
      · -- `A` diverges: one theorem, every `B`
        obtain ⟨K, d', hK, hd'0, hd'd, hfl⟩ :=
          depth_le_two_diverging_left_floor (c₀ := c₀) hB hd hd1
            (fun x hx hxd => hc₀ x hx (le_trans hxd hd1))
        exact ⟨K, d', hK, hd'0, hd'd, linear_floor_to_quad hK (le_trans hd'd hd1) hfl⟩
      · -- `A` constant-valued
        rcases depth_le_one_right_tetrachotomy B hB with
          ⟨β, hβ⟩ | hBv | hBd | ⟨L, hBL⟩
        · obtain ⟨K, d', hK, hd'0, hd'd, hfl⟩ :=
            depth_le_two_const_right_floor hA hβ hd hd1 hpos
          exact ⟨K, d', hK, hd'0, hd'd, linear_floor_to_quad hK (le_trans hd'd hd1) hfl⟩
        · exact hvarfloor A B hBv
        · exact (depth_le_two_bounded_left_diverging_right_absurd (W := exp α) hd hd1
            (fun x hx _ => by rw [hα x hx]; exact le_refl _)
            (fun x hx _ => hBd x hx) hpos).elim
        · obtain ⟨K, d', hK, hd'0, hd'd, hfl⟩ :=
            depth_le_two_const_left_expvar_right_floor hα hBL hd hd1 hpos
          exact ⟨K, d', hK, hd'0, hd'd, linear_floor_to_quad hK (le_trans hd'd hd1) hfl⟩
      · -- `A` bounded and moving
        rcases depth_le_one_right_tetrachotomy B hB with
          ⟨β, hβ⟩ | hBv | hBd | ⟨L, hBL⟩
        · obtain ⟨K, d', hK, hd'0, hd'd, hfl⟩ :=
            depth_le_two_const_right_floor hA hβ hd hd1 hpos
          exact ⟨K, d', hK, hd'0, hd'd, linear_floor_to_quad hK (le_trans hd'd hd1) hfl⟩
        · exact hvarfloor A B hBv
        · refine (depth_le_two_bounded_left_diverging_right_absurd
            (W := G * exp (exp 1 - 1)) hd hd1 (fun x hx hxd => ?_)
            (fun x hx _ => hBd x hx) hpos).elim
          refine le_trans (hupp x hx) ?_
          refine mul_le_mul_of_nonneg_left (exp_monotone ?_) (le_of_lt hG)
          have s := add_le_add_wit (exp_monotone (le_trans hxd hd1)) (le_refl (-1 : Real))
          have l : exp x + -1 = exp x - 1 := by mach_mpoly [exp x]
          have r : exp 1 + -1 = exp 1 - 1 := by mach_mpoly [exp 1]
          rw [l, r] at s; exact s
        · exact rung2_expvar_right_floor hG hBL hlow hupp hnec hd hd1 hpos

/-- # ▸▸▸ **The depth-3 bounded-left case is CLOSED, unconditionally.**

`rung2_positive_floor` discharges the hypothesis of `depth3_bounded_left_of_rung2`, so a left child
that stays bounded near `0` cannot produce `1/x` at depth 3 — no shape analysis of `t2` at the call
site, and no residual hypothesis.

With the two rank-mismatch theorems (`depth3_left_unbounded_absurd` at `∞`,
`depth3_left_pole_at_zero_absurd` at `0⁺`) covering the diverging left children, this is the third
and last behavioural class of depth-3 left child. -/
theorem depth3_bounded_left_absurd {t1 t2 : EMLTree} {W d : Real}
    (ht2 : t2.depth ≤ 2) (hd : 0 < d) (hd1 : d ≤ 1)
    (hW : ∀ x : Real, 0 < x → x ≤ d → exp (t1.eval x) ≤ W)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x) : False :=
  depth3_bounded_left_of_rung2 hd hd1 hW
    (fun d₀ hd₀0 hd₀d hposr =>
      rung2_positive_floor t2 ht2 hd₀0 (le_trans hd₀d hd1) hposr)
    h

/-- **Where a constant-valued left child fails to stay bounded.**

`t1 = eml (const α) B` has `exp (t1 x) = exp(exp α)/B x`, so it is bounded near `0` exactly when `B`
stays off `0`. Running `B`'s six shapes finds precisely two escapes: `B = var`, and
`B = eml var (const q)` at `log q = 1` — the two shapes whose value *reaches* `0` at the origin.
Everything else is bounded, by a positive floor on `B` or by the clamp. -/
theorem const_left_bounded_or_gap (α : Real) (B : EMLTree) (hB : B.depth ≤ 1) :
    (∃ W d : Real, 0 < d ∧ d ≤ 1 ∧ ∀ x : Real, 0 < x → x ≤ d →
        exp ((EMLTree.eml (EMLTree.const α) B).eval x) ≤ W)
    ∨ (B = EMLTree.var)
    ∨ (∃ q : Real, B = EMLTree.eml EMLTree.var (EMLTree.const q) ∧ log q = 1) := by
  -- a constant-valued `B` with a positive value, or clamped
  have hsplit : ∀ β : Real, (∀ x : Real, 0 < x → B.eval x = β) →
      (∃ W d : Real, 0 < d ∧ d ≤ 1 ∧ ∀ x : Real, 0 < x → x ≤ d →
        exp ((EMLTree.eml (EMLTree.const α) B).eval x) ≤ W) := by
    intro β hβ
    rcases lt_total 0 β with hp | hz | hn
    · exact ⟨exp (exp α - log β), 1, one_pos, le_refl 1,
        exp_const_left_bounded hp (fun x hx _ => le_of_eq (hβ x hx).symm)⟩
    · exact ⟨exp (exp α), 1, one_pos, le_refl 1,
        exp_const_left_bounded_clamped (fun x hx _ => by rw [hβ x hx, ← hz]; exact le_refl _)⟩
    · exact ⟨exp (exp α), 1, one_pos, le_refl 1,
        exp_const_left_bounded_clamped (fun x hx _ => by rw [hβ x hx]; exact le_of_lt hn)⟩
  cases B with
  | const q => exact Or.inl (hsplit q (fun _ _ => rfl))
  | var => exact Or.inr (Or.inl rfl)
  | eml a b =>
      cases a with
      | eml _ _ => exact absurd hB (by simp only [EMLTree.depth]; omega)
      | const p =>
          cases b with
          | eml _ _ => exact absurd hB (by simp only [EMLTree.depth]; omega)
          | const q => exact Or.inl (hsplit (exp p - log q) (fun _ _ => rfl))
          | var =>
              -- `exp p − log x ≥ exp p > 0` on `(0,1]`
              refine Or.inl ⟨exp (exp α - log (exp p)), 1, one_pos, le_refl 1, ?_⟩
              refine exp_const_left_bounded (exp_pos p) (fun x hx hx1 => ?_)
              show exp p ≤ exp p - log x
              have s := add_le_add_wit (le_refl (exp p))
                (neg_le_neg_wit (log_nonpos_of_le_one hx hx1))
              have l : exp p + -(0 : Real) = exp p := by mach_ring
              have r : exp p + -log x = exp p - log x := by mach_mpoly [exp p, log x]
              rw [l, r] at s; exact s
      | var =>
          cases b with
          | eml _ _ => exact absurd hB (by simp only [EMLTree.depth]; omega)
          | const q =>
              rcases lt_total (log q) 1 with hq | hq | hq
              · -- `exp x − log q ≥ 1 − log q > 0`
                have hb0 : (0 : Real) < 1 - log q := by
                  have u := add_lt_add_left hq (-log q)
                  have l : -log q + log q = (0 : Real) := by mach_ring
                  have r : -log q + 1 = 1 - log q := by mach_mpoly [log q]
                  rw [l, r] at u; exact u
                refine Or.inl ⟨exp (exp α - log (1 - log q)), 1, one_pos, le_refl 1, ?_⟩
                refine exp_const_left_bounded hb0 (fun x hx _ => ?_)
                show (1 : Real) - log q ≤ exp x - log q
                have s := add_le_add_wit (one_le_exp (le_of_lt hx)) (le_refl (-log q))
                have l : (1 : Real) + -log q = 1 - log q := by mach_mpoly [log q]
                have r : exp x + -log q = exp x - log q := by mach_mpoly [exp x, log q]
                rw [l, r] at s; exact s
              · exact Or.inr (Or.inr ⟨q, rfl, hq⟩)
              · -- `log q > 1`: clamped below `log (log q)`
                have hlq : (0 : Real) < log q := lt_trans_ax one_pos hq
                obtain ⟨w, hwpos, hw1, hwL⟩ :=
                  two_bound_witness' one_pos (log_pos_of_one_lt hq)
                refine Or.inl ⟨exp (exp α), w, hwpos, le_of_lt hw1, ?_⟩
                refine exp_const_left_bounded_clamped (fun x hx hxw => ?_)
                show exp x - log q ≤ 0
                have hlt : exp x < log q := by
                  have s := exp_lt (lt_of_le_of_lt hxw hwL)
                  rwa [exp_log hlq] at s
                have u := add_le_add_wit (le_of_lt hlt) (le_refl (-log q))
                have l : exp x + -log q = exp x - log q := by mach_mpoly [exp x, log q]
                have r : log q + -log q = (0 : Real) := by mach_ring
                rw [l, r] at u; exact u
          | var =>
              -- `exp x − log x ≥ 1` on `(0,1]`
              refine Or.inl ⟨exp (exp α - log 1), 1, one_pos, le_refl 1, ?_⟩
              refine exp_const_left_bounded one_pos (fun x hx hx1 => ?_)
              show (1 : Real) ≤ exp x - log x
              have s := add_le_add_wit (one_le_exp (le_of_lt hx))
                (neg_le_neg_wit (log_nonpos_of_le_one hx hx1))
              have l : (1 : Real) + -(0 : Real) = 1 := by mach_ring
              have r : exp x + -log x = exp x - log x := by mach_mpoly [exp x, log x]
              rw [l, r] at s; exact s

/-- The endgame shared by the pole arguments: `c·exp T ≤ T + log CC` is impossible once `T` is past
an explicit threshold. The `+1` in the threshold is what makes the contradiction **strict** —
without it `exp_ge_add_const` and the hypothesis are merely compatible at equality. -/
theorem exp_pole_contradiction {c CC T : Real} (hc : 0 < c) (hCC : 0 < CC)
    (hT : (1 + 1 + 1 + 1 : Real) + exp (log CC - log c + 1) ≤ log c + T)
    (hfin : c * exp T ≤ T + log CC) : False := by
  have hrw : c * exp T = exp (log c + T) := by rw [exp_add, exp_log hc]
  rw [hrw] at hfin
  have hbeat := exp_ge_add_const (log CC - log c + 1) (log c + T) hT
  have e : log c + T + (log CC - log c + 1) = T + log CC + 1 := by
    mach_mpoly [log c, T, log CC]
  rw [e] at hbeat
  have s := le_trans hbeat hfin
  have u := add_le_add_wit s (le_refl (-(T + log CC)))
  have l : T + log CC + 1 + -(T + log CC) = 1 := by mach_mpoly [T, log CC]
  have r : T + log CC + -(T + log CC) = (0 : Real) := by mach_ring
  rw [l, r] at u
  exact lt_irrefl_ax _ (lt_of_lt_of_le one_pos u)

/-- # ▸▸▸ **A LOG-SCALE pole in the left child is fatal, when its constant is positive.**

`t1 x ≥ c₀ − log x` with `c₀ > 0` gives `exp (t1 x) ≥ exp(c₀)·(1/x)` with `exp c₀ > 1` **strictly**.
The equation then leaves a positive residue after its own `1/x` is subtracted, so
`log (t2 x) ≥ (exp c₀ − 1)/x` and `t2` would have to be a double exponential in `1/x` — which the
depth-2 growth ceiling forbids.

This is the **third** pole regime, and the one the other two missed:
`depth3_bounded_left_absurd` wants `exp (t1 x)` bounded, and `depth3_left_pole_at_zero_absurd` wants
`t1 ≍ 1/x` (already a double exponential). A left child growing only like `−log x` sits between them.

Stated at an abstract evaluation point `x = exp(−T)` with its obligations as hypotheses, so the
proof carries no threshold arithmetic — the same design as the rank-mismatch theorems, and the
reason this one fits on a page.

`1 ≤ C` rather than `0 < C` because `log_le_of_le_exp_mul'` needs it; a caller can always enlarge a
growth ceiling, so this costs nothing. -/
theorem depth3_log_pole_at_absurd {t1 t2 : EMLTree} {c₀ C T : Real}
    (hc₀ : 0 < c₀) (hC1 : 1 ≤ C) (hT0 : 0 ≤ T)
    (hT : (1 + 1 + 1 + 1 : Real) + exp (log C - log (exp c₀ - 1) + 1)
        ≤ log (exp c₀ - 1) + T)
    (hlow : c₀ + T ≤ t1.eval (exp (-T)))
    (hceil : exp (-T) * t2.eval (exp (-T)) ≤ C)
    (h : ∀ x : Real, 0 < x → (EMLTree.eml t1 t2).eval x = 1 / x) : False := by
  have hx0 : (0 : Real) < exp (-T) := exp_pos _
  have hcpos : (0 : Real) < exp c₀ - 1 := by
    have h1 : (1 : Real) < exp c₀ := by
      have t := exp_lt hc₀; rwa [exp_zero] at t
    have u := add_lt_add_left h1 (-1 : Real)
    have l : (-1 : Real) + 1 = 0 := by mach_ring
    have r : (-1 : Real) + exp c₀ = exp c₀ - 1 := by mach_mpoly [exp c₀]
    rw [l, r] at u; exact u
  have hm : exp T * exp (-T) = 1 := by
    rw [← exp_add]
    have e : T + -T = (0 : Real) := by mach_ring
    rw [e, exp_zero]
  -- `1/x = exp T`
  have hinv : (1 : Real) / exp (-T) = exp T := by
    have hmi := mul_inv (exp (-T)) (ne_of_gt hx0)
    have s : exp T * (exp (-T) * (1 / exp (-T))) = exp T * 1 := by rw [hmi]
    have l : exp T * (exp (-T) * (1 / exp (-T)))
        = (exp T * exp (-T)) * (1 / exp (-T)) := by
      mach_mpoly [exp T, exp (-T), (1 / exp (-T) : Real)]
    rw [l, hm] at s
    have e1 : (1 : Real) * (1 / exp (-T)) = 1 / exp (-T) := by
      mach_mpoly [(1 / exp (-T) : Real)]
    have e2 : exp T * (1 : Real) = exp T := by mach_mpoly [exp T]
    rw [e1, e2] at s; exact s
  -- the residue: `log (t2 x) ≥ (exp c₀ − 1)·exp T`
  have heq := h _ hx0
  rw [hinv] at heq
  have hexp : exp c₀ * exp T ≤ exp (t1.eval (exp (-T))) := by
    have s := exp_monotone hlow
    rwa [exp_add] at s
  have hlogt2 : (exp c₀ - 1) * exp T ≤ log (t2.eval (exp (-T))) := by
    have s := add_le_add_wit hexp (le_refl (-exp T))
    have l : exp c₀ * exp T + -exp T = (exp c₀ - 1) * exp T := by
      mach_mpoly [exp c₀, exp T]
    have r : exp (t1.eval (exp (-T))) + -exp T = log (t2.eval (exp (-T))) := by
      have e : exp T = exp (t1.eval (exp (-T))) - log (t2.eval (exp (-T))) := heq.symm
      rw [e]
      mach_mpoly [exp (t1.eval (exp (-T))), log (t2.eval (exp (-T)))]
    rw [l, r] at s; exact s
  -- the ceiling: `log (t2 x) ≤ T + log C`
  have ht2up : t2.eval (exp (-T)) ≤ exp T * C := by
    have s2 := mul_le_mul_of_nonneg_left hceil (le_of_lt (exp_pos T))
    have l : exp T * (exp (-T) * t2.eval (exp (-T)))
        = (exp T * exp (-T)) * t2.eval (exp (-T)) := by
      mach_mpoly [exp T, exp (-T), t2.eval (exp (-T))]
    rw [l, hm] at s2
    have e1 : (1 : Real) * t2.eval (exp (-T)) = t2.eval (exp (-T)) := by
      mach_mpoly [t2.eval (exp (-T))]
    rw [e1] at s2; exact s2
  exact exp_pole_contradiction hcpos (lt_of_lt_of_le one_pos hC1) hT
    (le_trans hlogt2 (log_le_of_le_exp_mul' hT0 hC1 ht2up))

/-- **The pole theorem's threshold, once and for all.** Produces a `T` meeting all four obligations
of `depth3_log_pole_at_absurd` simultaneously. Every constraint is met by a *sum of positive terms*
— this corpus has no `max`, and a sum dominating each summand is how it does that. -/
theorem pole_threshold_exists (c₀ C d₁ d₂ : Real) (hc₀ : 0 < c₀) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) :
    ∃ T : Real, 0 ≤ T
      ∧ ((1 + 1 + 1 + 1 : Real) + exp (log C - log (exp c₀ - 1) + 1)
          ≤ log (exp c₀ - 1) + T)
      ∧ exp (-T) ≤ d₁ ∧ exp (-T) ≤ d₂ := by
  have hcpos : (0 : Real) < exp c₀ - 1 := by
    have h1 : (1 : Real) < exp c₀ := by
      have t := exp_lt hc₀; rwa [exp_zero] at t
    have u := add_lt_add_left h1 (-1 : Real)
    have l : (-1 : Real) + 1 = 0 := by mach_ring
    have r : (-1 : Real) + exp c₀ = exp c₀ - 1 := by mach_mpoly [exp c₀]
    rw [l, r] at u; exact u
  refine ⟨(1 + 1 + 1 + 1 : Real) + exp (-log d₁) + exp (-log d₂)
      + exp (log C - log (exp c₀ - 1) + 1) + exp (-log (exp c₀ - 1)), ?_, ?_, ?_, ?_⟩
  · exact le_of_lt (add_pos (add_pos (add_pos (add_pos
      (add_pos (add_pos (add_pos one_pos one_pos) one_pos) one_pos)
      (exp_pos _)) (exp_pos _)) (exp_pos _)) (exp_pos _))
  · -- the surplus is `log c + exp (−log c)` plus two positives
    have hkey : (0 : Real) < log (exp c₀ - 1) + exp (-log (exp c₀ - 1)) := by
      have s := exp_grows_strictly_thm (-log (exp c₀ - 1))
      have u := add_lt_add_left s (log (exp c₀ - 1))
      have l : log (exp c₀ - 1) + -log (exp c₀ - 1) = (0 : Real) := by mach_ring
      rw [l] at u; exact u
    have hsum : (0 : Real) < exp (-log d₁) + exp (-log d₂)
        + (log (exp c₀ - 1) + exp (-log (exp c₀ - 1))) :=
      add_pos (add_pos (exp_pos _) (exp_pos _)) hkey
    have u := add_le_add_wit (le_refl ((1 + 1 + 1 + 1 : Real)
      + exp (log C - log (exp c₀ - 1) + 1))) (le_of_lt hsum)
    have l : (1 + 1 + 1 + 1 : Real) + exp (log C - log (exp c₀ - 1) + 1) + 0
        = (1 + 1 + 1 + 1 : Real) + exp (log C - log (exp c₀ - 1) + 1) := by
      mach_mpoly [exp (log C - log (exp c₀ - 1) + 1)]
    have r : (1 + 1 + 1 + 1 : Real) + exp (log C - log (exp c₀ - 1) + 1)
          + (exp (-log d₁) + exp (-log d₂)
            + (log (exp c₀ - 1) + exp (-log (exp c₀ - 1))))
        = log (exp c₀ - 1) + ((1 + 1 + 1 + 1 : Real) + exp (-log d₁) + exp (-log d₂)
          + exp (log C - log (exp c₀ - 1) + 1) + exp (-log (exp c₀ - 1))) := by
      mach_mpoly [exp (log C - log (exp c₀ - 1) + 1), exp (-log d₁), exp (-log d₂),
        log (exp c₀ - 1), exp (-log (exp c₀ - 1))]
    rw [l, r] at u; exact u
  · -- `exp (−T) ≤ d₁`
    refine le_trans (exp_monotone ?_) (le_of_eq (exp_log hd₁))
    have s := add_le_add_wit (add_le_add_wit (add_le_add_wit (add_le_add_wit
      (le_of_lt (add_pos (add_pos (add_pos one_pos one_pos) one_pos) one_pos))
      (le_of_lt (exp_grows_strictly_thm (-log d₁)))) (le_of_lt (exp_pos (-log d₂))))
      (le_of_lt (exp_pos (log C - log (exp c₀ - 1) + 1))))
      (le_of_lt (exp_pos (-log (exp c₀ - 1))))
    have e : (0 : Real) + -log d₁ + 0 + 0 + 0 = -log d₁ := by mach_ring
    rw [e] at s
    have u := neg_le_neg_wit s
    have el : -(-log d₁) = log d₁ := by mach_ring
    rw [el] at u; exact u
  · refine le_trans (exp_monotone ?_) (le_of_eq (exp_log hd₂))
    have s := add_le_add_wit (add_le_add_wit (add_le_add_wit (add_le_add_wit
      (le_of_lt (add_pos (add_pos (add_pos one_pos one_pos) one_pos) one_pos))
      (le_of_lt (exp_pos (-log d₁)))) (le_of_lt (exp_grows_strictly_thm (-log d₂))))
      (le_of_lt (exp_pos (log C - log (exp c₀ - 1) + 1))))
      (le_of_lt (exp_pos (-log (exp c₀ - 1))))
    have e : (0 : Real) + 0 + -log d₂ + 0 + 0 = -log d₂ := by mach_ring
    rw [e] at s
    have u := neg_le_neg_wit s
    have el : -(-log d₂) = log d₂ := by mach_ring
    rw [el] at u; exact u

/-- # ▸▸▸▸ **THE LAST DEPTH-3 SHAPE.** `t1 = eml A (eml var (const q))`, `A` constant-valued,
`log q = 1`.

Here `B x = exp x − 1 → 0⁺`, so `t1 x = exp α − log (exp x − 1)` runs to `+∞` like `−log x`. Below a
cutoff `δ < exp α`, `exp x − 1 ≤ x·exp δ` gives

`t1 x ≥ (exp α − δ) − log x`

with the constant `exp α − δ` **strictly positive** — which is exactly what
`depth3_log_pole_at_absurd` needs. The strictness is the whole content: `exp α > 0` for every `α`,
so a `δ` below it always exists, and the pole's residue never vanishes. -/
theorem depth3_const_left_expvar_one_absurd {α q : Real} {A B t2 : EMLTree}
    (hA : ∀ x : Real, 0 < x → A.eval x = α)
    (hBq : ∀ x : Real, 0 < x → B.eval x = exp x - log q) (hq : log q = 1)
    (ht2 : t2.depth ≤ 2)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml A B) t2).eval x = 1 / x) : False := by
  obtain ⟨δ, hδpos, hδ1, hδα⟩ := two_bound_witness' one_pos (exp_pos α)
  obtain ⟨C, δ₂, hδ₂0, hδ₂1, hC⟩ := depth_le_two_growth_ceiling t2 ht2
  have hC1 : (1 : Real) ≤ 1 + exp C := by
    have s := add_le_add_wit (le_refl (1 : Real)) (le_of_lt (exp_pos C))
    have e : (1 : Real) + 0 = 1 := by mach_ring
    rw [e] at s; exact s
  have hc₀ : (0 : Real) < exp α - δ := by
    have u := add_lt_add_left hδα (-δ)
    have l : -δ + δ = (0 : Real) := by mach_ring
    have r : -δ + exp α = exp α - δ := by mach_mpoly [δ, exp α]
    rw [l, r] at u; exact u
  obtain ⟨T, hT0, hT, hTδ, hTδ₂⟩ :=
    pole_threshold_exists (exp α - δ) (1 + exp C) δ δ₂ hc₀ hδpos hδ₂0
  have hx0 : (0 : Real) < exp (-T) := exp_pos _
  refine depth3_log_pole_at_absurd hc₀ hC1 hT0 hT ?_ ?_ h
  · -- `t1 (exp (−T)) ≥ (exp α − δ) + T`
    show exp α - δ + T ≤ exp (A.eval (exp (-T))) - log (B.eval (exp (-T)))
    rw [hA _ hx0, hBq _ hx0, hq]
    have hupos : (0 : Real) < exp (exp (-T)) - 1 := by
      have s : (1 : Real) < exp (exp (-T)) := by
        have t := exp_lt hx0; rwa [exp_zero] at t
      have u := add_lt_add_left s (-1 : Real)
      have l : (-1 : Real) + 1 = 0 := by mach_ring
      have r : (-1 : Real) + exp (exp (-T)) = exp (exp (-T)) - 1 := by
        mach_mpoly [exp (exp (-T))]
      rw [l, r] at u; exact u
    -- `exp x − 1 ≤ x·exp x ≤ x·exp δ` below `δ`
    have hle : exp (exp (-T)) - 1 ≤ exp (-T) * exp δ :=
      le_trans exp_sub_one_le_mul_exp
        (mul_le_mul_of_nonneg_left (exp_monotone hTδ) (le_of_lt hx0))
    have hlog : log (exp (exp (-T)) - 1) ≤ -T + δ := by
      have s := log_le_log hupos hle
      rwa [log_mul hx0 (exp_pos δ), log_exp, log_exp] at s
    have s := add_le_add_wit (le_refl (exp α)) (neg_le_neg_wit hlog)
    have l : exp α + -(-T + δ) = exp α - δ + T := by mach_mpoly [exp α, T, δ]
    have r : exp α + -log (exp (exp (-T)) - 1)
        = exp α - log (exp (exp (-T)) - 1) := by
      mach_mpoly [exp α, log (exp (exp (-T)) - 1)]
    rw [l, r] at s; exact s
  · -- the ceiling, enlarged to `1 + exp C`
    refine le_trans (hC _ hx0 hTδ₂) ?_
    have u := add_le_add_wit (le_of_lt one_pos) (le_of_lt (exp_grows_strictly_thm C))
    have e : (0 : Real) + C = C := by mach_ring
    rw [e] at u; exact u

/-- The constant-valued-left-child branch of the depth-3 dispatch, factored out so both shapes that
produce a constant value (`const c` and `eml (const p) (const q)`) share it. -/
theorem depth3_const_left_dispatch {α : Real} {A B t2 : EMLTree}
    (hA1 : A.depth ≤ 1) (hA : ∀ x : Real, 0 < x → A.eval x = α)
    (hB : B.depth ≤ 1) (ht2 : t2.depth ≤ 2)
    (h : ∀ x : Real, 0 < x →
      (EMLTree.eml (EMLTree.eml A B) t2).eval x = 1 / x) : False := by
  have hswap : ∀ x : Real, 0 < x →
      (EMLTree.eml A B).eval x = (EMLTree.eml (EMLTree.const α) B).eval x := by
    intro x hx
    show exp (A.eval x) - log (B.eval x) = exp α - log (B.eval x)
    rw [hA x hx]
  rcases const_left_bounded_or_gap α B hB with ⟨W, d, hd, hd1, hW⟩ | hBv | ⟨q, hBq, hq⟩
  · refine depth3_bounded_left_absurd (W := W) ht2 hd hd1 (fun x hx hxd => ?_) h
    rw [hswap x hx]
    exact hW x hx hxd
  · subst hBv
    exact depth3_left_eml_var_absurd hA1 ht2 h
  · subst hBq
    exact depth3_const_left_expvar_one_absurd hA (fun _ _ => rfl) hq ht2 h

/-- # ▸▸▸▸▸ **`1/x ∉ EML₃`.**

Every depth-≤3 tree fails to be `1/x` on the positives. The dispatch sends an arbitrary depth-≤2
left child into exactly one of the behavioural classes proved above; nothing here is new
mathematics, only the case analysis that shows the classes are exhaustive.

Together with `inv_x_mem_EML` (a depth-6 witness) and `inv_x_not_in_eml_depth_le_2`, this settles
**`d(1/x) = 4`** — the depth question the arm has carried since it began. -/
theorem inv_x_not_in_eml_depth_le_3 (t : EMLTree) (ht : t.depth ≤ 3)
    (h : ∀ x : Real, 0 < x → t.eval x = 1 / x) : False := by
  cases t with
  | const c => exact inv_x_not_in_eml_depth_le_2 _ (by simp only [EMLTree.depth]; omega) h
  | var => exact inv_x_not_in_eml_depth_le_2 _ (by simp only [EMLTree.depth]; omega) h
  | eml t1 t2 =>
      have ht1 : t1.depth ≤ 2 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_left t1.depth t2.depth
        omega
      have ht2 : t2.depth ≤ 2 := by
        simp only [EMLTree.depth] at ht
        have := Nat.le_max_right t1.depth t2.depth
        omega
      cases t1 with
      | const c => exact depth3_leaf_const_absurd ht2 h
      | var => exact leaf_var_absurd ht2 h
      | eml A B =>
          have hA : A.depth ≤ 1 := by
            simp only [EMLTree.depth] at ht1
            have := Nat.le_max_left A.depth B.depth
            omega
          have hB : B.depth ≤ 1 := by
            simp only [EMLTree.depth] at ht1
            have := Nat.le_max_right A.depth B.depth
            omega
          cases A with
          | const c =>
              exact depth3_const_left_dispatch (α := c) hA (fun _ _ => rfl) hB ht2 h
          | var => exact depth3_left_var_left_absurd hB ht2 h
          | eml a b =>
              cases a with
              | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
              | const p =>
                  cases b with
                  | eml _ _ => exact absurd hA (by simp only [EMLTree.depth]; omega)
                  | const q =>
                      exact depth3_const_left_dispatch (α := exp p - log q) hA
                        (fun _ _ => rfl) hB ht2 h
                  | var => exact depth3_left_pole_at_zero_absurd hB ht2 h
              | var =>
                  have hb : b.depth ≤ 1 := by
                    simp only [EMLTree.depth] at hA
                    have := Nat.le_max_right EMLTree.var.depth b.depth
                    omega
                  exact depth3_left_eml_var_left_absurd hb hB ht2 h

/-- # ▸▸▸▸▸▸ **`d(1/x) = 4`.**

The depth question this arm has carried since it began. `invX4` is a depth-4 reciprocal
(`invX4_eval`, `invX4_depth`), and no tree of depth ≤ 3 is one — so 4 is attained and minimal.

The bracket's history: the arm spent 28 sessions trying to prove `1/x ∉ EML` at *any* depth, which
was false; `inv_x_mem_EML` refuted it with a depth-6 witness, `invX4` improved that to 4, and the
question turned from expressibility into complexity. `2 ≤ d` came first, then `3 ≤ d`, and the last
step was the depth-3 exclusion above. -/
theorem inv_x_depth_eq_four :
    (∀ x : Real, 0 < x → invX4.eval x = 1 / x) ∧ invX4.depth = 4
    ∧ ∀ t : EMLTree, t.depth ≤ 3 → ¬ (∀ x : Real, 0 < x → t.eval x = 1 / x) :=
  ⟨invX4_eval, invX4_depth, fun t ht h => inv_x_not_in_eml_depth_le_3 t ht h⟩

/-- # ▸ **`s(1/x) ∈ {9, 11}`** — the size bracket, sharpened by the depth result.

`inv_x_size_ge_seven` came from `depth ≤ 2` being impossible. With `depth ≤ 3` now impossible too,
the bridge `2·depth + 1 ≤ size` gives `size ≥ 9` directly, and `size_odd` rules out 10. `invX4`
caps it at 11.

**Still not `s = 11`.** A 9-node depth-4 reciprocal would undercut `invX4` and nothing here excludes
it — the depth arm cannot, since 9 nodes permit depth 4. That was flagged before the depth work
began and it survives the depth work exactly as flagged. -/
theorem inv_x_size_ge_nine (t : EMLTree) (h : ∀ x : Real, 0 < x → t.eval x = 1 / x) :
    9 ≤ t.size := by
  obtain ⟨k, hk⟩ := size_odd t
  have hd := two_mul_depth_succ_le_size t
  rcases Nat.lt_or_ge t.size 9 with hlt | hge
  · exfalso
    -- `size < 9` with `size` odd gives `size ≤ 7`, hence `depth ≤ 3`
    have hs7 : t.size ≤ 7 := by omega
    have hdep : t.depth ≤ 3 := by omega
    exact inv_x_not_in_eml_depth_le_3 t hdep h
  · exact hge

/-- The size bracket, with both ends. -/
theorem inv_x_size_nine_or_eleven (t : EMLTree)
    (h : ∀ x : Real, 0 < x → t.eval x = 1 / x)
    (hmin : ∀ u : EMLTree, (∀ x : Real, 0 < x → u.eval x = 1 / x) → t.size ≤ u.size) :
    t.size = 9 ∨ t.size = 11 := by
  have hlow := inv_x_size_ge_nine t h
  have hup : t.size ≤ 11 := by
    have h11 : invX4.size = 11 := by rfl
    have := hmin invX4 invX4_eval
    omega
  obtain ⟨k, hk⟩ := size_odd t
  omega

end MachLib