import MachLib.EMLDeepestNode
import MachLib.LambertW   -- two_lt_exp_one
import MachLib.CosNotInEML -- one_lt_exp_one

/-!
# Depth-2 case 9, the `u2` row — closed, 4 of 4

The smallest case-9 nodes have **depth 2**: `eml u w` with `u`, `w` each depth 1, so each is one of
four shapes — a 4×4 table. **This file closes ONE ROW**, and it is the row that matters.

`u2 a := eml (const a) var` has `exp (u2.eval x) = exp (exp a) / x` **exactly**. It is *the*
mechanism that produces `K/x` at all — the census's sweep found every reachable depth-2 `K` coming
from this left child. **The row asks which right children can pair with it.**

Division-free master equation (`u2_master`), from the existing `left_var_gen_eval_scaled`:

```
x · log (w.eval x)  =  exp (exp a) − K
```

| cell | `w` | `W(x)` | closed by |
|---|---|---|---|
| **w1** | `eml (const c₁) (const c₂)` | a constant | **the EXISTING two-point theorem** — not new reach |
| **w2** | `eml (const a′) var` | `B − log x` | **`u2_nonpos_forces_K_gt_one`, ONE point** |
| **w3** | `eml var (const c′)` | `exp x − L′` | splits — one point, or strict monotonicity |
| **w4** | `eml var var` | `exp x − log x` | two points; **reaches NO `K/x` at all** |

## What the totalisation of `log` does here

**`w2` needs only ONE point.** At `x = exp B` the child is exactly `0`, and this corpus totalises
`log 0 = 0`, so the master equation reads `x · 0 = exp (exp a) − K` and pins `K = exp (exp a) > 1`
immediately.

> **The totalisation — normally a nuisance, and the source of four over-strong hypotheses recorded
> on 2026-08-05 — is load-bearing here.** It also makes the pre-registered *two*-point plan for `w2`
> unnecessary: one point suffices, which is stronger than predicted.

## ⚠ SCOPE

**Three of four rows are untouched** (`u1`, `u3`, `u4` — 12 of 16 cells), **depth 2 only**, and case
9 at depth ≥ 3 is the general obstacle. **`1/x ∉ EML` is untouched.**
-/

namespace MachLib
namespace Real

open EMLTree

/-! ## The master equation and its two immediate consequences -/

/-- **`exp (exp a) > 1`**, for every `a`. The floor the whole row rests on. -/
theorem exp_exp_gt_one (a : Real) : 1 < exp (exp a) := by
  have h : exp (0 : Real) < exp (exp a) := exp_lt (exp_pos a)
  rw [exp_zero] at h
  exact h

/-- **The `u2` master equation, division-free.** `x · log (w.eval x) = exp (exp a) − K`. -/
theorem u2_master {a K x : Real} (w : EMLTree) (hx : 0 < x)
    (e : x * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) w).eval x = K) :
    x * log (w.eval x) = exp (exp a) - K := by
  have hs := left_var_gen_eval_scaled (EMLTree.const a) w x hx
  rw [e] at hs
  have hs2 : K = exp (exp a) - x * log (w.eval x) := hs
  have e2 : x * log (w.eval x) = exp (exp a) - (exp (exp a) - x * log (w.eval x)) := by mach_ring
  rw [e2, ← hs2]

/-- **ONE point where the right child is non-positive pins `K = exp (exp a) > 1`.**

The totalisation `log (≤0) = 0` collapses the master equation's whole right-hand term. **Strictly
stronger than the two-point route**, and it is what closes `w2` and half of `w3`. -/
theorem u2_nonpos_forces_K_gt_one {a K x : Real} {w : EMLTree} (hx : 0 < x)
    (hnp : w.eval x ≤ 0)
    (e : x * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var) w).eval x = K) :
    1 < K := by
  have hm := u2_master w hx e
  rw [log_nonpos hnp] at hm
  have h0 : (0 : Real) = exp (exp a) - K := by rw [← hm]; mach_ring
  have hK : K = exp (exp a) := by
    have ee : K = exp (exp a) - (exp (exp a) - K) := by mach_ring
    rw [ee, ← h0]; mach_ring
  rw [hK]
  exact exp_exp_gt_one a

/-! ## Small numeric facts, all from `two_lt_exp_one` — no `exp_tangent_line_strict` -/

/-- `0 < 1 + 1`. -/
theorem one_add_one_pos : (0 : Real) < 1 + 1 := lt_trans_ax zero_lt_one_ax one_lt_one_plus_one

/-- `1 ≠ 1 + 1`. -/
theorem one_ne_two : (1 : Real) ≠ 1 + 1 := by
  intro h
  have hlt : (1 : Real) < 1 + 1 := one_lt_one_plus_one
  rw [← h] at hlt
  exact lt_irrefl_ax 1 hlt

/-- `p < q → p − r < q − r`. Local: the corpus's copy lives behind an import this file does not
take. -/
theorem sub_lt_sub_right_lt {p q : Real} (h : p < q) (r : Real) : p - r < q - r := by
  have h1 := add_lt_add_left h (-r)
  have eL : -r + p = p - r := by mach_mpoly [p, r]
  have eR : -r + q = q - r := by mach_mpoly [q, r]
  rw [eL, eR] at h1
  exact h1

/-- `a < b → 0 < c → c·a < c·b`. Local, for the same reason. -/
theorem mul_lt_mul_pos_left {a b c : Real} (h : a < b) (hc : 0 < c) : c * a < c * b := by
  have h1 := mul_lt_mul_of_pos_right h hc
  have eL : a * c = c * a := by mach_ring
  have eR : b * c = c * b := by mach_ring
  rw [eL, eR] at h1
  exact h1

/-- **`exp (exp 1) > exp 1 + 1`** — the `w4` numeric core.

Chain: `exp 1 > 1+1` ⟹ `exp (exp 1) > exp (1+1) = exp 1 · exp 1 > (1+1) · exp 1 = exp 1 + exp 1 >
exp 1 + 1`. **Uses `two_lt_exp_one` only** — the `exp_tangent_line_strict` axiom that
`var_var_not_mx` had to pay for is NOT needed. -/
theorem exp_exp_one_gt_exp_one_add_one : exp 1 + 1 < exp (exp 1) := by
  have h1 : exp (1 + 1 : Real) < exp (exp 1) := exp_lt two_lt_exp_one
  have h2 : exp (1 + 1 : Real) = exp 1 * exp 1 := exp_add 1 1
  have h3 : (1 + 1 : Real) * exp 1 < exp 1 * exp 1 :=
    mul_lt_mul_of_pos_right two_lt_exp_one (exp_pos 1)
  have h4 : exp 1 + 1 < (1 + 1 : Real) * exp 1 := by
    have hb := add_lt_add_left one_lt_exp_one (exp 1)
    have eL : exp 1 + 1 = exp 1 + 1 := rfl
    have eR : exp 1 + exp 1 = (1 + 1 : Real) * exp 1 := by mach_ring
    rw [eR] at hb
    rw [eL]
    exact hb
  rw [h2] at h1
  exact lt_trans_ax (lt_trans_ax h4 h3) h1

/-! ## w1 — ALREADY COVERED by the existing theorem, and said so -/

/-- **`w1`: the right child is constant-valued, so the existing general theorem applies unchanged.**

**This is NOT new reach.** `one_over_x_not_left_var_gen` already closes every constant-valued right
child; the only content here is supplying two points. Stated explicitly because this arm claimed
`a·sin` as new reach earlier today when a meta-lemma already had it. -/
theorem u2_w1_not_inv_x {a c₁ c₂ : Real}
    (e₁ : (1 : Real) * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var)
            (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))).eval 1 = 1)
    (e₂ : ((1 : Real) + 1) * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var)
            (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))).eval (1 + 1) = 1) :
    False :=
  one_over_x_not_left_var_gen zero_lt_one_ax one_add_one_pos one_ne_two rfl rfl e₁ e₂

/-! ## w2 — ONE point, on the totalisation of `log` -/

/-- **`w2` reaches only `K = exp (exp a) > 1`, from a SINGLE point.**

At `x = exp (exp a′)` the child `exp a′ − log x` is exactly `0`, and `log 0 = 0`. -/
theorem u2_w2_K_gt_one {a a' K : Real}
    (e : exp (exp a') * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var)
            (EMLTree.eml (EMLTree.const a') EMLTree.var)).eval (exp (exp a')) = K) :
    1 < K := by
  have hz : (EMLTree.eml (EMLTree.const a') EMLTree.var).eval (exp (exp a')) = 0 := by
    show exp a' - log (exp (exp a')) = 0
    rw [log_exp]; mach_ring
  exact u2_nonpos_forces_K_gt_one (exp_pos _) (by rw [hz]; exact le_refl 0) e

/-- **`w2` cannot reach `1/x`.** -/
theorem u2_w2_not_inv_x {a a' : Real}
    (e : exp (exp a') * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var)
            (EMLTree.eml (EMLTree.const a') EMLTree.var)).eval (exp (exp a')) = 1) :
    False :=
  lt_irrefl_ax _ (u2_w2_K_gt_one e)

/-! ## w3 — splits on `log c′`, and neither branch needs a new axiom -/

/-- **`w3`, branch `1 < log c′`: one point kills it.** At `x = log (log c′)` the child
`exp x − log c′` is exactly `0`. -/
theorem u2_w3_big_K_gt_one {a c' K : Real} (hc : 1 < log c')
    (e : log (log c') * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var)
            (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval (log (log c')) = K) :
    1 < K := by
  have hpos : (0 : Real) < log c' := lt_trans_ax zero_lt_one_ax hc
  have hlogpos : (0 : Real) < log (log c') := by
    have h := log_lt_log zero_lt_one_ax hc
    rw [log_one] at h
    exact h
  have hz : (EMLTree.eml EMLTree.var (EMLTree.const c')).eval (log (log c')) = 0 := by
    show exp (log (log c')) - log c' = 0
    rw [exp_log hpos]; mach_ring
  exact u2_nonpos_forces_K_gt_one hlogpos (by rw [hz]; exact le_refl 0) e

/-- **`w3`, branch `log c′ ≤ 1`: strict monotonicity kills it — for EVERY `K`.**

`W(x) = exp x − log c′` is `> 1` at `x = 1` (because `exp 1 > 1+1`) and strictly increasing, so
`x · log (W x)` is strictly increasing and cannot take the same value at `1` and `1+1`. -/
theorem u2_w3_small_absurd {a c' K : Real} (hc : log c' ≤ 1)
    (e₁ : (1 : Real) * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var)
            (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval 1 = K)
    (e₂ : ((1 : Real) + 1) * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var)
            (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval (1 + 1) = K) :
    False := by
  have m₁ := u2_master _ zero_lt_one_ax e₁
  have m₂ := u2_master _ one_add_one_pos e₂
  -- child values
  have v₁ : (EMLTree.eml EMLTree.var (EMLTree.const c')).eval 1 = exp 1 - log c' := rfl
  have v₂ : (EMLTree.eml EMLTree.var (EMLTree.const c')).eval (1 + 1)
      = exp (1 + 1) - log c' := rfl
  rw [v₁] at m₁
  rw [v₂] at m₂
  -- 1 < W(1)
  have hW₁ : (1 : Real) < exp 1 - log c' := by
    have hstep : (1 : Real) + 1 - 1 < exp 1 - log c' := by
      have hA : (1 : Real) + 1 < exp 1 := two_lt_exp_one
      have hB := sub_le_sub_right hc (0 : Real)
      -- 1+1 - 1 < exp 1 - log c'  from  1+1 < exp 1  and  log c' ≤ 1
      have h1 : (1 : Real) + 1 - 1 < exp 1 - 1 := by
        have := sub_lt_sub_right_lt hA (1 : Real)
        exact this
      have h2 : exp 1 - (1 : Real) ≤ exp 1 - log c' := by
        have hn : -(1 : Real) ≤ -log c' := by
          have := sub_le_sub_right hc (log c' + 1)
          have eL : (1 : Real) - (log c' + 1) = -log c' := by mach_mpoly [log c']
          have eR : log c' - (log c' + 1) = -(1 : Real) := by mach_mpoly [log c']
          rw [eL, eR] at this
          exact this
        have := add_le_add_left hn (exp 1)
        have eL : exp 1 + -(1 : Real) = exp 1 - 1 := by mach_mpoly [exp 1]
        have eR : exp 1 + -log c' = exp 1 - log c' := by mach_mpoly [exp 1, log c']
        rw [eL, eR] at this
        exact this
      exact lt_of_lt_of_le h1 h2
    have e : (1 : Real) + 1 - 1 = 1 := by mach_ring
    rw [e] at hstep
    exact hstep
  have hW₁pos : (0 : Real) < exp 1 - log c' := lt_trans_ax zero_lt_one_ax hW₁
  -- W(1) < W(1+1)
  have hWlt : exp 1 - log c' < exp (1 + 1) - log c' :=
    sub_lt_sub_right_lt (exp_lt one_lt_one_plus_one) (log c')
  -- logs
  have hlog₁ : (0 : Real) < log (exp 1 - log c') := by
    have h := log_lt_log zero_lt_one_ax hW₁
    rw [log_one] at h
    exact h
  have hlog₂ : log (exp 1 - log c') < log (exp (1 + 1) - log c') :=
    log_lt_log hW₁pos hWlt
  -- the two master equations force equality of 1·log W(1) and (1+1)·log W(1+1)
  have hEq : (1 : Real) * log (exp 1 - log c') = (1 + 1) * log (exp (1 + 1) - log c') := by
    rw [m₁, m₂]
  -- but the right side is strictly bigger
  have hstep1 : (1 + 1 : Real) * log (exp 1 - log c')
      < (1 + 1) * log (exp (1 + 1) - log c') :=
    mul_lt_mul_pos_left hlog₂ one_add_one_pos
  have hstep2 : (1 : Real) * log (exp 1 - log c') < (1 + 1) * log (exp 1 - log c') :=
    mul_lt_mul_of_pos_right one_lt_one_plus_one hlog₁
  have hfin : (1 : Real) * log (exp 1 - log c') < (1 + 1) * log (exp (1 + 1) - log c') :=
    lt_trans_ax hstep2 hstep1
  rw [hEq] at hfin
  exact lt_irrefl_ax _ hfin

/-! ## w4 — two points, and it reaches NO `K/x` at all -/

/-- **`w4` reaches no `K/x` whatsoever**, for any `a` and any `K`.

`x = 1` forces `exp (exp a) − K = 1`; `x = exp 1` then forces it to equal
`exp 1 · log (exp (exp 1) − 1)`, which exceeds `1`. -/
theorem u2_w4_absurd {a K : Real}
    (e₁ : (1 : Real) * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var)
            (EMLTree.eml EMLTree.var EMLTree.var)).eval 1 = K)
    (e₂ : exp 1 * (EMLTree.eml (EMLTree.eml (EMLTree.const a) EMLTree.var)
            (EMLTree.eml EMLTree.var EMLTree.var)).eval (exp 1) = K) :
    False := by
  have m₁ := u2_master _ zero_lt_one_ax e₁
  have m₂ := u2_master _ (exp_pos 1) e₂
  -- child at 1 is exp 1
  have v₁ : (EMLTree.eml EMLTree.var EMLTree.var).eval 1 = exp 1 := by
    show exp (1 : Real) - log (1 : Real) = exp 1
    rw [log_one]; mach_ring
  -- child at exp 1 is exp (exp 1) - 1
  have v₂ : (EMLTree.eml EMLTree.var EMLTree.var).eval (exp 1) = exp (exp 1) - 1 := by
    show exp (exp 1) - log (exp 1) = exp (exp 1) - 1
    rw [log_exp]
  rw [v₁, log_exp] at m₁
  rw [v₂] at m₂
  -- m₁ : 1 * 1 = exp (exp a) - K
  -- m₂ : exp 1 * log (exp (exp 1) - 1) = exp (exp a) - K
  have hEq : (1 : Real) * 1 = exp 1 * log (exp (exp 1) - 1) := by rw [m₁, m₂]
  -- but the right side exceeds 1
  have hgt : exp 1 < exp (exp 1) - 1 := by
    have h := exp_exp_one_gt_exp_one_add_one
    have hs := sub_lt_sub_right_lt h 1
    have eL : exp 1 + 1 - 1 = exp 1 := by mach_mpoly [exp 1]
    rw [eL] at hs
    exact hs
  have hlog : (1 : Real) < log (exp (exp 1) - 1) := by
    have h := log_lt_log (exp_pos 1) hgt
    rw [log_exp] at h
    exact h
  have hprod : exp 1 * 1 < exp 1 * log (exp (exp 1) - 1) :=
    mul_lt_mul_pos_left hlog (exp_pos 1)
  have hone : (1 : Real) * 1 < exp 1 * 1 := by
    have h := mul_lt_mul_of_pos_right one_lt_exp_one zero_lt_one_ax
    exact h
  have hfin : (1 : Real) * 1 < exp 1 * log (exp (exp 1) - 1) := lt_trans_ax hone hprod
  rw [← hEq] at hfin
  exact lt_irrefl_ax _ hfin

end Real
end MachLib
