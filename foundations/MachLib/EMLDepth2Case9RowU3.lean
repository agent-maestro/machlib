import MachLib.EMLDepth2Case9RowU4

/-!
# Depth-2 case 9, the `u3` row — and the lemma that unifies the other three

`u3 = eml var (const c₂)` has **no `var` in its right slot**, so `mul_exp_sub_log` does **not** apply
and the `x` never cancels:

```
x · exp (exp x − L) − x · log (W x) = K ,   L := log c₂
```

## ▸ ONE LEMMA UNDER ALL THE ROWS — and it explains `u2`'s exception

Every row's two-non-positive-point argument is the same theorem. With `W ≤ 0` at both points,
`log W = 0` at both, and each equation collapses to `xᵢ · exp (u.eval xᵢ) = K`. **So two points
contradict exactly when that product differs between them** (`two_nonpos_absurd_of_product_ne`).

| row | `x · exp (u.eval x)` | product differs? |
|---|---|---|
| `u1` (constant `α`) | `x · exp α` | ✅ |
| **`u2`** (`exp a − log x`) | **`exp (exp a)` — CONSTANT** | ❌ |
| `u3` (`exp x − L`) | `x · exp (exp x) · exp (−L)` | ✅ |
| `u4` (`exp x − log x`) | `exp (exp x)` | ✅ |

> ### `u2` is the exception FOR A REASON: its product is constant — the very cancellation that made `u2` cheap by the other route (one point pinning `K = exp (exp a) > 1`). Its oddity is a consequence, not an accident.

## The `u3` row

| cell | status |
|---|---|
| **w2** (`B − log x`) | ✅ two non-positive points |
| **w3**, `exp 1 < log c′` | ✅ two non-positive points |
| **w1** (constant) | ✅ **THREE points** — one second difference kills `log β` **and** `K` |
| **w3**, `log c′ ≤ exp 1`, **w4** | 🔴 **OPEN** — positive child throughout; needs a point depending on `M` and `K` |

⚠ **`w1` was first estimated at FOUR points** by counting three free parameters. **The count was
right and the conclusion wrong:** `log β` enters linearly in `x` and `K` as a constant, so a single
second difference annihilates both. **Counting parameters is not counting equations.**

**Not done, deliberately:** `u1`/`u4`'s existing proofs are *not* refactored onto the new lemma.
They are correct as they stand, and churn for elegance is not worth a regression risk.

## ⚠ Axiom disclosure

Numeric facts about `e` rest on the disclosed tangent-line axiom `exp_gt_one_plus_self` via
`two_lt_exp_one`. **`1/x ∉ EML` untouched. Depth 2 only.**
-/

namespace MachLib
namespace Real

open EMLTree

/-! ## The unifying lemma -/

/-- **Two non-positive points contradict whenever `x · exp (u.eval x)` differs between them.**

Fully general: **any** `u`, **any** `w`, **any** depth, and **no positivity hypothesis on the
points** — the proof reads none of that.

This is the shared skeleton of `const_left_two_nonpos_absurd` (`u1`) and `u4_two_nonpos_absurd`
(`u4`), and it is what `u2` cannot use, because for `u2` the product is the constant
`exp (exp a)`. -/
theorem two_nonpos_absurd_of_product_ne {u w : EMLTree} {K x₁ x₂ : Real}
    (hw₁ : w.eval x₁ ≤ 0) (hw₂ : w.eval x₂ ≤ 0)
    (hne : x₁ * exp (u.eval x₁) ≠ x₂ * exp (u.eval x₂))
    (e₁ : x₁ * (EMLTree.eml u w).eval x₁ = K)
    (e₂ : x₂ * (EMLTree.eml u w).eval x₂ = K) :
    False := by
  have v₁ : (EMLTree.eml u w).eval x₁ = exp (u.eval x₁) - log (w.eval x₁) := rfl
  have v₂ : (EMLTree.eml u w).eval x₂ = exp (u.eval x₂) - log (w.eval x₂) := rfl
  rw [v₁, log_nonpos hw₁] at e₁
  rw [v₂, log_nonpos hw₂] at e₂
  apply hne
  have r₁ : x₁ * exp (u.eval x₁) = K := by
    rw [← e₁]; mach_mpoly [x₁, exp (u.eval x₁)]
  have r₂ : x₂ * exp (u.eval x₂) = K := by
    rw [← e₂]; mach_mpoly [x₂, exp (u.eval x₂)]
  exact r₁.trans r₂.symm

/-- **`u2`'s product really is constant** — so `two_nonpos_absurd_of_product_ne` provably cannot be
used there, and `u2`'s different route was necessary rather than stylistic. -/
theorem u2_product_is_constant (a x : Real) (hx : 0 < x) :
    x * exp ((EMLTree.eml (EMLTree.const a) EMLTree.var).eval x) = exp (exp a) := by
  show x * exp (exp a - log x) = exp (exp a)
  exact mul_exp_sub_log hx

/-! ## `u3`'s product is strictly increasing -/

/-- `x · exp (exp x)` is strictly increasing on the positives. -/
theorem x_exp_exp_strict_mono {x₁ x₂ : Real} (h₁ : 0 < x₁) (h : x₁ < x₂) :
    x₁ * exp (exp x₁) < x₂ * exp (exp x₂) :=
  lt_trans_ax (mul_lt_mul_of_pos_right h (exp_pos (exp x₁)))
    (mul_lt_mul_pos_left (exp_lt (exp_lt h)) (lt_trans_ax h₁ h))

/-- **`u3`'s product differs at distinct positive points.**

`x · exp (exp x − L) = (x · exp (exp x)) · exp (−L)` and `exp (−L) > 0`, so the strict monotonicity
of `x · exp (exp x)` transfers. -/
theorem u3_product_ne {c₂ x₁ x₂ : Real} (h₁ : 0 < x₁) (h : x₁ < x₂) :
    x₁ * exp ((EMLTree.eml EMLTree.var (EMLTree.const c₂)).eval x₁)
      ≠ x₂ * exp ((EMLTree.eml EMLTree.var (EMLTree.const c₂)).eval x₂) := by
  have hsplit : ∀ y : Real, y * exp (exp y - log c₂)
      = (y * exp (exp y)) * exp (-log c₂) := by
    intro y
    have e : exp (exp y - log c₂) = exp (exp y) * exp (-log c₂) := by
      rw [← exp_add]
      have ee : exp y + -log c₂ = exp y - log c₂ := by mach_mpoly [exp y, log c₂]
      rw [ee]
    rw [e]; mach_ring
  show x₁ * exp (exp x₁ - log c₂) ≠ x₂ * exp (exp x₂ - log c₂)
  rw [hsplit x₁, hsplit x₂]
  intro heq
  have hlt : (x₁ * exp (exp x₁)) * exp (-log c₂) < (x₂ * exp (exp x₂)) * exp (-log c₂) :=
    mul_lt_mul_of_pos_right (x_exp_exp_strict_mono h₁ h) (exp_pos _)
  rw [heq] at hlt
  exact lt_irrefl_ax _ hlt

/-! ## The two cells that close -/

/-- **`u3` over `w2` is impossible.** At `exp B` and `exp (B+1)` the right child is `0` and `−1`. -/
theorem u3_w2_absurd {c₂ a' K : Real}
    (e₁ : exp (exp a') * (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c₂))
            (EMLTree.eml (EMLTree.const a') EMLTree.var)).eval (exp (exp a')) = K)
    (e₂ : exp (exp a' + 1) * (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c₂))
            (EMLTree.eml (EMLTree.const a') EMLTree.var)).eval (exp (exp a' + 1)) = K) :
    False := by
  have hz₁ : (EMLTree.eml (EMLTree.const a') EMLTree.var).eval (exp (exp a')) = 0 := by
    show exp a' - log (exp (exp a')) = 0
    rw [log_exp]; mach_ring
  have hz₂ : (EMLTree.eml (EMLTree.const a') EMLTree.var).eval (exp (exp a' + 1)) = -1 := by
    show exp a' - log (exp (exp a' + 1)) = -1
    rw [log_exp]; mach_mpoly [exp a']
  have hneg : (-1 : Real) ≤ 0 := by
    have h := add_lt_add_left zero_lt_one_ax (-1 : Real)
    have eL : (-1 : Real) + 0 = -1 := by mach_mpoly []
    have eR : (-1 : Real) + 1 = 0 := by mach_mpoly []
    rw [eL, eR] at h
    exact le_of_lt h
  exact two_nonpos_absurd_of_product_ne (by rw [hz₁]; exact le_refl 0)
    (by rw [hz₂]; exact hneg)
    (u3_product_ne (exp_pos _) (exp_lt (lt_add_of_pos_right zero_lt_one_ax))) e₁ e₂

/-- **`u3` over `w3` is impossible when `exp 1 < log c′`.** Points `1` and `log (log c′)`. -/
theorem u3_w3_big_absurd {c₂ c' K : Real} (hc : exp 1 < log c')
    (e₁ : (1 : Real) * (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c₂))
            (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval 1 = K)
    (e₂ : log (log c') * (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c₂))
            (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval (log (log c')) = K) :
    False := by
  have hlogpos : (0 : Real) < log c' := lt_trans_ax (exp_pos 1) hc
  have hone : (1 : Real) < log (log c') := by
    have h := log_lt_log (exp_pos 1) hc
    rw [log_exp] at h
    exact h
  have hnp₁ : (EMLTree.eml EMLTree.var (EMLTree.const c')).eval 1 ≤ 0 := by
    show exp 1 - log c' ≤ 0
    have h := sub_lt_sub_right_lt hc (log c')
    have eR : log c' - log c' = 0 := by mach_ring
    rw [eR] at h
    exact le_of_lt h
  have hz₂ : (EMLTree.eml EMLTree.var (EMLTree.const c')).eval (log (log c')) = 0 := by
    show exp (log (log c')) - log c' = 0
    rw [exp_log hlogpos]; mach_ring
  exact two_nonpos_absurd_of_product_ne hnp₁ (by rw [hz₂]; exact le_refl 0)
    (u3_product_ne zero_lt_one_ax hone) e₁ e₂

/-! ## `w1` — THREE points, not four

`RESULT_ROW_U3.md` estimated this cell at **four** points, by counting three free parameters
(`M`, `log β`, `K`). **The count was right and the conclusion wrong.** For a constant child the
equation is `P(x) − c·x = K`: the `c·x` term is linear and `K` is constant, so **one second
difference annihilates both.**

> ### Counting PARAMETERS is not counting EQUATIONS. -/

/-- `1 < exp 3 − exp 2`. `exp 3 = exp 2 · exp 1 > exp 2 + exp 2 > exp 2 + 1`. -/
theorem exp_three_sub_exp_two_gt_one : (1 : Real) < exp (1 + 1 + 1) - exp (1 + 1) := by
  apply lt_of_sub_pos
  have e : exp (1 + 1 + 1 : Real) - exp (1 + 1) - 1 = exp (1 + 1 + 1) - (exp (1 + 1) + 1) := by
    mach_mpoly [exp (1 + 1 + 1), exp (1 + 1)]
  rw [e]
  apply sub_pos_of_lt
  have h1 : exp (1 + 1 : Real) + 1 < exp (1 + 1) + exp (1 + 1) :=
    add_lt_add_left (lt_trans_ax one_lt_one_plus_one
      (lt_trans_ax two_lt_four exp_two_gt_four)) (exp (1 + 1))
  have h2 : exp (1 + 1 : Real) + exp (1 + 1) < exp (1 + 1 + 1) := by
    rw [exp_add (1 + 1) 1]
    have hh := mul_lt_mul_pos_left two_lt_exp_one (exp_pos (1 + 1))
    have e2 : exp (1 + 1 : Real) * ((1 : Real) + 1) = exp (1 + 1) + exp (1 + 1) := by
      mach_mpoly [exp (1 + 1)]
    rw [e2] at hh
    exact hh
  exact lt_trans_ax h1 h2

/-- **The `u3` master equation.** No positivity hypothesis on `x` — the proof reads none. -/
theorem u3_master {c₂ K x : Real} (w : EMLTree)
    (e : x * (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c₂)) w).eval x = K) :
    x * exp (exp x - log c₂) - x * log (w.eval x) = K := by
  have v : (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c₂)) w).eval x
      = exp (exp x - log c₂) - log (w.eval x) := rfl
  rw [v] at e
  have expand : x * (exp (exp x - log c₂) - log (w.eval x))
      = x * exp (exp x - log c₂) - x * log (w.eval x) := by
    mach_mpoly [x, exp (exp x - log c₂), log (w.eval x)]
  rw [expand] at e
  exact e

/-- **`u3` over `w1` is impossible.** Three points; the second difference kills `log β` and `K`
together, leaving `A₁ − 4A₂ + 3A₃ = 0`, refuted by `3A₃ > 4A₂`. -/
theorem u3_w1_absurd {c₂ d₁ d₂ K : Real}
    (e₁ : (1 : Real) * (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c₂))
            (EMLTree.eml (EMLTree.const d₁) (EMLTree.const d₂))).eval 1 = K)
    (e₂ : ((1 : Real) + 1) * (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c₂))
            (EMLTree.eml (EMLTree.const d₁) (EMLTree.const d₂))).eval (1 + 1) = K)
    (e₃ : ((1 : Real) + 1 + 1) * (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c₂))
            (EMLTree.eml (EMLTree.const d₁) (EMLTree.const d₂))).eval (1 + 1 + 1) = K) :
    False := by
  have m₁ := u3_master _ e₁
  have m₂ := u3_master _ e₂
  have m₃ := u3_master _ e₃
  have wv : ∀ y : Real, (EMLTree.eml (EMLTree.const d₁) (EMLTree.const d₂)).eval y
      = exp d₁ - log d₂ := fun _ => rfl
  rw [wv] at m₁ m₂ m₃
  -- second difference kills log β and K together
  have hsd : (1 : Real) * exp (exp 1 - log c₂)
      - ((1 + 1) * (1 + 1)) * exp (exp (1 + 1) - log c₂)
      + (1 + 1 + 1) * exp (exp (1 + 1 + 1) - log c₂) = 0 := by
    have e : (1 : Real) * exp (exp 1 - log c₂)
        - ((1 + 1) * (1 + 1)) * exp (exp (1 + 1) - log c₂)
        + (1 + 1 + 1) * exp (exp (1 + 1 + 1) - log c₂)
        = ((1 : Real) * exp (exp 1 - log c₂) - 1 * log (exp d₁ - log d₂))
          - (1 + 1) * (((1 : Real) + 1) * exp (exp (1 + 1) - log c₂)
              - (1 + 1) * log (exp d₁ - log d₂))
          + (((1 : Real) + 1 + 1) * exp (exp (1 + 1 + 1) - log c₂)
              - (1 + 1 + 1) * log (exp d₁ - log d₂)) := by
      mach_mpoly [exp (exp 1 - log c₂), exp (exp (1 + 1) - log c₂),
        exp (exp (1 + 1 + 1) - log c₂), log (exp d₁ - log d₂)]
    rw [e, m₁, m₂, m₃]
    mach_mpoly [K]
  -- A₃ > 2·A₂
  have hstep : exp (exp (1 + 1 : Real) - log c₂) * exp (exp (1 + 1 + 1) - exp (1 + 1))
      = exp (exp (1 + 1 + 1 : Real) - log c₂) := by
    rw [← exp_add]
    have e : (exp (1 + 1 : Real) - log c₂) + (exp (1 + 1 + 1) - exp (1 + 1))
        = exp (1 + 1 + 1) - log c₂ := by
      mach_mpoly [exp (1 + 1), exp (1 + 1 + 1), log c₂]
    rw [e]
  have hA3 : ((1 : Real) + 1) * exp (exp (1 + 1) - log c₂)
      < exp (exp (1 + 1 + 1) - log c₂) := by
    have hr : (1 + 1 : Real) < exp (exp (1 + 1 + 1) - exp (1 + 1)) :=
      lt_trans_ax two_lt_exp_one (exp_lt exp_three_sub_exp_two_gt_one)
    have hh := mul_lt_mul_pos_left hr (exp_pos (exp (1 + 1 : Real) - log c₂))
    rw [hstep] at hh
    have e : exp (exp (1 + 1 : Real) - log c₂) * ((1 : Real) + 1)
        = ((1 : Real) + 1) * exp (exp (1 + 1) - log c₂) := by mach_ring
    rw [e] at hh
    exact hh
  -- 3·A₃ > 4·A₂
  have hbig : ((1 + 1 : Real) * (1 + 1)) * exp (exp (1 + 1) - log c₂)
      < (1 + 1 + 1) * exp (exp (1 + 1 + 1) - log c₂) := by
    have h6 := mul_lt_mul_pos_left hA3 three_pos
    apply lt_trans_ax _ h6
    apply lt_of_sub_pos
    have e : ((1 + 1 + 1 : Real) * (((1 : Real) + 1) * exp (exp (1 + 1) - log c₂)))
        - ((1 + 1) * (1 + 1)) * exp (exp (1 + 1) - log c₂)
        = (1 + 1) * exp (exp (1 + 1) - log c₂) := by
      mach_mpoly [exp (exp (1 + 1) - log c₂)]
    rw [e]
    exact mul_pos one_add_one_pos (exp_pos _)
  -- assemble
  have hpos : (0 : Real) < (1 : Real) * exp (exp 1 - log c₂)
      - ((1 + 1) * (1 + 1)) * exp (exp (1 + 1) - log c₂)
      + (1 + 1 + 1) * exp (exp (1 + 1 + 1) - log c₂) := by
    apply lt_of_sub_pos
    have e : ((1 : Real) * exp (exp 1 - log c₂)
        - ((1 + 1) * (1 + 1)) * exp (exp (1 + 1) - log c₂)
        + (1 + 1 + 1) * exp (exp (1 + 1 + 1) - log c₂)) - 0
        = ((1 + 1 + 1) * exp (exp (1 + 1 + 1) - log c₂)
            - ((1 + 1) * (1 + 1)) * exp (exp (1 + 1) - log c₂))
          + (1 : Real) * exp (exp 1 - log c₂) := by
      mach_mpoly [exp (exp 1 - log c₂), exp (exp (1 + 1) - log c₂),
        exp (exp (1 + 1 + 1) - log c₂)]
    rw [e]
    exact add_pos_real (sub_pos_of_lt hbig)
      (by
        have hh := mul_lt_mul_pos_left (exp_pos (exp (1 : Real) - log c₂)) zero_lt_one_ax
        have eL : (1 : Real) * 0 = 0 := by mach_ring
        rw [eL] at hh
        exact hh)
  rw [hsd] at hpos
  exact lt_irrefl_ax 0 hpos

end Real
end MachLib
