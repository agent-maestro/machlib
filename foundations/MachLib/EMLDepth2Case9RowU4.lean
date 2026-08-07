import MachLib.EMLFreeScaleElimination

/-!
# Depth-2 case 9, the `u4` row — and it is EASIER than `u1`, for one identifiable reason

`u4 = eml var var` has **`var` in its left child's right slot**, so `mul_exp_sub_log` applies exactly
as it did for `u2`, and the master equation is

> ### `x · log (W x) = exp (exp x) − K`

| row | master RHS | free parameters |
|---|---|---|
| `u2` | `exp (exp a) − K` | one (the combination) |
| `u1` | `x · exp α − K` | **two**, one a **FREE SCALE** |
| **`u4`** | **`exp (exp x) − K`** | **one** (`K`) — the `x`-dependence is KNOWN |

**`u4` has no free scale.** `w4` needed three points and `(e³−2)² > e⁵` under `u1`; here it needs
**two points and a crude bound** — direct evidence that **the free scale, not the shape of `W`, was
what made `u1` hard.**

## The row

| cell | how | status |
|---|---|---|
| **w1** (constant) | three points → `exp(exp 3) > 2·exp(exp 2)` | ✅ |
| **w2** (`B − log x`) | two non-positive points | ✅ |
| **w3**, `exp 1 < log c′` | two non-positive points | ✅ |
| **w3**, `log c′ ≤ exp 1` | positive child throughout | 🔴 **OPEN** — same wall as `u1` |
| **w4** (`exp x − log x`) | **two** points | ✅ |

## ⚠ AXIOM DISCLOSURE, stated up front

Every numeric fact about `e` here rests on the disclosed tangent-line axiom `exp_gt_one_plus_self`,
reached via `two_lt_exp_one`. **This is said in advance rather than discovered afterwards** — the
correction recorded in `RESULT_FREE_SCALE.md`.

## ⚠ SCOPE

**`u3` row untouched** — its left child `eml var (const c)` has no `var` in the right slot, so
`mul_exp_sub_log` does not apply and `x · exp(exp x − L)` survives. **Depth 2 only.
`1/x ∉ EML` untouched.**
-/

namespace MachLib
namespace Real

open EMLTree

/-! ## The `u4` master equation -/

/-- **`x · log (w.eval x) = exp (exp x) − K`.** One free parameter, no free scale. -/
theorem u4_master {K x : Real} (w : EMLTree) (hx : 0 < x)
    (e : x * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) w).eval x = K) :
    x * log (w.eval x) = exp (exp x) - K := by
  have hs := left_var_gen_eval_scaled EMLTree.var w x hx
  rw [e] at hs
  have hs2 : K = exp (exp x) - x * log (w.eval x) := hs
  have e2 : x * log (w.eval x)
      = exp (exp x) - (exp (exp x) - x * log (w.eval x)) := by mach_ring
  rw [e2, ← hs2]

/-- **Two distinct non-positive points contradict.** Each forces `K = exp (exp xᵢ)`, and `exp` is
injective — so the points would have to coincide. -/
theorem u4_two_nonpos_absurd {w : EMLTree} {K x₁ x₂ : Real}
    (h₁ : 0 < x₁) (h₂ : 0 < x₂) (hne : x₁ ≠ x₂)
    (hw₁ : w.eval x₁ ≤ 0) (hw₂ : w.eval x₂ ≤ 0)
    (e₁ : x₁ * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) w).eval x₁ = K)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) w).eval x₂ = K) :
    False := by
  have m₁ := u4_master w h₁ e₁
  have m₂ := u4_master w h₂ e₂
  rw [log_nonpos hw₁] at m₁
  rw [log_nonpos hw₂] at m₂
  have k₁ : exp (exp x₁) = K := by
    have e : exp (exp x₁) = (exp (exp x₁) - K) + K := by mach_ring
    rw [e, ← m₁]; mach_ring
  have k₂ : exp (exp x₂) = K := by
    have e : exp (exp x₂) = (exp (exp x₂) - K) + K := by mach_ring
    rw [e, ← m₂]; mach_ring
  exact hne (exp_injective (exp_injective (k₁.trans k₂.symm)))

/-! ## w2 and w3-large — two non-positive points -/

/-- **`u4` over `w2` is impossible.** -/
theorem u4_w2_absurd {a' K : Real}
    (e₁ : exp (exp a') * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
            (EMLTree.eml (EMLTree.const a') EMLTree.var)).eval (exp (exp a')) = K)
    (e₂ : exp (exp a' + 1) * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
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
  have hne : exp (exp a') ≠ exp (exp a' + 1) := by
    intro h
    have hlt : exp (exp a') < exp (exp a' + 1) := exp_lt (lt_add_of_pos_right zero_lt_one_ax)
    rw [← h] at hlt
    exact lt_irrefl_ax _ hlt
  exact u4_two_nonpos_absurd (exp_pos _) (exp_pos _) hne
    (by rw [hz₁]; exact le_refl 0) (by rw [hz₂]; exact hneg) e₁ e₂

/-- **`u4` over `w3` is impossible when `exp 1 < log c′`.** -/
theorem u4_w3_big_absurd {c' K : Real} (hc : exp 1 < log c')
    (e₁ : (1 : Real) * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
            (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval 1 = K)
    (e₂ : log (log c') * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
            (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval (log (log c')) = K) :
    False := by
  have hlogpos : (0 : Real) < log c' := lt_trans_ax (exp_pos 1) hc
  have hnp₁ : (EMLTree.eml EMLTree.var (EMLTree.const c')).eval 1 ≤ 0 := by
    show exp 1 - log c' ≤ 0
    have h := sub_lt_sub_right_lt hc (log c')
    have eR : log c' - log c' = 0 := by mach_ring
    rw [eR] at h
    exact le_of_lt h
  have hz₂ : (EMLTree.eml EMLTree.var (EMLTree.const c')).eval (log (log c')) = 0 := by
    show exp (log (log c')) - log c' = 0
    rw [exp_log hlogpos]; mach_ring
  have hone : (1 : Real) < log (log c') := by
    have h := log_lt_log (exp_pos 1) hc
    rw [log_exp] at h
    exact h
  have hloglogpos : (0 : Real) < log (log c') := lt_trans_ax zero_lt_one_ax hone
  have hne : (1 : Real) ≠ log (log c') := by
    intro h
    rw [← h] at hone
    exact lt_irrefl_ax _ hone
  exact u4_two_nonpos_absurd zero_lt_one_ax hloglogpos hne hnp₁
    (by rw [hz₂]; exact le_refl 0) e₁ e₂

/-! ## w1 — THREE points, on `exp(exp 3) > 2·exp(exp 2)` -/

/-- **`exp (exp 3) > 2 · exp (exp 2)`.** `exp 3 − exp 2 > 1` because `exp 3 = exp 2 · exp 1 >
exp 2 + exp 2 > exp 2 + 1`, so the ratio `exp (exp 3 − exp 2)` exceeds `exp 1 > 2`. -/
theorem two_exp_exp_two_lt_exp_exp_three :
    (1 + 1 : Real) * exp (exp (1 + 1)) < exp (exp (1 + 1 + 1)) := by
  have hgap : (1 : Real) < exp (1 + 1 + 1) - exp (1 + 1) := by
    apply lt_of_sub_pos
    have e : exp (1 + 1 + 1 : Real) - exp (1 + 1) - 1 = exp (1 + 1 + 1) - (exp (1 + 1) + 1) := by
      mach_mpoly [exp (1 + 1 + 1), exp (1 + 1)]
    rw [e]
    apply sub_pos_of_lt
    -- exp 2 + 1 < exp 2 + exp 2 = 2·exp 2 < exp 2 · exp 1 = exp 3
    have h1 : exp (1 + 1 : Real) + 1 < exp (1 + 1) + exp (1 + 1) :=
      add_lt_add_left (lt_trans_ax one_lt_one_plus_one
        (lt_trans_ax two_lt_four exp_two_gt_four)) (exp (1 + 1))
    have h2 : exp (1 + 1 : Real) + exp (1 + 1) < exp (1 + 1 + 1) := by
      have hsplit : exp (1 + 1 + 1 : Real) = exp (1 + 1) * exp 1 := exp_add (1 + 1) 1
      rw [hsplit]
      have hh := mul_lt_mul_pos_left two_lt_exp_one (exp_pos (1 + 1))
      have e : exp (1 + 1 : Real) * ((1 : Real) + 1) = exp (1 + 1) + exp (1 + 1) := by
        mach_mpoly [exp (1 + 1)]
      rw [e] at hh
      exact hh
    exact lt_trans_ax h1 h2
  have hratio : (1 + 1 : Real) < exp (exp (1 + 1 + 1) - exp (1 + 1)) :=
    lt_trans_ax two_lt_exp_one (exp_lt hgap)
  have hsplit : exp (exp (1 + 1 + 1 : Real))
      = exp (exp (1 + 1)) * exp (exp (1 + 1 + 1) - exp (1 + 1)) := by
    rw [← exp_add]
    have e : exp (1 + 1 : Real) + (exp (1 + 1 + 1) - exp (1 + 1)) = exp (1 + 1 + 1) := by
      mach_mpoly [exp (1 + 1), exp (1 + 1 + 1)]
    rw [e]
  rw [hsplit]
  have hh := mul_lt_mul_pos_left hratio (exp_pos (exp (1 + 1)))
  have e : exp (exp (1 + 1 : Real)) * ((1 : Real) + 1) = (1 + 1) * exp (exp (1 + 1)) := by
    mach_ring
  rw [e] at hh
  exact hh

/-- **`u4` over `w1` is impossible.** The child is constant, so three points give two independent
equations after eliminating `K`; they force `2·exp(exp 2) − exp(exp 1) = exp(exp 3)`, which fails. -/
theorem u4_w1_absurd {d₁ d₂ K : Real}
    (e₁ : (1 : Real) * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
            (EMLTree.eml (EMLTree.const d₁) (EMLTree.const d₂))).eval 1 = K)
    (e₂ : ((1 : Real) + 1) * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
            (EMLTree.eml (EMLTree.const d₁) (EMLTree.const d₂))).eval (1 + 1) = K)
    (e₃ : ((1 : Real) + 1 + 1) * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
            (EMLTree.eml (EMLTree.const d₁) (EMLTree.const d₂))).eval (1 + 1 + 1) = K) :
    False := by
  have m₁ := u4_master _ zero_lt_one_ax e₁
  have m₂ := u4_master _ one_add_one_pos e₂
  have m₃ := u4_master _ three_pos e₃
  have wv : ∀ x : Real, (EMLTree.eml (EMLTree.const d₁) (EMLTree.const d₂)).eval x
      = exp d₁ - log d₂ := fun _ => rfl
  rw [wv] at m₁ m₂ m₃
  -- eliminate K pairwise
  have hL : log (exp d₁ - log d₂) = exp (exp (1 + 1)) - exp (exp 1) := by
    have e : log (exp d₁ - log d₂)
        = ((1 + 1 : Real) * log (exp d₁ - log d₂)) - ((1 : Real) * log (exp d₁ - log d₂)) := by
      mach_ring
    rw [e, m₂, m₁]
    mach_mpoly [exp (exp (1 + 1)), exp (exp 1), K]
  have h2L : (1 + 1 : Real) * log (exp d₁ - log d₂)
      = exp (exp (1 + 1 + 1)) - exp (exp 1) := by
    have e : (1 + 1 : Real) * log (exp d₁ - log d₂)
        = ((1 + 1 + 1 : Real) * log (exp d₁ - log d₂))
          - ((1 : Real) * log (exp d₁ - log d₂)) := by mach_ring
    rw [e, m₃, m₁]
    mach_mpoly [exp (exp (1 + 1 + 1)), exp (exp 1), K]
  rw [hL] at h2L
  -- h2L : 2·(exp(exp 2) − exp(exp 1)) = exp(exp 3) − exp(exp 1)  — but RHS is strictly bigger
  have hgt : (1 + 1 : Real) * (exp (exp (1 + 1)) - exp (exp 1))
      < exp (exp (1 + 1 + 1)) - exp (exp 1) := by
    apply lt_of_sub_pos
    have e : (exp (exp (1 + 1 + 1)) - exp (exp 1))
        - (1 + 1 : Real) * (exp (exp (1 + 1)) - exp (exp 1))
        = (exp (exp (1 + 1 + 1)) - (1 + 1) * exp (exp (1 + 1))) + exp (exp 1) := by
      mach_mpoly [exp (exp (1 + 1 + 1)), exp (exp (1 + 1)), exp (exp 1)]
    rw [e]
    exact add_pos_real (sub_pos_of_lt two_exp_exp_two_lt_exp_exp_three) (exp_pos (exp 1))
  rw [h2L] at hgt
  exact lt_irrefl_ax _ hgt

/-! ## w4 — TWO points, where `u1` needed three -/

/-- **`u4` over `w4` is impossible, on two points.**

`x = 1` pins `K = exp(exp 1) − 1`. At `x = exp 1` the left side is below `e²` and the right side is
above it.

**Under `u1` this same `W` needed three points and `(e³−2)² > e⁵`.** The difference is the free
scale, not the shape of `W`. -/
theorem u4_w4_absurd {K : Real}
    (e₁ : (1 : Real) * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
            (EMLTree.eml EMLTree.var EMLTree.var)).eval 1 = K)
    (e₂ : exp 1 * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
            (EMLTree.eml EMLTree.var EMLTree.var)).eval (exp 1) = K) :
    False := by
  have m₁ := u4_master _ zero_lt_one_ax e₁
  have m₂ := u4_master _ (exp_pos 1) e₂
  have v₁ : (EMLTree.eml EMLTree.var EMLTree.var).eval 1 = exp 1 := by
    show exp (1 : Real) - log (1 : Real) = exp 1
    rw [log_one]; mach_ring
  have v₂ : (EMLTree.eml EMLTree.var EMLTree.var).eval (exp 1) = exp (exp 1) - 1 := by
    show exp (exp 1) - log (exp 1) = exp (exp 1) - 1
    rw [log_exp]
  rw [v₁, log_exp] at m₁
  rw [v₂] at m₂
  -- m₁ : 1 * 1 = exp (exp 1) − K
  -- m₂ : exp 1 * log (exp (exp 1) − 1) = exp (exp (exp 1)) − K
  -- LHS of m₂ is below e²
  have hVpos : (0 : Real) < exp (exp 1) - 1 :=
    sub_pos_of_lt (lt_trans_ax one_lt_exp_one (exp_lt one_lt_exp_one))
  have hlogsmall : log (exp (exp 1) - 1) < exp 1 := by
    have hlt : exp (exp 1) - 1 < exp (exp 1) := by
      apply lt_of_sub_pos
      have e : exp (exp 1) - (exp (exp 1) - 1) = 1 := by mach_mpoly [exp (exp 1)]
      rw [e]; exact zero_lt_one_ax
    have h := log_lt_log hVpos hlt
    rw [log_exp] at h
    exact h
  have hLHS : exp 1 * log (exp (exp 1) - 1) < exp 1 * exp 1 :=
    mul_lt_mul_pos_left hlogsmall (exp_pos 1)
  -- RHS of m₂ exceeds e²
  have hKval : K = exp (exp 1) - 1 := by
    have e : K = exp (exp 1) - ((1 : Real) * 1) := by
      have ee : K = exp (exp 1) - (exp (exp 1) - K) := by mach_ring
      rw [ee, ← m₁]
    rw [e]; mach_ring
  have hRHS : exp 1 * exp 1 < exp (exp (exp 1)) - K := by
    rw [hKval]
    -- e² < e^e
    have h_ee : exp 1 * exp 1 < exp (exp 1) := by
      have e : exp (1 + 1 : Real) = exp 1 * exp 1 := exp_add 1 1
      rw [← e]
      exact exp_lt two_lt_exp_one
    -- 1 < e^e − e, from exp_exp_one_gt_exp_one_add_one
    have h_gap : (1 : Real) < exp (exp 1) - exp 1 := by
      apply lt_of_sub_pos
      have e : exp (exp 1) - exp 1 - 1 = exp (exp 1) - (exp 1 + 1) := by
        mach_mpoly [exp (exp 1), exp 1]
      rw [e]
      exact sub_pos_of_lt exp_exp_one_gt_exp_one_add_one
    -- 2 < exp (e^e − e)
    have h_fac : (1 + 1 : Real) < exp (exp (exp 1) - exp 1) :=
      lt_trans_ax two_lt_exp_one (exp_lt h_gap)
    -- e^(e^e) = e^e · exp(e^e − e) > 2·e^e
    have hsplit : exp (exp (exp 1)) = exp (exp 1) * exp (exp (exp 1) - exp 1) := by
      rw [← exp_add]
      have e : exp 1 + (exp (exp 1) - exp 1) = exp (exp 1) := by
        mach_mpoly [exp 1, exp (exp 1)]
      rw [e]
    have h2ee : exp (exp 1) * (1 + 1) < exp (exp (exp 1)) := by
      rw [hsplit]
      exact mul_lt_mul_pos_left h_fac (exp_pos (exp 1))
    -- assemble: (A − 2B) + (B − C) + 1 > 0
    apply lt_of_sub_pos
    have e : exp (exp (exp 1)) - (exp (exp 1) - 1) - exp 1 * exp 1
        = (exp (exp (exp 1)) - exp (exp 1) * (1 + 1))
          + (exp (exp 1) - exp 1 * exp 1) + 1 := by
      mach_mpoly [exp (exp (exp 1)), exp (exp 1), exp 1]
    rw [e]
    exact add_pos_real (add_pos_real (sub_pos_of_lt h2ee) (sub_pos_of_lt h_ee)) zero_lt_one_ax
  exact lt_irrefl_ax _ (lt_trans_ax hLHS (m₂ ▸ hRHS))

/-! ## `w3`-small — three points, a bounded left side against an astronomical right side

The last `u4` cell. Its child `exp x − L′` is **positive throughout** (for `L′ ≤ exp 1`), so the
non-positive route is unavailable. **A second difference at `1, 2, 3` kills `K` and leaves**

```
log W₁ − 4·log W₂ + 3·log W₃  =  exp (exp 1) − 2·exp (exp 2) + exp (exp 3)
```

with `L′` the only survivor — **left side below 6, right side above 14.** -/

/-- `log (e − L′) ≤ log (e² − L′)` for `L′ ≤ e`.

**Two cases, and the split is forced by totalisation:** at `L′ = e` the smaller child is exactly `0`,
so `log` of it is `0` and `log_lt_log` does not apply. -/
theorem log_w1_le_log_w2 {L : Real} (hL : L ≤ exp 1) :
    log (exp 1 - L) ≤ log (exp (1 + 1) - L) := by
  have hA : (1 : Real) < exp (1 + 1) - exp 1 := by
    apply lt_of_sub_pos
    have e : exp (1 + 1 : Real) - exp 1 - 1 = exp (1 + 1) - (exp 1 + 1) := by
      mach_mpoly [exp (1 + 1), exp 1]
    rw [e]
    apply sub_pos_of_lt
    rw [exp_add 1 1]
    have h1 : exp 1 + 1 < exp 1 + exp 1 := add_lt_add_left one_lt_exp_one (exp 1)
    have h2 : exp 1 + exp 1 < exp 1 * exp 1 := by
      have hh := mul_lt_mul_pos_left two_lt_exp_one (exp_pos 1)
      have e2 : exp 1 * ((1 : Real) + 1) = exp 1 + exp 1 := by mach_mpoly [exp 1]
      rw [e2] at hh
      exact hh
    exact lt_trans_ax h1 h2
  have hW2 : (1 : Real) < exp (1 + 1) - L := by
    apply lt_of_sub_pos
    have e : exp (1 + 1 : Real) - L - 1 = (exp (1 + 1) - exp 1 - 1) + (exp 1 - L) := by
      mach_mpoly [exp (1 + 1), exp 1, L]
    rw [e]
    rcases (le_iff_lt_or_eq L (exp 1)).mp hL with h | h
    · exact add_pos_real (sub_pos_of_lt hA) (sub_pos_of_lt h)
    · rw [h]
      have ez : exp 1 - exp 1 = (0 : Real) := by mach_ring
      rw [ez]
      have ez2 : exp (1 + 1 : Real) - exp 1 - 1 + 0 = exp (1 + 1) - exp 1 - 1 := by mach_ring
      rw [ez2]
      exact sub_pos_of_lt hA
  have hW2pos : (0 : Real) < exp (1 + 1) - L := lt_trans_ax zero_lt_one_ax hW2
  rcases lt_total (exp 1 - L) 0 with h | h | h
  · rw [log_nonpos (le_of_lt h)]
    have hlog : (0 : Real) < log (exp (1 + 1) - L) := by
      have hh := log_lt_log zero_lt_one_ax hW2
      rw [log_one] at hh
      exact hh
    exact le_of_lt hlog
  · rw [log_nonpos (le_of_eq h)]
    have hlog : (0 : Real) < log (exp (1 + 1) - L) := by
      have hh := log_lt_log zero_lt_one_ax hW2
      rw [log_one] at hh
      exact hh
    exact le_of_lt hlog
  · apply le_of_lt
    apply log_lt_log h
    apply lt_of_sub_pos
    have e : (exp (1 + 1 : Real) - L) - (exp 1 - L) = exp (1 + 1) - exp 1 := by
      mach_mpoly [exp (1 + 1), exp 1, L]
    rw [e]
    exact sub_pos_of_lt (exp_lt (lt_add_of_pos_right zero_lt_one_ax))

/-- **`e³ − L′ < e²·(e² − L′)` for `L′ ≤ e`.**

Written as a polynomial in `E := exp 1`, the difference is `(E⁴ − 2E³ + E) + (E − L′)(E² − 1)`:
the first bracket is `E·(E²(E−2) + 1) > 0` because `E > 2`, and the second is a product of a
non-negative and a positive. -/
theorem cube_sub_lt_sq_mul {L : Real} (hL : L ≤ exp 1) :
    exp (1 + 1 + 1) - L < exp (1 + 1) * (exp (1 + 1) - L) := by
  have e2 : exp (1 + 1 : Real) = exp 1 * exp 1 := exp_add 1 1
  have e3 : exp (1 + 1 + 1 : Real) = exp 1 * exp 1 * exp 1 := by
    rw [exp_add (1 + 1) 1, e2]
  apply lt_of_sub_pos
  rw [e2, e3]
  have esplit : (exp 1 * exp 1) * ((exp 1 * exp 1) - L) - ((exp 1 * exp 1 * exp 1) - L)
      = (exp 1 * (exp 1 * exp 1 * (exp 1 - (1 + 1)) + 1))
        + (exp 1 - L) * (exp 1 * exp 1 - 1) := by
    mach_mpoly [exp 1, L]
  rw [esplit]
  have hE2 : (1 : Real) < exp 1 * exp 1 := by
    rw [← e2]
    exact lt_trans_ax (lt_trans_ax one_lt_one_plus_one two_lt_four) exp_two_gt_four
  have hfirst : (0 : Real) < exp 1 * (exp 1 * exp 1 * (exp 1 - (1 + 1)) + 1) :=
    mul_pos (exp_pos 1)
      (add_pos_real (mul_pos (mul_pos (exp_pos 1) (exp_pos 1)) (sub_pos_of_lt two_lt_exp_one))
        zero_lt_one_ax)
  have hsecond : (0 : Real) ≤ (exp 1 - L) * (exp 1 * exp 1 - 1) := by
    rcases (le_iff_lt_or_eq L (exp 1)).mp hL with h | h
    · exact le_of_lt (mul_pos (sub_pos_of_lt h) (sub_pos_of_lt hE2))
    · rw [h]
      have ez : exp 1 - exp 1 = (0 : Real) := by mach_ring
      rw [ez]
      have ez2 : (0 : Real) * (exp 1 * exp 1 - 1) = 0 := by mach_ring
      rw [ez2]
      exact le_refl 0
  rcases (le_iff_lt_or_eq 0 ((exp 1 - L) * (exp 1 * exp 1 - 1))).mp hsecond with h | h
  · exact add_pos_real hfirst h
  · have e0 : exp 1 * (exp 1 * exp 1 * (exp 1 - (1 + 1)) + 1)
        + (exp 1 - L) * (exp 1 * exp 1 - 1)
        = exp 1 * (exp 1 * exp 1 * (exp 1 - (1 + 1)) + 1) := by
      rw [← h]; mach_ring
    rw [e0]
    exact hfirst

/-- `log (e³ − L′) < 2 + log (e² − L′)` for `L′ ≤ e`. -/
theorem log_w3_lt_two_add_log_w2 {L : Real} (hL : L ≤ exp 1)
    (hW2 : (0 : Real) < exp (1 + 1) - L) :
    log (exp (1 + 1 + 1) - L) < (1 + 1) + log (exp (1 + 1) - L) := by
  have hpos3 : (0 : Real) < exp (1 + 1 + 1) - L :=
    lt_trans_ax hW2 (by
      apply lt_of_sub_pos
      have e : (exp (1 + 1 + 1 : Real) - L) - (exp (1 + 1) - L)
          = exp (1 + 1 + 1) - exp (1 + 1) := by
        mach_mpoly [exp (1 + 1 + 1), exp (1 + 1), L]
      rw [e]
      exact sub_pos_of_lt (exp_lt (lt_add_of_pos_right zero_lt_one_ax)))
  have h := log_lt_log hpos3 (cube_sub_lt_sq_mul hL)
  rw [log_mul (exp_pos (1 + 1)) hW2, log_exp] at h
  exact h

/-- `0 ≤ a → 0 < b → 0 < a + b`. -/
theorem add_pos_of_nonneg_of_pos {a b : Real} (ha : 0 ≤ a) (hb : 0 < b) : 0 < a + b := by
  rcases (le_iff_lt_or_eq 0 a).mp ha with h | h
  · exact add_pos_real h hb
  · rw [← h]
    have e : (0 : Real) + b = b := by mach_ring
    rw [e]
    exact hb

/-- `exp 3 − exp 2 > 2`, since `e³ − e² = e²·(e − 1) > 4·1`. -/
theorem exp_three_sub_exp_two_gt_two : (1 + 1 : Real) < exp (1 + 1 + 1) - exp (1 + 1) := by
  have hsplit : exp (1 + 1 + 1 : Real) - exp (1 + 1) = exp (1 + 1) * (exp 1 - 1) := by
    rw [exp_add (1 + 1) 1]; mach_mpoly [exp (1 + 1), exp 1]
  rw [hsplit]
  have hE1 : (1 : Real) < exp 1 - 1 := by
    apply lt_of_sub_pos
    have e : exp 1 - 1 - 1 = exp 1 - (1 + 1) := by mach_ring
    rw [e]; exact sub_pos_of_lt two_lt_exp_one
  have h1 : ((1 + 1 : Real) * (1 + 1)) * (exp 1 - 1) < exp (1 + 1) * (exp 1 - 1) :=
    mul_lt_mul_of_pos_right exp_two_gt_four (lt_trans_ax zero_lt_one_ax hE1)
  have h2 : (1 + 1 : Real) < ((1 + 1 : Real) * (1 + 1)) * (exp 1 - 1) := by
    have hh := mul_lt_mul_pos_left hE1 (mul_pos one_add_one_pos one_add_one_pos)
    have e : ((1 + 1 : Real) * (1 + 1)) * 1 = (1 + 1) + (1 + 1) := by mach_ring
    rw [e] at hh
    exact lt_trans_ax (lt_add_of_pos_right one_add_one_pos) hh
  exact lt_trans_ax h2 h1

/-- `exp (exp 3) > 3 · exp (exp 2)`. -/
theorem three_exp_exp_two_lt_exp_exp_three :
    (1 + 1 + 1 : Real) * exp (exp (1 + 1)) < exp (exp (1 + 1 + 1)) := by
  have hratio : (1 + 1 + 1 : Real) < exp (exp (1 + 1 + 1) - exp (1 + 1)) := by
    have h := exp_lt exp_three_sub_exp_two_gt_two
    have h4 : (1 + 1 + 1 : Real) < exp (1 + 1) := by
      have e4 : (1 + 1 : Real) * (1 + 1) = (1 + 1 + 1) + 1 := by mach_ring
      have hh := exp_two_gt_four
      rw [e4] at hh
      exact lt_trans_ax (lt_add_of_pos_right zero_lt_one_ax) hh
    exact lt_trans_ax h4 h
  have hsplit : exp (exp (1 + 1 + 1 : Real))
      = exp (exp (1 + 1)) * exp (exp (1 + 1 + 1) - exp (1 + 1)) := by
    rw [← exp_add]
    have e : exp (1 + 1 : Real) + (exp (1 + 1 + 1) - exp (1 + 1)) = exp (1 + 1 + 1) := by
      mach_mpoly [exp (1 + 1), exp (1 + 1 + 1)]
    rw [e]
  rw [hsplit]
  have hh := mul_lt_mul_pos_left hratio (exp_pos (exp (1 + 1 : Real)))
  have e : exp (exp (1 + 1 : Real)) * ((1 : Real) + 1 + 1)
      = (1 + 1 + 1 : Real) * exp (exp (1 + 1)) := by mach_ring
  rw [e] at hh
  exact hh

/-- **`u4` over `w3` is impossible on the small branch too** (`log c′ ≤ exp 1`).

The child is positive throughout, so the non-positive route is unavailable. **Three points; the
second difference kills `K` and leaves a bounded left side against an astronomical right side.** -/
theorem u4_w3_small_absurd {c' K : Real} (hc : log c' ≤ exp 1)
    (e₁ : (1 : Real) * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
            (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval 1 = K)
    (e₂ : ((1 : Real) + 1) * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
            (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval (1 + 1) = K)
    (e₃ : ((1 : Real) + 1 + 1) * (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
            (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval (1 + 1 + 1) = K) :
    False := by
  have m₁ := u4_master _ zero_lt_one_ax e₁
  have m₂ := u4_master _ one_add_one_pos e₂
  have m₃ := u4_master _ three_pos e₃
  have wv : ∀ y : Real, (EMLTree.eml EMLTree.var (EMLTree.const c')).eval y
      = exp y - log c' := fun _ => rfl
  rw [wv] at m₁ m₂ m₃
  -- W₂ > 0
  have hW2pos : (0 : Real) < exp (1 + 1) - log c' := by
    apply lt_of_sub_pos
    have e : exp (1 + 1 : Real) - log c' - 0 = (exp (1 + 1) - exp 1) + (exp 1 - log c') := by
      mach_mpoly [exp (1 + 1), exp 1, log c']
    rw [e]
    rcases (le_iff_lt_or_eq (log c') (exp 1)).mp hc with h | h
    · exact add_pos_real (sub_pos_of_lt (exp_lt (lt_add_of_pos_right zero_lt_one_ax)))
        (sub_pos_of_lt h)
    · rw [h]
      have ez : exp 1 - exp 1 = (0 : Real) := by mach_ring
      rw [ez]
      have ez2 : exp (1 + 1 : Real) - exp 1 + 0 = exp (1 + 1) - exp 1 := by mach_ring
      rw [ez2]
      exact sub_pos_of_lt (exp_lt (lt_add_of_pos_right zero_lt_one_ax))
  -- the second difference
  have hsd : (1 : Real) * log (exp 1 - log c')
      - (1 + 1) * (((1 : Real) + 1) * log (exp (1 + 1) - log c'))
      + ((1 : Real) + 1 + 1) * log (exp (1 + 1 + 1) - log c')
      = exp (exp 1) - (1 + 1) * exp (exp (1 + 1)) + exp (exp (1 + 1 + 1)) := by
    rw [m₁, m₂, m₃]; mach_mpoly [exp (exp 1), exp (exp (1 + 1)), exp (exp (1 + 1 + 1)), K]
  -- LEFT side < 6
  have hleft : (1 : Real) * log (exp 1 - log c')
      - (1 + 1) * (((1 : Real) + 1) * log (exp (1 + 1) - log c'))
      + ((1 : Real) + 1 + 1) * log (exp (1 + 1 + 1) - log c')
      < (1 + 1 + 1) * (1 + 1) := by
    have hA := log_w1_le_log_w2 hc
    have hB := log_w3_lt_two_add_log_w2 hc hW2pos
    apply lt_of_sub_pos
    have e : ((1 + 1 + 1 : Real) * (1 + 1))
        - ((1 : Real) * log (exp 1 - log c')
          - (1 + 1) * (((1 : Real) + 1) * log (exp (1 + 1) - log c'))
          + ((1 : Real) + 1 + 1) * log (exp (1 + 1 + 1) - log c'))
        = (log (exp (1 + 1) - log c') - log (exp 1 - log c'))
          + (1 + 1 + 1) * (((1 + 1) + log (exp (1 + 1) - log c'))
              - log (exp (1 + 1 + 1) - log c')) := by
      mach_mpoly [log (exp 1 - log c'), log (exp (1 + 1) - log c'),
        log (exp (1 + 1 + 1) - log c')]
    rw [e]
    exact add_pos_of_nonneg_of_pos (sub_nonneg_of_le hA) (mul_pos three_pos (sub_pos_of_lt hB))
  -- RIGHT side > 6
  have hright : ((1 : Real) + 1 + 1) * (1 + 1)
      < exp (exp 1) - (1 + 1) * exp (exp (1 + 1)) + exp (exp (1 + 1 + 1)) := by
    apply lt_of_sub_pos
    have e : (exp (exp 1) - (1 + 1) * exp (exp (1 + 1)) + exp (exp (1 + 1 + 1)))
        - ((1 : Real) + 1 + 1) * (1 + 1)
        = (exp (exp (1 + 1 + 1)) - (1 + 1 + 1) * exp (exp (1 + 1)))
          + (exp (exp (1 + 1)) - (1 + 1 + 1))
          + (exp (exp 1) - (1 + 1 + 1)) := by
      mach_mpoly [exp (exp 1), exp (exp (1 + 1)), exp (exp (1 + 1 + 1))]
    rw [e]
    have h3 : (1 + 1 + 1 : Real) < exp (1 + 1) := by
      have e4 : (1 + 1 : Real) * (1 + 1) = (1 + 1 + 1) + 1 := by mach_ring
      have hh := exp_two_gt_four
      rw [e4] at hh
      exact lt_trans_ax (lt_add_of_pos_right zero_lt_one_ax) hh
    have hexp2gt2 : (1 + 1 : Real) < exp (1 + 1) := lt_trans_ax two_lt_four exp_two_gt_four
    have hA : (1 + 1 + 1 : Real) < exp (exp (1 + 1)) := lt_trans_ax h3 (exp_lt hexp2gt2)
    have hB : (1 + 1 + 1 : Real) < exp (exp 1) := lt_trans_ax h3 (exp_lt two_lt_exp_one)
    exact add_pos_real (add_pos_real (sub_pos_of_lt three_exp_exp_two_lt_exp_exp_three)
      (sub_pos_of_lt hA)) (sub_pos_of_lt hB)
  rw [hsd] at hleft
  exact lt_irrefl_ax _ (lt_trans_ax hleft hright)

end Real
end MachLib