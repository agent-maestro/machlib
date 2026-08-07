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

end Real
end MachLib
