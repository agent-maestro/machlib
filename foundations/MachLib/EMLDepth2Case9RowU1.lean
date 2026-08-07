import MachLib.EMLDepth2Case9RowU2

/-!
# Depth-2 case 9, the `u1` row — partial, and the obstruction is STRUCTURAL

`u2` closed 4 of 4 cheaply. **`u1` does not**, and the reason is one line of algebra.

## The two master equations

| left child | master equation |
|---|---|
| `u2 = eml (const a) var` | `x · log (W x) = exp (exp a) − K` — **RHS CONSTANT in `x`** |
| `u1` constant-valued, value `α` | `x · log (W x) = x · exp α − K` — **RHS AFFINE, FREE SLOPE** |

`u2`'s `exp` cancels the `x` **exactly** — that is *why* one or two points sufficed there.

> ### `u1` carries a free scale `exp α > 0`. No finite set of points can be contradicted by MAGNITUDE alone: any magnitude is absorbed by choosing `α`. The contradiction must come from the SHAPE of `log W`.

## The row

| cell | `W(x)` | status |
|---|---|---|
| **w1** | constant | ✅ **`K = 0` forced** — no `K ≠ 0` at all |
| **w2** | `B − log x` | ✅ two non-positive points |
| **w3**, `exp 1 < log c′` | `exp x − L′` | ✅ two non-positive points (`x = 1`, `x = log (log c′)`) |
| **w3**, `1 < log c′ ≤ exp 1` | | 🔴 **OPEN** — needs a second point strictly below `log (log c′)`; density/division this corpus lacks |
| **w3**, `log c′ ≤ 1` | | 🔴 **OPEN** — the free scale |
| **w4** | `exp x − log x` | 🔴 **OPEN** — the free scale |

**Two distinct obstructions, both named in the pre-registration before being hit.**

## ⚠ SCOPE

**`u3`, `u4` rows untouched (8 of 16 cells). Depth 2 only. `1/x ∉ EML` untouched.**
-/

namespace MachLib
namespace Real

open EMLTree

/-! ## The two master equations, and the difference between them -/

/-- **The `u1` master equation.** For a left child taking the value `α` at `x`:

`x · log (w.eval x) = x · exp α − K`

**Compare `u2_master`, whose right-hand side is `exp (exp a) − K` — CONSTANT in `x`.** The `x ·`
here is the free scale, and it is the whole difference between the two rows. -/
theorem u1_master {α K x : Real} {u w : EMLTree} (hu : u.eval x = α)
    (e : x * (EMLTree.eml u w).eval x = K) :
    x * log (w.eval x) = x * exp α - K := by
  have v : (EMLTree.eml u w).eval x = exp (u.eval x) - log (w.eval x) := rfl
  rw [v, hu] at e
  have expand : x * (exp α - log (w.eval x)) = x * exp α - x * log (w.eval x) := by
    mach_mpoly [x, exp α, log (w.eval x)]
  rw [expand] at e
  have e2 : x * log (w.eval x)
      = x * exp α - (x * exp α - x * log (w.eval x)) := by mach_mpoly [x, exp α, log (w.eval x)]
  rw [e2, e]

/-! ## G2 — two non-positive points kill ANY constant-valued left child, at ANY depth -/

/-- **Two non-positive points are outright contradictory**, for any `u` agreeing at the two points
and any `w` non-positive at both.

**Positivity of the points is NOT a hypothesis** — the proof never reads it. Stated that way
deliberately: a hypothesis `0 < x₁` here would be over-strong, the failure this arm recorded four
times on 2026-08-05. **Nor is any depth bound needed** — `u` and `w` are arbitrary trees. -/
theorem const_left_two_nonpos_absurd {u w : EMLTree} {K x₁ x₂ : Real}
    (hne : x₁ ≠ x₂)
    (hu : u.eval x₁ = u.eval x₂)
    (hw₁ : w.eval x₁ ≤ 0) (hw₂ : w.eval x₂ ≤ 0)
    (e₁ : x₁ * (EMLTree.eml u w).eval x₁ = K)
    (e₂ : x₂ * (EMLTree.eml u w).eval x₂ = K) :
    False := by
  have v₁ : (EMLTree.eml u w).eval x₁ = exp (u.eval x₁) - log (w.eval x₁) := rfl
  have v₂ : (EMLTree.eml u w).eval x₂ = exp (u.eval x₂) - log (w.eval x₂) := rfl
  rw [v₁, log_nonpos hw₁] at e₁
  rw [v₂, log_nonpos hw₂, ← hu] at e₂
  -- e₁ : x₁ * (exp (u.eval x₁) - 0) = K,  e₂ : x₂ * (exp (u.eval x₁) - 0) = K
  have h : (x₁ - x₂) * exp (u.eval x₁) = 0 := by
    have ee : (x₁ - x₂) * exp (u.eval x₁)
        = x₁ * (exp (u.eval x₁) - 0) - x₂ * (exp (u.eval x₁) - 0) := by
      mach_mpoly [x₁, x₂, exp (u.eval x₁)]
    rw [ee, e₁, e₂]; mach_ring
  have hx : x₁ - x₂ ≠ 0 := by
    intro hz; apply hne
    have ee : x₁ = x₂ + (x₁ - x₂) := by mach_ring
    rw [ee, hz]; mach_ring
  have hE : exp (u.eval x₁) = 0 :=
    Classical.byContradiction (fun hE => (mul_ne_zero hx hE) h)
  have hpos := exp_pos (u.eval x₁)
  rw [hE] at hpos
  exact lt_irrefl_ax 0 hpos

/-! ## w1 — the node is constant-valued, and that forces `K = 0` at any depth -/

/-- **A constant-valued node reaches only `K = 0`.** Fully general: any tree, any depth, provided it
takes the same value at two distinct points.

`x₁ · v = K = x₂ · v` with `x₁ ≠ x₂` forces `v = 0`, hence `K = 0` — **and `K = 0` is the zero
function, not `K/x`.** -/
theorem const_valued_forces_K_zero {t : EMLTree} {K x₁ x₂ : Real}
    (hne : x₁ ≠ x₂)
    (hconst : t.eval x₁ = t.eval x₂)
    (e₁ : x₁ * t.eval x₁ = K) (e₂ : x₂ * t.eval x₂ = K) :
    K = 0 := by
  rw [← hconst] at e₂
  have h : (x₁ - x₂) * t.eval x₁ = 0 := by
    have ee : (x₁ - x₂) * t.eval x₁ = x₁ * t.eval x₁ - x₂ * t.eval x₁ := by
      mach_mpoly [x₁, x₂, t.eval x₁]
    rw [ee, e₁, e₂]; mach_ring
  have hx : x₁ - x₂ ≠ 0 := by
    intro hz; apply hne
    have ee : x₁ = x₂ + (x₁ - x₂) := by mach_ring
    rw [ee, hz]; mach_ring
  have hv : t.eval x₁ = 0 :=
    Classical.byContradiction (fun hv => (mul_ne_zero hx hv) h)
  rw [← e₁, hv]; mach_ring

/-- **`u1` over `w1` reaches only `K = 0`.** Both children constant-valued ⟹ the node is
constant-valued ⟹ `const_valued_forces_K_zero`. -/
theorem u1_w1_forces_K_zero {c₁ c₂ d₁ d₂ K x₁ x₂ : Real} (hne : x₁ ≠ x₂)
    (e₁ : x₁ * (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
            (EMLTree.eml (EMLTree.const d₁) (EMLTree.const d₂))).eval x₁ = K)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
            (EMLTree.eml (EMLTree.const d₁) (EMLTree.const d₂))).eval x₂ = K) :
    K = 0 :=
  const_valued_forces_K_zero hne rfl e₁ e₂

/-- **So `u1` over `w1` cannot reach `1/x`.** -/
theorem u1_w1_not_inv_x {c₁ c₂ d₁ d₂ x₁ x₂ : Real} (hne : x₁ ≠ x₂)
    (e₁ : x₁ * (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
            (EMLTree.eml (EMLTree.const d₁) (EMLTree.const d₂))).eval x₁ = 1)
    (e₂ : x₂ * (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
            (EMLTree.eml (EMLTree.const d₁) (EMLTree.const d₂))).eval x₂ = 1) :
    False := by
  have h := u1_w1_forces_K_zero hne e₁ e₂
  exact zero_ne_one_ax h.symm

/-! ## w2 — two non-positive points, supplied -/

/-- **`u1` over `w2` is impossible.** At `x = exp B` and `x = exp (B+1)` the right child
`exp a′ − log x` is `0` and `−1`; both non-positive, so `const_left_two_nonpos_absurd` applies. -/
theorem u1_w2_absurd {c₁ c₂ a' K : Real}
    (e₁ : exp (exp a') * (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
            (EMLTree.eml (EMLTree.const a') EMLTree.var)).eval (exp (exp a')) = K)
    (e₂ : exp (exp a' + 1) * (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
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
    have hlt : exp (exp a') < exp (exp a' + 1) := by
      apply exp_lt
      have hb := add_lt_add_left zero_lt_one_ax (exp a')
      have eL : exp a' + 0 = exp a' := by mach_mpoly [exp a']
      rw [eL] at hb
      exact hb
    rw [← h] at hlt
    exact lt_irrefl_ax _ hlt
  exact const_left_two_nonpos_absurd hne rfl (by rw [hz₁]; exact le_refl 0)
    (by rw [hz₂]; exact hneg) e₁ e₂

/-! ## w3 — the branch that closes -/

/-- **`u1` over `w3` is impossible when `exp 1 < log c′`.**

Then `1` and `log (log c′)` are two distinct points at which `exp x − log c′` is non-positive:
`exp 1 < log c′` directly, and `exp (log (log c′)) = log c′` exactly.

**The hypothesis is `exp 1 < log c′`, not `1 < log c′`** — the weaker condition is what makes the
SECOND point available, and finding a second point is the whole difficulty of this cell. -/
theorem u1_w3_big_absurd {c₁ c₂ c' K : Real} (hc : exp 1 < log c')
    (e₁ : (1 : Real) * (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
            (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval 1 = K)
    (e₂ : log (log c') * (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
            (EMLTree.eml EMLTree.var (EMLTree.const c'))).eval (log (log c')) = K) :
    False := by
  have hlogpos : (0 : Real) < log c' := lt_trans_ax (exp_pos 1) hc
  have hz₁ : (EMLTree.eml EMLTree.var (EMLTree.const c')).eval 1 = exp 1 - log c' := rfl
  have hnp₁ : (EMLTree.eml EMLTree.var (EMLTree.const c')).eval 1 ≤ 0 := by
    rw [hz₁]
    have h := sub_lt_sub_right_lt hc (log c')
    have eR : log c' - log c' = 0 := by mach_ring
    rw [eR] at h
    exact le_of_lt h
  have hz₂ : (EMLTree.eml EMLTree.var (EMLTree.const c')).eval (log (log c')) = 0 := by
    show exp (log (log c')) - log c' = 0
    rw [exp_log hlogpos]; mach_ring
  have hne : (1 : Real) ≠ log (log c') := by
    intro h
    have hlt : (1 : Real) < log (log c') := by
      have hh := log_lt_log (exp_pos 1) hc
      rw [log_exp] at hh
      exact hh
    rw [← h] at hlt
    exact lt_irrefl_ax _ hlt
  exact const_left_two_nonpos_absurd hne rfl hnp₁ (by rw [hz₂]; exact le_refl 0) e₁ e₂

end Real
end MachLib
