import MachLib.EMLDepth2Case9RowU1

/-!
# The free scale, eliminated — three points kill both `exp α` and `K`

`RESULT_ROW_U1.md` left `w4` open behind **the free scale**: the `u1` master equation
`x · log (W x) = x · exp α − K` is **affine in `x` with two free parameters**, so no one- or
two-point argument can contradict it by magnitude.

## The elimination

An affine function has **vanishing second difference** on equally spaced points. At `x = 1, 2, 3`
both `exp α` and `K` cancel at once:

> ### `log W(1) − 4·log W(2) + 3·log W(3) = 0` — a claim in the `W`-PARAMETERS ALONE.

`u1_second_difference` proves this for **any** constant-valued left child at **any** depth.

## Applied to `w4`, which has NO parameters

`W(x) = exp x − log x`, so `W(1) = exp 1` and `log W(1) = 1`, leaving the closed numeric claim

```
1 − 4·log (e² − log 2) + 3·log (e³ − log 3)  =  0
```

refuted by `u1_w4_absurd`. Everything comes from **`two_lt_exp_one` (`e > 2`), division-free**:

* `log (e² − log 2) < 2` — immediate, since `log 2 > 0`;
* `(e³ − 2)² > e⁵` — from `4(e³−2) > 3e³` (needs `e³ > 8`) and `9·e > 16` (needs `e > 2`).

**Squaring rather than cubing keeps every numeral below 20**, which matters in a corpus whose ring
normaliser has a numeral-scale wall. `lt_of_mul_lt_mul_pos_left` replaces every division.

## ▸ POINTS vs PARAMETERS — the general lesson

Three points give **one** equation after elimination. So:

> ### A parameter-free right child dies to three points. A ONE-parameter right child does not — the parameter absorbs the single equation.

**`w3` is one-parameter and is NOT closed here.** Hand-computed: its three-point relation is `−2` at
`L′ = 0` and positive as `L′ → ∞`, so it crosses zero and some `L′` satisfies it. **A fourth point
would be needed.** That is a limit of the method, not a fact about `w3`.

## ⚠ SCOPE

**`w3`'s two cells stay open. `u3`, `u4` rows untouched (8 of 16 cells). Depth 2 only.
`1/x ∉ EML` untouched.**
-/

namespace MachLib
namespace Real

open EMLTree

/-! ## The elimination -/

/-- **Three points eliminate BOTH `exp α` and `K`.** General: any tree, any depth. -/
theorem u1_second_difference {α K : Real} {u w : EMLTree}
    (hu₁ : u.eval 1 = α) (hu₂ : u.eval (1 + 1) = α) (hu₃ : u.eval (1 + 1 + 1) = α)
    (e₁ : (1 : Real) * (EMLTree.eml u w).eval 1 = K)
    (e₂ : ((1 : Real) + 1) * (EMLTree.eml u w).eval (1 + 1) = K)
    (e₃ : ((1 : Real) + 1 + 1) * (EMLTree.eml u w).eval (1 + 1 + 1) = K) :
    (1 : Real) * log (w.eval 1)
      - (1 + 1) * (((1 : Real) + 1) * log (w.eval (1 + 1)))
      + ((1 : Real) + 1 + 1) * log (w.eval (1 + 1 + 1)) = 0 := by
  have m₁ := u1_master hu₁ e₁
  have m₂ := u1_master hu₂ e₂
  have m₃ := u1_master hu₃ e₃
  rw [m₁, m₂, m₃]
  mach_mpoly [exp α, K]

/-! ## Order helpers — `lt_of_mul_lt_mul_pos_left` is what replaces division -/

/-- `0 < b → a < a + b`. -/
theorem lt_add_of_pos_right {a b : Real} (hb : 0 < b) : a < a + b := by
  have h := add_lt_add_left hb a
  have eL : a + 0 = a := by mach_ring
  rw [eL] at h
  exact h

/-- `0 < a → 0 < b → 0 < a + b`. -/
theorem add_pos_real {a b : Real} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  lt_trans_ax ha (lt_add_of_pos_right hb)

/-- **Cancel a positive left factor.** Replaces every division this file would otherwise need. -/
theorem lt_of_mul_lt_mul_pos_left {a b c : Real} (hc : 0 < c) (h : c * a < c * b) : a < b := by
  rcases lt_total a b with hab | hab | hab
  · exact hab
  · exfalso; rw [hab] at h; exact lt_irrefl_ax _ h
  · exfalso; exact lt_irrefl_ax _ (lt_trans_ax h (mul_lt_mul_pos_left hab hc))

/-- `0 < b − a → a < b`. -/
theorem lt_of_sub_pos {a b : Real} (h : 0 < b - a) : a < b := by
  have hh := add_lt_add_left h a
  have eL : a + 0 = a := by mach_ring
  have eR : a + (b - a) = b := by mach_mpoly [a, b]
  rw [eL, eR] at hh
  exact hh

/-- Squaring preserves strict order on positives. -/
theorem square_lt_square {a b : Real} (ha : 0 < a) (h : a < b) : a * a < b * b :=
  lt_trans_ax (mul_lt_mul_of_pos_right h ha) (mul_lt_mul_pos_left h (lt_trans_ax ha h))

/-- `(c·a)·(c·a) = (c·c)·(a·a)`. **Stated over VARIABLES on purpose** — proving the instantiated
form directly makes `mach_mpoly` expand `16·P²` and hit this corpus's numeral-scale wall. -/
theorem sq_mul (c a : Real) : (c * a) * (c * a) = (c * c) * (a * a) := by mach_ring

/-- `(c·a)·b = c·(b·a)`. Same reason: keep the coefficient symbolic. -/
theorem mul_swap_right (c a b : Real) : (c * a) * b = c * (b * a) := by mach_ring

/-! ## Numeric facts, all from `two_lt_exp_one` -/

/-- `0 < 1+1+1`. -/
theorem three_pos : (0 : Real) < 1 + 1 + 1 := add_pos_real one_add_one_pos zero_lt_one_ax

/-- `0 < 1+1+1+1`. -/
theorem four_pos : (0 : Real) < 1 + 1 + 1 + 1 := add_pos_real three_pos zero_lt_one_ax

/-- `e² > 4`. -/
theorem exp_two_gt_four : (1 + 1 : Real) * (1 + 1) < exp (1 + 1) := by
  rw [exp_add 1 1]
  exact lt_trans_ax (mul_lt_mul_of_pos_right two_lt_exp_one one_add_one_pos)
    (mul_lt_mul_pos_left two_lt_exp_one (exp_pos 1))

/-- `e³ > 8`. -/
theorem exp_three_gt_eight : (1 + 1 : Real) * (1 + 1) * (1 + 1) < exp (1 + 1 + 1) := by
  rw [exp_add (1 + 1) 1]
  exact lt_trans_ax (mul_lt_mul_of_pos_right exp_two_gt_four one_add_one_pos)
    (mul_lt_mul_pos_left two_lt_exp_one (exp_pos (1 + 1)))

/-- `log 2 > 0`. -/
theorem log_two_pos : (0 : Real) < log (1 + 1) := by
  have h := log_lt_log zero_lt_one_ax one_lt_one_plus_one
  rw [log_one] at h
  exact h

/-- `2 < 4`. -/
theorem two_lt_four : (1 + 1 : Real) < (1 + 1) * (1 + 1) := by
  have e : (1 + 1 : Real) * (1 + 1) = (1 + 1) + (1 + 1) := by mach_ring
  rw [e]; exact lt_add_of_pos_right one_add_one_pos

/-- `log 2 < 2`.

**NOT via `exp_grows_strictly_thm`**, which rests on the tangent-line axiom
`exp_gt_one_plus_self`. `2 < 4 < e²` comes from `two_lt_exp_one` alone, and that is enough. -/
theorem log_two_lt_two : log (1 + 1 : Real) < 1 + 1 := by
  have h := log_lt_log one_add_one_pos (lt_trans_ax two_lt_four exp_two_gt_four)
  rw [log_exp] at h
  exact h

/-- `log 3 < 2`. -/
theorem log_three_lt_two : log (1 + 1 + 1 : Real) < 1 + 1 := by
  have h34 : (1 + 1 + 1 : Real) < (1 + 1) * (1 + 1) := by
    have e : (1 + 1 : Real) * (1 + 1) = (1 + 1 + 1) + 1 := by mach_ring
    rw [e]; exact lt_add_of_pos_right zero_lt_one_ax
  have h := log_lt_log three_pos (lt_trans_ax h34 exp_two_gt_four)
  rw [log_exp] at h
  exact h

/-! ## `(e³ − 2)² > e⁵` — the one real numeric fact -/

/-- `2 < e³`. -/
theorem two_lt_exp_three : (1 + 1 : Real) < exp (1 + 1 + 1) := by
  have h28 : (1 + 1 : Real) < (1 + 1) * (1 + 1) * (1 + 1) := by
    have e : (1 + 1 : Real) * (1 + 1) * (1 + 1) = (1 + 1) + ((1 + 1) + (1 + 1) + (1 + 1)) := by
      mach_ring
    rw [e]
    exact lt_add_of_pos_right (add_pos_real (add_pos_real one_add_one_pos one_add_one_pos)
      one_add_one_pos)
  exact lt_trans_ax h28 exp_three_gt_eight

set_option maxHeartbeats 1600000 in
/-- **`(e³ − 2)² > e⁵`.** From `4(e³−2) > 3e³` and `9e > 16`, squaring not cubing. -/
theorem exp_five_lt_cube_minus_two_sq :
    exp (1 + 1 + 1 + 1 + 1 : Real)
      < (exp (1 + 1 + 1) - (1 + 1)) * (exp (1 + 1 + 1) - (1 + 1)) := by
  have hP : (0 : Real) < exp (1 + 1 + 1) - (1 + 1) := sub_pos_of_lt two_lt_exp_three
  -- 3·e³ < 4·(e³ − 2)
  have h43 : (1 + 1 + 1 : Real) * exp (1 + 1 + 1)
      < (1 + 1 + 1 + 1) * (exp (1 + 1 + 1) - (1 + 1)) := by
    apply lt_of_sub_pos
    have key : (1 + 1 + 1 + 1 : Real) * (exp (1 + 1 + 1) - (1 + 1))
        - (1 + 1 + 1) * exp (1 + 1 + 1)
        = exp (1 + 1 + 1) - (1 + 1) * (1 + 1) * (1 + 1) := by
      mach_mpoly [exp (1 + 1 + 1)]
    rw [key]
    exact sub_pos_of_lt exp_three_gt_eight
  -- square both sides
  have h3Epos : (0 : Real) < (1 + 1 + 1) * exp (1 + 1 + 1) := mul_pos three_pos (exp_pos _)
  have hsq := square_lt_square h3Epos h43
  -- rewrite both sides
  have hE2 : exp (1 + 1 + 1 : Real) * exp (1 + 1 + 1)
      = exp (1 + 1 + 1 + 1 + 1) * exp 1 := by
    rw [← exp_add (1 + 1 + 1 : Real) (1 + 1 + 1), ← exp_add (1 + 1 + 1 + 1 + 1 : Real) 1]
    have e : (1 + 1 + 1 : Real) + (1 + 1 + 1) = (1 + 1 + 1 + 1 + 1) + 1 := by mach_ring
    rw [e]
  have eL := sq_mul (1 + 1 + 1 : Real) (exp (1 + 1 + 1))
  have eR := sq_mul (1 + 1 + 1 + 1 : Real) (exp (1 + 1 + 1) - (1 + 1))
  rw [eL, eR, hE2] at hsq
  -- hsq : 9 * (e⁵ * e) < 16 * P²
  -- and 16 * e⁵ < 9 * (e⁵ * e) because 16 < 9e
  have h16_9e : (1 + 1 + 1 + 1 : Real) * (1 + 1 + 1 + 1)
      < ((1 + 1 + 1) * (1 + 1 + 1)) * exp 1 := by
    have h18 : ((1 + 1 + 1 : Real) * (1 + 1 + 1)) * (1 + 1)
        < ((1 + 1 + 1) * (1 + 1 + 1)) * exp 1 :=
      mul_lt_mul_pos_left two_lt_exp_one (mul_pos three_pos three_pos)
    apply lt_trans_ax _ h18
    apply lt_of_sub_pos
    have e : ((1 + 1 + 1 : Real) * (1 + 1 + 1)) * (1 + 1)
        - (1 + 1 + 1 + 1) * (1 + 1 + 1 + 1) = 1 + 1 := by mach_ring
    rw [e]; exact one_add_one_pos
  have hstep : ((1 + 1 + 1 + 1 : Real) * (1 + 1 + 1 + 1)) * exp (1 + 1 + 1 + 1 + 1)
      < ((1 + 1 + 1) * (1 + 1 + 1)) * (exp (1 + 1 + 1 + 1 + 1) * exp 1) := by
    have h := mul_lt_mul_of_pos_right h16_9e (exp_pos (1 + 1 + 1 + 1 + 1))
    have e := mul_swap_right ((1 + 1 + 1 : Real) * (1 + 1 + 1)) (exp 1)
      (exp (1 + 1 + 1 + 1 + 1))
    rw [e] at h
    exact h
  have hfin := lt_trans_ax hstep hsq
  exact lt_of_mul_lt_mul_pos_left (mul_pos four_pos four_pos) hfin

/-! ## `w4` — the parameter-free cell, closed -/

/-- `log (e² − log 2) < 2`. -/
theorem logW2_lt_two : log (exp (1 + 1 : Real) - log (1 + 1)) < 1 + 1 := by
  have hW2pos : (0 : Real) < exp (1 + 1) - log (1 + 1) :=
    sub_pos_of_lt (lt_trans_ax (lt_trans_ax log_two_lt_two two_lt_four) exp_two_gt_four)
  have hlt : exp (1 + 1 : Real) - log (1 + 1) < exp (1 + 1) := by
    apply lt_of_sub_pos
    have e : exp (1 + 1 : Real) - (exp (1 + 1) - log (1 + 1)) = log (1 + 1) := by
      mach_mpoly [exp (1 + 1), log (1 + 1)]
    rw [e]; exact log_two_pos
  have h := log_lt_log hW2pos hlt
  rw [log_exp] at h
  exact h

/-- `log (e³ − log 3) + log (e³ − log 3) > 5`. -/
theorem logV_add_logV_gt_five :
    (1 : Real) + 1 + 1 + 1 + 1
      < log (exp (1 + 1 + 1 : Real) - log (1 + 1 + 1))
        + log (exp (1 + 1 + 1 : Real) - log (1 + 1 + 1)) := by
  have hVpos : (0 : Real) < exp (1 + 1 + 1) - log (1 + 1 + 1) :=
    sub_pos_of_lt (lt_trans_ax log_three_lt_two two_lt_exp_three)
  have hPpos : (0 : Real) < exp (1 + 1 + 1) - (1 + 1) := sub_pos_of_lt two_lt_exp_three
  have hPV : exp (1 + 1 + 1 : Real) - (1 + 1) < exp (1 + 1 + 1) - log (1 + 1 + 1) := by
    apply lt_of_sub_pos
    have e : (exp (1 + 1 + 1 : Real) - log (1 + 1 + 1)) - (exp (1 + 1 + 1) - (1 + 1))
        = (1 + 1) - log (1 + 1 + 1) := by
      mach_mpoly [exp (1 + 1 + 1), log (1 + 1 + 1)]
    rw [e]; exact sub_pos_of_lt log_three_lt_two
  have hV2 : exp (1 + 1 + 1 + 1 + 1 : Real)
      < (exp (1 + 1 + 1) - log (1 + 1 + 1)) * (exp (1 + 1 + 1) - log (1 + 1 + 1)) :=
    lt_trans_ax exp_five_lt_cube_minus_two_sq (square_lt_square hPpos hPV)
  have h := log_lt_log (exp_pos (1 + 1 + 1 + 1 + 1)) hV2
  rw [log_exp, log_mul hVpos hVpos] at h
  exact h

/-- **The second-difference relation is contradictory under the two bounds.**

`A < 2` gives `4A < 8`; `B + B > 5` gives `B > 2` and hence `3B > 7`; so
`1 − 4A + 3B > 1 − 8 + 7 = 0`, and it cannot be `0`.

**Stated over bare reals `A`, `B`** so no numeral ever meets a transcendental atom — the same
discipline that fixed `sq_mul`. -/
theorem sd_contradiction {A B : Real} (hA : A < 1 + 1)
    (hB : (1 : Real) + 1 + 1 + 1 + 1 < B + B)
    (h : (1 : Real) * 1 - (1 + 1) * ((1 + 1) * A) + (1 + 1 + 1) * B = 0) :
    False := by
  -- B > 2
  have h45 : (1 : Real) + 1 + (1 + 1) < 1 + 1 + 1 + 1 + 1 := by
    have e : (1 : Real) + 1 + (1 + 1) + 1 = 1 + 1 + 1 + 1 + 1 := by mach_ring
    rw [← e]; exact lt_add_of_pos_right zero_lt_one_ax
  have hB2 : (1 : Real) + 1 < B := by
    rcases lt_total B (1 + 1) with hb | hb | hb
    · exfalso
      have s1 : B + B < B + (1 + 1) := add_lt_add_left hb B
      have s2 : (1 : Real) + 1 + B < (1 + 1) + (1 + 1) := add_lt_add_left hb (1 + 1)
      have e : B + ((1 : Real) + 1) = (1 + 1) + B := by mach_ring
      rw [e] at s1
      exact lt_irrefl_ax _ (lt_trans_ax (lt_trans_ax hB (lt_trans_ax s1 s2)) h45)
    · exfalso
      rw [hb] at hB
      exact lt_irrefl_ax _ (lt_trans_ax hB h45)
    · exact hb
  -- 3B > 7
  have h3B : (1 : Real) + 1 + 1 + 1 + 1 + 1 + 1 < (1 + 1 + 1) * B := by
    have esplit : (1 + 1 + 1 : Real) * B = (B + B) + B := by mach_ring
    rw [esplit]
    have s1 : ((1 : Real) + 1 + 1 + 1 + 1) + (1 + 1) < (B + B) + B := by
      have t1 : ((1 : Real) + 1 + 1 + 1 + 1) + (1 + 1) < (B + B) + (1 + 1) := by
        have u := add_lt_add_left hB (1 + 1 : Real)
        have eL : (1 + 1 : Real) + ((1 : Real) + 1 + 1 + 1 + 1)
            = ((1 : Real) + 1 + 1 + 1 + 1) + (1 + 1) := by mach_ring
        have eR : (1 + 1 : Real) + (B + B) = (B + B) + (1 + 1) := by mach_ring
        rw [eL, eR] at u; exact u
      have t2 : (B + B) + ((1 : Real) + 1) < (B + B) + B := add_lt_add_left hB2 (B + B)
      exact lt_trans_ax t1 t2
    have e7 : ((1 : Real) + 1 + 1 + 1 + 1) + (1 + 1) = 1 + 1 + 1 + 1 + 1 + 1 + 1 := by mach_ring
    rw [e7] at s1
    exact s1
  -- 4A < 8
  have h4A : (1 + 1 : Real) * ((1 + 1) * A) < (1 + 1) * ((1 + 1) * (1 + 1)) :=
    mul_lt_mul_pos_left (mul_lt_mul_pos_left hA one_add_one_pos) one_add_one_pos
  -- assemble
  have hsplit : (1 : Real) * 1 - (1 + 1) * ((1 + 1) * A) + (1 + 1 + 1) * B
      = ((1 + 1) * ((1 + 1) * (1 + 1)) - (1 + 1) * ((1 + 1) * A))
        + ((1 + 1 + 1) * B - (1 + 1 + 1 + 1 + 1 + 1 + 1)) := by
    mach_mpoly [A, B]
  rw [hsplit] at h
  have hpos : (0 : Real) < ((1 + 1) * ((1 + 1) * (1 + 1)) - (1 + 1) * ((1 + 1) * A))
      + ((1 + 1 + 1) * B - (1 + 1 + 1 + 1 + 1 + 1 + 1)) :=
    add_pos_real (sub_pos_of_lt h4A) (sub_pos_of_lt h3B)
  rw [h] at hpos
  exact lt_irrefl_ax 0 hpos

set_option maxHeartbeats 1600000 in
/-- **`u1` over `w4` reaches no `K/x` whatsoever.**

Three points eliminate `exp α` and `K`; what is left is the parameter-free numeric claim
`1 − 4·log(e² − log 2) + 3·log(e³ − log 3) = 0`, and the left side is strictly positive. -/
theorem u1_w4_absurd {c₁ c₂ K : Real}
    (e₁ : (1 : Real) * (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
            (EMLTree.eml EMLTree.var EMLTree.var)).eval 1 = K)
    (e₂ : ((1 : Real) + 1) * (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
            (EMLTree.eml EMLTree.var EMLTree.var)).eval (1 + 1) = K)
    (e₃ : ((1 : Real) + 1 + 1) * (EMLTree.eml (EMLTree.eml (EMLTree.const c₁) (EMLTree.const c₂))
            (EMLTree.eml EMLTree.var EMLTree.var)).eval (1 + 1 + 1) = K) :
    False := by
  have hsd := u1_second_difference (α := exp c₁ - log c₂) rfl rfl rfl e₁ e₂ e₃
  have v₁ : (EMLTree.eml EMLTree.var EMLTree.var).eval 1 = exp 1 := by
    show exp (1 : Real) - log (1 : Real) = exp 1
    rw [log_one]; mach_ring
  rw [v₁, log_exp] at hsd
  exact sd_contradiction logW2_lt_two logV_add_logV_gt_five hsd

/-! ## The FOUR-point system — stating the remaining obligation precisely

`u1_second_difference` uses the points `1, 2, 3`. Since `x · log (W x)` is **affine**, its second
difference vanishes at **any** three equally spaced points — so `2, 3, 4` gives a *second,
independent* relation, and the two together are what the open cells need.

> ### The remaining obligation is not "more points". Numerically the two relations already separate: at the only root of the `1,2,3` relation on the branch `L′ ≤ e` (`L* ≈ 2.6213`) the `2,3,4` relation takes the value `≈ 0.883`. **What is missing is a proof that two transcendental functions have no COMMON root** — a root-separation problem, not a bookkeeping one. -/

/-- **The second difference at `2, 3, 4`** — independent of the one at `1, 2, 3`.

Together with `u1_second_difference` this is the four-point system. **Neither closes the open cells
on its own; stating both is what makes the remaining obligation precise.** -/
theorem u1_second_difference_234 {α K : Real} {u w : EMLTree}
    (hu₂ : u.eval (1 + 1) = α) (hu₃ : u.eval (1 + 1 + 1) = α)
    (hu₄ : u.eval (1 + 1 + 1 + 1) = α)
    (e₂ : ((1 : Real) + 1) * (EMLTree.eml u w).eval (1 + 1) = K)
    (e₃ : ((1 : Real) + 1 + 1) * (EMLTree.eml u w).eval (1 + 1 + 1) = K)
    (e₄ : ((1 : Real) + 1 + 1 + 1) * (EMLTree.eml u w).eval (1 + 1 + 1 + 1) = K) :
    ((1 : Real) + 1) * log (w.eval (1 + 1))
      - (1 + 1) * (((1 : Real) + 1 + 1) * log (w.eval (1 + 1 + 1)))
      + ((1 : Real) + 1 + 1 + 1) * log (w.eval (1 + 1 + 1 + 1)) = 0 := by
  have m₂ := u1_master hu₂ e₂
  have m₃ := u1_master hu₃ e₃
  have m₄ := u1_master hu₄ e₄
  rw [m₂, m₃, m₄]
  mach_mpoly [exp α, K]

/-- **`F` is DISCONTINUOUS at `L′ = exp 1`, because `log` is totalised.**

At `L′ = exp 1` the child `exp 1 − L′` is exactly `0`, and `log 0 = 0` — not the `−∞` a genuine
logarithm would give. **So the three-point relation's value jumps at that parameter**, and the
`L′ = exp 1` endpoint is not a limit of the interior.

Recorded because the hand-computation that first located the relation's root **got its sign and its
location wrong**, and this discontinuity is why sampling near the endpoint misleads. -/
theorem log_child_at_endpoint : log (exp 1 - exp 1) = 0 := by
  have e : exp 1 - exp 1 = (0 : Real) := by mach_ring
  rw [e]
  exact log_nonpos (le_refl 0)

end Real
end MachLib
