import MachLib.Exp
import MachLib.Log
import MachLib.Forge
import MachLib.SinNotInEMLDepth2Sweep

/-!
# Iterated Exponential Bounds — analytic infrastructure for depth-2 sin

Two small numerical facts about `π` and `e`, used to close the last 3
depth-2 sin barrier cases:
- `pi_gt_three : 3 < π`
- `exp_one_lt_three : exp 1 < 3`

Both were axioms here once. `pi_gt_three` is a theorem in `Trig.lean` since
2026-10-04; `exp_one_lt_three` is a theorem below since 2026-11-24.

Combined: `exp 1 < π`, hence `exp(exp 1) < exp π` by strict monotonicity.

This is the key inequality for closing Cases 4 and 5 where the hkey
equation forces `exp(exp(...)) - exp(exp 1) = exp π - 1` and we need
to bound LHS strictly above RHS.

No Mathlib dependency. Zero-Mathlib gate stays PASS.
-/

namespace MachLib
namespace Real

-- `pi_gt_three` was an axiom here until 2026-10-04: a theorem in `Trig.lean`, from `pi_lower_bound`.

/-- `0 ≤ a ≤ b` and `0 ≤ c ≤ d` give `a * c ≤ b * d`. -/
private theorem e_bound_mul_le {a b c d : Real} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) :
    a * c ≤ b * d := by
  have h1 : a * c ≤ a * d := mul_le_mul_of_nonneg_left hcd ha
  have hd : 0 ≤ d := le_trans hc hcd
  have h2 : a * d ≤ b * d := by
    rw [mul_comm a d, mul_comm b d]; exact mul_le_mul_of_nonneg_left hab hd
  exact le_trans h1 h2

private theorem e_bound_natCast_six : natCast 6 = 1 + 1 + 1 + 1 + 1 + 1 := by
  have e6 : natCast 6 = natCast 5 + 1 := natCast_succ 5
  have e5 : natCast 5 = natCast 4 + 1 := natCast_succ 4
  have e4 : natCast 4 = natCast 3 + 1 := natCast_succ 3
  have e3 : natCast 3 = natCast 2 + 1 := natCast_succ 2
  have e2 : natCast 2 = natCast 1 + 1 := natCast_succ 1
  have e1 : natCast 1 = natCast 0 + 1 := natCast_succ 0
  rw [e6, e5, e4, e3, e2, e1, natCast_zero, zero_add]

private theorem e_bound_natCast_three : natCast 3 = (1 + 1 + 1 : Real) := by
  have e3 : natCast 3 = natCast 2 + 1 := natCast_succ 2
  have e2 : natCast 2 = natCast 1 + 1 := natCast_succ 1
  have e1 : natCast 1 = natCast 0 + 1 := natCast_succ 0
  rw [e3, e2, e1, natCast_zero, zero_add]

/-- `exp 1 < 3`. (e < 3.) An axiom until 2026-11-24. The tangent line `1 + x ≤ exp x` at `x = -1/6` gives
`exp (-1/6) ≥ 5/6`, so `exp (-1) ≥ (5/6)⁶`, i.e. `15625 · e ≤ 46656`, and `46656 < 46875 = 3 · 15625`. The bound
proved is `e ≤ (6/5)⁶ ≈ 2.986`. No larger step than `1/6` works (at `1/5`, `(5/4)⁵ ≈ 3.05`); smaller ones do
(`(7/6)⁷ ≈ 2.94`). -/
theorem exp_one_lt_three : exp 1 < (1 + 1 + 1 : Real) := by
  have hN : (0 : Real) < natCast 6 := natCast_pos (by decide)
  have hN0 : natCast 6 ≠ (0 : Real) := ne_of_gt hN
  let t : Real := 1 / natCast 6
  have hNt : natCast 6 * t = 1 := mul_inv _ hN0
  let z : Real := exp (-t)
  -- the tangent line at 0, read at -t: 1 - t ≤ z, scaled by 6: 5 ≤ 6 z
  have htan : 1 + -t ≤ z := one_add_le_exp (-t)
  have h5 : natCast 5 ≤ natCast 6 * z := by
    have hs := mul_le_mul_of_nonneg_left htan (le_of_lt hN)
    have he : natCast 6 * (1 + -t) = natCast 5 := by
      have e1 : natCast 6 * (1 + -t) = natCast 6 + -(natCast 6 * t) := by mach_ring
      have e6 : natCast 6 = natCast 5 + 1 := natCast_succ 5
      rw [e1, hNt, e6]
      mach_ring
    rw [he] at hs; exact hs
  have h50 : (0 : Real) ≤ natCast 5 := natCast_nonneg 5
  -- sixth powers: (5)^6 ≤ (6 z)^6
  have h2 : natCast 5 * natCast 5 ≤ (natCast 6 * z) * (natCast 6 * z) := e_bound_mul_le h50 h5 h50 h5
  have h2' : (0 : Real) ≤ natCast 5 * natCast 5 := mul_nonneg h50 h50
  have h4 : (natCast 5 * natCast 5) * (natCast 5 * natCast 5)
      ≤ ((natCast 6 * z) * (natCast 6 * z)) * ((natCast 6 * z) * (natCast 6 * z)) :=
    e_bound_mul_le h2' h2 h2' h2
  have h4' : (0 : Real) ≤ (natCast 5 * natCast 5) * (natCast 5 * natCast 5) := mul_nonneg h2' h2'
  have h6 : ((natCast 5 * natCast 5) * (natCast 5 * natCast 5)) * (natCast 5 * natCast 5)
      ≤ (((natCast 6 * z) * (natCast 6 * z)) * ((natCast 6 * z) * (natCast 6 * z)))
          * ((natCast 6 * z) * (natCast 6 * z)) :=
    e_bound_mul_le h4' h4 h2' h2
  -- z^6 = exp (-1)
  have hz6 : z * z * z * z * z * z = exp (-1) := by
    have hsum : -t + -t + -t + -t + -t + -t = -1 := by
      have e1 : -t + -t + -t + -t + -t + -t = -((1 + 1 + 1 + 1 + 1 + 1) * t) := by mach_ring
      rw [e1, ← e_bound_natCast_six, hNt]
    rw [← hsum, exp_add, exp_add, exp_add, exp_add, exp_add]
  have hL : ((natCast 5 * natCast 5) * (natCast 5 * natCast 5)) * (natCast 5 * natCast 5) = natCast 15625 := by
    repeat rw [← natCast_mul]
  have hR : (((natCast 6 * z) * (natCast 6 * z)) * ((natCast 6 * z) * (natCast 6 * z)))
          * ((natCast 6 * z) * (natCast 6 * z)) = natCast 46656 * exp (-1) := by
    have e1 : (((natCast 6 * z) * (natCast 6 * z)) * ((natCast 6 * z) * (natCast 6 * z)))
          * ((natCast 6 * z) * (natCast 6 * z))
        = (((natCast 6 * natCast 6) * (natCast 6 * natCast 6)) * (natCast 6 * natCast 6))
          * (z * z * z * z * z * z) := by mach_ring
    rw [e1, hz6]
    repeat rw [← natCast_mul]
  rw [hL, hR] at h6
  -- multiply by e = exp 1 > 0: 15625 e ≤ 46656
  have he1 : exp (-1) * exp 1 = 1 := by rw [← exp_add, show (-1 : Real) + 1 = 0 from by mach_ring, exp_zero]
  have h7 : natCast 15625 * exp 1 ≤ natCast 46656 := by
    have hs := mul_le_mul_of_nonneg_left h6 (le_of_lt (exp_pos 1))
    rw [show exp 1 * (natCast 46656 * exp (-1)) = natCast 46656 * (exp (-1) * exp 1) from by mach_ring,
        he1, mul_one_ax, mul_comm] at hs
    exact hs
  have h8 : natCast 46656 < (natCast 15625 : Real) * natCast 3 := by
    rw [← natCast_mul]; exact natCast_lt_natCast (by decide)
  have h9 : natCast 15625 * exp 1 < natCast 15625 * natCast 3 := lt_of_le_of_lt h7 h8
  rw [← e_bound_natCast_three]
  rcases lt_total (exp 1) (natCast 3) with hlt | heq | hgt
  · exact hlt
  · rw [heq] at h9; exact absurd h9 (lt_irrefl_ax _)
  · have hc := mul_le_mul_of_nonneg_left (le_of_lt hgt) (natCast_nonneg 15625)
    exact absurd (lt_of_lt_of_le h9 hc) (lt_irrefl_ax _)

theorem exp_one_lt_pi : exp 1 < pi :=
  lt_trans_ax exp_one_lt_three pi_gt_three

theorem exp_exp_one_lt_exp_pi : exp (exp 1) < exp pi :=
  exp_lt exp_one_lt_pi

end Real
end MachLib

namespace MachLib

open Real

/-- Helper: from `a < b`, derive `pi < exp pi - log pi` (the main
inequality chain used in Cases 4 and 5). -/
private theorem exp_pi_sub_log_pi_gt_pi : pi < exp pi - log pi := by
  -- log π < π (log_lt_self) and exp π > 2π (exp_gt_two_x). Combine:
  -- π + log π < π + π = 2π < exp π, hence exp π - log π > π.
  have h_log_lt : log pi < pi := log_lt_self_of_pos pi pi_pos
  have h_exp_gt : (1 + 1) * pi < exp pi := exp_gt_two_x pi
  have h_two_pi_eq : (1 + 1 : Real) * pi = pi + pi := by
    rw [mul_comm, mul_distrib, mul_one_ax]
  rw [h_two_pi_eq] at h_exp_gt
  have h_add : pi + log pi < pi + pi := add_lt_add_left h_log_lt pi
  have step1 : pi + log pi < exp pi := lt_trans_ax h_add h_exp_gt
  -- Add -log π to both sides: π + log π + -log π < exp π + -log π.
  -- LHS = π, RHS = exp π - log π.
  have step2 := add_lt_add_left step1 (-log pi)
  rw [← add_assoc, add_comm (-log pi) pi, add_assoc pi (-log pi) (log pi),
      neg_add_self, add_zero,
      add_comm (-log pi) (exp pi), ← sub_def] at step2
  exact step2

/-- Row 3 vv-vc: t1 = `.eml(.var, .var)`, t2 = `.eml(.var, .const d)`.

Closes via:
1. hkey: `exp(exp(exp π - log π)) - exp(exp 1) = exp π - 1`.
2. `exp π - log π > π` (helper).
3. So `exp(exp π - log π) > exp π > 1 + π > 1` by exp_lt chain.
4. So `exp(exp(exp π - log π)) > exp π` (since `exp π - log π > π`
   implies `exp(exp π - log π) > exp π`, and we need to go one more level).

Actually the simpler chain:
- `exp π - log π > π` (helper).
- `exp(exp π - log π) > exp π` (exp_lt).
- `exp(exp(exp π - log π)) > exp(exp π)` (exp_lt again).
- `exp(exp π) > 1 + exp π` (Taylor).
- So `LHS = exp(exp(exp π - log π)) - exp(exp 1) > exp(exp π) - exp(exp 1)`.
- `exp(exp π) > exp π * exp 1` ? Or use `exp(exp π) - exp(exp 1) > exp π - 1`?
- Need `exp(exp π) > exp π - 1 + exp(exp 1)`, i.e.,
  `exp(exp π) - exp(exp 1) > exp π - 1`.
- We have `exp(exp π) > 1 + exp π` (Taylor). And `exp(exp 1) < exp π`
  (from exp_exp_one_lt_exp_pi). So `1 + exp π - exp(exp 1) > 1 + exp π - exp π = 1`. ✓ But want `> exp π - 1`.
- Actually `exp(exp π) - exp(exp 1) > (1 + exp π) - exp π = 1`. So LHS > 1.
  Want `> exp π - 1`. Need stronger lower bound.
- Use `exp(exp π) > 2 · exp π` (exp_gt_two_x at exp π). Then
  `exp(exp π) - exp(exp 1) > 2 · exp π - exp(exp 1) > 2 · exp π - exp π = exp π`
  (using `exp(exp 1) < exp π`). So LHS > exp π > exp π - 1 = RHS. ✓ -/
theorem sin_not_in_eml_t1_vv_t2_eml_vc (d : Real) :
    ¬ (∀ x : Real,
        (EMLTree.eml (.eml .var .var) (.eml .var (.const d))).eval x =
          Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  have hπ := hsin pi
  simp only [EMLTree.eval, sin_zero, sin_pi, exp_zero, log_zero, sub_zero] at h0 hπ
  -- Extract log values + positivity + exp_log.
  have hlog0 : log (1 - log d) = exp 1 := by
    have step : exp 1 - log (1 - log d) + log (1 - log d) =
                  0 + log (1 - log d) := by rw [h0]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  have hlogπ : log (exp pi - log d) = exp (exp pi - log pi) := by
    have step : exp (exp pi - log pi) - log (exp pi - log d) +
                  log (exp pi - log d) =
                  0 + log (exp pi - log d) := by rw [hπ]
    rw [sub_def, add_assoc, neg_add_self, add_zero, zero_add] at step
    exact step.symm
  have hpos0 : 0 < 1 - log d := by
    apply log_pos_arg_pos; rw [hlog0]; exact exp_pos _
  have hposπ : 0 < exp pi - log d := by
    apply log_pos_arg_pos; rw [hlogπ]; exact exp_pos _
  have hA : 1 - log d = exp (exp 1) := by
    have : exp (log (1 - log d)) = exp (exp 1) := by rw [hlog0]
    rw [exp_log hpos0] at this; exact this
  have hB : exp pi - log d = exp (exp (exp pi - log pi)) := by
    have : exp (log (exp pi - log d)) = exp (exp (exp pi - log pi)) := by
      rw [hlogπ]
    rw [exp_log hposπ] at this; exact this
  -- Key equation:
  have hkey : exp (exp (exp pi - log pi)) - exp (exp 1) = exp pi - 1 := by
    rw [← hB, ← hA]
    rw [sub_def, sub_def, sub_def, neg_add, neg_neg_helper,
        add_assoc, ← add_assoc (-log d) (-1) (log d),
        add_comm (-log d) (-1),
        add_assoc (-1) (-log d) (log d), neg_add_self, add_zero,
        ← sub_def]
  -- Contradiction chain.
  -- Step A: exp π - log π > π (helper).
  have hA1 : pi < exp pi - log pi := exp_pi_sub_log_pi_gt_pi
  -- Step B: exp(exp π - log π) > exp π.
  have hB1 : exp pi < exp (exp pi - log pi) := exp_lt hA1
  -- Step C: exp(exp(exp π - log π)) > exp(exp π).
  have hC1 : exp (exp pi) < exp (exp (exp pi - log pi)) := exp_lt hB1
  -- Step D: exp(exp π) > 2 · exp π (exp_gt_two_x).
  have hD1 : (1 + 1) * exp pi < exp (exp pi) := exp_gt_two_x (exp pi)
  -- Step E: combine C and D: exp(exp(exp π - log π)) > 2 · exp π.
  have hE : (1 + 1) * exp pi < exp (exp (exp pi - log pi)) :=
    lt_trans_ax hD1 hC1
  -- Step F: exp(exp(exp π - log π)) - exp(exp 1) > 2 · exp π - exp(exp 1).
  have hF : (1 + 1) * exp pi - exp (exp 1) <
              exp (exp (exp pi - log pi)) - exp (exp 1) := by
    -- From hE: add -exp(exp 1) on the left.
    have step := add_lt_add_left hE (-exp (exp 1))
    rw [add_comm (-exp (exp 1)) ((1+1) * exp pi),
        add_comm (-exp (exp 1)) (exp (exp (exp pi - log pi))),
        ← sub_def, ← sub_def] at step
    exact step
  -- Step G: 2 · exp π - exp(exp 1) > exp π (using exp(exp 1) < exp π).
  have hG : exp pi < (1 + 1) * exp pi - exp (exp 1) := by
    have h_two_exp_eq : (1 + 1 : Real) * exp pi = exp pi + exp pi := by
      rw [mul_comm, mul_distrib, mul_one_ax]
    rw [h_two_exp_eq]
    -- goal: exp pi < exp pi + exp pi - exp(exp 1)
    -- equivalent: 0 < exp pi - exp(exp 1), i.e., exp(exp 1) < exp pi
    have h_sub_pos : 0 < exp pi - exp (exp 1) :=
      sub_pos_of_lt exp_exp_one_lt_exp_pi
    have step := add_lt_add_left h_sub_pos (exp pi)
    rw [add_zero, sub_def, ← add_assoc, ← sub_def] at step
    exact step
  -- Step H: exp π > exp π - 1 (trivial).
  have hH : exp pi - 1 < exp pi := by
    have hneg : (-1 : Real) < 0 := by
      have step := add_lt_add_left zero_lt_one_ax (-1)
      rw [add_zero, neg_add_self] at step
      exact step
    have step := add_lt_add_left hneg (exp pi)
    rw [add_zero, ← sub_def] at step
    exact step
  -- Step I: combine. hkey says LHS = RHS = exp π - 1.
  -- We have LHS > 2 · exp π - exp(exp 1) > exp π > exp π - 1.
  -- So LHS > exp π - 1, but hkey says LHS = exp π - 1. Contradiction.
  have hLHS_gt_RHS : exp pi - 1 < exp (exp (exp pi - log pi)) - exp (exp 1) :=
    lt_trans_ax hH (lt_trans_ax hG hF)
  rw [hkey] at hLHS_gt_RHS
  exact lt_irrefl_ax _ hLHS_gt_RHS

-- =================================================================
-- Cases 2 and 4 (Row 3 cv-cv and Row 3 vc-vc) deferred:
--
-- These two cases have free parameter `log d1` (or `log d`) that
-- can be arbitrarily large, so the 2-point evaluation hkey
-- `exp(exp v) - exp(exp u) = v - u` with `v - u` fixed at `exp π - 1`
-- has solutions for specific `log d1` values (around -21 in the
-- numerical analysis). The 2-point system is satisfiable; 3-point
-- evaluation (e.g., x = 1) is needed to over-determine and contradict.
--
-- The iterated exponential bound used to close Case 5 doesn't apply
-- here because Case 5's special structure (`log π` instead of a free
-- `log d1`) lets us bound `exp π - log π > π` uniformly. Cases 2 and 4
-- lack that uniform bound.
--
-- Closure of Cases 2 and 4 belongs in a dedicated 3-point-evaluation
-- artifact that derives a sharper constraint by combining x=0, x=1,
-- and x=π equations into an over-determined system.

end MachLib
