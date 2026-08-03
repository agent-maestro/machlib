import MachLib.Iteration
import MachLib.AffineContraction

/-!
# Monitor soundness — composition over a multiplicative chain

Bar 3 (multiplicative half) of the monitor-metatheory arm.

A conclusion-shaped monitor witnesses the residual `r i = 1 - b i * y i` at each step.
This file proves what silence across `n` steps entitles you to conclude for a chain
composed by multiplication.

**No contraction hypothesis is required.** The recurrence is affine with `L = 1 + c`,
which `iterate_error_bound` accepts (it needs `0 ≤ L`, not `L < 1`), so the existing
contraction backbone carries this directly.

The *iterative* half — where `y` of one step becomes the operand `b` of the next — is
NOT proven here and is not implied by this file.
-/

namespace MachLib
open Real

/-- Running product of `(1 - r i)`; `r i` is step `i`'s monitored residual. -/
noncomputable def prodResid (r : Nat → Real) : Nat → Real
  | 0     => 1
  | n + 1 => prodResid r n * (1 - r n)

theorem prodResid_zero (r : Nat → Real) : prodResid r 0 = 1 := rfl
theorem prodResid_succ (r : Nat → Real) (n : Nat) :
    prodResid r (n + 1) = prodResid r n * (1 - r n) := rfl

/-- `|P| ≤ 1 + |1 - P|`. -/
theorem abs_le_one_add_abs_one_sub (P : Real) : abs P ≤ 1 + abs (1 - P) := by
  calc abs P = abs (1 + (P - 1)) := by rw [show (1 : Real) + (P - 1) = P from by mach_ring]
    _ ≤ abs 1 + abs (P - 1) := abs_add _ _
    _ = 1 + abs (1 - P) := by
        rw [abs_one, show P - 1 = -(1 - P) from by mach_ring, abs_neg]

/-- **The step recurrence.** Monitor silence at step `n` gives an affine bound with
`L = 1 + c`, `ε = c`. -/
theorem monitor_step_recurrence (r : Nat → Real) (c : Real) (hc : 0 ≤ c)
    (hM : ∀ i, abs (r i) ≤ c) (n : Nat) :
    abs (1 - prodResid r (n + 1)) ≤ (1 + c) * abs (1 - prodResid r n) + c := by
  have hsplit : 1 - prodResid r (n + 1)
      = (1 - prodResid r n) + prodResid r n * r n := by
    rw [prodResid_succ]; mach_ring
  have h1 : abs (1 - prodResid r (n + 1))
      ≤ abs (1 - prodResid r n) + abs (prodResid r n * r n) := by
    rw [hsplit]; exact abs_add _ _
  have h2 : abs (prodResid r n * r n) = abs (prodResid r n) * abs (r n) := abs_mul _ _
  have hA : abs (prodResid r n) * abs (r n) ≤ abs (prodResid r n) * c :=
    mul_le_mul_of_nonneg_left (hM n) (abs_nonneg _)
  have hB : c * abs (prodResid r n) ≤ c * (1 + abs (1 - prodResid r n)) :=
    mul_le_mul_of_nonneg_left (abs_le_one_add_abs_one_sub _) hc
  have h3 : abs (prodResid r n) * abs (r n)
      ≤ (1 + abs (1 - prodResid r n)) * c := by
    rw [show abs (prodResid r n) * c = c * abs (prodResid r n) from by mach_ring] at hA
    rw [show c * (1 + abs (1 - prodResid r n))
          = (1 + abs (1 - prodResid r n)) * c from by mach_ring] at hB
    exact le_trans hA hB
  have h4 : abs (1 - prodResid r n) + (1 + abs (1 - prodResid r n)) * c
      = (1 + c) * abs (1 - prodResid r n) + c := by mach_ring
  have h5 := add_le_add_both (le_refl (abs (1 - prodResid r n))) (le_trans (le_of_eq h2) h3)
  exact le_trans h1 (le_trans h5 (le_of_eq h4))

/-- **BAR 3, multiplicative half.** If a conclusion-shaped monitor is silent at every
step — `|1 - bᵢ·yᵢ| ≤ c` for all `i` — then the chain composed by multiplication carries
relative error at most `(1+c)ⁿ - 1`, **for that trace**.

No contraction hypothesis. -/
theorem monitor_compose_mul (r : Nat → Real) (c : Real) (hc : 0 ≤ c)
    (hM : ∀ i, abs (r i) ≤ c) (n : Nat) :
    abs (1 - prodResid r n) ≤ npow n (1 + c) - 1 := by
  have hL : (0 : Real) ≤ 1 + c := by
    have h := add_le_add_both (le_of_lt one_pos) hc
    have e : (0 : Real) + 0 = 0 := by mach_ring
    rw [e] at h; exact h
  have h0 : abs (1 - prodResid r 0) ≤ 0 := by
    rw [prodResid_zero, show (1 : Real) - 1 = 0 from by mach_ring, abs_zero]
    exact le_refl 0
  have hbound := iterate_error_bound (fun k => abs (1 - prodResid r k)) hL hc h0
    (fun k => monitor_step_recurrence r c hc hM k) n
  have htel := geom_telescope (1 + c) n
  -- `geom` and `npow` are Nat-recursive; keep them opaque or `mach_ring` unfolds them.
  generalize hG : geom (1 + c) n = G at htel hbound
  generalize hP : npow n (1 + c) = P at htel
  have e1 : c * G = -((1 - (1 + c)) * G) := by mach_ring
  rw [e1, htel] at hbound
  have e2 : -(1 - P) = P - 1 := by mach_ring
  rw [e2] at hbound
  exact hbound

/-! ## Bar 3, ITERATIVE half — where the output feeds the next step's operand -/

/-- **Monitor silence, converted to a per-step DEVIATION.**

If a step computes `g * y` where `y` is a monitored reciprocal of `b` (`b * binv = 1` exactly),
then silence bounds the deviation from the exact step by `c` times the *exact step's own
magnitude* — because the residual IS the relative error. Division-free. -/
theorem monitor_deviation_bound (g b binv y c : Real)
    (hinv : b * binv = 1)
    (hres : abs (1 - b * y) ≤ c) :
    abs (g * y - g * binv) ≤ abs (g * binv) * c := by
  have key : g * y - g * binv = (g * binv) * -(1 - b * y) := by
    have h : (g * binv) * -(1 - b * y) = g * ((b * binv) * y) - g * binv := by
      mach_mpoly [g, b, binv, y]
    rw [h, hinv]; mach_mpoly [g, y, binv]
  rw [key, abs_mul, abs_neg]
  exact mul_le_mul_of_nonneg_left hres (abs_nonneg _)

/-- **BAR 3, ITERATIVE half.** A monitored kernel inside a state-feedback loop
`x_{k+1} = f(x_k)`: silence at every step gives a trace bound `(c·M) · geom L n`.

**The contraction hypothesis does NOT vanish here — it RELOCATES.** `L` is the Lipschitz
constant of **the surrounding system's step map**, not of the reciprocal and not of the monitor.
The bound is finite as `n → ∞` iff `L < 1`, and that is a fact about the application. -/
theorem monitor_compose_iter {f : Real → Real} {L c M : Real} {xc xe : Nat → Real}
    (hL0 : 0 ≤ L) (hcM : 0 ≤ c * M)
    (hlip : ∀ x y, abs (f x - f y) ≤ L * abs (x - y))
    (h0 : abs (xc 0 - xe 0) ≤ 0)
    (hexact : ∀ k, xe (k + 1) = f (xe k))
    (hstep : ∀ k, abs (xc (k + 1) - f (xc k)) ≤ c * M)
    (n : Nat) :
    abs (xc n - xe n) ≤ (c * M) * geom L n :=
  (lipschitz_trajectory_bound hL0 hcM hlip h0 hexact hstep n).1

end MachLib
