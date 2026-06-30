import MachLib.ClosedLoopSafety

/-!
# Lyapunov sublevel-set safety — the envelope for a VECTOR state

`ClosedLoopSafety` keeps a *scalar* plant inside `|x| ≤ X`. Real plants have a vector state
(position *and* velocity, …) and the safe set is a sublevel set of a Lyapunov function `V`, not an
interval. This file lifts the guarantee to that setting.

The lift is almost free: the scalar invariance argument never used that the bounded quantity was
`|x|` — only that it satisfied a contraction `m_{k+1} ≤ ρ·m_k + δ`. So the *same* induction proves
that ANY non-negative Lyapunov sequence `V` with `V_{k+1} ≤ ρ·V_k + δ` stays under its sublevel
threshold. That is `measure_sublevel_invariant`; `safe_envelope_invariant` is its `V = |x|` case.

`two_mode_clamp_envelope` is a fully-proven vector instance: a **two-mode** plant (two stable
first-order modes sharing one saturating actuator) kept inside the weighted-ℓ¹ sublevel set
`p₁|x₁| + p₂|x₂| ≤ X`. This is the *diagonalisable / real-eigenvalue* case, where a weighted-ℓ¹
Lyapunov function contracts by the triangle inequality alone — no matrix theory.

**Honest frontier.** A genuinely *coupled* oscillator (mass–spring–damper: position has no
self-damping, the decay only shows up in a non-diagonal quadratic `V = xᵀPx`) needs the discrete
Lyapunov inequality `AᵀPA ⪯ ρ²P`, i.e. a numeric semidefiniteness/SOS check that MachLib's
Mathlib-free automation cannot yet discharge (no `nlinarith`/`polyrith`, and `mach_ring` can't
evaluate decimal coefficients). `measure_sublevel_invariant` is stated precisely so that such a
quadratic contraction, once produced, plugs straight in as its `hstep` hypothesis — the coupled
case is reduced to "exhibit the Lyapunov certificate", not assumed.

All theorems here are `sorryAx`-free (rest only on MachLib's documented Real-field axioms).
-/

namespace MachLib.Real

/-- **Lyapunov sublevel-set invariance (vector-state core).** Any Lyapunov sequence `V` that
contracts (`V_{k+1} ≤ ρ·V_k + δ`) and starts under a threshold `X` wide enough to absorb the offset
(`ρ·X + δ ≤ X`) stays under it forever. Identical induction to `safe_envelope_invariant`, with the
scalar `|x_k|` replaced by an arbitrary `V_k` — which is exactly why the closed-loop argument
generalises from intervals to sublevel sets, and accepts a quadratic `V` as readily as `|x|`. -/
theorem measure_sublevel_invariant {V : Nat → Real} {ρ δ X : Real}
    (hρ : 0 ≤ ρ) (hinv : ρ * X + δ ≤ X) (h0 : V 0 ≤ X)
    (hstep : ∀ k, V (k + 1) ≤ ρ * V k + δ) :
    ∀ k, V k ≤ X := by
  intro k
  induction k with
  | zero => exact h0
  | succ n ih =>
      exact le_trans (hstep n)
        (le_trans (add_le_add_both (mul_le_mul_of_nonneg_left ih hρ) (le_refl δ)) hinv)

/-- **One stable mode under a shared saturating actuator.** For `x_{k+1} = a·x_k + b·clamp(v_k,−U,U)
+ w_k` with `|a| ≤ ρ` and `|w_k| ≤ W`, one step grows `|x|` by at most `ρ·|x_k| + (|b|·U + W)` — the
clamp caps the control contribution at `|b|·U` no matter what `v_k` is. The per-mode building block
of the vector envelope. -/
theorem mode_step_bound {x v w : Nat → Real} {a b U W ρ : Real}
    (hplant : ∀ k, x (k + 1) = a * x k + b * clamp (v k) (-U) U + w k)
    (ha : abs a ≤ ρ) (hU : 0 ≤ U) (hw : ∀ k, abs (w k) ≤ W) (k : Nat) :
    abs (x (k + 1)) ≤ ρ * abs (x k) + (abs b * U + W) := by
  rw [hplant k]
  have hclamp : abs (clamp (v k) (-U) U) ≤ U := by
    have h := clamp_abs_le (v k) (-U) U; rwa [abs_neg, abs_of_nonneg hU, max_self] at h
  refine le_trans (abs_add (a * x k + b * clamp (v k) (-U) U) (w k)) ?_
  refine le_trans
    (add_le_add_both (abs_add (a * x k) (b * clamp (v k) (-U) U)) (le_refl (abs (w k)))) ?_
  rw [abs_mul, abs_mul]
  refine le_trans (add_le_add_both (add_le_add_both
      (mul_le_mul_of_nonneg_right ha (abs_nonneg (x k)))
      (mul_le_mul_of_nonneg_left hclamp (abs_nonneg b)))
      (hw k)) ?_
  exact le_of_eq (by mach_ring)

/-- **A two-mode plant stays in a weighted-ℓ¹ sublevel set, for all time.** Two stable first-order
modes `x₁, x₂` (`|aᵢ| ≤ ρ < 1`) driven by ONE saturating actuator `clamp(v_k,−U,U)` with bounded
disturbances. The Lyapunov function `V = p₁|x₁| + p₂|x₂|` (any positive weights) contracts by the
triangle inequality, so the sublevel set `V ≤ X` is forward-invariant whenever `X` absorbs the
offset `δ = p₁(|b₁|U+W₁) + p₂(|b₂|U+W₂)`. The diagonalisable / real-eigenvalue vector case, fully
proven; the coupled-oscillator case is the stated frontier (see module docstring). -/
theorem two_mode_clamp_envelope
    {x1 x2 v w1 w2 : Nat → Real} {a1 a2 b1 b2 U W1 W2 p1 p2 ρ X : Real}
    (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) (hρ : 0 ≤ ρ)
    (hplant1 : ∀ k, x1 (k + 1) = a1 * x1 k + b1 * clamp (v k) (-U) U + w1 k)
    (hplant2 : ∀ k, x2 (k + 1) = a2 * x2 k + b2 * clamp (v k) (-U) U + w2 k)
    (ha1 : abs a1 ≤ ρ) (ha2 : abs a2 ≤ ρ) (hU : 0 ≤ U)
    (hw1 : ∀ k, abs (w1 k) ≤ W1) (hw2 : ∀ k, abs (w2 k) ≤ W2)
    (hinv : ρ * X + (p1 * (abs b1 * U + W1) + p2 * (abs b2 * U + W2)) ≤ X)
    (h0 : p1 * abs (x1 0) + p2 * abs (x2 0) ≤ X) :
    ∀ k, p1 * abs (x1 k) + p2 * abs (x2 k) ≤ X := by
  refine measure_sublevel_invariant (V := fun k => p1 * abs (x1 k) + p2 * abs (x2 k))
    hρ hinv h0 (fun k => ?_)
  have m1 := mode_step_bound hplant1 ha1 hU hw1 k
  have m2 := mode_step_bound hplant2 ha2 hU hw2 k
  refine le_trans (add_le_add_both
      (mul_le_mul_of_nonneg_left m1 hp1) (mul_le_mul_of_nonneg_left m2 hp2)) ?_
  exact le_of_eq (by mach_ring)

end MachLib.Real
