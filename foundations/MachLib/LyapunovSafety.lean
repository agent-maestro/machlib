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

/-! ## Coupled two-state plant — off-diagonal dynamics, weighted-ℓ¹ envelope -/

/-- Four-term triangle bound: `|a·p + c·q + b·cl + w| ≤ |a||p| + |c||q| + |b|·U + W` when the
actuator term is clamp-bounded (`|cl| ≤ U`) and the disturbance is bounded (`|w| ≤ W`). The
per-row building block when each state feeds BOTH next-states (off-diagonal coupling). -/
theorem coupled_term_bound (a c b p q cl w U W : Real)
    (hcl : abs cl ≤ U) (hw : abs w ≤ W) :
    abs (a * p + c * q + b * cl + w) ≤ abs a * abs p + abs c * abs q + abs b * U + W := by
  refine le_trans (abs_add (a * p + c * q + b * cl) w) ?_
  refine le_trans (add_le_add_both (abs_add (a * p + c * q) (b * cl)) (le_refl (abs w))) ?_
  refine le_trans (add_le_add_both
    (add_le_add_both (abs_add (a * p) (c * q)) (le_refl (abs (b * cl)))) (le_refl (abs w))) ?_
  rw [abs_mul, abs_mul, abs_mul]
  refine le_trans (add_le_add_both
    (add_le_add_both (le_refl (abs a * abs p + abs c * abs q))
      (mul_le_mul_of_nonneg_left hcl (abs_nonneg b))) hw) ?_
  exact le_of_eq (by mach_ring)

/-- Regroup a weighted sum of two affine rows by state (offset split as `Da+Db` to match the
flattened `…+|b|·U+W` shape `coupled_term_bound` produces; clean atoms keep `mach_ring` off the
atom-count cliff). -/
theorem regroup_2x2 (p1 p2 A1 C1 Da1 Db1 A2 C2 Da2 Db2 X1 X2 : Real) :
    p1 * (A1 * X1 + C1 * X2 + Da1 + Db1) + p2 * (A2 * X1 + C2 * X2 + Da2 + Db2)
    = (p1 * A1 + p2 * A2) * X1 + (p1 * C1 + p2 * C2) * X2
      + (p1 * (Da1 + Db1) + p2 * (Da2 + Db2)) := by
  mach_ring

theorem regroup_rho (rho p1 p2 X1 X2 D : Real) :
    (rho * p1) * X1 + (rho * p2) * X2 + D = rho * (p1 * X1 + p2 * X2) + D := by mach_ring

/-- **A genuinely COUPLED two-state plant stays in a weighted-ℓ¹ envelope, for all time.** State
`(x₁, x₂)` with FULL 2×2 dynamics (off-diagonal `a₁₂, a₂₁ ≠ 0` allowed), one saturating actuator,
bounded disturbances. The weighted-ℓ¹ Lyapunov function `V = p₁|x₁| + p₂|x₂|` contracts whenever the
plant is **column-diagonally-dominant under the weights** — `p₁|a₁₁|+p₂|a₂₁| ≤ ρ·p₁` and
`p₁|a₁₂|+p₂|a₂₂| ≤ ρ·p₂` with `ρ < 1` (the weighted-ℓ¹ matrix measure below 1). Proven by the
triangle inequality; the sublevel set `V ≤ X` is forward-invariant.

This removes the "two independent modes" limitation of `two_mode_clamp_envelope` — coupling is now
allowed, at the price of an explicit diagonal-dominance condition. The remaining frontier is a plant
that is stable but NOT weighted-ℓ¹-dominant (a pure oscillator: position has no self-damping); there
the decay only shows up in a non-diagonal quadratic `V = xᵀPx`, whose decrease is an SOS certificate
— see `neg_sos_nonpos`, the sufficiency seed for that case. -/
theorem coupled_two_state_clamp_envelope
    {x1 x2 v w1 w2 : Nat → Real} {a11 a12 a21 a22 b1 b2 U W1 W2 p1 p2 ρ X : Real}
    (hp1 : 0 ≤ p1) (hp2 : 0 ≤ p2) (hρ : 0 ≤ ρ) (hU : 0 ≤ U)
    (hplant1 : ∀ k, x1 (k + 1) = a11 * x1 k + a12 * x2 k + b1 * clamp (v k) (-U) U + w1 k)
    (hplant2 : ∀ k, x2 (k + 1) = a21 * x1 k + a22 * x2 k + b2 * clamp (v k) (-U) U + w2 k)
    (hcol1 : p1 * abs a11 + p2 * abs a21 ≤ ρ * p1)
    (hcol2 : p1 * abs a12 + p2 * abs a22 ≤ ρ * p2)
    (hw1 : ∀ k, abs (w1 k) ≤ W1) (hw2 : ∀ k, abs (w2 k) ≤ W2)
    (hinv : ρ * X + (p1 * (abs b1 * U + W1) + p2 * (abs b2 * U + W2)) ≤ X)
    (h0 : p1 * abs (x1 0) + p2 * abs (x2 0) ≤ X) :
    ∀ k, p1 * abs (x1 k) + p2 * abs (x2 k) ≤ X := by
  have hcl : ∀ k, abs (clamp (v k) (-U) U) ≤ U := by
    intro k; have h := clamp_abs_le (v k) (-U) U; rwa [abs_neg, abs_of_nonneg hU, max_self] at h
  refine measure_sublevel_invariant (V := fun k => p1 * abs (x1 k) + p2 * abs (x2 k))
    hρ hinv h0 (fun k => ?_)
  show p1 * abs (x1 (k + 1)) + p2 * abs (x2 (k + 1)) ≤
      ρ * (p1 * abs (x1 k) + p2 * abs (x2 k)) + (p1 * (abs b1 * U + W1) + p2 * (abs b2 * U + W2))
  rw [hplant1 k, hplant2 k]
  have m1 := coupled_term_bound a11 a12 b1 (x1 k) (x2 k) (clamp (v k) (-U) U) (w1 k) U W1 (hcl k) (hw1 k)
  have m2 := coupled_term_bound a21 a22 b2 (x1 k) (x2 k) (clamp (v k) (-U) U) (w2 k) U W2 (hcl k) (hw2 k)
  refine le_trans (add_le_add_both
    (mul_le_mul_of_nonneg_left m1 hp1) (mul_le_mul_of_nonneg_left m2 hp2)) ?_
  refine le_trans (le_of_eq (regroup_2x2 p1 p2 (abs a11) (abs a12) (abs b1 * U) W1
    (abs a21) (abs a22) (abs b2 * U) W2 (abs (x1 k)) (abs (x2 k)))) ?_
  refine le_trans (add_le_add_both (add_le_add_both
    (mul_le_mul_of_nonneg_right hcol1 (abs_nonneg (x1 k)))
    (mul_le_mul_of_nonneg_right hcol2 (abs_nonneg (x2 k)))) (le_refl _)) ?_
  exact le_of_eq (regroup_rho ρ p1 p2 (abs (x1 k)) (abs (x2 k))
    (p1 * (abs b1 * U + W1) + p2 * (abs b2 * U + W2)))

/-! ## Seed for the deeper (non-dominant) coupled case: the SOS sufficiency core -/

/-- **A Lyapunov decrease written as minus a sum of weighted squares is ≤ 0.** The genuinely-coupled
oscillator (no weighted-ℓ¹ dominance) needs a non-diagonal quadratic `V = xᵀPx`; its one-step
decrease `ΔV = V(x_{k+1}) − ρ·V(x_k)` is a quadratic form, and the discrete Lyapunov condition is
exactly that this form is negative semidefinite, i.e. equals `−(p·(x₁+r·x₂)² + q·x₂²)` for some
SOS certificate `p, q ≥ 0` (a completed square). This lemma discharges that the certificate form is
`≤ 0` — reducing the coupled case to *exhibiting* `(p, q, r)` and a ring identity, never to an
axiom. The numeric certificate for a specific plant is elementary arithmetic (decimals MachLib's
ring can't evaluate, so it lives in the application, like the scalar envelope number). -/
theorem neg_sos_nonpos {p q : Real} (hp : 0 ≤ p) (hq : 0 ≤ q) (r x1 x2 : Real) :
    -(p * ((x1 + r * x2) * (x1 + r * x2)) + q * (x2 * x2)) ≤ 0 :=
  neg_nonpos_of_nonneg
    (add_nonneg_ea (mul_nonneg hp (mul_self_nonneg _)) (mul_nonneg hq (mul_self_nonneg _)))

end MachLib.Real
