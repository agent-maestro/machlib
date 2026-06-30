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

The genuinely *coupled* cases are also covered here:
* `coupled_two_state_clamp_envelope` — off-diagonal `A`, under a weighted-ℓ¹ diagonal-dominance
  condition (triangle inequality, fully proven).
* `quadratic_lyapunov_sublevel` — a non-diagonal quadratic `V = xᵀPx` (the oscillator: position has
  no self-damping), with clamp+disturbance, via the **parallelogram law** (no Young/S-procedure, no
  sqrt). Fully proven; the parallelogram's factor 2 costs a `ρ < ½` (well-damped) condition.
* `quadratic_lyapunov_sublevel_tight` — removes `ρ < ½`: the V-norm `√V` contracts at rate `√ρ` for
  ANY `ρ < 1`. Fully proven *modulo* one true hypothesis, the V-norm triangle inequality, which
  reduces to Cauchy–Schwarz.

* `quadratic_lyapunov_sublevel_tight'` — the SAME but UNCONDITIONAL: the V-norm triangle inequality
  is proven (`vq_minkowski`), so there are no hypotheses beyond the standard Lyapunov certificate.
  Fully closed, any `ρ < 1`.

**Tooling note.** The triangle inequality reduces to Cauchy–Schwarz, whose Gram identity
`V(x)V(y) − B² = αγ(…)²` is a degree-4 polynomial identity `mach_ring` cannot discharge (it does not
cancel `+c+c−c−c → 0`). But MachLib's OTHER normaliser, **`mach_mpoly`**, *is* a complete polynomial
normaliser and proves it directly (verified `sorryAx`-free). Lesson: for any identity needing
cancellation, use `mach_mpoly`, not the all-`try` `mach_ring`.

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

/-! ## Full coupled oscillator — a non-diagonal quadratic Lyapunov function, via the parallelogram law

The pure oscillator (position has no self-damping) is NOT weighted-ℓ¹-dominant, so
`coupled_two_state_clamp_envelope` does not reach it. The decay lives only in a non-diagonal
quadratic `V`. We take `V` in SOS coordinates, `Vq α β γ a b = α·(a+β·b)² + γ·b²` (`α,γ ≥ 0` ⟹
`V ≥ 0`), and handle the disturbance with the **parallelogram law** instead of a Young/S-procedure:
`V(h+g) + V(h−g) = 2V(h) + 2V(g)` is a ring identity, and `V(h−g) ≥ 0`, so the cross-term drops out
and `V(Ax+g) ≤ 2·V(Ax) + 2·V(g)` — no sqrt, no division, no completing-the-square over the
disturbance. The price is the factor 2: the contraction rate is `2ρ`, so this needs a
sufficiently-damped homogeneous decrease `2ρ < 1` (`V(Ax) ≤ ρ·V(x)` with `ρ < ½`). That is the
honest scope — a tighter rate needs the V-norm triangle inequality (Minkowski / Cauchy–Schwarz),
which needs `sqrt_mul`/`sq_sqrt` MachLib's sqrt layer does not yet provide. -/

/-- Diagonal quadratic form in SOS coordinates `(p, b)` with weights `α, γ`. The `p`-coordinate is
opaque here, which keeps `mach_ring` off the `β` cross-term expansion that times it out. -/
noncomputable def Wq (α γ p b : Real) : Real := α * (p * p) + γ * (b * b)

/-- Quadratic Lyapunov function: `Wq` evaluated at the completed-square coordinate `p = a + β·b`.
A genuinely non-diagonal `xᵀPx` (the `β` couples the two states). `α,γ ≥ 0` make it PSD. -/
noncomputable def Vq (α β γ a b : Real) : Real := Wq α γ (a + β * b) b

/-- `Wq` is non-negative when its weights are. -/
theorem wq_nonneg {α γ : Real} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (p b : Real) : 0 ≤ Wq α γ p b := by
  unfold Wq
  exact add_nonneg_ea (mul_nonneg hα (mul_self_nonneg _)) (mul_nonneg hγ (mul_self_nonneg _))

theorem vq_nonneg {α γ : Real} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (β a b : Real) : 0 ≤ Vq α β γ a b :=
  wq_nonneg hα hγ _ _

/-- Parallelogram law for the diagonal form `Wq`. `mach_ring` is not a complete ring normaliser —
it cannot reduce `+c+c−c−c → 0` (the squared-sum cross-term cancellation). So we route around it:
expand each `Wq` into a pure-square part `S` plus a cross part `C` (no cancellation — `mach_ring`
does FOIL+regroup fine), then collapse `(S+C)+(S−C) → S+S` with `C` held OPAQUE (the one shape
`mach_ring` does cancel), and finish with an AC rearrangement. -/
theorem wq_parallelogram (α γ ph pg b2 g2 : Real) :
    Wq α γ (ph + pg) (b2 + g2) + Wq α γ (ph - pg) (b2 - g2)
      = (Wq α γ ph b2 + Wq α γ ph b2) + (Wq α γ pg g2 + Wq α γ pg g2) := by
  have key : ∀ S C : Real, (S + C) + (S - C) = S + S := fun S C => by mach_ring
  have hadd : Wq α γ (ph + pg) (b2 + g2)
      = (α * (ph * ph) + γ * (b2 * b2) + (α * (pg * pg) + γ * (g2 * g2)))
        + (α * (ph * pg + pg * ph) + γ * (b2 * g2 + g2 * b2)) := by unfold Wq; mach_ring
  have hsub : Wq α γ (ph - pg) (b2 - g2)
      = (α * (ph * ph) + γ * (b2 * b2) + (α * (pg * pg) + γ * (g2 * g2)))
        - (α * (ph * pg + pg * ph) + γ * (b2 * g2 + g2 * b2)) := by unfold Wq; mach_ring
  rw [hadd, hsub, key (α * (ph * ph) + γ * (b2 * b2) + (α * (pg * pg) + γ * (g2 * g2)))
        (α * (ph * pg + pg * ph) + γ * (b2 * g2 + g2 * b2))]
  unfold Wq; mach_ring

/-- `Vq` in the additive SOS coordinate: `Vq(h+g) = Wq(p_h+p_g, h2+g2)` where `p = a+β·b` is linear,
so it splits additively. Proven by rewriting only the LINEAR argument — `mach_ring` never squares,
so no `β` cross-term blow-up. -/
theorem vq_as_wq_add (α β γ h1 h2 g1 g2 : Real) :
    Vq α β γ (h1 + g1) (h2 + g2)
      = Wq α γ ((h1 + β * h2) + (g1 + β * g2)) (h2 + g2) := by
  unfold Vq
  rw [show (h1 + g1) + β * (h2 + g2) = (h1 + β * h2) + (g1 + β * g2) from by mach_ring]

theorem vq_as_wq_sub (α β γ h1 h2 g1 g2 : Real) :
    Vq α β γ (h1 - g1) (h2 - g2)
      = Wq α γ ((h1 + β * h2) - (g1 + β * g2)) (h2 - g2) := by
  unfold Vq
  rw [show (h1 - g1) + β * (h2 - g2) = (h1 + β * h2) - (g1 + β * g2) from by mach_ring]

/-- `Vq` is `Wq` at the completed-square coordinate, by definition. -/
theorem vq_def (α β γ a b : Real) : Vq α β γ a b = Wq α γ (a + β * b) b := rfl

/-- **Parallelogram bound: the disturbance cross-term drops out.** `V(h+g) ≤ (V(h)+V(h)) +
(V(g)+V(g))` for the quadratic form, from the parallelogram law and `V(h−g) ≥ 0`. No sqrt, no Young
inequality, no S-procedure. (`E+E` rather than `2·E`: MachLib's Real has no `OfNat 2`, so doubling
is addition.) -/
theorem vq_add_le {α γ : Real} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (β h1 h2 g1 g2 : Real) :
    Vq α β γ (h1 + g1) (h2 + g2)
      ≤ (Vq α β γ h1 h2 + Vq α β γ h1 h2) + (Vq α β γ g1 g2 + Vq α β γ g1 g2) := by
  -- parallelogram in Wq coordinates: Vq(h+g) + Vq(h−g) = 2Vq(h) + 2Vq(g)
  have hpar : Vq α β γ (h1 + g1) (h2 + g2) + Vq α β γ (h1 - g1) (h2 - g2)
      = (Vq α β γ h1 h2 + Vq α β γ h1 h2) + (Vq α β γ g1 g2 + Vq α β γ g1 g2) := by
    rw [vq_as_wq_add, vq_as_wq_sub, wq_parallelogram, vq_def α β γ h1 h2, vq_def α β γ g1 g2]
  have hpos : 0 ≤ Vq α β γ (h1 - g1) (h2 - g2) := vq_nonneg hα hγ β _ _
  have step1 : Vq α β γ (h1 + g1) (h2 + g2)
      ≤ Vq α β γ (h1 + g1) (h2 + g2) + Vq α β γ (h1 - g1) (h2 - g2) := by
    have h := add_le_add_both (le_refl (Vq α β γ (h1 + g1) (h2 + g2))) hpos
    rwa [add_zero] at h
  exact le_trans step1 (le_of_eq hpar)

/-- **A coupled oscillator stays in a quadratic sublevel set, for all time.** Plant
`x_{k+1} = A·x_k + g_k` (full 2×2 `A`, `g` the clamped control + bounded disturbance), with a
non-diagonal quadratic Lyapunov function `Vq α β γ`. Given a sufficiently-damped homogeneous decrease
`V(A·x) ≤ ρ·V(x)` (the SOS/LMI certificate — `ρ < ½` so the parallelogram factor 2 still contracts)
and a disturbance bound `V(g) ≤ Vg`, the sublevel set `{V ≤ X}` is forward-invariant whenever
`X` absorbs the offset (`2ρ·X + 2·Vg ≤ X`). The first machine-checked safety envelope for a genuinely
coupled (non-ℓ¹-dominant) plant — the oscillator case. -/
theorem quadratic_lyapunov_sublevel
    {x1 x2 g1 g2 : Nat → Real} {a11 a12 a21 a22 α β γ ρ Vg X : Real}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (h2ρ : 0 ≤ ρ + ρ)
    (hplant1 : ∀ k, x1 (k + 1) = (a11 * x1 k + a12 * x2 k) + g1 k)
    (hplant2 : ∀ k, x2 (k + 1) = (a21 * x1 k + a22 * x2 k) + g2 k)
    (hhom : ∀ k, Vq α β γ (a11 * x1 k + a12 * x2 k) (a21 * x1 k + a22 * x2 k)
              ≤ ρ * Vq α β γ (x1 k) (x2 k))
    (hdist : ∀ k, Vq α β γ (g1 k) (g2 k) ≤ Vg)
    (hinv : (ρ + ρ) * X + (Vg + Vg) ≤ X)
    (h0 : Vq α β γ (x1 0) (x2 0) ≤ X) :
    ∀ k, Vq α β γ (x1 k) (x2 k) ≤ X := by
  refine measure_sublevel_invariant (V := fun k => Vq α β γ (x1 k) (x2 k)) h2ρ hinv h0 (fun k => ?_)
  show Vq α β γ (x1 (k + 1)) (x2 (k + 1)) ≤ (ρ + ρ) * Vq α β γ (x1 k) (x2 k) + (Vg + Vg)
  rw [hplant1 k, hplant2 k]
  refine le_trans (vq_add_le hα hγ β (a11 * x1 k + a12 * x2 k) (a21 * x1 k + a22 * x2 k)
    (g1 k) (g2 k)) ?_
  refine le_trans (add_le_add_both
    (add_le_add_both (hhom k) (hhom k)) (add_le_add_both (hdist k) (hdist k))) ?_
  exact le_of_eq (by mach_ring)

/-! ## Tight rate — removing the `ρ < ½` restriction via the V-norm (rate √ρ)

`quadratic_lyapunov_sublevel` pays a factor 2 (the parallelogram drop of `V(h−g)`), so it needs
`2ρ < 1`, i.e. `ρ < ½` — which excludes under-damped plants. The tight bound works in the **V-norm**
`‖x‖_V = √V(x)`: it is sub-additive (triangle inequality / Minkowski, because `V` is a PSD quadratic
form), so `‖Ax+g‖_V ≤ ‖Ax‖_V + ‖g‖_V ≤ √ρ·‖x‖_V + ‖g‖_V` — a scalar contraction at rate **`√ρ < 1`
for ANY ρ < 1**, no factor 2. This trades a real restriction (`ρ < ½`, which rules out real plants)
for an *always-true* fact (the triangle inequality, which rules out nothing).

The sqrt machinery (`sqrt_sq`, `sqrt_mul`) is proven here from MachLib's sqrt axioms. This theorem
takes the V-norm triangle inequality `htri` as a hypothesis; `quadratic_lyapunov_sublevel_tight'`
below **discharges it** (via `vq_minkowski`, whose Cauchy–Schwarz Gram identity `mach_mpoly` proves),
so the unconditional bound needs no triangle hypothesis at all. -/

/-- `√(z·z) = z` for `z ≥ 0` (from the order axioms `le_sqrt_of_sq_le` / `sqrt_le_of_le_sq`). -/
theorem sqrt_sq {z : Real} (hz : 0 ≤ z) : sqrt (z * z) = z :=
  le_antisymm (sqrt_le_of_le_sq hz (le_refl (z * z))) (le_sqrt_of_sq_le hz (le_refl (z * z)))

/-- `√(a·b) = √a·√b` for `a,b ≥ 0` (from `sqrt_sq_nonneg` + `sqrt_sq`). -/
theorem sqrt_mul {a b : Real} (ha : 0 ≤ a) (hb : 0 ≤ b) : sqrt (a * b) = sqrt a * sqrt b := by
  have hz : 0 ≤ sqrt a * sqrt b := mul_nonneg (sqrt_nonneg a) (sqrt_nonneg b)
  have hsq : (sqrt a * sqrt b) * (sqrt a * sqrt b) = a * b := by
    rw [show (sqrt a * sqrt b) * (sqrt a * sqrt b) = (sqrt a * sqrt a) * (sqrt b * sqrt b) from
          by mach_ring, sqrt_sq_nonneg a ha, sqrt_sq_nonneg b hb]
  rw [← hsq]; exact sqrt_sq hz

/-- sqrt monotone (local: the library `sqrt_mono` is in a module outside this import chain). -/
theorem sqrt_le_sqrt {a b : Real} (ha : 0 ≤ a) (hab : a ≤ b) : sqrt a ≤ sqrt b :=
  le_sqrt_of_sq_le (sqrt_nonneg a) (by rw [sqrt_sq_nonneg a ha]; exact hab)

/-- product monotone on non-negative factors (local: library `mul_le_mul'` is outside this chain). -/
theorem mul_le_mul_pair {a b c d : Real} (ha : 0 ≤ a) (hab : a ≤ b) (hc : 0 ≤ c) (hcd : c ≤ d) :
    a * c ≤ b * d :=
  le_trans (mul_le_mul_of_nonneg_right hab hc) (mul_le_mul_of_nonneg_left hcd (le_trans ha hab))

/-- **Tight coupled-oscillator safety (rate √ρ, any ρ < 1).** Same plant as
`quadratic_lyapunov_sublevel` but no `ρ < ½`: the V-norm contracts at `√ρ`. Given the homogeneous
decrease `V(Ax) ≤ ρ·V(x)`, the disturbance bound `V(g) ≤ Vg`, and the V-norm triangle inequality on
the per-step split (`htri`, true since √V is a norm — see module note), the quadratic sublevel set
`{V ≤ X²}` is forward-invariant whenever `√ρ·X + √Vg ≤ X`. -/
theorem quadratic_lyapunov_sublevel_tight
    {x1 x2 g1 g2 : Nat → Real} {a11 a12 a21 a22 α β γ ρ Vg X : Real}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hρ : 0 ≤ ρ)
    (hplant1 : ∀ k, x1 (k + 1) = (a11 * x1 k + a12 * x2 k) + g1 k)
    (hplant2 : ∀ k, x2 (k + 1) = (a21 * x1 k + a22 * x2 k) + g2 k)
    (hhom : ∀ k, Vq α β γ (a11 * x1 k + a12 * x2 k) (a21 * x1 k + a22 * x2 k)
              ≤ ρ * Vq α β γ (x1 k) (x2 k))
    (hdist : ∀ k, Vq α β γ (g1 k) (g2 k) ≤ Vg)
    (htri : ∀ k, sqrt (Vq α β γ (x1 (k + 1)) (x2 (k + 1)))
              ≤ sqrt (Vq α β γ (a11 * x1 k + a12 * x2 k) (a21 * x1 k + a22 * x2 k))
                + sqrt (Vq α β γ (g1 k) (g2 k)))
    (hinv : sqrt ρ * X + sqrt Vg ≤ X)
    (h0 : sqrt (Vq α β γ (x1 0) (x2 0)) ≤ X) :
    ∀ k, Vq α β γ (x1 k) (x2 k) ≤ X * X := by
  have hnormhom : ∀ k, sqrt (Vq α β γ (a11 * x1 k + a12 * x2 k) (a21 * x1 k + a22 * x2 k))
      ≤ sqrt ρ * sqrt (Vq α β γ (x1 k) (x2 k)) := by
    intro k
    refine le_trans (sqrt_le_sqrt (vq_nonneg hα hγ _ _ _) (hhom k)) (le_of_eq ?_)
    exact sqrt_mul hρ (vq_nonneg hα hγ _ _ _)
  have hstep : ∀ k, sqrt (Vq α β γ (x1 (k + 1)) (x2 (k + 1)))
      ≤ sqrt ρ * sqrt (Vq α β γ (x1 k) (x2 k)) + sqrt Vg := by
    intro k
    exact le_trans (htri k)
      (add_le_add_both (hnormhom k) (sqrt_le_sqrt (vq_nonneg hα hγ _ _ _) (hdist k)))
  have hm := measure_sublevel_invariant (V := fun k => sqrt (Vq α β γ (x1 k) (x2 k)))
    (sqrt_nonneg ρ) hinv h0 hstep
  intro k
  have hmk := hm k
  have key : sqrt (Vq α β γ (x1 k) (x2 k)) * sqrt (Vq α β γ (x1 k) (x2 k)) ≤ X * X :=
    mul_le_mul_pair (sqrt_nonneg _) hmk (sqrt_nonneg _) hmk
  rwa [sqrt_sq_nonneg _ (vq_nonneg hα hγ β (x1 k) (x2 k))] at key

/-! ## Discharging the triangle hypothesis: Cauchy–Schwarz via `mach_mpoly`

`mach_ring` cannot prove the Cauchy–Schwarz Gram identity (degree-4, cancellation), but MachLib's
OTHER normaliser `mach_mpoly` *can* — it is a real polynomial normaliser, not the all-`try` `mach_ring`.
So the V-norm triangle inequality is provable after all, and `quadratic_lyapunov_sublevel_tight` loses
its one hypothesis (`htri`). The lesson: for any identity needing cancellation, reach for `mach_mpoly`,
not `mach_ring`. -/

/-- Total order on `Real` (re-proved here; the library's is `private`). -/
theorem le_total_real (a b : Real) : a ≤ b ∨ b ≤ a := by
  rcases lt_total a b with h | h | h
  · exact Or.inl (le_of_lt h)
  · exact Or.inl (le_of_eq h)
  · exact Or.inr (le_of_lt h)

/-- **Cauchy–Schwarz for the diagonal form `Wq`.** `(αpq+γbc)² ≤ (αp²+γb²)(αq²+γc²)` for `α,γ ≥ 0`.
The Gram surplus `(αp²+γb²)(αq²+γc²) − B² = αγ(pc−bq)²` is a degree-4 identity `mach_mpoly` discharges
(stated additively to avoid subtraction); the surplus is `≥ 0`. -/
theorem wq_cauchy_schwarz {α γ : Real} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (p b q c : Real) :
    (α * (p * q) + γ * (b * c)) * (α * (p * q) + γ * (b * c))
      ≤ (α * (p * p) + γ * (b * b)) * (α * (q * q) + γ * (c * c)) := by
  have hgram : (α * (p * p) + γ * (b * b)) * (α * (q * q) + γ * (c * c))
      = ((α * (p * q) + γ * (b * c)) * (α * (p * q) + γ * (b * c)))
        + α * γ * ((p * c - b * q) * (p * c - b * q)) := by mach_mpoly [α, γ, p, b, q, c]
  rw [hgram]
  exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hα hγ) (mul_self_nonneg _))

/-- Cauchy–Schwarz in `√` form: `B ≤ √(Wq(p,b)·Wq(q,c))` (any sign of `B`). -/
theorem bW_le_sqrt {α γ : Real} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (p b q c : Real) :
    α * (p * q) + γ * (b * c) ≤ sqrt ((α * (p * p) + γ * (b * b)) * (α * (q * q) + γ * (c * c))) := by
  rcases le_total_real (α * (p * q) + γ * (b * c)) 0 with h | h
  · exact le_trans h (sqrt_nonneg _)
  · exact le_sqrt_of_sq_le h (wq_cauchy_schwarz hα hγ p b q c)

/-- **Minkowski (triangle inequality) for the `Wq` V-norm.** `√Wq(p+q,b+c) ≤ √Wq(p,b)+√Wq(q,c)`. -/
theorem wq_minkowski {α γ : Real} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (p b q c : Real) :
    sqrt (Wq α γ (p + q) (b + c)) ≤ sqrt (Wq α γ p b) + sqrt (Wq α γ q c) := by
  have hz : 0 ≤ sqrt (Wq α γ p b) + sqrt (Wq α γ q c) :=
    add_nonneg_ea (sqrt_nonneg _) (sqrt_nonneg _)
  apply sqrt_le_of_le_sq hz
  have hsqA : sqrt (Wq α γ p b) * sqrt (Wq α γ p b) = Wq α γ p b :=
    sqrt_sq_nonneg _ (wq_nonneg hα hγ p b)
  have hsqB : sqrt (Wq α γ q c) * sqrt (Wq α γ q c) = Wq α γ q c :=
    sqrt_sq_nonneg _ (wq_nonneg hα hγ q c)
  have hBW : α * (p * q) + γ * (b * c) ≤ sqrt (Wq α γ p b) * sqrt (Wq α γ q c) := by
    have h := bW_le_sqrt hα hγ p b q c
    rwa [show (α * (p * p) + γ * (b * b)) * (α * (q * q) + γ * (c * c))
          = Wq α γ p b * Wq α γ q c from rfl,
        sqrt_mul (wq_nonneg hα hγ p b) (wq_nonneg hα hγ q c)] at h
  have hpolar : Wq α γ (p + q) (b + c)
      = sqrt (Wq α γ p b) * sqrt (Wq α γ p b)
        + ((α * (p * q) + γ * (b * c)) + (α * (p * q) + γ * (b * c)))
        + sqrt (Wq α γ q c) * sqrt (Wq α γ q c) := by
    rw [hsqA, hsqB]; unfold Wq; mach_mpoly [α, γ, p, b, q, c]
  have hrhs : (sqrt (Wq α γ p b) + sqrt (Wq α γ q c)) * (sqrt (Wq α γ p b) + sqrt (Wq α γ q c))
      = sqrt (Wq α γ p b) * sqrt (Wq α γ p b)
        + (sqrt (Wq α γ p b) * sqrt (Wq α γ q c) + sqrt (Wq α γ p b) * sqrt (Wq α γ q c))
        + sqrt (Wq α γ q c) * sqrt (Wq α γ q c) := by
    mach_mpoly [sqrt (Wq α γ p b), sqrt (Wq α γ q c)]
  rw [hpolar, hrhs]
  exact add_le_add_both (add_le_add_both (le_refl _) (add_le_add_both hBW hBW)) (le_refl _)

/-- Minkowski lifted to the non-diagonal `Vq` (via the additive SOS coordinate). -/
theorem vq_minkowski {α γ : Real} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (β h1 h2 g1 g2 : Real) :
    sqrt (Vq α β γ (h1 + g1) (h2 + g2))
      ≤ sqrt (Vq α β γ h1 h2) + sqrt (Vq α β γ g1 g2) := by
  rw [vq_as_wq_add, vq_def, vq_def]
  exact wq_minkowski hα hγ (h1 + β * h2) h2 (g1 + β * g2) g2

/-- **The tight oscillator bound, UNCONDITIONAL.** Same as `quadratic_lyapunov_sublevel_tight` but the
V-norm triangle inequality is now PROVEN (`vq_minkowski`, via `mach_mpoly` Cauchy–Schwarz), so `htri`
is gone: given only the homogeneous decrease `V(Ax) ≤ ρ·V(x)`, the disturbance bound `V(g) ≤ Vg`, and
`√ρ·X + √Vg ≤ X`, the coupled oscillator stays in `{V ≤ X²}` — for ANY ρ < 1, no hypotheses beyond the
standard Lyapunov certificate. -/
theorem quadratic_lyapunov_sublevel_tight'
    {x1 x2 g1 g2 : Nat → Real} {a11 a12 a21 a22 α β γ ρ Vg X : Real}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hρ : 0 ≤ ρ)
    (hplant1 : ∀ k, x1 (k + 1) = (a11 * x1 k + a12 * x2 k) + g1 k)
    (hplant2 : ∀ k, x2 (k + 1) = (a21 * x1 k + a22 * x2 k) + g2 k)
    (hhom : ∀ k, Vq α β γ (a11 * x1 k + a12 * x2 k) (a21 * x1 k + a22 * x2 k)
              ≤ ρ * Vq α β γ (x1 k) (x2 k))
    (hdist : ∀ k, Vq α β γ (g1 k) (g2 k) ≤ Vg)
    (hinv : sqrt ρ * X + sqrt Vg ≤ X)
    (h0 : sqrt (Vq α β γ (x1 0) (x2 0)) ≤ X) :
    ∀ k, Vq α β γ (x1 k) (x2 k) ≤ X * X :=
  quadratic_lyapunov_sublevel_tight hα hγ hρ hplant1 hplant2 hhom hdist
    (fun k => by
      rw [hplant1 k, hplant2 k]
      exact vq_minkowski hα hγ β (a11 * x1 k + a12 * x2 k) (a21 * x1 k + a22 * x2 k) (g1 k) (g2 k))
    hinv h0

end MachLib.Real
