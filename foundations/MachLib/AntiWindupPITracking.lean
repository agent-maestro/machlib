import MachLib.ClampBetween
import MachLib.TwoStateTracking
import MachLib.Decimal

/-!
# Tracking through an anti-windup clamp — the PI loop

**What is proved.** A PI loop whose stored integrator is clamped to `[κ(−U − Kp·e), κ(U − Kp·e)]`,
with `Ki·κ = 1` so that `Kp·e + Ki·J` never leaves `[−U, U]`, tracks a perturbed copy of itself
**uniformly in time**. `antiwindup_pi_tracks_exact` bounds an eigen-functional measure of
`(x − xₑ, J − Jₑ)` by `Lⁿ·m₀ + ε·geom L n`, and `antiwindup_pi_tracks_exact_x` recovers
`w₁w₂·|x − xₑ|` from it. The per-step perturbations `dI`, `dx` are hypotheses, as in
`SignedLoopEnvelope`: the bound holds for any datapath whose per-step error fits the envelope.

**Why this clamp, and not a constant `|J| ≤ M`.** Measured before any Lean was written, with a
bit-exact model of the emitted RTL validated digit-for-digit against the Arty captures
(monogate-research harness, 2026-09-12). The loop as built has no integrator clamp and no
grid-proportional tracking bound: integrator drift grows with time spent saturated. A constant clamp
is bounded only when `M ≤ U/Ki`, and proving it would need a dwell-time argument, because while the
output is pinned and the integrator is free the error dynamics have an eigenvalue of exactly `1`.
The error-dependent clamp removes that mode. It is also the better controller: about 10 s to settle
after 100 s of windup, where the constant clamp had not settled after 20 s.

**How.** Name the closed-loop eigenvalues `λ₁ > λ₂`. The gains are then forced, as in
`SignedPILoop`: `g·Kp = 1 − g − λ₁λ₂` and `g·Ki·h = (1 − λ₁)(1 − λ₂)`. A clamped step lies
*between* two linear steps (`clamp_sub_between_shift`):

* **free vertex** — both integrators free: the PI matrix, contracted by its left eigenvectors
  `(λᵢ − 1, g·Ki)` at rate `max |λᵢ|` (`m2_contract_of_eigen`);
* **clamped vertex** — both on their bounds: `δJ = κ·Kp·δx`, `δu = 0`, state row `1 − g`. The same
  functionals send it to `κᵢ·δx`, where `κᵢ = (1 − g)·λᵢ − λ₁λ₂` and `κ₁ − κ₂ = (1 − g)(λ₁ − λ₂)`.

Weighting the functionals by `w₁ = −κ₂`, `w₂ = κ₁` balances them, and the clamped vertex then
contracts at exactly `1 − g`. Both weights are nonnegative iff `λ₂ ≤ 1 − g ≤ λ₁`, i.e. the plant
pole lies between the closed-loop eigenvalues (equivalently `Ki·h·(1 − g) ≤ g·Kp`), which the silicon
gains satisfy. A measure of an affine path is at most its value at an endpoint
(`m2_affine_between`), so each step contracts at any `L ≥ max(|λ₁|, |λ₂|, 1 − g)`. Every eigen
relation is a ring identity: the certificate uses no decimals and no square roots.

**Checked before it was proved.** Every identity symbolically. The per-step inequality over 1.6 M
noise-free steps with large initial gaps: no violations, while controls at rate `λ₂`, at rate `1 − g`,
and with a componentwise measure all fired. Then a saturation-heavy run, where an equal-weights
control fired only in the clamped mode.

**Not claimed.** No Q-grid instantiation: the `dI`, `dx` envelope is assumed, not derived from bits.
No derivative term, no complex eigenvalues, nothing about the constant clamp, and nothing about the
loop as built, which has no integrator clamp. `antiwindup_pi_specimen` instantiates the whole
statement at concrete gains, so its hypotheses are satisfiable and its measure is non-degenerate.
-/

namespace MachLib

namespace Real

/-! ### The measure along an affine path -/

theorem m2_affine_lin (a b c1 e1 c2 e2 z : Real) :
    a * (c1 + e1 * z) + b * (c2 + e2 * z) = (a * c1 + b * c2) + (a * e1 + b * e2) * z := by
  mach_mpoly [a, b, c1, e1, c2, e2, z]

/-- **The measure of an affine path is at most its value at one of the endpoints.** -/
theorem m2_affine_between (p q r s c1 e1 c2 e2 t s1 s2 : Real)
    (h : (s1 ≤ t ∧ t ≤ s2) ∨ (s2 ≤ t ∧ t ≤ s1)) :
    m2 p q r s (c1 + e1 * t) (c2 + e2 * t)
      ≤ max (m2 p q r s (c1 + e1 * s1) (c2 + e2 * s1))
            (m2 p q r s (c1 + e1 * s2) (c2 + e2 * s2)) := by
  unfold m2
  rw [m2_affine_lin p q c1 e1 c2 e2 t, m2_affine_lin r s c1 e1 c2 e2 t,
      m2_affine_lin p q c1 e1 c2 e2 s1, m2_affine_lin r s c1 e1 c2 e2 s1,
      m2_affine_lin p q c1 e1 c2 e2 s2, m2_affine_lin r s c1 e1 c2 e2 s2]
  apply max_le
  · refine le_trans (abs_between_le_max (affine_between _ _ t s1 s2 h)) ?_
    exact max_le (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_trans (le_max_left _ _) (le_max_right _ _))
  · refine le_trans (abs_between_le_max (affine_between _ _ t s1 s2 h)) ?_
    exact max_le (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_trans (le_max_right _ _) (le_max_right _ _))

/-! ### The free vertex -/

theorem antiwindup_free_eig_u {g Kp Ki h l1 l2 : Real}
    (hkp : g * Kp = 1 - g - l1 * l2) (hki : g * Ki * h = (1 - l1) * (1 - l2))
    (w l : Real) (hl : l = l1 ∨ l = l2) :
    w * (l - 1) * (1 - g - g * Kp - g * Ki * h) + w * (g * Ki) * (-h) = l * (w * (l - 1)) := by
  have e1 : w * (l - 1) * (1 - g - g * Kp - g * Ki * h) + w * (g * Ki) * (-h)
      = w * ((l - 1) * (1 - g - (g * Kp) - (g * Ki * h)) - (g * Ki * h)) := by
    mach_mpoly [w, l, g, Kp, Ki, h]
  rw [e1, hkp, hki]
  rcases hl with hl | hl
  · rw [hl]; mach_mpoly [w, l1, l2, g]
  · rw [hl]; mach_mpoly [w, l1, l2, g]

theorem antiwindup_free_eig_v (w l g Ki : Real) :
    w * (l - 1) * (g * Ki) + w * (g * Ki) * 1 = l * (w * (g * Ki)) := by
  mach_mpoly [w, l, g, Ki]

/-- **Free vertex: the weighted eigen-functional measure contracts at `L ≥ |λ₁|, |λ₂|`.** -/
theorem antiwindup_free_vertex (g Kp Ki h l1 l2 w1 w2 L u v : Real)
    (hkp : g * Kp = 1 - g - l1 * l2) (hki : g * Ki * h = (1 - l1) * (1 - l2))
    (hL1 : abs l1 ≤ L) (hL2 : abs l2 ≤ L) :
    m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki))
        ((1 - g - g * Kp - g * Ki * h) * u + (g * Ki) * v) ((-h) * u + 1 * v)
      ≤ L * m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki)) u v :=
  m2_contract_of_eigen
    (antiwindup_free_eig_u hkp hki w1 l1 (Or.inl rfl)) (antiwindup_free_eig_v w1 l1 g Ki)
    (antiwindup_free_eig_u hkp hki w2 l2 (Or.inr rfl)) (antiwindup_free_eig_v w2 l2 g Ki)
    hL1 hL2 u v

/-! ### The clamped vertex -/

private theorem antiwindup_cancel_left {a b c : Real} (hc : 0 < c) (h : c * a ≤ c * b) :
    a ≤ b := by
  rcases lt_total b a with hlt | heq | hgt
  · exfalso
    have h1 : b * c < a * c := mul_lt_mul_of_pos_right hlt hc
    have e1 : c * a = a * c := by mach_mpoly [a, c]
    have e2 : c * b = b * c := by mach_mpoly [b, c]
    rw [e1, e2] at h
    exact lt_irrefl_ax (b * c) (lt_of_lt_of_le h1 h)
  · rw [heq]
    exact le_refl a
  · exact le_of_lt hgt

theorem antiwindup_factor (w1 w2 M c k : Real) (hsum : w2 + w1 = c * k) :
    w2 * M + w1 * M = c * (k * M) := by
  have e : w2 * M + w1 * M = (w2 + w1) * M := by mach_mpoly [w1, w2, M]
  rw [e, hsum]
  mach_mpoly [c, k, M]

/-- Two weighted functionals whose weighted difference is `c·z`, `c > 0`, control `|z|`. -/
theorem antiwindup_weighted_diff (w1 w2 F1 F2 c k z : Real) (hw1n : 0 ≤ w1) (hw2n : 0 ≤ w2)
    (hc : 0 < c) (hT : w2 * F1 - w1 * F2 = c * z) (hsum : w2 + w1 = c * k) :
    abs z ≤ k * max (abs F1) (abs F2) := by
  have h1 : abs (w2 * F1) ≤ w2 * max (abs F1) (abs F2) := by
    rw [abs_mul, abs_of_nonneg hw2n]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hw2n
  have h2 : abs (w1 * F2) ≤ w1 * max (abs F1) (abs F2) := by
    rw [abs_mul, abs_of_nonneg hw1n]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hw1n
  have h3 : abs (w2 * F1 - w1 * F2) ≤ abs (w2 * F1) + abs (w1 * F2) := by
    have e : w2 * F1 - w1 * F2 = w2 * F1 + -(w1 * F2) := by mach_mpoly [w1, w2, F1, F2]
    rw [e]
    have t := abs_add (w2 * F1) (-(w1 * F2))
    rw [abs_neg] at t
    exact t
  rw [hT, abs_mul, abs_of_nonneg (le_of_lt hc)] at h3
  have h4 : c * abs z ≤ c * (k * max (abs F1) (abs F2)) := by
    refine le_trans h3 (le_trans (add_le_add_both h1 h2) ?_)
    exact le_of_eq (antiwindup_factor w1 w2 (max (abs F1) (abs F2)) c k hsum)
  exact antiwindup_cancel_left hc h4

/-- **`w₁·w₂·|δx|` is controlled by the measure.** The norm-recovery half of the clamped vertex. -/
theorem antiwindup_x_le_m2 (g Ki l1 l2 w1 w2 u v : Real)
    (hw1 : w1 = l2 * (l1 - (1 - g))) (hw2 : w2 = l1 * ((1 - g) - l2))
    (hw1n : 0 ≤ w1) (hw2n : 0 ≤ w2) (hgap : l2 < l1) :
    abs (w1 * w2 * u)
      ≤ (1 - g) * m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki)) u v := by
  unfold m2
  refine antiwindup_weighted_diff w1 w2 _ _ (l1 - l2) (1 - g) (w1 * w2 * u) hw1n hw2n
    (sub_pos_of_lt hgap) ?_ ?_
  · mach_mpoly [w1, w2, l1, l2, g, Ki, u, v]
  · rw [hw1, hw2]
    mach_mpoly [l1, l2, g]

/-- **Clamped vertex: both integrators on their bounds, the measure contracts at `1 − g`.** -/
theorem antiwindup_clamped_vertex (g Kp Ki κ l1 l2 w1 w2 u v : Real)
    (hkp : g * Kp = 1 - g - l1 * l2) (hkap : Ki * κ = 1)
    (hw1 : w1 = l2 * (l1 - (1 - g))) (hw2 : w2 = l1 * ((1 - g) - l2))
    (hw1n : 0 ≤ w1) (hw2n : 0 ≤ w2) (hgap : l2 < l1) :
    m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki))
        ((1 - g) * u) ((κ * Kp) * u)
      ≤ (1 - g) * m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki)) u v := by
  have hgk : g * Ki * (κ * Kp) = g * Kp := by
    calc g * Ki * (κ * Kp) = (Ki * κ) * (g * Kp) := by mach_mpoly [g, Ki, κ, Kp]
      _ = 1 * (g * Kp) := by rw [hkap]
      _ = g * Kp := by mach_mpoly [g, Kp]
  have f1 : w1 * (l1 - 1) * ((1 - g) * u) + w1 * (g * Ki) * ((κ * Kp) * u) = w1 * w2 * u := by
    calc w1 * (l1 - 1) * ((1 - g) * u) + w1 * (g * Ki) * ((κ * Kp) * u)
        = w1 * (l1 - 1) * ((1 - g) * u) + w1 * (g * Ki * (κ * Kp)) * u := by
          mach_mpoly [w1, l1, g, Ki, κ, Kp, u]
      _ = w1 * (l1 - 1) * ((1 - g) * u) + w1 * (g * Kp) * u := by rw [hgk]
      _ = w1 * (l1 - 1) * ((1 - g) * u) + w1 * (1 - g - l1 * l2) * u := by rw [hkp]
      _ = w1 * w2 * u := by rw [hw2]; mach_mpoly [w1, l1, l2, g, u]
  have f2 : w2 * (l2 - 1) * ((1 - g) * u) + w2 * (g * Ki) * ((κ * Kp) * u) = -(w1 * w2 * u) := by
    calc w2 * (l2 - 1) * ((1 - g) * u) + w2 * (g * Ki) * ((κ * Kp) * u)
        = w2 * (l2 - 1) * ((1 - g) * u) + w2 * (g * Ki * (κ * Kp)) * u := by
          mach_mpoly [w2, l2, g, Ki, κ, Kp, u]
      _ = w2 * (l2 - 1) * ((1 - g) * u) + w2 * (g * Kp) * u := by rw [hgk]
      _ = w2 * (l2 - 1) * ((1 - g) * u) + w2 * (1 - g - l1 * l2) * u := by rw [hkp]
      _ = -(w1 * w2 * u) := by rw [hw1]; mach_mpoly [w2, l1, l2, g, u]
  have hx := antiwindup_x_le_m2 g Ki l1 l2 w1 w2 u v hw1 hw2 hw1n hw2n hgap
  unfold m2 at hx ⊢
  rw [f1, f2, abs_neg, max_self]
  exact hx

/-! ### One step, and the trajectory -/

/-- **One step of both loops.** The computed loop carries a perturbation `dI` on the stored
integrator and `dx` on the state; `c`, `ce` name the two clamps. -/
theorem antiwindup_pi_step (g Kp Ki κ h U l1 l2 w1 w2 L : Real)
    (hkp : g * Kp = 1 - g - l1 * l2) (hki : g * Ki * h = (1 - l1) * (1 - l2)) (hkap : Ki * κ = 1)
    (hw1 : w1 = l2 * (l1 - (1 - g))) (hw2 : w2 = l1 * ((1 - g) - l2))
    (hw1n : 0 ≤ w1) (hw2n : 0 ≤ w2) (hgap : l2 < l1)
    (hL1 : abs l1 ≤ L) (hL2 : abs l2 ≤ L) (hLg : 1 - g ≤ L)
    (s x xe J Je dI dx c ce : Real)
    (hc : c = clamp (J + h * (s - x)) (κ * (-U - Kp * (s - x))) (κ * (U - Kp * (s - x))))
    (hce : ce = clamp (Je + h * (s - xe)) (κ * (-U - Kp * (s - xe))) (κ * (U - Kp * (s - xe)))) :
    m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki))
        ((x + g * (Kp * (s - x) + Ki * (c + dI) - x) + dx) - (xe + g * (Kp * (s - xe) + Ki * ce - xe)))
        ((c + dI) - ce)
      ≤ L * m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki)) (x - xe) (J - Je)
        + m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki)) (g * Ki * dI + dx) dI := by
  have hlo : κ * (-U - Kp * (s - x)) = κ * (-U - Kp * (s - xe)) + κ * Kp * (x - xe) := by
    mach_mpoly [κ, U, Kp, s, x, xe]
  have hhi : κ * (U - Kp * (s - x)) = κ * (U - Kp * (s - xe)) + κ * Kp * (x - xe) := by
    mach_mpoly [κ, U, Kp, s, x, xe]
  have hbet := clamp_sub_between_shift (J + h * (s - x)) (Je + h * (s - xe)) _ _ _ _
    (κ * Kp * (x - xe)) hlo hhi
  rw [← hc, ← hce] at hbet
  have hA : (J + h * (s - x)) - (Je + h * (s - xe)) = (J - Je) + (-h) * (x - xe) := by
    mach_mpoly [J, Je, h, s, x, xe]
  rw [hA] at hbet
  have hX : (x + g * (Kp * (s - x) + Ki * (c + dI) - x) + dx) - (xe + g * (Kp * (s - xe) + Ki * ce - xe))
      = ((1 - g - g * Kp) * (x - xe) + (g * Ki * dI + dx)) + (g * Ki) * (c - ce) := by
    mach_mpoly [g, Kp, Ki, s, x, xe, c, ce, dI, dx]
  have hJ : (c + dI) - ce = dI + 1 * (c - ce) := by mach_mpoly [c, ce, dI]
  rw [hX, hJ]
  refine le_trans (m2_affine_between _ _ _ _ _ _ _ _ (c - ce) _ _ hbet) ?_
  apply max_le
  · have e1 : ((1 - g - g * Kp) * (x - xe) + (g * Ki * dI + dx)) + (g * Ki) * ((J - Je) + (-h) * (x - xe))
        = ((1 - g - g * Kp - g * Ki * h) * (x - xe) + (g * Ki) * (J - Je)) + (g * Ki * dI + dx) := by
      mach_mpoly [g, Kp, Ki, h, x, xe, J, Je, dI, dx]
    have e2 : dI + 1 * ((J - Je) + (-h) * (x - xe)) = ((-h) * (x - xe) + 1 * (J - Je)) + dI := by
      mach_mpoly [dI, J, Je, h, x, xe]
    rw [e1, e2]
    refine le_trans (m2_subadd _ _ _ _ _ _ _ _) ?_
    exact add_le_add_both
      (antiwindup_free_vertex g Kp Ki h l1 l2 w1 w2 L (x - xe) (J - Je) hkp hki hL1 hL2) (le_refl _)
  · have hgk : g * Ki * (κ * Kp * (x - xe)) = g * Kp * (x - xe) := by
      calc g * Ki * (κ * Kp * (x - xe)) = (Ki * κ) * (g * Kp * (x - xe)) := by
            mach_mpoly [g, Ki, κ, Kp, x, xe]
        _ = 1 * (g * Kp * (x - xe)) := by rw [hkap]
        _ = g * Kp * (x - xe) := by mach_mpoly [g, Kp, x, xe]
    have e1 : ((1 - g - g * Kp) * (x - xe) + (g * Ki * dI + dx)) + (g * Ki) * (κ * Kp * (x - xe))
        = (1 - g) * (x - xe) + (g * Ki * dI + dx) := by
      calc ((1 - g - g * Kp) * (x - xe) + (g * Ki * dI + dx)) + (g * Ki) * (κ * Kp * (x - xe))
          = ((1 - g - g * Kp) * (x - xe) + (g * Ki * dI + dx)) + g * Ki * (κ * Kp * (x - xe)) := by
            mach_mpoly [g, Kp, Ki, κ, x, xe, dI, dx]
        _ = ((1 - g - g * Kp) * (x - xe) + (g * Ki * dI + dx)) + g * Kp * (x - xe) := by rw [hgk]
        _ = (1 - g) * (x - xe) + (g * Ki * dI + dx) := by mach_mpoly [g, Kp, Ki, x, xe, dI, dx]
    have e2 : dI + 1 * (κ * Kp * (x - xe)) = (κ * Kp) * (x - xe) + dI := by
      mach_mpoly [dI, κ, Kp, x, xe]
    rw [e1, e2]
    refine le_trans (m2_subadd _ _ _ _ _ _ _ _) ?_
    refine add_le_add_both ?_ (le_refl _)
    refine le_trans (antiwindup_clamped_vertex g Kp Ki κ l1 l2 w1 w2 (x - xe) (J - Je)
      hkp hkap hw1 hw2 hw1n hw2n hgap) ?_
    exact mul_le_mul_of_nonneg_right hLg (m2_nonneg _ _ _ _ _ _)

/-- **The trajectory: the perturbed anti-windup PI loop tracks the exact one, uniformly in time.** -/
theorem antiwindup_pi_tracks_exact {g Kp Ki κ h U l1 l2 w1 w2 L ε : Real}
    {sp x xe J Je dI dx : Nat → Real}
    (hkp : g * Kp = 1 - g - l1 * l2) (hki : g * Ki * h = (1 - l1) * (1 - l2)) (hkap : Ki * κ = 1)
    (hw1 : w1 = l2 * (l1 - (1 - g))) (hw2 : w2 = l1 * ((1 - g) - l2))
    (hw1n : 0 ≤ w1) (hw2n : 0 ≤ w2) (hgap : l2 < l1)
    (hL1 : abs l1 ≤ L) (hL2 : abs l2 ≤ L) (hLg : 1 - g ≤ L) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hexJ : ∀ k, Je (k + 1) = clamp (Je k + h * (sp k - xe k))
        (κ * (-U - Kp * (sp k - xe k))) (κ * (U - Kp * (sp k - xe k))))
    (hexX : ∀ k, xe (k + 1) = xe k + g * (Kp * (sp k - xe k) + Ki * Je (k + 1) - xe k))
    (hcJ : ∀ k, J (k + 1) = clamp (J k + h * (sp k - x k))
        (κ * (-U - Kp * (sp k - x k))) (κ * (U - Kp * (sp k - x k))) + dI k)
    (hcX : ∀ k, x (k + 1) = x k + g * (Kp * (sp k - x k) + Ki * J (k + 1) - x k) + dx k)
    (hpert : ∀ k, m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki))
        (g * Ki * dI k + dx k) (dI k) ≤ ε)
    (n : Nat) :
    m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki)) (x n - xe n) (J n - Je n)
      ≤ npow n L * m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki))
            (x 0 - xe 0) (J 0 - Je 0)
        + ε * geom L n := by
  refine iterate_affine_bound
    (fun k => m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki))
      (x k - xe k) (J k - Je k)) hL hε ?_ n
  intro k
  show m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki))
      (x (k + 1) - xe (k + 1)) (J (k + 1) - Je (k + 1))
    ≤ L * m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki))
      (x k - xe k) (J k - Je k) + ε
  rw [hcX k, hexX k, hcJ k, hexJ k]
  refine le_trans (antiwindup_pi_step g Kp Ki κ h U l1 l2 w1 w2 L hkp hki hkap hw1 hw2 hw1n hw2n
    hgap hL1 hL2 hLg (sp k) (x k) (xe k) (J k) (Je k) (dI k) (dx k) _ _ rfl rfl) ?_
  exact add_le_add_both (le_refl _) (hpert k)

/-- **The plant state itself:** `w₁·w₂·|x − xₑ|` inherits the same uniform bound. -/
theorem antiwindup_pi_tracks_exact_x {g Kp Ki κ h U l1 l2 w1 w2 L ε : Real}
    {sp x xe J Je dI dx : Nat → Real}
    (hkp : g * Kp = 1 - g - l1 * l2) (hki : g * Ki * h = (1 - l1) * (1 - l2)) (hkap : Ki * κ = 1)
    (hw1 : w1 = l2 * (l1 - (1 - g))) (hw2 : w2 = l1 * ((1 - g) - l2))
    (hw1n : 0 ≤ w1) (hw2n : 0 ≤ w2) (hgap : l2 < l1)
    (hL1 : abs l1 ≤ L) (hL2 : abs l2 ≤ L) (hLg : 1 - g ≤ L) (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hg1 : 0 ≤ 1 - g)
    (hexJ : ∀ k, Je (k + 1) = clamp (Je k + h * (sp k - xe k))
        (κ * (-U - Kp * (sp k - xe k))) (κ * (U - Kp * (sp k - xe k))))
    (hexX : ∀ k, xe (k + 1) = xe k + g * (Kp * (sp k - xe k) + Ki * Je (k + 1) - xe k))
    (hcJ : ∀ k, J (k + 1) = clamp (J k + h * (sp k - x k))
        (κ * (-U - Kp * (sp k - x k))) (κ * (U - Kp * (sp k - x k))) + dI k)
    (hcX : ∀ k, x (k + 1) = x k + g * (Kp * (sp k - x k) + Ki * J (k + 1) - x k) + dx k)
    (hpert : ∀ k, m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki))
        (g * Ki * dI k + dx k) (dI k) ≤ ε)
    (n : Nat) :
    abs (w1 * w2 * (x n - xe n))
      ≤ (1 - g) * (npow n L * m2 (w1 * (l1 - 1)) (w1 * (g * Ki)) (w2 * (l2 - 1)) (w2 * (g * Ki))
            (x 0 - xe 0) (J 0 - Je 0) + ε * geom L n) :=
  le_trans (antiwindup_x_le_m2 g Ki l1 l2 w1 w2 (x n - xe n) (J n - Je n) hw1 hw2 hw1n hw2n hgap)
    (mul_le_mul_of_nonneg_left
      (antiwindup_pi_tracks_exact hkp hki hkap hw1 hw2 hw1n hw2n hgap hL1 hL2 hLg hL hε
        hexJ hexX hcJ hcX hpert n) hg1)

/-! ### The control law stays in the band

The integrator clamp is chosen so that `Kp·e + Ki·J'` can never leave `[−U, U]`. So a kernel may
carry a defensive output clamp — to absorb fixed-point overshoot — and still be exactly the loop
`antiwindup_pi_tracks_exact` is about: in exact arithmetic that clamp never acts. This is what a
compiled controller's step is joined to the loop through. -/

/-- **The unclamped control law never leaves the band.** -/
theorem antiwindup_control_in_band (Kp Ki κ U e J : Real)
    (hkap : Ki * κ = 1) (hKi : 0 ≤ Ki) (hκ : 0 ≤ κ) (hU : 0 ≤ U) :
    -U ≤ Kp * e + Ki * clamp J (κ * (-U - Kp * e)) (κ * (U - Kp * e)) ∧
    Kp * e + Ki * clamp J (κ * (-U - Kp * e)) (κ * (U - Kp * e)) ≤ U := by
  have hUU : -U ≤ U := by
    have h0 : 0 + 0 ≤ U + U := add_le_add_both hU hU
    rw [zero_add] at h0
    have h1 := add_le_add_both h0 (le_refl (-U))
    rw [zero_add] at h1
    have e1 : (U + U) + -U = U := by mach_mpoly [U]
    rw [e1] at h1
    exact h1
  have hlohi : κ * (-U - Kp * e) ≤ κ * (U - Kp * e) :=
    mul_le_mul_of_nonneg_left (sub_le_sub_right hUU (Kp * e)) hκ
  have hlo := lo_le_clamp J (κ * (-U - Kp * e)) (κ * (U - Kp * e)) hlohi
  have hhi := clamp_le_hi J (κ * (-U - Kp * e)) (κ * (U - Kp * e))
  have elo : Ki * (κ * (-U - Kp * e)) = -U - Kp * e := by
    calc Ki * (κ * (-U - Kp * e)) = (Ki * κ) * (-U - Kp * e) := by mach_mpoly [Ki, κ, U, Kp, e]
      _ = 1 * (-U - Kp * e) := by rw [hkap]
      _ = -U - Kp * e := by mach_mpoly [U, Kp, e]
  have ehi : Ki * (κ * (U - Kp * e)) = U - Kp * e := by
    calc Ki * (κ * (U - Kp * e)) = (Ki * κ) * (U - Kp * e) := by mach_mpoly [Ki, κ, U, Kp, e]
      _ = 1 * (U - Kp * e) := by rw [hkap]
      _ = U - Kp * e := by mach_mpoly [U, Kp, e]
  have ml := mul_le_mul_of_nonneg_left hlo hKi
  have mh := mul_le_mul_of_nonneg_left hhi hKi
  rw [elo] at ml
  rw [ehi] at mh
  have eL : Kp * e + (-U - Kp * e) = -U := by mach_mpoly [Kp, e, U]
  have eH : Kp * e + (U - Kp * e) = U := by mach_mpoly [Kp, e, U]
  constructor
  · have t := add_le_add_both (le_refl (Kp * e)) ml
    rw [eL] at t
    exact t
  · have t := add_le_add_both (le_refl (Kp * e)) mh
    rw [eH] at t
    exact t

/-- **An output clamp downstream of the anti-windup law is inactive in exact arithmetic.** -/
theorem antiwindup_output_clamp_inactive (Kp Ki κ U e J : Real)
    (hkap : Ki * κ = 1) (hKi : 0 ≤ Ki) (hκ : 0 ≤ κ) (hU : 0 ≤ U) :
    clamp (Kp * e + Ki * clamp J (κ * (-U - Kp * e)) (κ * (U - Kp * e))) (-U) U
      = Kp * e + Ki * clamp J (κ * (-U - Kp * e)) (κ * (U - Kp * e)) :=
  clamp_eq_self (antiwindup_control_in_band Kp Ki κ U e J hkap hKi hκ hU).1
    (antiwindup_control_in_band Kp Ki κ U e J hkap hKi hκ hU).2

/-! ### The specimen — the hypotheses are satisfiable and the measure is a norm

Recorded failure mode of this corpus: a capstone whose hypotheses nothing satisfies, true vacuously
while every gate passes. So the loops are DEFINED here, the recurrence hypotheses hold by `rfl`, and
the gain hypotheses are discharged at concrete numbers: `g = 0.25`, `Kp = 1.25`, `Ki = 0.25`,
`κ = 4.0`, `h = 1`, closed-loop eigenvalues `λ₁ = 0.875`, `λ₂ = 0.5`. The plant pole `0.75` lies
strictly between them, so both weights are strictly positive (`0.0625`, `0.21875`) and the measure is
a norm, not the degenerate seminorm a deadbeat specimen would give (`m3_vacuous_at_deadbeat`). -/

/-- The exact anti-windup PI loop, `(x, J)` over time. -/
noncomputable def antiwindupPI (g Kp Ki κ h U : Real) (sp : Nat → Real) (x0 J0 : Real) :
    Nat → Real × Real
  | 0 => (x0, J0)
  | k + 1 =>
      let st := antiwindupPI g Kp Ki κ h U sp x0 J0 k
      let Jn := clamp (st.2 + h * (sp k - st.1))
        (κ * (-U - Kp * (sp k - st.1))) (κ * (U - Kp * (sp k - st.1)))
      (st.1 + g * (Kp * (sp k - st.1) + Ki * Jn - st.1), Jn)

/-- The same loop with a per-step perturbation on the stored integrator and on the state. -/
noncomputable def antiwindupPIPert (g Kp Ki κ h U : Real) (sp dI dx : Nat → Real) (x0 J0 : Real) :
    Nat → Real × Real
  | 0 => (x0, J0)
  | k + 1 =>
      let st := antiwindupPIPert g Kp Ki κ h U sp dI dx x0 J0 k
      let Jn := clamp (st.2 + h * (sp k - st.1))
        (κ * (-U - Kp * (sp k - st.1))) (κ * (U - Kp * (sp k - st.1))) + dI k
      (st.1 + g * (Kp * (sp k - st.1) + Ki * Jn - st.1) + dx k, Jn)

/-- `mach_decimal` adds and multiplies decimal literals but does not subtract one from another, so a
subtraction is proved from the addition it inverts. -/
theorem antiwindup_sub_eq_of_add_eq {a b c : Real} (h : c + b = a) : a - b = c := by
  rw [← h]
  mach_mpoly [c, b]

theorem antiwindup_specimen_gains :
    (0.25 : Real) * 1.25 = 1 - 0.25 - 0.875 * 0.5 ∧
    (0.25 : Real) * 0.25 * 1 = (1 - 0.875) * (1 - 0.5) ∧
    (0.25 : Real) * 4.0 = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · have a1 : (0.25 : Real) * 1.25 = 0.3125 := by mach_decimal
    have a2 : (0.875 : Real) * 0.5 = 0.4375 := by mach_decimal
    have a3 : (1 : Real) - 0.25 = 0.7500 := by mach_decimal
    have a4 : (0.7500 : Real) - 0.4375 = 0.3125 := antiwindup_sub_eq_of_add_eq (by mach_decimal)
    rw [a1, a2, a3, a4]
  · mach_decimal
  · mach_decimal_ofnat

theorem antiwindup_specimen_weights :
    0 < (0.5 : Real) * (0.875 - (1 - 0.25)) ∧ 0 < (0.875 : Real) * ((1 - 0.25) - 0.5) := by
  have b1 : (1 : Real) - 0.25 = 0.750 := by mach_decimal
  have b2 : (0.875 : Real) - 0.750 = 0.125 := antiwindup_sub_eq_of_add_eq (by mach_decimal)
  have b3 : (0.5 : Real) * 0.125 = 0.0625 := by mach_decimal
  have b45 : (0.5 : Real) = 0.500 := by mach_decimal
  have b4 : (0.750 : Real) - 0.500 = 0.250 := antiwindup_sub_eq_of_add_eq (by mach_decimal)
  have b5 : (0.875 : Real) * 0.250 = 0.21875 := by mach_decimal
  rw [b1, b2, b3, b45, b4, b5]
  exact ⟨by mach_decimal, by mach_decimal⟩

/-- **The specimen.** At the concrete gains, the loop run with no perturbation tracks itself from
any two starting points, for any setpoint sequence, with rate `0.875`. -/
theorem antiwindup_pi_specimen (sp : Nat → Real) (x0 J0 x0' J0' : Real) (n : Nat) :
    m2 ((0.5 : Real) * (0.875 - (1 - 0.25)) * (0.875 - 1))
       ((0.5 : Real) * (0.875 - (1 - 0.25)) * (0.25 * 0.25))
       ((0.875 : Real) * ((1 - 0.25) - 0.5) * (0.5 - 1))
       ((0.875 : Real) * ((1 - 0.25) - 0.5) * (0.25 * 0.25))
       ((antiwindupPIPert 0.25 1.25 0.25 4.0 1 1 sp (fun _ => 0) (fun _ => 0) x0' J0' n).1
          - (antiwindupPI 0.25 1.25 0.25 4.0 1 1 sp x0 J0 n).1)
       ((antiwindupPIPert 0.25 1.25 0.25 4.0 1 1 sp (fun _ => 0) (fun _ => 0) x0' J0' n).2
          - (antiwindupPI 0.25 1.25 0.25 4.0 1 1 sp x0 J0 n).2)
      ≤ npow n 0.875 * m2 ((0.5 : Real) * (0.875 - (1 - 0.25)) * (0.875 - 1))
          ((0.5 : Real) * (0.875 - (1 - 0.25)) * (0.25 * 0.25))
          ((0.875 : Real) * ((1 - 0.25) - 0.5) * (0.5 - 1))
          ((0.875 : Real) * ((1 - 0.25) - 0.5) * (0.25 * 0.25))
          (x0' - x0) (J0' - J0)
        + 0 * geom 0.875 n := by
  obtain ⟨hkp, hki, hkap⟩ := antiwindup_specimen_gains
  obtain ⟨hw1p, hw2p⟩ := antiwindup_specimen_weights
  have h875 : (0 : Real) < 0.875 := by mach_decimal
  have h5 : (0 : Real) < 0.5 := by mach_decimal
  have hgap : (0.5 : Real) < 0.875 := by mach_decimal
  have hLg : (1 : Real) - 0.25 ≤ 0.875 := by mach_decimal
  have hL1 : abs (0.875 : Real) ≤ 0.875 := by
    rw [abs_of_nonneg (le_of_lt h875)]
    exact le_refl _
  have hL2 : abs (0.5 : Real) ≤ 0.875 := by
    rw [abs_of_nonneg (le_of_lt h5)]
    exact le_of_lt hgap
  refine antiwindup_pi_tracks_exact (U := 1) (κ := 4.0) (h := 1)
    (x := fun k => (antiwindupPIPert 0.25 1.25 0.25 4.0 1 1 sp (fun _ => 0) (fun _ => 0) x0' J0' k).1)
    (xe := fun k => (antiwindupPI 0.25 1.25 0.25 4.0 1 1 sp x0 J0 k).1)
    (J := fun k => (antiwindupPIPert 0.25 1.25 0.25 4.0 1 1 sp (fun _ => 0) (fun _ => 0) x0' J0' k).2)
    (Je := fun k => (antiwindupPI 0.25 1.25 0.25 4.0 1 1 sp x0 J0 k).2)
    (dI := fun _ => 0) (dx := fun _ => 0)
    hkp hki hkap rfl rfl (le_of_lt hw1p) (le_of_lt hw2p) hgap hL1 hL2 hLg (le_of_lt h875) (le_refl 0)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ?_ n
  intro k
  show m2 _ _ _ _ (0.25 * 0.25 * 0 + 0) 0 ≤ 0
  rw [mul_zero, add_zero]
  unfold m2
  rw [mul_zero, mul_zero, add_zero, mul_zero, mul_zero, add_zero, abs_zero, max_self]
  exact le_refl 0

/-- **The specimen's measure is a norm:** both weights are strictly positive and `λ₁ ≠ λ₂`, so the
`|x − xₑ|` bound of `antiwindup_pi_tracks_exact_x` carries a strictly positive coefficient. -/
theorem antiwindup_specimen_nondegenerate :
    0 < (0.5 : Real) * (0.875 - (1 - 0.25)) * ((0.875 : Real) * ((1 - 0.25) - 0.5)) :=
  mul_pos antiwindup_specimen_weights.1 antiwindup_specimen_weights.2

end Real

end MachLib
