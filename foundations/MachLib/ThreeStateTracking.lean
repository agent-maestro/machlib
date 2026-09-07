import MachLib.TwoStateTracking

/-!
# Tracking a three-state loop — the derivative term

**A correction, recorded because the estimate was mine and it was wrong.** When the two-state case
was finished, `what_is_proven.md` and this project's notes said the derivative term "will not come
free the way the last two did — the 2×2 eigenstructure was forced by the integrator row `[−1,1]`,
and a 3×3's is not, so the functionals will have to be constructed rather than read off."

**It is forced, and it is free.** A PID loop over `(x, i, xₚ)` has *two* structural rows, not one:
the integrator `i' = −x + i + r` and the delay `xₚ' = x`. Between them they pin the left
eigenvectors exactly as the single integrator row did one dimension down. For the closed-loop
matrix

```
M = [ A  B  C ]        A = a − Kp − Kd,  B = Ki,  C = Kd
    [ −1 1  0 ]        (integrator)
    [  1 0  0 ]        (delay)
```

the left eigenvector for `λ` is `(λ(λ−1), λ·B, (λ−1)·C)` — and with the gains written through the
characteristic equation,

```
A = e₁ − 1,   B = e₂ − e₁ + 1 − e₃,   C = −e₃
```

(`eᵢ` the elementary symmetric functions of `λ₁, λ₂, λ₃`) **all nine relations are ring identities
in the eigenvalues**. Two of the three columns are identities outright, for any gains; the third
is the characteristic polynomial, which is the factorisation identity
`λᵢ³ − e₁λᵢ² + e₂λᵢ − e₃ = (λᵢ−λ₁)(λᵢ−λ₂)(λᵢ−λ₃) = 0`.

So the same structure that made the PI case free makes the PID case free, and the prediction that
it would not was a guess made from the shape of the problem rather than from the algebra. Checking
it cost one command.

**Scope.** Three *real* eigenvalues. A design with one real eigenvalue and a complex pair needs the
squared measure of `QuadTracking` extended to three dimensions, which this file does not do.

**When `m3` is a norm, exactly.** `m3` is built from three linear functionals and is a seminorm
always; it is a *norm* only when they are independent. The determinant of the three factors, and
the factorisation is sharp:

```
det = −λ₁λ₂λ₃ · (λ₁−1)(λ₂−1)(λ₃−1) · (λ₁−λ₂)(λ₁−λ₃)(λ₂−λ₃)
```

so the measure is a norm **iff the eigenvalues are distinct and none of them is `0` or `1`**. Three
separate ways to lose it, and only one of them is the repeated-eigenvalue case one would think of.

**The deadbeat design is therefore VACUOUS here, and that is worth stating loudly** because the
two-state case shipped a deadbeat specimen *as its evidence*. At `λ₁ = λ₂ = λ₃ = 0` the gains are
`A = −1`, `B = 1`, `C = 0` and the left eigenvector `(λ(λ−1), λB, (λ−1)C)` collapses to `(0,0,0)`
for every `λᵢ` — all three functionals vanish, `m3 ≡ 0`, and `three_state_tracks_exact` degenerates
to `0 ≤ 0`. It is still true. It says nothing. `m3_vacuous_at_deadbeat` below is the convict
specimen, so nobody reaches for the two-state playbook and reports a bound that cannot fail.

A caller wanting a *norm* must therefore pick a design off that hypersurface — which is generic, but
is a real condition and not a formality. The statement does not hide any of this.
-/

namespace MachLib

namespace Real

/-! ### The measure -/

/-- A seminorm on a three-component state, as the maximum of three linear functionals. -/
noncomputable def m3 (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u v w : Real) : Real :=
  max (max (abs (a₁ * u + b₁ * v + c₁ * w)) (abs (a₂ * u + b₂ * v + c₂ * w)))
      (abs (a₃ * u + b₃ * v + c₃ * w))

theorem m3_nonneg (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u v w : Real) :
    0 ≤ m3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u v w :=
  max_nonneg_left (max_nonneg_left (abs_nonneg _))

/-- **Convict specimen: the deadbeat design makes this measure say nothing.** At
`λ₁ = λ₂ = λ₃ = 0` the left eigenvector `(λ(λ−1), λB, (λ−1)C)` is `(0,0,0)` for every `λᵢ`, so all
three functionals vanish identically and `three_state_tracks_exact` degenerates to `0 ≤ 0`.

This is here because the two-state case shipped a deadbeat specimen as its *evidence*, and reusing
that instinct one dimension up would produce a theorem that cannot fail and therefore cannot
inform. See the norm criterion in the header: `m3` is a norm iff the eigenvalues are distinct and
none is `0` or `1`. -/
theorem m3_vacuous_at_deadbeat (u v w : Real) :
    m3 0 0 0 0 0 0 0 0 0 u v w = 0 := by
  have e : ∀ p q r : Real, (0 : Real) * p + 0 * q + 0 * r = 0 := by
    intro p q r
    mach_mpoly [p, q, r]
  unfold m3
  rw [e u v w, abs_zero, max_self, max_self]

/-- Subadditivity — the only property the error recursion needs, and the reason the functionals
are applied before the absolute value. -/
theorem m3_subadd (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u₁ v₁ w₁ u₂ v₂ w₂ : Real) :
    m3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ (u₁ + u₂) (v₁ + v₂) (w₁ + w₂)
      ≤ m3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u₁ v₁ w₁
        + m3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u₂ v₂ w₂ := by
  refine max_le (max_le ?_ ?_) ?_
  · have e : a₁ * (u₁ + u₂) + b₁ * (v₁ + v₂) + c₁ * (w₁ + w₂)
        = (a₁ * u₁ + b₁ * v₁ + c₁ * w₁) + (a₁ * u₂ + b₁ * v₂ + c₁ * w₂) := by
      mach_mpoly [a₁, b₁, c₁, u₁, u₂, v₁, v₂, w₁, w₂]
    rw [e]
    exact le_trans (abs_add _ _)
      (add_le_add_both (le_max_of_le_left (le_max_left _ _) _)
                       (le_max_of_le_left (le_max_left _ _) _))
  · have e : a₂ * (u₁ + u₂) + b₂ * (v₁ + v₂) + c₂ * (w₁ + w₂)
        = (a₂ * u₁ + b₂ * v₁ + c₂ * w₁) + (a₂ * u₂ + b₂ * v₂ + c₂ * w₂) := by
      mach_mpoly [a₂, b₂, c₂, u₁, u₂, v₁, v₂, w₁, w₂]
    rw [e]
    exact le_trans (abs_add _ _)
      (add_le_add_both (le_max_of_le_left (le_max_right _ _) _)
                       (le_max_of_le_left (le_max_right _ _) _))
  · have e : a₃ * (u₁ + u₂) + b₃ * (v₁ + v₂) + c₃ * (w₁ + w₂)
        = (a₃ * u₁ + b₃ * v₁ + c₃ * w₁) + (a₃ * u₂ + b₃ * v₂ + c₃ * w₂) := by
      mach_mpoly [a₃, b₃, c₃, u₁, u₂, v₁, v₂, w₁, w₂]
    rw [e]
    exact le_trans (abs_add _ _)
      (add_le_add_both (le_max_right _ _) (le_max_right _ _))

/-- **From left-eigenvector data to the contraction.** Nine relations in, one contraction out;
each functional is carried to `λᵢ` times itself, so the maximum contracts by any common bound on
the moduli. -/
theorem m3_contract_of_eigen
    {A₁₁ A₁₂ A₁₃ A₂₁ A₂₂ A₂₃ A₃₁ A₃₂ A₃₃ : Real}
    {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ lam₁ lam₂ lam₃ L : Real}
    (e₁₁ : a₁ * A₁₁ + b₁ * A₂₁ + c₁ * A₃₁ = lam₁ * a₁)
    (e₁₂ : a₁ * A₁₂ + b₁ * A₂₂ + c₁ * A₃₂ = lam₁ * b₁)
    (e₁₃ : a₁ * A₁₃ + b₁ * A₂₃ + c₁ * A₃₃ = lam₁ * c₁)
    (e₂₁ : a₂ * A₁₁ + b₂ * A₂₁ + c₂ * A₃₁ = lam₂ * a₂)
    (e₂₂ : a₂ * A₁₂ + b₂ * A₂₂ + c₂ * A₃₂ = lam₂ * b₂)
    (e₂₃ : a₂ * A₁₃ + b₂ * A₂₃ + c₂ * A₃₃ = lam₂ * c₂)
    (e₃₁ : a₃ * A₁₁ + b₃ * A₂₁ + c₃ * A₃₁ = lam₃ * a₃)
    (e₃₂ : a₃ * A₁₂ + b₃ * A₂₂ + c₃ * A₃₂ = lam₃ * b₃)
    (e₃₃ : a₃ * A₁₃ + b₃ * A₂₃ + c₃ * A₃₃ = lam₃ * c₃)
    (hl₁ : abs lam₁ ≤ L) (hl₂ : abs lam₂ ≤ L) (hl₃ : abs lam₃ ≤ L)
    (u v w : Real) :
    m3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃
        (A₁₁ * u + A₁₂ * v + A₁₃ * w)
        (A₂₁ * u + A₂₂ * v + A₂₃ * w)
        (A₃₁ * u + A₃₂ * v + A₃₃ * w)
      ≤ L * m3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u v w := by
  have row : ∀ (a b c lam : Real),
      a * A₁₁ + b * A₂₁ + c * A₃₁ = lam * a →
      a * A₁₂ + b * A₂₂ + c * A₃₂ = lam * b →
      a * A₁₃ + b * A₂₃ + c * A₃₃ = lam * c →
      a * (A₁₁ * u + A₁₂ * v + A₁₃ * w) + b * (A₂₁ * u + A₂₂ * v + A₂₃ * w)
        + c * (A₃₁ * u + A₃₂ * v + A₃₃ * w) = lam * (a * u + b * v + c * w) := by
    intro a b c lam h1 h2 h3
    have e : a * (A₁₁ * u + A₁₂ * v + A₁₃ * w) + b * (A₂₁ * u + A₂₂ * v + A₂₃ * w)
        + c * (A₃₁ * u + A₃₂ * v + A₃₃ * w)
        = (a * A₁₁ + b * A₂₁ + c * A₃₁) * u + (a * A₁₂ + b * A₂₂ + c * A₃₂) * v
          + (a * A₁₃ + b * A₂₃ + c * A₃₃) * w := by
      mach_mpoly [a, b, c, A₁₁, A₁₂, A₁₃, A₂₁, A₂₂, A₂₃, A₃₁, A₃₂, A₃₃, u, v, w]
    rw [e, h1, h2, h3]
    mach_mpoly [lam, a, b, c, u, v, w]
  have step : ∀ (a b c lam : Real), abs lam ≤ L →
      a * A₁₁ + b * A₂₁ + c * A₃₁ = lam * a →
      a * A₁₂ + b * A₂₂ + c * A₃₂ = lam * b →
      a * A₁₃ + b * A₂₃ + c * A₃₃ = lam * c →
      abs (a * (A₁₁ * u + A₁₂ * v + A₁₃ * w) + b * (A₂₁ * u + A₂₂ * v + A₂₃ * w)
            + c * (A₃₁ * u + A₃₂ * v + A₃₃ * w))
        ≤ L * abs (a * u + b * v + c * w) := by
    intro a b c lam hl h1 h2 h3
    rw [row a b c lam h1 h2 h3, abs_mul]
    exact mul_le_mul_of_nonneg_right hl (abs_nonneg _)
  refine max_le (max_le ?_ ?_) ?_
  · exact le_trans (step a₁ b₁ c₁ lam₁ hl₁ e₁₁ e₁₂ e₁₃)
      (mul_le_mul_of_nonneg_left (le_max_of_le_left (le_max_left _ _) _)
        (le_trans (abs_nonneg lam₁) hl₁))
  · exact le_trans (step a₂ b₂ c₂ lam₂ hl₂ e₂₁ e₂₂ e₂₃)
      (mul_le_mul_of_nonneg_left (le_max_of_le_left (le_max_right _ _) _)
        (le_trans (abs_nonneg lam₂) hl₂))
  · exact le_trans (step a₃ b₃ c₃ lam₃ hl₃ e₃₁ e₃₂ e₃₃)
      (mul_le_mul_of_nonneg_left (le_max_right _ _)
        (le_trans (abs_nonneg lam₃) hl₃))

/-- **A perturbation confined to the state row, measured — and it is NOT free here.**

In the two-state case both functionals begin with `1`, so a state-row perturbation is measured at
exactly its own size and the datapath's per-step error passes through untouched. The PID
functionals begin with `λᵢ(λᵢ−1)` instead, so the perturbation is **scaled** by whatever dominates
those three coefficients. That factor is a real cost the caller pays, not an artefact: normalising
the eigenvectors would need division, which this corpus does not have, and hiding the factor by
rescaling the measure would only move it into the other side of the bound. -/
theorem m3_state_only_le {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ K : Real}
    (h₁ : abs a₁ ≤ K) (h₂ : abs a₂ ≤ K) (h₃ : abs a₃ ≤ K) (u : Real) :
    m3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u 0 0 ≤ K * abs u := by
  have e : ∀ a b c : Real, a * u + b * 0 + c * 0 = a * u := by
    intro a b c
    rw [mul_zero, mul_zero, add_zero, add_zero]
  refine max_le (max_le ?_ ?_) ?_
  · rw [e, abs_mul]; exact mul_le_mul_of_nonneg_right h₁ (abs_nonneg u)
  · rw [e, abs_mul]; exact mul_le_mul_of_nonneg_right h₂ (abs_nonneg u)
  · rw [e, abs_mul]; exact mul_le_mul_of_nonneg_right h₃ (abs_nonneg u)

/-! ### The tracking theorem -/

/-- **A three-state computed trajectory tracks its exact one.** Same shape as the two-state
version, and the same two-line reduction to `iterate_affine_bound`, which was always generic over
the sequence. -/
theorem three_state_tracks_exact
    {A₁₁ A₁₂ A₁₃ C₁ A₂₁ A₂₂ A₂₃ C₂ A₃₁ A₃₂ A₃₃ C₃ L ε : Real}
    {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : Real}
    {x i z xe ie ze dx di dz : Nat → Real}
    (hL : 0 ≤ L) (hε : 0 ≤ ε)
    (hex : ∀ k, xe (k + 1) = A₁₁ * xe k + A₁₂ * ie k + A₁₃ * ze k + C₁)
    (hei : ∀ k, ie (k + 1) = A₂₁ * xe k + A₂₂ * ie k + A₂₃ * ze k + C₂)
    (hez : ∀ k, ze (k + 1) = A₃₁ * xe k + A₃₂ * ie k + A₃₃ * ze k + C₃)
    (hcx : ∀ k, x (k + 1) = A₁₁ * x k + A₁₂ * i k + A₁₃ * z k + C₁ + dx k)
    (hci : ∀ k, i (k + 1) = A₂₁ * x k + A₂₂ * i k + A₂₃ * z k + C₂ + di k)
    (hcz : ∀ k, z (k + 1) = A₃₁ * x k + A₃₂ * i k + A₃₃ * z k + C₃ + dz k)
    (hcontract : ∀ u v w : Real,
      m3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃
          (A₁₁ * u + A₁₂ * v + A₁₃ * w)
          (A₂₁ * u + A₂₂ * v + A₂₃ * w)
          (A₃₁ * u + A₃₂ * v + A₃₃ * w)
        ≤ L * m3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u v w)
    (hpert : ∀ k, m3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ (dx k) (di k) (dz k) ≤ ε)
    (n : Nat) :
    m3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ (x n - xe n) (i n - ie n) (z n - ze n)
      ≤ npow n L * m3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ (x 0 - xe 0) (i 0 - ie 0) (z 0 - ze 0)
        + ε * geom L n := by
  refine iterate_affine_bound
    (fun k => m3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ (x k - xe k) (i k - ie k) (z k - ze k)) hL hε ?_ n
  intro k
  have ex : x (k + 1) - xe (k + 1)
      = (A₁₁ * (x k - xe k) + A₁₂ * (i k - ie k) + A₁₃ * (z k - ze k)) + dx k := by
    rw [hcx k, hex k]
    mach_mpoly [A₁₁, A₁₂, A₁₃, C₁, x k, xe k, i k, ie k, z k, ze k, dx k]
  have ei : i (k + 1) - ie (k + 1)
      = (A₂₁ * (x k - xe k) + A₂₂ * (i k - ie k) + A₂₃ * (z k - ze k)) + di k := by
    rw [hci k, hei k]
    mach_mpoly [A₂₁, A₂₂, A₂₃, C₂, x k, xe k, i k, ie k, z k, ze k, di k]
  have ez : z (k + 1) - ze (k + 1)
      = (A₃₁ * (x k - xe k) + A₃₂ * (i k - ie k) + A₃₃ * (z k - ze k)) + dz k := by
    rw [hcz k, hez k]
    mach_mpoly [A₃₁, A₃₂, A₃₃, C₃, x k, xe k, i k, ie k, z k, ze k, dz k]
  rw [ex, ei, ez]
  refine le_trans (m3_subadd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ?_
  exact add_le_add_both (hcontract (x k - xe k) (i k - ie k) (z k - ze k)) (hpert k)

/-- From `a − b = 0` conclude `a = b`. -/
private theorem eq_of_sub_zero {a b : Real} (h : a - b = 0) : a = b := by
  have e : a = (a - b) + b := by mach_mpoly [a, b]
  rw [e, h, zero_add]

/-! ### The PID eigenstructure, forced and free -/

/-- **All nine relations, as ring identities in the three eigenvalues.**

Gains through the characteristic equation: `A = e₁ − 1`, `B = e₂ − e₁ + 1 − e₃`, `C = −e₃`, with
`e₁ = λ₁+λ₂+λ₃`, `e₂ = λ₁λ₂+λ₁λ₃+λ₂λ₃`, `e₃ = λ₁λ₂λ₃`. Left eigenvector for `λ`:
`(λ(λ−1), λ·B, (λ−1)·C)`. Two columns are identities for any gains; the third is the
factorisation `λᵢ³ − e₁λᵢ² + e₂λᵢ − e₃ = 0`. -/
theorem pid_eigen_relation (lam l₁ l₂ l₃ : Real)
    (hlam : (lam - l₁) * (lam - l₂) * (lam - l₃) = 0) :
    (lam * (lam - 1)) * ((l₁ + l₂ + l₃) - 1)
        + (lam * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃)) * (-1)
        + ((lam - 1) * (-(l₁*l₂*l₃))) * 1
      = lam * (lam * (lam - 1))
    ∧ (lam * (lam - 1)) * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃)
        + (lam * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃)) * 1
        + ((lam - 1) * (-(l₁*l₂*l₃))) * 0
      = lam * (lam * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
    ∧ (lam * (lam - 1)) * (-(l₁*l₂*l₃))
        + (lam * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃)) * 0
        + ((lam - 1) * (-(l₁*l₂*l₃))) * 0
      = lam * ((lam - 1) * (-(l₁*l₂*l₃))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the characteristic equation, in the form the factorisation supplies
    refine eq_of_sub_zero ?_
    have e : (lam * (lam - 1)) * ((l₁ + l₂ + l₃) - 1)
        + (lam * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃)) * (-1)
        + ((lam - 1) * (-(l₁*l₂*l₃))) * 1
        - lam * (lam * (lam - 1))
        = -((lam - l₁) * (lam - l₂) * (lam - l₃)) := by
      mach_mpoly [lam, l₁, l₂, l₃]
    rw [e, hlam]
    mach_ring
  · mach_mpoly [lam, l₁, l₂, l₃]
  · mach_mpoly [lam, l₁, l₂, l₃]

/-- The relations hold **at each eigenvalue**, the hypothesis discharging itself because
`λᵢ − λᵢ = 0`. This is the specimen for `pid_eigen_relation`: without it the theorem would be
conditional on a root condition nobody had exhibited. -/
theorem pid_eigen_relation_at_root (l₁ l₂ l₃ : Real) :
    ((l₁ - l₁) * (l₁ - l₂) * (l₁ - l₃) = 0)
    ∧ ((l₂ - l₁) * (l₂ - l₂) * (l₂ - l₃) = 0)
    ∧ ((l₃ - l₁) * (l₃ - l₂) * (l₃ - l₃) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · mach_mpoly [l₁, l₂, l₃]
  · mach_mpoly [l₁, l₂, l₃]
  · mach_mpoly [l₁, l₂, l₃]

/-- **The PID contraction, discharged for every design with three real eigenvalues.**

The nine relations come from `pid_eigen_relation` at each of `λ₁, λ₂, λ₃`, whose root hypotheses
are `pid_eigen_relation_at_root`. As in the two-state case nothing design-specific is required
beyond naming the eigenvalues of the caller's own quantised gains and bounding their moduli. -/
theorem pid_eigen_contraction {l₁ l₂ l₃ L : Real}
    (h₁ : abs l₁ ≤ L) (h₂ : abs l₂ ≤ L) (h₃ : abs l₃ ≤ L) (u v w : Real) :
    m3 (l₁ * (l₁ - 1)) (l₁ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
         ((l₁ - 1) * (-(l₁*l₂*l₃)))
       (l₂ * (l₂ - 1)) (l₂ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
         ((l₂ - 1) * (-(l₁*l₂*l₃)))
       (l₃ * (l₃ - 1)) (l₃ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
         ((l₃ - 1) * (-(l₁*l₂*l₃)))
        (((l₁ + l₂ + l₃) - 1) * u
          + ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃) * v
          + (-(l₁*l₂*l₃)) * w)
        ((-1) * u + 1 * v + 0 * w)
        (1 * u + 0 * v + 0 * w)
      ≤ L * m3 (l₁ * (l₁ - 1)) (l₁ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₁ - 1) * (-(l₁*l₂*l₃)))
               (l₂ * (l₂ - 1)) (l₂ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₂ - 1) * (-(l₁*l₂*l₃)))
               (l₃ * (l₃ - 1)) (l₃ * ((l₁*l₂ + l₁*l₃ + l₂*l₃) - (l₁ + l₂ + l₃) + 1 - l₁*l₂*l₃))
                 ((l₃ - 1) * (-(l₁*l₂*l₃)))
               u v w := by
  obtain ⟨r₁, r₂, r₃⟩ := pid_eigen_relation_at_root l₁ l₂ l₃
  obtain ⟨p₁, p₂, p₃⟩ := pid_eigen_relation l₁ l₁ l₂ l₃ r₁
  obtain ⟨q₁, q₂, q₃⟩ := pid_eigen_relation l₂ l₁ l₂ l₃ r₂
  obtain ⟨s₁, s₂, s₃⟩ := pid_eigen_relation l₃ l₁ l₂ l₃ r₃
  exact m3_contract_of_eigen p₁ p₂ p₃ q₁ q₂ q₃ s₁ s₂ s₃ h₁ h₂ h₃ u v w

end Real

end MachLib
