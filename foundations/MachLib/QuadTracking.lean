import MachLib.TwoStateTracking

/-!
# Tracking a two-state loop with COMPLEX eigenvalues, without square roots

**The gap this closes.** `TwoStateTracking`'s measure is a maximum of two linear functionals, and
it contracts only when those functionals are real left eigenvectors — that is, when the
closed-loop eigenvalues are real. An under-damped design has a complex pair `σ ± iω`, no real
eigenvector, and that measure does not exist for it. `SignedPILoop` says so and excludes the case.

**Why the standard tool is not available.** The textbook answer is a quadratic Lyapunov function
`V(v) = vᵀPv` and the norm `√V`. The error recursion needs a triangle inequality for that norm,
which is Cauchy–Schwarz, and `√` — and this is a Mathlib-free corpus with no square-root
machinery to spend on either.

**What replaces it.** Work with the **squared** measure and never take a root. Two facts make that
go through, and both are elementary:

1. In real-Jordan coordinates a complex pair acts as a rotation-scaling, and a rotation-scaling
   multiplies the squared measure by exactly `σ² + ω²` — an *equality*, and a ring identity
   (`n2_rotscale`). No inequality is spent on the contraction itself.
2. The cross term in `n2(x + y)` is split by a sum of squares rather than by Cauchy–Schwarz:
   for `α·β = 1`, `α·n2(x) + β·n2(y) − 2⟨x,y⟩` is `β · Σᵢ(α·xᵢ − yᵢ)²`, visibly non-negative
   (`n2_young`). Writing the reciprocal as a second variable with `α·β = 1` keeps division out
   too.

**The price, stated rather than hidden.** The contraction factor is `(1+α)(σ²+ω²)` and not
`σ² + ω²`, and the per-step term is inflated to `(1+β)·n2(η)`. The caller chooses `α`; any
`α` with `(1+α)(σ²+ω²) < 1` works, and such an `α` exists exactly when `σ² + ω² < 1`, which is
the design being stable. The conclusion bounds the *squared* error, which is what a caller of a
square-root-free development can use.

**Scope.** Like `TwoStateTracking` this is the measure and the tracking theorem; the PI
instantiation is `pi_complex_rotscale` below, where — as in the real case — the eigenstructure
turns out to be forced and free.
-/

namespace MachLib

namespace Real

/-! ### The squared measure -/

/-- The squared measure in the coordinates `(p·u + q·v, r·u + s·v)`. For a complex pair those
coordinates are the real-Jordan ones, in which the map is a rotation-scaling. -/
noncomputable def n2 (p q r s u v : Real) : Real :=
  (p * u + q * v) * (p * u + q * v) + (r * u + s * v) * (r * u + s * v)

theorem n2_nonneg (p q r s u v : Real) : 0 ≤ n2 p q r s u v :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- **A rotation-scaling multiplies the squared measure by exactly `σ² + ω²`.**

The hypotheses are the real-Jordan relations: the two functionals are carried into
`σ·w₁ − ω·w₂` and `ω·w₁ + σ·w₂`. The conclusion is an *equality* and its proof is a ring identity
— `(σw₁ − ωw₂)² + (ωw₁ + σw₂)² = (σ²+ω²)(w₁² + w₂²)` — so the contraction costs no inequality at
all. That is the whole reason this route avoids Cauchy–Schwarz. -/
theorem n2_rotscale
    {A B D E p q r s sig om : Real}
    (h₁u : p * A + q * D = sig * p - om * r) (h₁v : p * B + q * E = sig * q - om * s)
    (h₂u : r * A + s * D = om * p + sig * r) (h₂v : r * B + s * E = om * q + sig * s)
    (u v : Real) :
    n2 p q r s (A * u + B * v) (D * u + E * v)
      = (sig * sig + om * om) * n2 p q r s u v := by
  have hw₁ : p * (A * u + B * v) + q * (D * u + E * v)
      = sig * (p * u + q * v) - om * (r * u + s * v) := by
    have e : p * (A * u + B * v) + q * (D * u + E * v)
        = (p * A + q * D) * u + (p * B + q * E) * v := by
      mach_mpoly [p, q, A, B, D, E, u, v]
    rw [e, h₁u, h₁v]
    mach_mpoly [sig, om, p, q, r, s, u, v]
  have hw₂ : r * (A * u + B * v) + s * (D * u + E * v)
      = om * (p * u + q * v) + sig * (r * u + s * v) := by
    have e : r * (A * u + B * v) + s * (D * u + E * v)
        = (r * A + s * D) * u + (r * B + s * E) * v := by
      mach_mpoly [r, s, A, B, D, E, u, v]
    rw [e, h₂u, h₂v]
    mach_mpoly [sig, om, p, q, r, s, u, v]
  show (p * (A * u + B * v) + q * (D * u + E * v)) * _ + _ = _
  rw [hw₁, hw₂]
  show _ = (sig * sig + om * om)
      * ((p * u + q * v) * (p * u + q * v) + (r * u + s * v) * (r * u + s * v))
  mach_mpoly [sig, om, p * u + q * v, r * u + s * v]

/-- **The cross term, split without Cauchy–Schwarz.** For `α·β = 1` with both non-negative,

`n2(x + y) ≤ (1+α)·n2(x) + (1+β)·n2(y)`,

because the slack is `β·(α·x₁ − y₁)² + β·(α·x₂ − y₂)²` — a sum of squares. Carrying the
reciprocal as a second variable constrained by `α·β = 1` keeps division out of the statement as
well as out of the proof. -/
theorem n2_young {p q r s : Real} (α β : Real) (hαβ : α * β = 1) (hβ : 0 ≤ β)
    (u₁ v₁ u₂ v₂ : Real) :
    n2 p q r s (u₁ + u₂) (v₁ + v₂)
      ≤ (1 + α) * n2 p q r s u₁ v₁ + (1 + β) * n2 p q r s u₂ v₂ := by
  -- abbreviate the four coordinates
  let a₁ := p * u₁ + q * v₁
  let a₂ := p * u₂ + q * v₂
  let b₁ := r * u₁ + s * v₁
  let b₂ := r * u₂ + s * v₂
  have hsplit : n2 p q r s (u₁ + u₂) (v₁ + v₂)
      = (a₁ + a₂) * (a₁ + a₂) + (b₁ + b₂) * (b₁ + b₂) := by
    show (p * (u₁ + u₂) + q * (v₁ + v₂)) * (p * (u₁ + u₂) + q * (v₁ + v₂))
        + (r * (u₁ + u₂) + s * (v₁ + v₂)) * (r * (u₁ + u₂) + s * (v₁ + v₂)) = _
    show _ = ((p * u₁ + q * v₁) + (p * u₂ + q * v₂)) * ((p * u₁ + q * v₁) + (p * u₂ + q * v₂))
        + ((r * u₁ + s * v₁) + (r * u₂ + s * v₂)) * ((r * u₁ + s * v₁) + (r * u₂ + s * v₂))
    mach_mpoly [p, q, r, s, u₁, u₂, v₁, v₂]
  have hrhs : (1 + α) * n2 p q r s u₁ v₁ + (1 + β) * n2 p q r s u₂ v₂
      = (1 + α) * (a₁ * a₁ + b₁ * b₁) + (1 + β) * (a₂ * a₂ + b₂ * b₂) := rfl
  rw [hsplit, hrhs]
  -- the slack is β·(α·a₁ − a₂)² + β·(α·b₁ − b₂)², using α·β = 1
  have hslack : (1 + α) * (a₁ * a₁ + b₁ * b₁) + (1 + β) * (a₂ * a₂ + b₂ * b₂)
      - ((a₁ + a₂) * (a₁ + a₂) + (b₁ + b₂) * (b₁ + b₂))
      = β * ((α * a₁ - a₂) * (α * a₁ - a₂)) + β * ((α * b₁ - b₂) * (α * b₁ - b₂)) := by
    have e : β * ((α * a₁ - a₂) * (α * a₁ - a₂)) + β * ((α * b₁ - b₂) * (α * b₁ - b₂))
        = (α * β) * (α * (a₁ * a₁) + α * (b₁ * b₁))
          - (α * β) * ((1 + 1) * (a₁ * a₂) + (1 + 1) * (b₁ * b₂))
          + β * (a₂ * a₂ + b₂ * b₂) := by
      mach_mpoly [α, β, a₁, a₂, b₁, b₂]
    rw [e, hαβ]
    mach_mpoly [α, β, a₁, a₂, b₁, b₂]
  have hnn : 0 ≤ β * ((α * a₁ - a₂) * (α * a₁ - a₂)) + β * ((α * b₁ - b₂) * (α * b₁ - b₂)) :=
    add_nonneg (mul_nonneg hβ (mul_self_nonneg _)) (mul_nonneg hβ (mul_self_nonneg _))
  rw [← hslack] at hnn
  exact le_of_sub_nonneg hnn

/-! ### The tracking theorem -/

/-- **A two-state computed trajectory tracks its exact one, with the SQUARED error measured by
`n2` and a complex-capable contraction.**

Same shape as `two_state_tracks_exact`, with the maximum-of-functionals measure replaced by the
squared one and the subadditivity step replaced by `n2_young`. The contraction factor carries the
`(1+α)` the cross-term split costs, and the per-step term the `(1+β)`. -/
theorem two_state_tracks_exact_quad
    {A B C D E F sig om α β ε : Real}
    {p q r s : Real}
    {x i xe ie dx di : Nat → Real}
    (hαβ : α * β = 1) (hβ : 0 ≤ β) (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (hrot : sig * sig + om * om ≥ 0)
    (hexact : ∀ k, xe (k + 1) = A * xe k + B * ie k + C)
    (hexacti : ∀ k, ie (k + 1) = D * xe k + E * ie k + F)
    (hcomp : ∀ k, x (k + 1) = A * x k + B * i k + C + dx k)
    (hcompi : ∀ k, i (k + 1) = D * x k + E * i k + F + di k)
    (h₁u : p * A + q * D = sig * p - om * r) (h₁v : p * B + q * E = sig * q - om * s)
    (h₂u : r * A + s * D = om * p + sig * r) (h₂v : r * B + s * E = om * q + sig * s)
    (hpert : ∀ k, (1 + β) * n2 p q r s (dx k) (di k) ≤ ε)
    (n : Nat) :
    n2 p q r s (x n - xe n) (i n - ie n)
      ≤ npow n ((1 + α) * (sig * sig + om * om))
          * n2 p q r s (x 0 - xe 0) (i 0 - ie 0)
        + ε * geom ((1 + α) * (sig * sig + om * om)) n := by
  refine iterate_affine_bound (fun k => n2 p q r s (x k - xe k) (i k - ie k))
    (mul_nonneg (le_trans (le_of_lt zero_lt_one_ax) (le_add_of_nonneg_right hα)) hrot) hε ?_ n
  intro k
  have ex : x (k + 1) - xe (k + 1)
      = (A * (x k - xe k) + B * (i k - ie k)) + dx k := by
    rw [hcomp k, hexact k]
    mach_mpoly [A, B, C, x k, xe k, i k, ie k, dx k]
  have ei : i (k + 1) - ie (k + 1)
      = (D * (x k - xe k) + E * (i k - ie k)) + di k := by
    rw [hcompi k, hexacti k]
    mach_mpoly [D, E, F, x k, xe k, i k, ie k, di k]
  rw [ex, ei]
  refine le_trans (n2_young α β hαβ hβ _ _ _ _) ?_
  rw [n2_rotscale h₁u h₁v h₂u h₂v]
  have hreassoc : (1 + α) * ((sig * sig + om * om) * n2 p q r s (x k - xe k) (i k - ie k))
      = (1 + α) * (sig * sig + om * om) * n2 p q r s (x k - xe k) (i k - ie k) := by
    mach_mpoly [α, sig * sig + om * om, n2 p q r s (x k - xe k) (i k - ie k)]
  rw [hreassoc]
  exact add_le_add_both (le_refl _) (hpert k)

/-! ### The PI loop's complex eigenstructure is forced, and free -/

/-- **The real-Jordan relations for a PI loop with a complex pair, discharged identically.**

As in the real case the integrator row `[−1, 1]` forces everything. Writing the gains through the
characteristic equation for a complex pair — `A = 2σ − 1` (written `(1+1)·σ − 1`, since `(2 : Real)` does not elaborate here), `B = (σ−1)² + ω²` — the real-Jordan
functionals are `(1, σ−1)` and `(0, −ω)`, and all four relations are ring identities in `σ, ω`.
No side condition, no decimal arithmetic, and no case analysis on the discriminant.

`ω = 0` degenerates the second functional to zero, which is exactly the real case that
`TwoStateTracking`'s measure already handles; the two are complementary rather than overlapping. -/
theorem pi_complex_rotscale (sig om : Real) :
    (1 * ((1 + 1) * sig - 1) + (sig - 1) * (-1) = sig * 1 - om * 0)
    ∧ (1 * ((sig - 1) * (sig - 1) + om * om) + (sig - 1) * 1 = sig * (sig - 1) - om * (-om))
    ∧ (0 * ((1 + 1) * sig - 1) + (-om) * (-1) = om * 1 + sig * 0)
    ∧ (0 * ((sig - 1) * (sig - 1) + om * om) + (-om) * 1 = om * (sig - 1) + sig * (-om)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · mach_mpoly [sig, om]
  · mach_mpoly [sig, om]
  · mach_mpoly [sig, om]
  · mach_mpoly [sig, om]

/-! ### Specimens — the hypotheses hold, and the contraction regime is reachable

Two questions a reader has. First, is the hypothesis set satisfiable at all — `α·β = 1` with both
non-negative, alongside the four rotation-scaling relations? Second, and the one that matters,
does any design actually land in the contracting regime, given that the cross-term split costs a
factor `(1 + α)`? Both are answered by exhibiting a design rather than by argument. -/

/-- `α = β = 1` satisfies the reciprocal constraint, so the cross-term split is available at the
symmetric choice — the one that costs a factor of two and asks nothing of the design. -/
theorem n2_young_symmetric_specimen : (1 : Real) * 1 = 1 := mul_one_ax 1

/-- **The contracting regime is reachable.** At the symmetric split `α = β = 1` and the design
`σ = 0`, `ω = e⁻¹` — a genuinely complex pair, since `ω ≠ 0` — the contraction factor
`(1+α)(σ² + ω²)` is below one.

The proof needs no numerics: `1 + 1 < e` is `exp_gt_one_plus_self` at `1`, multiplying through by
`e⁻¹ > 0` gives `(1+1)·e⁻¹ < 1`, and `e⁻¹ · e⁻¹ < e⁻¹` because `e⁻¹ < 1`. So a factor-of-two loss
still leaves room, which is the honest answer to "is the `(1+α)` fatal" — it is not, though it
does shrink the admissible design region by that factor. -/
theorem pi_complex_contraction_specimen :
    (1 + 1) * (0 * 0 + exp (-1) * exp (-1)) < 1 := by
  have hpos : (0 : Real) < exp (-1) := exp_pos _
  have hlt1 : exp (-1) < 1 := by
    have w := exp_lt (show (-1 : Real) < 0 by
      have u := add_lt_add_left zero_lt_one_ax (-(1 : Real))
      have f1 : -(1 : Real) + 0 = -1 := by mach_ring
      have f2 : -(1 : Real) + 1 = 0 := by mach_ring
      rw [f1, f2] at u; exact u)
    rw [exp_zero] at w; exact w
  -- (1+1) · e⁻¹ < 1, from 1 + 1 < e and e·e⁻¹ = 1
  have htwo : (1 + 1) * exp (-1) < 1 := by
    have he : (1 : Real) + 1 < exp 1 := exp_gt_one_plus_self 1 zero_lt_one_ax
    have hmul := mul_lt_mul_of_pos_right he hpos
    have hone : exp 1 * exp (-1) = 1 := by
      have w := exp_neg_self_mul 1
      rw [mul_comm] at w; exact w
    rw [hone] at hmul; exact hmul
  -- e⁻¹ · e⁻¹ < e⁻¹, so the product is below (1+1)·e⁻¹
  have hsq : exp (-1) * exp (-1) < exp (-1) := by
    have h := mul_lt_mul_of_pos_right hlt1 hpos
    rw [one_mul_thm] at h; exact h
  have hstep : (1 + 1) * (0 * 0 + exp (-1) * exp (-1)) < (1 + 1) * exp (-1) := by
    have hz : (0 : Real) * 0 + exp (-1) * exp (-1) = exp (-1) * exp (-1) := by
      mach_mpoly [exp (-1)]
    rw [hz]
    have htwopos : (0 : Real) < 1 + 1 := by
      have u := add_lt_add_left zero_lt_one_ax (1 : Real)
      have e : (1 : Real) + 0 = 1 := by mach_ring
      rw [e] at u
      exact lt_trans_ax zero_lt_one_ax u
    have h := mul_lt_mul_of_pos_right hsq htwopos
    have e1 : exp (-1) * exp (-1) * (1 + 1) = (1 + 1) * (exp (-1) * exp (-1)) := by
      mach_mpoly [exp (-1)]
    have e2 : exp (-1) * (1 + 1) = (1 + 1) * exp (-1) := by mach_mpoly [exp (-1)]
    rw [e1, e2] at h; exact h
  exact lt_trans_ax hstep htwo

end Real

end MachLib
