import MachLib.ThreeStateTracking
import MachLib.QuadTracking

/-!
# A three-state loop with a complex pair — the last damping gap

`ThreeStateTracking` handles a PID design whose three closed-loop eigenvalues are **real**, using a
maximum of three linear functionals. An under-damped PID design has one real eigenvalue `r` and a
conjugate pair `σ ± iω`, for which two of those functionals do not exist. `QuadTracking` closed the
same gap one dimension down, for PI; this file closes it here, and with it every PID design is
covered whatever its damping.

## The shape of the answer

The state space splits into a real eigendirection and a two-dimensional real-Jordan block, so the
measure splits the same way:

```
n3 = f²  +  (g₁² + g₂²)
```

`f` is the real left eigenvector, `g₁, g₂` the real and imaginary parts of the complex one. Under
one step the first term is multiplied by exactly `r²` and the second by exactly `σ² + ω²`, both
**equalities** proved as ring identities. The contraction is then `max(r², σ²+ω²)` and costs no
inequality of its own — the same reason the two-dimensional version avoided Cauchy–Schwarz.

Everything else is inherited: no square roots anywhere, and the cross term in `n3(x+y)` splits by a
**sum of squares** with `α·β = 1` rather than by Cauchy–Schwarz, exactly as `n2_young` does.

## Forced and free, a third time — and this time it was checked first

The nine relations below are ring identities in `r, σ, ω`. Writing the gains through the
characteristic equation in its factored real form,

```
A = r + 2σ − 1,   B = 2rσ + (σ²+ω²) − r − 2σ + 1 − r(σ²+ω²),   C = −r(σ²+ω²)
```

the functionals

```
f  = ( r(r−1),        r·B,  (r−1)·C )
g₁ = ( σ²−ω²−σ,       σ·B,  (σ−1)·C )
g₂ = ( 2σω−ω,         ω·B,   ω·C    )
```

satisfy `f·M = r·f`, `g₁·M = σg₁ − ωg₂`, `g₂·M = ωg₁ + σg₂` identically. The PID loop's two
structural rows — the integrator and the delay — force this exactly as they forced the real case.

The estimate for the real case was made by eyeballing the problem and was **wrong**; that is
recorded in `ThreeStateTracking`'s header. This one was checked symbolically *before* any prose was
written, which is the correction actually worth keeping.

## When the measure is a norm

The three functionals have determinant

```
det = ω · r · (r−1) · (σ²+ω²) · ((r−σ)²+ω²) · ((σ−1)²+ω²)
```

and the last two factors cannot vanish when `ω ≠ 0`. So `n3` is a norm exactly when **`ω ≠ 0` and
`r` is neither `0` nor `1`** — the same two excluded values as the real case, with `ω ≠ 0` standing
in for distinctness. `ω = 0` is precisely the real case `ThreeStateTracking` already handles, so
the two measures are complementary rather than overlapping and neither needs to know about the
other.

## The price, carried in the statement

As in `QuadTracking` the cross-term split costs a factor: the contraction is
`(1+α)·max(r², σ²+ω²)` and the per-step term is inflated by `(1+β)`. That is a real loss and it is
written into the conclusion rather than hidden.

## Not claimed

No bit-level datapath instantiation for this case — `SignedPIDLoop` joins the *real*-eigenvalue
theorem to `spidloop`, and the corresponding join here is not done. No anti-windup.
-/

namespace MachLib

namespace Real

/-! ### The measure -/

/-- The squared measure on a three-component state: one real coordinate and a real-Jordan pair.
The grouping is deliberate — the pair is the part a rotation-scaling acts on. -/
noncomputable def n3 (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u v w : Real) : Real :=
  (a₁ * u + b₁ * v + c₁ * w) * (a₁ * u + b₁ * v + c₁ * w)
  + ((a₂ * u + b₂ * v + c₂ * w) * (a₂ * u + b₂ * v + c₂ * w)
     + (a₃ * u + b₃ * v + c₃ * w) * (a₃ * u + b₃ * v + c₃ * w))

theorem n3_nonneg (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u v w : Real) :
    0 ≤ n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u v w :=
  add_nonneg (mul_self_nonneg _)
    (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))

/-! ### One step, exactly -/

/-- **A step multiplies the real part by exactly `r²` and the Jordan pair by exactly `σ²+ω²`.**

Both are equalities and both are ring identities, so a step of the loop costs no inequality at all.
That is what makes the whole route work without square roots: the only inequality in the eventual
bound comes from the cross-term split, never from the dynamics. -/
theorem n3_split
    {A₁₁ A₁₂ A₁₃ A₂₁ A₂₂ A₂₃ A₃₁ A₃₂ A₃₃ : Real}
    {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ rr sig om : Real}
    (f₁ : a₁ * A₁₁ + b₁ * A₂₁ + c₁ * A₃₁ = rr * a₁)
    (f₂ : a₁ * A₁₂ + b₁ * A₂₂ + c₁ * A₃₂ = rr * b₁)
    (f₃ : a₁ * A₁₃ + b₁ * A₂₃ + c₁ * A₃₃ = rr * c₁)
    (p₁ : a₂ * A₁₁ + b₂ * A₂₁ + c₂ * A₃₁ = sig * a₂ - om * a₃)
    (p₂ : a₂ * A₁₂ + b₂ * A₂₂ + c₂ * A₃₂ = sig * b₂ - om * b₃)
    (p₃ : a₂ * A₁₃ + b₂ * A₂₃ + c₂ * A₃₃ = sig * c₂ - om * c₃)
    (q₁ : a₃ * A₁₁ + b₃ * A₂₁ + c₃ * A₃₁ = om * a₂ + sig * a₃)
    (q₂ : a₃ * A₁₂ + b₃ * A₂₂ + c₃ * A₃₂ = om * b₂ + sig * b₃)
    (q₃ : a₃ * A₁₃ + b₃ * A₂₃ + c₃ * A₃₃ = om * c₂ + sig * c₃)
    (u v w : Real) :
    n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃
        (A₁₁ * u + A₁₂ * v + A₁₃ * w)
        (A₂₁ * u + A₂₂ * v + A₂₃ * w)
        (A₃₁ * u + A₃₂ * v + A₃₃ * w)
      = (rr * rr) * ((a₁ * u + b₁ * v + c₁ * w) * (a₁ * u + b₁ * v + c₁ * w))
        + (sig * sig + om * om)
            * ((a₂ * u + b₂ * v + c₂ * w) * (a₂ * u + b₂ * v + c₂ * w)
               + (a₃ * u + b₃ * v + c₃ * w) * (a₃ * u + b₃ * v + c₃ * w)) := by
  have row : ∀ (a b c : Real),
      a * (A₁₁ * u + A₁₂ * v + A₁₃ * w) + b * (A₂₁ * u + A₂₂ * v + A₂₃ * w)
        + c * (A₃₁ * u + A₃₂ * v + A₃₃ * w)
      = (a * A₁₁ + b * A₂₁ + c * A₃₁) * u + (a * A₁₂ + b * A₂₂ + c * A₃₂) * v
        + (a * A₁₃ + b * A₂₃ + c * A₃₃) * w := by
    intro a b c
    mach_mpoly [a, b, c, A₁₁, A₁₂, A₁₃, A₂₁, A₂₂, A₂₃, A₃₁, A₃₂, A₃₃, u, v, w]
  have hf : a₁ * (A₁₁ * u + A₁₂ * v + A₁₃ * w) + b₁ * (A₂₁ * u + A₂₂ * v + A₂₃ * w)
        + c₁ * (A₃₁ * u + A₃₂ * v + A₃₃ * w)
      = rr * (a₁ * u + b₁ * v + c₁ * w) := by
    rw [row a₁ b₁ c₁, f₁, f₂, f₃]
    mach_mpoly [rr, a₁, b₁, c₁, u, v, w]
  have hg₁ : a₂ * (A₁₁ * u + A₁₂ * v + A₁₃ * w) + b₂ * (A₂₁ * u + A₂₂ * v + A₂₃ * w)
        + c₂ * (A₃₁ * u + A₃₂ * v + A₃₃ * w)
      = sig * (a₂ * u + b₂ * v + c₂ * w) - om * (a₃ * u + b₃ * v + c₃ * w) := by
    rw [row a₂ b₂ c₂, p₁, p₂, p₃]
    mach_mpoly [sig, om, a₂, b₂, c₂, a₃, b₃, c₃, u, v, w]
  have hg₂ : a₃ * (A₁₁ * u + A₁₂ * v + A₁₃ * w) + b₃ * (A₂₁ * u + A₂₂ * v + A₂₃ * w)
        + c₃ * (A₃₁ * u + A₃₂ * v + A₃₃ * w)
      = om * (a₂ * u + b₂ * v + c₂ * w) + sig * (a₃ * u + b₃ * v + c₃ * w) := by
    rw [row a₃ b₃ c₃, q₁, q₂, q₃]
    mach_mpoly [sig, om, a₂, b₂, c₂, a₃, b₃, c₃, u, v, w]
  show (a₁ * (A₁₁ * u + A₁₂ * v + A₁₃ * w) + b₁ * (A₂₁ * u + A₂₂ * v + A₂₃ * w)
        + c₁ * (A₃₁ * u + A₃₂ * v + A₃₃ * w)) * _ + (_ + _) = _
  rw [hf, hg₁, hg₂]
  mach_mpoly [rr, sig, om, a₁ * u + b₁ * v + c₁ * w, a₂ * u + b₂ * v + c₂ * w,
              a₃ * u + b₃ * v + c₃ * w]

/-- **The contraction**, from the exact split and two modulus bounds. `L` dominates `r²` and
`σ²+ω²`; no relation between them is needed, and no case split on which is larger. -/
theorem n3_contract_of_eigen
    {A₁₁ A₁₂ A₁₃ A₂₁ A₂₂ A₂₃ A₃₁ A₃₂ A₃₃ : Real}
    {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ rr sig om L : Real}
    (f₁ : a₁ * A₁₁ + b₁ * A₂₁ + c₁ * A₃₁ = rr * a₁)
    (f₂ : a₁ * A₁₂ + b₁ * A₂₂ + c₁ * A₃₂ = rr * b₁)
    (f₃ : a₁ * A₁₃ + b₁ * A₂₃ + c₁ * A₃₃ = rr * c₁)
    (p₁ : a₂ * A₁₁ + b₂ * A₂₁ + c₂ * A₃₁ = sig * a₂ - om * a₃)
    (p₂ : a₂ * A₁₂ + b₂ * A₂₂ + c₂ * A₃₂ = sig * b₂ - om * b₃)
    (p₃ : a₂ * A₁₃ + b₂ * A₂₃ + c₂ * A₃₃ = sig * c₂ - om * c₃)
    (q₁ : a₃ * A₁₁ + b₃ * A₂₁ + c₃ * A₃₁ = om * a₂ + sig * a₃)
    (q₂ : a₃ * A₁₂ + b₃ * A₂₂ + c₃ * A₃₂ = om * b₂ + sig * b₃)
    (q₃ : a₃ * A₁₃ + b₃ * A₂₃ + c₃ * A₃₃ = om * c₂ + sig * c₃)
    (hr : rr * rr ≤ L) (hc : sig * sig + om * om ≤ L)
    (u v w : Real) :
    n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃
        (A₁₁ * u + A₁₂ * v + A₁₃ * w)
        (A₂₁ * u + A₂₂ * v + A₂₃ * w)
        (A₃₁ * u + A₃₂ * v + A₃₃ * w)
      ≤ L * n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u v w := by
  rw [n3_split f₁ f₂ f₃ p₁ p₂ p₃ q₁ q₂ q₃ u v w]
  have hL : L * n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u v w
      = L * ((a₁ * u + b₁ * v + c₁ * w) * (a₁ * u + b₁ * v + c₁ * w))
        + L * ((a₂ * u + b₂ * v + c₂ * w) * (a₂ * u + b₂ * v + c₂ * w)
               + (a₃ * u + b₃ * v + c₃ * w) * (a₃ * u + b₃ * v + c₃ * w)) := by
    show L * ((a₁ * u + b₁ * v + c₁ * w) * (a₁ * u + b₁ * v + c₁ * w)
              + ((a₂ * u + b₂ * v + c₂ * w) * (a₂ * u + b₂ * v + c₂ * w)
                 + (a₃ * u + b₃ * v + c₃ * w) * (a₃ * u + b₃ * v + c₃ * w))) = _
    mach_mpoly [L, (a₁ * u + b₁ * v + c₁ * w) * (a₁ * u + b₁ * v + c₁ * w),
                (a₂ * u + b₂ * v + c₂ * w) * (a₂ * u + b₂ * v + c₂ * w),
                (a₃ * u + b₃ * v + c₃ * w) * (a₃ * u + b₃ * v + c₃ * w)]
  rw [hL]
  refine add_le_add_both (mul_le_mul_of_nonneg_right hr (mul_self_nonneg _))
    (mul_le_mul_of_nonneg_right hc
      (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)))

/-! ### The cross term, again without Cauchy–Schwarz -/

/-- **Subadditivity up to `α, β`**, by a sum of squares. Identical in spirit to `n2_young`, with a
third square carried along; the reciprocal is again a second variable constrained by `α·β = 1`, so
no division appears in the statement or the proof. -/
theorem n3_young {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : Real} (α β : Real)
    (hαβ : α * β = 1) (hβ : 0 ≤ β)
    (u₁ v₁ w₁ u₂ v₂ w₂ : Real) :
    n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ (u₁ + u₂) (v₁ + v₂) (w₁ + w₂)
      ≤ (1 + α) * n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u₁ v₁ w₁
        + (1 + β) * n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u₂ v₂ w₂ := by
  let x₁ := a₁ * u₁ + b₁ * v₁ + c₁ * w₁
  let x₂ := a₁ * u₂ + b₁ * v₂ + c₁ * w₂
  let y₁ := a₂ * u₁ + b₂ * v₁ + c₂ * w₁
  let y₂ := a₂ * u₂ + b₂ * v₂ + c₂ * w₂
  let z₁ := a₃ * u₁ + b₃ * v₁ + c₃ * w₁
  let z₂ := a₃ * u₂ + b₃ * v₂ + c₃ * w₂
  have hsplit : n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ (u₁ + u₂) (v₁ + v₂) (w₁ + w₂)
      = (x₁ + x₂) * (x₁ + x₂) + ((y₁ + y₂) * (y₁ + y₂) + (z₁ + z₂) * (z₁ + z₂)) := by
    show (a₁ * (u₁ + u₂) + b₁ * (v₁ + v₂) + c₁ * (w₁ + w₂))
          * (a₁ * (u₁ + u₂) + b₁ * (v₁ + v₂) + c₁ * (w₁ + w₂))
        + ((a₂ * (u₁ + u₂) + b₂ * (v₁ + v₂) + c₂ * (w₁ + w₂))
            * (a₂ * (u₁ + u₂) + b₂ * (v₁ + v₂) + c₂ * (w₁ + w₂))
           + (a₃ * (u₁ + u₂) + b₃ * (v₁ + v₂) + c₃ * (w₁ + w₂))
            * (a₃ * (u₁ + u₂) + b₃ * (v₁ + v₂) + c₃ * (w₁ + w₂))) = _
    show _ = ((a₁ * u₁ + b₁ * v₁ + c₁ * w₁) + (a₁ * u₂ + b₁ * v₂ + c₁ * w₂))
          * ((a₁ * u₁ + b₁ * v₁ + c₁ * w₁) + (a₁ * u₂ + b₁ * v₂ + c₁ * w₂))
        + (((a₂ * u₁ + b₂ * v₁ + c₂ * w₁) + (a₂ * u₂ + b₂ * v₂ + c₂ * w₂))
            * ((a₂ * u₁ + b₂ * v₁ + c₂ * w₁) + (a₂ * u₂ + b₂ * v₂ + c₂ * w₂))
           + ((a₃ * u₁ + b₃ * v₁ + c₃ * w₁) + (a₃ * u₂ + b₃ * v₂ + c₃ * w₂))
            * ((a₃ * u₁ + b₃ * v₁ + c₃ * w₁) + (a₃ * u₂ + b₃ * v₂ + c₃ * w₂)))
    mach_mpoly [a₁, b₁, c₁, a₂, b₂, c₂, a₃, b₃, c₃, u₁, u₂, v₁, v₂, w₁, w₂]
  have hrhs : (1 + α) * n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u₁ v₁ w₁
        + (1 + β) * n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ u₂ v₂ w₂
      = (1 + α) * (x₁ * x₁ + (y₁ * y₁ + z₁ * z₁))
        + (1 + β) * (x₂ * x₂ + (y₂ * y₂ + z₂ * z₂)) := rfl
  rw [hsplit, hrhs]
  have hslack : (1 + α) * (x₁ * x₁ + (y₁ * y₁ + z₁ * z₁))
        + (1 + β) * (x₂ * x₂ + (y₂ * y₂ + z₂ * z₂))
      - ((x₁ + x₂) * (x₁ + x₂) + ((y₁ + y₂) * (y₁ + y₂) + (z₁ + z₂) * (z₁ + z₂)))
      = β * ((α * x₁ - x₂) * (α * x₁ - x₂)) + β * ((α * y₁ - y₂) * (α * y₁ - y₂))
        + β * ((α * z₁ - z₂) * (α * z₁ - z₂)) := by
    have e : β * ((α * x₁ - x₂) * (α * x₁ - x₂)) + β * ((α * y₁ - y₂) * (α * y₁ - y₂))
          + β * ((α * z₁ - z₂) * (α * z₁ - z₂))
        = (α * β) * (α * (x₁ * x₁) + α * (y₁ * y₁) + α * (z₁ * z₁))
          - (α * β) * ((x₁ * x₂ + x₁ * x₂) + (y₁ * y₂ + y₁ * y₂) + (z₁ * z₂ + z₁ * z₂))
          + β * (x₂ * x₂ + y₂ * y₂ + z₂ * z₂) := by
      mach_mpoly [α, β, x₁, x₂, y₁, y₂, z₁, z₂]
    rw [e, hαβ]
    mach_mpoly [α, β, x₁, x₂, y₁, y₂, z₁, z₂]
  have hnn : 0 ≤ β * ((α * x₁ - x₂) * (α * x₁ - x₂)) + β * ((α * y₁ - y₂) * (α * y₁ - y₂))
        + β * ((α * z₁ - z₂) * (α * z₁ - z₂)) :=
    add_nonneg (add_nonneg (mul_nonneg hβ (mul_self_nonneg _))
      (mul_nonneg hβ (mul_self_nonneg _))) (mul_nonneg hβ (mul_self_nonneg _))
  rw [← hslack] at hnn
  exact le_of_sub_nonneg hnn

/-! ### The tracking theorem -/

/-- **A three-state computed trajectory tracks its exact one, in the squared measure.**

Same shape as `three_state_tracks_exact`, with the maximum-of-functionals measure replaced by the
squared one and the subadditivity step by `n3_young`. The contraction factor carries the `(1+α)`
the cross-term split costs; the per-step term carries the `(1+β)`. -/
theorem three_state_tracks_exact_quad
    {A₁₁ A₁₂ A₁₃ C₁ A₂₁ A₂₂ A₂₃ C₂ A₃₁ A₃₂ A₃₃ C₃ : Real}
    {a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ rr sig om L α β ε : Real}
    {x i z xe ie ze dx di dz : Nat → Real}
    (hαβ : α * β = 1) (hβ : 0 ≤ β) (hα : 0 ≤ α) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hex : ∀ k, xe (k + 1) = A₁₁ * xe k + A₁₂ * ie k + A₁₃ * ze k + C₁)
    (hei : ∀ k, ie (k + 1) = A₂₁ * xe k + A₂₂ * ie k + A₂₃ * ze k + C₂)
    (hez : ∀ k, ze (k + 1) = A₃₁ * xe k + A₃₂ * ie k + A₃₃ * ze k + C₃)
    (hcx : ∀ k, x (k + 1) = A₁₁ * x k + A₁₂ * i k + A₁₃ * z k + C₁ + dx k)
    (hci : ∀ k, i (k + 1) = A₂₁ * x k + A₂₂ * i k + A₂₃ * z k + C₂ + di k)
    (hcz : ∀ k, z (k + 1) = A₃₁ * x k + A₃₂ * i k + A₃₃ * z k + C₃ + dz k)
    (f₁ : a₁ * A₁₁ + b₁ * A₂₁ + c₁ * A₃₁ = rr * a₁)
    (f₂ : a₁ * A₁₂ + b₁ * A₂₂ + c₁ * A₃₂ = rr * b₁)
    (f₃ : a₁ * A₁₃ + b₁ * A₂₃ + c₁ * A₃₃ = rr * c₁)
    (p₁ : a₂ * A₁₁ + b₂ * A₂₁ + c₂ * A₃₁ = sig * a₂ - om * a₃)
    (p₂ : a₂ * A₁₂ + b₂ * A₂₂ + c₂ * A₃₂ = sig * b₂ - om * b₃)
    (p₃ : a₂ * A₁₃ + b₂ * A₂₃ + c₂ * A₃₃ = sig * c₂ - om * c₃)
    (q₁ : a₃ * A₁₁ + b₃ * A₂₁ + c₃ * A₃₁ = om * a₂ + sig * a₃)
    (q₂ : a₃ * A₁₂ + b₃ * A₂₂ + c₃ * A₃₂ = om * b₂ + sig * b₃)
    (q₃ : a₃ * A₁₃ + b₃ * A₂₃ + c₃ * A₃₃ = om * c₂ + sig * c₃)
    (hr : rr * rr ≤ L) (hc : sig * sig + om * om ≤ L)
    (hpert : ∀ k, (1 + β) * n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ (dx k) (di k) (dz k) ≤ ε)
    (n : Nat) :
    n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ (x n - xe n) (i n - ie n) (z n - ze n)
      ≤ npow n ((1 + α) * L)
          * n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ (x 0 - xe 0) (i 0 - ie 0) (z 0 - ze 0)
        + ε * geom ((1 + α) * L) n := by
  have h1α : (0 : Real) ≤ 1 + α :=
    le_trans (le_of_lt zero_lt_one_ax) (le_add_of_nonneg_right hα)
  refine iterate_affine_bound
    (fun k => n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ (x k - xe k) (i k - ie k) (z k - ze k))
    (mul_nonneg h1α hL) hε ?_ n
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
  refine le_trans (n3_young α β hαβ hβ _ _ _ _ _ _) ?_
  refine le_trans (add_le_add_both
    (mul_le_mul_of_nonneg_left
      (n3_contract_of_eigen f₁ f₂ f₃ p₁ p₂ p₃ q₁ q₂ q₃ hr hc
        (x k - xe k) (i k - ie k) (z k - ze k)) h1α)
    (hpert k)) ?_
  have hre : (1 + α) * (L * n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ (x k - xe k) (i k - ie k) (z k - ze k))
      = (1 + α) * L * n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ (x k - xe k) (i k - ie k) (z k - ze k) := by
    mach_mpoly [α, L, n3 a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ (x k - xe k) (i k - ie k) (z k - ze k)]
  rw [hre]
  exact le_refl _

/-! ### The PID loop's complex eigenstructure is forced, and free

Checked symbolically **before** any of this prose was written. The estimate for the real case was
made the other way round and was wrong; `ThreeStateTracking`'s header records that, and this is the
correction in practice rather than in principle. -/

/-- **The nine real-Jordan relations for a PID loop with one real eigenvalue and a complex pair,
all ring identities in `r, σ, ω`.**

The gains are written through the characteristic equation in its factored real form
`(x − r)(x² − 2σx + (σ²+ω²))`. Doubling is written additively (`sig + sig`, not `(1+1)*sig`)
because `CLAUDE.md` records that the normaliser stalls when literal constants must be distributed
over sums. The `0` entries of the delay and integrator rows are cleared by rewriting before the
normaliser sees them, for the same reason. -/
theorem pid_complex_real_direction (rr sig om : Real) :
    -- the real eigendirection
    ((rr * (rr - 1)) * (rr + sig + sig - 1)
       + (rr * (rr * sig + rr * sig + (sig * sig + om * om) - rr - sig - sig + 1
                - rr * (sig * sig + om * om))) * (-1)
       + ((rr - 1) * (-(rr * (sig * sig + om * om)))) * 1
     = rr * (rr * (rr - 1)))
    ∧ ((rr * (rr - 1)) * (rr * sig + rr * sig + (sig * sig + om * om) - rr - sig - sig + 1
                          - rr * (sig * sig + om * om))
       + (rr * (rr * sig + rr * sig + (sig * sig + om * om) - rr - sig - sig + 1
                - rr * (sig * sig + om * om))) * 1
       + ((rr - 1) * (-(rr * (sig * sig + om * om)))) * 0
     = rr * (rr * (rr * sig + rr * sig + (sig * sig + om * om) - rr - sig - sig + 1
                   - rr * (sig * sig + om * om))))
    ∧ ((rr * (rr - 1)) * (-(rr * (sig * sig + om * om)))
       + (rr * (rr * sig + rr * sig + (sig * sig + om * om) - rr - sig - sig + 1
                - rr * (sig * sig + om * om))) * 0
       + ((rr - 1) * (-(rr * (sig * sig + om * om)))) * 0
     = rr * ((rr - 1) * (-(rr * (sig * sig + om * om))))) := by
  refine ⟨?_, ?_, ?_⟩
  · mach_mpoly [rr, sig, om]
  · rw [mul_zero, add_zero]; mach_mpoly [rr, sig, om]
  · rw [mul_zero, mul_zero, add_zero, add_zero]; mach_mpoly [rr, sig, om]


/-- **The three relations for the first real-Jordan functional**, `g₁·M = σ·g₁ − ω·g₂`. Ring
identities in `r, σ, ω`, like the real direction above. -/
theorem pid_complex_jordan_first (rr sig om : Real) :
    ((sig * sig - om * om - sig) * (rr + sig + sig - 1) + (sig * (rr * sig + rr * sig + (sig * sig +
    om * om) - rr - sig - sig + 1 - rr * (sig * sig + om * om))) * (-1) + ((sig - 1) * (-(rr *
    (sig * sig + om * om)))) * 1 = sig * (sig * sig - om * om - sig) - om * (sig * om + sig * om
    - om))
    ∧ ((sig * sig - om * om - sig) * (rr * sig + rr * sig + (sig * sig + om * om) - rr - sig - sig + 1
      - rr * (sig * sig + om * om)) + (sig * (rr * sig + rr * sig + (sig * sig + om * om) - rr -
      sig - sig + 1 - rr * (sig * sig + om * om))) * 1 + ((sig - 1) * (-(rr * (sig * sig + om *
      om)))) * 0 = sig * (sig * (rr * sig + rr * sig + (sig * sig + om * om) - rr - sig - sig +
      1 - rr * (sig * sig + om * om))) - om * (om * (rr * sig + rr * sig + (sig * sig + om * om)
      - rr - sig - sig + 1 - rr * (sig * sig + om * om))))
    ∧ ((sig * sig - om * om - sig) * (-(rr * (sig * sig + om * om))) + (sig * (rr * sig + rr * sig +
      (sig * sig + om * om) - rr - sig - sig + 1 - rr * (sig * sig + om * om))) * 0 + ((sig - 1)
      * (-(rr * (sig * sig + om * om)))) * 0 = sig * ((sig - 1) * (-(rr * (sig * sig + om *
      om)))) - om * (om * (-(rr * (sig * sig + om * om))))) := by
  refine ⟨?_, ?_, ?_⟩
  · mach_mpoly [rr, sig, om]
  · rw [mul_zero, add_zero]; mach_mpoly [rr, sig, om]
  · rw [mul_zero, mul_zero, add_zero, add_zero]; mach_mpoly [rr, sig, om]

/-- **The three relations for the second real-Jordan functional**, `g₂·M = ω·g₁ + σ·g₂`. With
`pid_complex_real_direction` and `pid_complex_jordan_first` this completes the nine, so
`n3_contract_of_eigen` applies to every PID design with one real eigenvalue and a complex pair. -/
theorem pid_complex_jordan_second (rr sig om : Real) :
    ((sig * om + sig * om - om) * (rr + sig + sig - 1) + (om * (rr * sig + rr * sig + (sig * sig +
    om * om) - rr - sig - sig + 1 - rr * (sig * sig + om * om))) * (-1) + (om * (-(rr * (sig *
    sig + om * om)))) * 1 = om * (sig * sig - om * om - sig) + sig * (sig * om + sig * om - om))
    ∧ ((sig * om + sig * om - om) * (rr * sig + rr * sig + (sig * sig + om * om) - rr - sig - sig + 1
      - rr * (sig * sig + om * om)) + (om * (rr * sig + rr * sig + (sig * sig + om * om) - rr -
      sig - sig + 1 - rr * (sig * sig + om * om))) * 1 + (om * (-(rr * (sig * sig + om * om))))
      * 0 = om * (sig * (rr * sig + rr * sig + (sig * sig + om * om) - rr - sig - sig + 1 - rr *
      (sig * sig + om * om))) + sig * (om * (rr * sig + rr * sig + (sig * sig + om * om) - rr -
      sig - sig + 1 - rr * (sig * sig + om * om))))
    ∧ ((sig * om + sig * om - om) * (-(rr * (sig * sig + om * om))) + (om * (rr * sig + rr * sig +
      (sig * sig + om * om) - rr - sig - sig + 1 - rr * (sig * sig + om * om))) * 0 + (om *
      (-(rr * (sig * sig + om * om)))) * 0 = om * ((sig - 1) * (-(rr * (sig * sig + om * om))))
      + sig * (om * (-(rr * (sig * sig + om * om))))) := by
  refine ⟨?_, ?_, ?_⟩
  · mach_mpoly [rr, sig, om]
  · rw [mul_zero, add_zero]; mach_mpoly [rr, sig, om]
  · rw [mul_zero, mul_zero, add_zero, add_zero]; mach_mpoly [rr, sig, om]


/-! ### A specimen — the contracting regime is reachable, at a genuinely complex design

Two questions a reader has, and neither is answered by argument. Are the two modulus hypotheses
`hr` and `hc` simultaneously satisfiable? And does any design land in the *contracting* regime,
given that the cross-term split costs a factor `(1+α)` on top of `max(r², σ²+ω²)`? -/

/-- **Both, at `r = e⁻¹`, `σ = 0`, `ω = e⁻¹`, with `α = β = 1`.**

`L = e⁻¹·e⁻¹` dominates both `r²` and `σ²+ω²` with equality, and the contraction factor
`(1+α)·L = 2e⁻²` is below one — proved with no numerics, reusing `QuadTracking`'s
`pi_complex_contraction_specimen`, whose quantity is literally the same one. The last conjunct is
`ω ≠ 0` in its positive form: the design is **genuinely complex**, so `n3` is a norm here rather
than a seminorm, and this is not the real case in disguise. -/
theorem pid_complex_contraction_specimen :
    (exp (-1) * exp (-1) ≤ exp (-1) * exp (-1))
    ∧ (0 * 0 + exp (-1) * exp (-1) ≤ exp (-1) * exp (-1))
    ∧ ((1 + 1) * (exp (-1) * exp (-1)) < 1)
    ∧ (0 < exp (-1)) := by
  refine ⟨le_refl _, ?_, ?_, exp_pos _⟩
  · rw [zero_mul, zero_add]
    exact le_refl _
  · have h := pi_complex_contraction_specimen
    rw [zero_mul, zero_add] at h
    exact h

end Real

end MachLib
