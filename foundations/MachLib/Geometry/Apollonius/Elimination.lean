import MachLib.Geometry.Apollonius.Mode
import MachLib.QuadraticRoots

/-!
# The linearisation, for arbitrary input circles

`SymmetricTriple` did one class of one family concretely. This does the step that is actually
general: **the difference of any two tangency equations is linear**, so the three-equation system is
one quadratic equation plus a 2×2 linear system, whatever the inputs and whatever the mode.

## What forces the general-position hypothesis

Nothing here chooses a genericity condition. Cramer's rule needs its determinant nonzero, the
determinant of this particular system works out to `4·(twice the signed area of the triangle of
centres)`, and so the hypothesis that appears is exactly

    the three centres are not collinear

— independent of the radii, and independent of the mode. That is the whole reason to write the
elimination before defining `ApolloniusGeneralPosition`: had the definition been written first it
would have been a plausible guess, and this is a derivation.

Note what is *not* here. Substituting the Cramer centre back into the first equation yields the
quadratic in `r`, but its coefficients in full generality are a twelve-variable expression, and
`mach_mpoly` is not the tool for that (the corpus gotcha "keep coefficients symbolic" is a warning
about exactly this scale). The reduction to *one equation in `r` alone* is proved here; naming its
coefficients is a separate step, and `SymmetricTriple` shows what that looks like when the family is
concrete enough to write them down.
-/

namespace MachLib
namespace Geometry
namespace Apollonius

open Real

/-- **The difference of two tangency equations is linear.**

The quadratic part `x² + y² − r²` is common to every tangency equation and cancels; what survives
is linear in `x`, `y` and `r` with coefficients built from the centres, the radii and the two signs.
This is the linearisation, stated once for arbitrary circles and signs rather than per configuration. -/
theorem tangentEq_iff_linear (p₁ p₂ π q₁ q₂ κ : Real) (s t : Sign) (x y r : Real)
    (hP : tangentEq p₁ p₂ π s x y r) :
    tangentEq q₁ q₂ κ t x y r
      ↔ (1 + 1) * (q₁ - p₁) * x + (1 + 1) * (q₂ - p₂) * y
          + (1 + 1) * (t.val * κ - s.val * π) * r
        = (q₁ * q₁ + q₂ * q₂ - κ * κ) - (p₁ * p₁ + p₂ * p₂ - π * π) := by
  rw [tangentEq_expanded] at hP
  rw [tangentEq_expanded]
  constructor
  · intro hQ
    refine QuadraticRoots.eq_of_sub_eq_zero ?_
    have e : (1 + 1) * (q₁ - p₁) * x + (1 + 1) * (q₂ - p₂) * y
          + (1 + 1) * (t.val * κ - s.val * π) * r
        - ((q₁ * q₁ + q₂ * q₂ - κ * κ) - (p₁ * p₁ + p₂ * p₂ - π * π))
        = (((x - p₁) * (x - p₁) + (y - p₂) * (y - p₂))
            - (r * r + (1 + 1) * (s.val * π) * r + π * π))
          - (((x - q₁) * (x - q₁) + (y - q₂) * (y - q₂))
            - (r * r + (1 + 1) * (t.val * κ) * r + κ * κ)) := by
      mach_mpoly [x, y, r, p₁, p₂, π, q₁, q₂, κ, s.val, t.val]
    rw [e, hP, hQ]
    mach_mpoly [r, s.val, t.val, π, κ]
  · intro hlin
    refine QuadraticRoots.eq_of_sub_eq_zero ?_
    have e : ((x - q₁) * (x - q₁) + (y - q₂) * (y - q₂))
          - (r * r + (1 + 1) * (t.val * κ) * r + κ * κ)
        = (((x - p₁) * (x - p₁) + (y - p₂) * (y - p₂))
            - (r * r + (1 + 1) * (s.val * π) * r + π * π))
          - ((1 + 1) * (q₁ - p₁) * x + (1 + 1) * (q₂ - p₂) * y
             + (1 + 1) * (t.val * κ - s.val * π) * r
             - ((q₁ * q₁ + q₂ * q₂ - κ * κ) - (p₁ * p₁ + p₂ * p₂ - π * π))) := by
      mach_mpoly [x, y, r, p₁, p₂, π, q₁, q₂, κ, s.val, t.val]
    rw [e, hP, hlin]
    mach_mpoly [r, s.val, t.val, π, κ, p₁, p₂, q₁, q₂] <;> mach_ring

/-- **Twice the signed area of the triangle of centres.** Vanishes exactly when the centres are
collinear. -/
noncomputable def centresDet (A B C : Circle) : Real :=
  (B.x - A.x) * (C.y - A.y) - (B.y - A.y) * (C.x - A.x)

/-- The three centres are collinear. Named as the *negation* of what the elimination needs, so the
general-position hypothesis reads as a geometric statement rather than as a determinant condition. -/
def CentresCollinear (A B C : Circle) : Prop := centresDet A B C = 0

/-- **The system is one equation plus a 2×2 linear system**, for any inputs and any mode. -/
theorem solvesMode_iff_linear (A B C : Circle) (m : Mode) (x y r : Real) :
    SolvesMode A B C m x y r
      ↔ (tangentEq A.x A.y A.r m.sA x y r
          ∧ ((1 + 1) * (B.x - A.x) * x + (1 + 1) * (B.y - A.y) * y
              + (1 + 1) * (m.sB.val * B.r - m.sA.val * A.r) * r
             = (B.x * B.x + B.y * B.y - B.r * B.r) - (A.x * A.x + A.y * A.y - A.r * A.r))
          ∧ ((1 + 1) * (C.x - A.x) * x + (1 + 1) * (C.y - A.y) * y
              + (1 + 1) * (m.sC.val * C.r - m.sA.val * A.r) * r
             = (C.x * C.x + C.y * C.y - C.r * C.r) - (A.x * A.x + A.y * A.y - A.r * A.r))) := by
  constructor
  · rintro ⟨hA, hB, hC⟩
    exact ⟨hA,
      (tangentEq_iff_linear A.x A.y A.r B.x B.y B.r m.sA m.sB x y r hA).mp hB,
      (tangentEq_iff_linear A.x A.y A.r C.x C.y C.r m.sA m.sC x y r hA).mp hC⟩
  · rintro ⟨hA, hB, hC⟩
    exact ⟨hA,
      (tangentEq_iff_linear A.x A.y A.r B.x B.y B.r m.sA m.sB x y r hA).mpr hB,
      (tangentEq_iff_linear A.x A.y A.r C.x C.y C.r m.sA m.sC x y r hA).mpr hC⟩


/-- **The linear system's determinant is `4·centresDet`.**

This is the sentence the whole module exists to produce. The 2×2 system that the linearisation
leaves behind is nonsingular exactly when the three *centres* are not collinear — a condition on the
centres alone, independent of the radii and independent of the mode. No genericity assumption was
chosen; this one was computed. -/
theorem linear_det (A B C : Circle) :
    ((1 + 1) * (B.x - A.x)) * ((1 + 1) * (C.y - A.y))
      - ((1 + 1) * (B.y - A.y)) * ((1 + 1) * (C.x - A.x))
    = (1 + 1) * (1 + 1) * centresDet A B C := by
  unfold centresDet; mach_mpoly [A.x, A.y, B.x, B.y, C.x, C.y]

private theorem four_ne_zero : ((1 : Real) + 1) * (1 + 1) ≠ 0 :=
  ne_of_gt (mul_pos (add_pos zero_lt_one_ax zero_lt_one_ax)
                    (add_pos zero_lt_one_ax zero_lt_one_ax))

/-- **Non-collinear centres pin the centre of a solution to its radius.**

Two solutions of the *same* mode with the *same* radius are the same circle. The proof is the
homogeneous case of Cramer: the difference of the two centres satisfies the linear system with zero
right-hand side, and a nonsingular system has only the trivial solution.

This is where non-collinearity earns its keep, and it is the first half of distinctness — after it,
telling two solutions apart reduces to telling their radii apart. -/
theorem centre_unique (A B C : Circle) (m : Mode) (hcol : ¬ CentresCollinear A B C)
    (x₁ y₁ x₂ y₂ r : Real)
    (h₁ : SolvesMode A B C m x₁ y₁ r) (h₂ : SolvesMode A B C m x₂ y₂ r) :
    x₁ = x₂ ∧ y₁ = y₂ := by
  have hdet : ((1 + 1) * (B.x - A.x)) * ((1 + 1) * (C.y - A.y))
      - ((1 + 1) * (B.y - A.y)) * ((1 + 1) * (C.x - A.x)) ≠ 0 := by
    rw [linear_det]
    intro h
    exact hcol (QuadraticRoots.right_of_mul_eq_zero four_ne_zero h)
  obtain ⟨_, hB₁, hC₁⟩ := (solvesMode_iff_linear A B C m x₁ y₁ r).mp h₁
  obtain ⟨_, hB₂, hC₂⟩ := (solvesMode_iff_linear A B C m x₂ y₂ r).mp h₂
  -- the difference of the centres solves the homogeneous system
  have hhB : (1 + 1) * (B.x - A.x) * (x₁ - x₂) + (1 + 1) * (B.y - A.y) * (y₁ - y₂) = 0 := by
    have e : (1 + 1) * (B.x - A.x) * (x₁ - x₂) + (1 + 1) * (B.y - A.y) * (y₁ - y₂)
        = ((1 + 1) * (B.x - A.x) * x₁ + (1 + 1) * (B.y - A.y) * y₁
            + (1 + 1) * (m.sB.val * B.r - m.sA.val * A.r) * r)
          - ((1 + 1) * (B.x - A.x) * x₂ + (1 + 1) * (B.y - A.y) * y₂
            + (1 + 1) * (m.sB.val * B.r - m.sA.val * A.r) * r) := by
      mach_mpoly [A.x, A.y, B.x, B.y, x₁, x₂, y₁, y₂, r, m.sA.val, m.sB.val, A.r, B.r]
    rw [e, hB₁, hB₂]
    mach_mpoly [A.x, A.y, A.r, B.x, B.y, B.r]
  have hhC : (1 + 1) * (C.x - A.x) * (x₁ - x₂) + (1 + 1) * (C.y - A.y) * (y₁ - y₂) = 0 := by
    have e : (1 + 1) * (C.x - A.x) * (x₁ - x₂) + (1 + 1) * (C.y - A.y) * (y₁ - y₂)
        = ((1 + 1) * (C.x - A.x) * x₁ + (1 + 1) * (C.y - A.y) * y₁
            + (1 + 1) * (m.sC.val * C.r - m.sA.val * A.r) * r)
          - ((1 + 1) * (C.x - A.x) * x₂ + (1 + 1) * (C.y - A.y) * y₂
            + (1 + 1) * (m.sC.val * C.r - m.sA.val * A.r) * r) := by
      mach_mpoly [A.x, A.y, C.x, C.y, x₁, x₂, y₁, y₂, r, m.sA.val, m.sC.val, A.r, C.r]
    rw [e, hC₁, hC₂]
    mach_mpoly [A.x, A.y, A.r, C.x, C.y, C.r]
  obtain ⟨hx, hy⟩ := (QuadraticRoots.cramer_2x2 hdet).mp ⟨hhB, hhC⟩
  constructor
  · refine QuadraticRoots.eq_of_sub_eq_zero (QuadraticRoots.right_of_mul_eq_zero hdet ?_)
    rw [hx]; mach_mpoly [A.x, A.y, B.y, C.y]
  · refine QuadraticRoots.eq_of_sub_eq_zero (QuadraticRoots.right_of_mul_eq_zero hdet ?_)
    rw [hy]; mach_mpoly [A.x, A.y, B.x, C.x]


/-! ## The general reduction: arbitrary non-collinear triple → one quadratic

`solvesMode_iff_linear` turns three tangency equations into one tangency equation plus two linear
equations, and `centre_unique` solves those for the centre whenever the centres are not collinear.
What remained was substituting that centre back and reading off the quadratic in `r` — and that step
had been abandoned twice as "the coefficients explode".

**They do not.** The explosion came from expanding the geometry into coordinates before normalising.
Stated over the *abstract* Cramer data — the determinant `D`, the numerator pairs `(X₀, X₁)`,
`(Y₀, Y₁)`, and the centre offsets `U`, `V` — the reduction is a short polynomial identity in eight
atoms with no constant above `1`.

This is the same principle that closed the concrete coordinates: **normalise the abstraction, not the
expansion.** -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
/-- **The Apollonius quadratic, for an arbitrary triple.**

Given a centre determined affinely by the radius — `D·x = X₀ + X₁r`, `D·y = Y₀ + Y₁r`, which is what
Cramer's rule supplies when `D ≠ 0` — the remaining tangency equation to circle `(p, q, π)` at mode
sign `sv` is, after clearing `D²`, exactly

```
    (X₁² + Y₁² − D²)·r²  +  (2UX₁ + 2VY₁ − 2D²·svπ)·r  +  (U² + V² − D²π²)  =  0
```

with `U = X₀ − Dp`, `V = Y₀ − Dq`. No hypothesis about the configuration is used beyond `sv² = 1`,
so this holds for **every** triple and **every** mode; non-collinearity enters only where `D ≠ 0` is
needed to produce the affine centre in the first place. -/
theorem quadratic_of_linear (D X₀ X₁ Y₀ Y₁ p q π sv x y r U V : Real)
    (hx : D * x = X₀ + X₁ * r) (hy : D * y = Y₀ + Y₁ * r) (hs : sv * sv = 1)
    (hU : U = X₀ - D * p) (hV : V = Y₀ - D * q) :
    D * D * ((x - p) * (x - p) + (y - q) * (y - q) - (r + sv * π) * (r + sv * π))
      = (X₁ * X₁ + Y₁ * Y₁ - D * D) * (r * r)
        + ((1 + 1) * (U * X₁) + (1 + 1) * (V * Y₁) - (1 + 1) * (D * D) * (sv * π)) * r
        + (U * U + V * V - D * D * (π * π)) := by
  have ex : D * D * ((x - p) * (x - p)) = (D * x - D * p) * (D * x - D * p) := by mach_ring
  have ey : D * D * ((y - q) * (y - q)) = (D * y - D * q) * (D * y - D * q) := by mach_ring
  have er : D * D * ((r + sv * π) * (r + sv * π))
      = D * D * (r * r) + (1 + 1) * (D * D) * (sv * π) * r + D * D * ((sv * sv) * (π * π)) := by
    mach_ring
  have split : D * D * ((x - p) * (x - p) + (y - q) * (y - q) - (r + sv * π) * (r + sv * π))
      = D * D * ((x - p) * (x - p)) + D * D * ((y - q) * (y - q))
        - D * D * ((r + sv * π) * (r + sv * π)) := by mach_ring
  rw [split, ex, ey, er, hx, hy, hs]
  have gx : X₀ + X₁ * r - D * p = U + X₁ * r := by rw [hU]; mach_ring
  have gy : Y₀ + Y₁ * r - D * q = V + Y₁ * r := by rw [hV]; mach_ring
  rw [gx, gy]
  mach_mpoly [U, V, X₁, Y₁, D, r, sv, π]

/-- **The tangency holds iff the quadratic vanishes**, given `D ≠ 0`. The `D²` scaling is invertible,
so nothing is lost by clearing it. -/
theorem solves_iff_quadratic (D X₀ X₁ Y₀ Y₁ p q π sv x y r U V : Real) (hD : D ≠ 0)
    (hx : D * x = X₀ + X₁ * r) (hy : D * y = Y₀ + Y₁ * r) (hs : sv * sv = 1)
    (hU : U = X₀ - D * p) (hV : V = Y₀ - D * q) :
    ((x - p) * (x - p) + (y - q) * (y - q) = (r + sv * π) * (r + sv * π))
    ↔ (X₁ * X₁ + Y₁ * Y₁ - D * D) * (r * r)
        + ((1 + 1) * (U * X₁) + (1 + 1) * (V * Y₁) - (1 + 1) * (D * D) * (sv * π)) * r
        + (U * U + V * V - D * D * (π * π)) = 0 := by
  have key := quadratic_of_linear D X₀ X₁ Y₀ Y₁ p q π sv x y r U V hx hy hs hU hV
  have hD2 : D * D ≠ 0 := fun h => hD (QuadraticRoots.right_of_mul_eq_zero hD h)
  constructor
  · intro h
    have z : (x - p) * (x - p) + (y - q) * (y - q) - (r + sv * π) * (r + sv * π) = 0 := by
      rw [h]; mach_ring
    rw [← key, z]; mach_ring
  · intro h
    refine QuadraticRoots.eq_of_sub_eq_zero ?_
    refine QuadraticRoots.mul_left_cancel hD2 ?_
    rw [key, h]; mach_ring

end Apollonius
end Geometry
end MachLib
