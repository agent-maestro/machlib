import MachLib.Geometry.Apollonius.SymmetricTriple

/-!
# The degree-drop locus is where an Apollonius circle becomes a **line**

`SymmetricTriple.lean` records that the `(o,i,i)` class quadratic has leading coefficient
`32ρ² − 4d²`, vanishing exactly at `d² = 8ρ²`, and that the middle coefficient `8d²ρ` stays positive
there — so the equation degenerates to a genuine linear one, not to a constant. That left the count
reading `8 → 7 → 8` across the locus, with no account of where the eighth solution went.

**It escapes to infinity.** Homogenising the radius as `r = R/S`,

```
A R² + B R S + C S² = 0,     A = 0  ⟹  S · (B R + C S) = 0
```

so projectively there are still two roots: the finite one `B R + C S = 0`, and `S = 0`, a solution of
infinite radius. A circle of infinite radius is a line, and in this configuration that line is
concrete.

## What the line is

An oriented line `{p : n·p = c}` with `|n| = 1` is tangent to the three unit-normal-signed circles
exactly when `n·cᵢ − c = sᵢ ρ`. For the `(o,i,i)` signs — outer at `A`, inner at `B` and `C` — the
centres `(0,0)`, `(d,0)`, `(0,d)` give `c = −ρ` and `n_x d = n_y d = −2ρ`. Multiplying `|n|² = 1`
through by `d²` turns the unit condition into

```
(n_x d)² + (n_y d)² = d²    ⟹    4ρ² + 4ρ² = d²    ⟹    d² = 8ρ²
```

with **no division**, which is why the proof below never needs `d ≠ 0` in that direction.

So `oii_lead_zero_iff_tangent_line`: the leading coefficient vanishes **if and only if** the class
admits a common tangent line. The `8 → 7 → 8` anomaly is an artefact of counting only finite
circles; in the compactified count it is `8 → 8 → 8`.

The other sign classes are not affected, and the arithmetic says why: the signs `(s₀,s₁,s₂)` force
`[(s₁−s₀)² + (s₂−s₀)²] ρ² = d²`, whose bracket is `0`, `4` or `8`. Only `(o,i,i)` — both companions
opposite to the first — produces `8`.
-/

namespace MachLib
namespace Geometry
namespace Apollonius
namespace SymmetricTriple

open Real

variable (d ρ : Real)

/-- **A common tangent line for the `(o,i,i)` class**: a unit normal `n` and offset `c` with the
first circle on one side and the other two on the other, all at distance `ρ`.

Written as an existential over the coefficients rather than through a `Line` structure, so that the
statement says exactly what it means and nothing is hidden in a definition. -/
def OIITangentLine : Prop :=
  ∃ nx ny c : Real,
    nx * nx + ny * ny = 1
    ∧ nx * 0 + ny * 0 - c = ρ
    ∧ nx * d + ny * 0 - c = -ρ
    ∧ nx * 0 + ny * d - c = -ρ

private theorem eq_of_mul_eq_mul_right {a b c : Real} (hc : c ≠ 0) (h : a * c = b * c) : a = b := by
  have ea : a * c * (1 / c) = a := by
    have e : a * c * (1 / c) = a * (c * (1 / c)) := by mach_mpoly [a, c, (1 : Real) / c]
    rw [e, mul_inv c hc]; mach_ring
  have eb : b * c * (1 / c) = b := by
    have e : b * c * (1 / c) = b * (c * (1 / c)) := by mach_mpoly [b, c, (1 : Real) / c]
    rw [e, mul_inv c hc]; mach_ring
  rw [← ea, ← eb, h]

private theorem div_mul_self {a c : Real} (hc : c ≠ 0) : a / c * c = a := by
  rw [div_def a c hc]
  have e : a * (1 / c) * c = a * (c * (1 / c)) := by mach_mpoly [a, c, (1 : Real) / c]
  rw [e, mul_inv c hc]; mach_ring

private theorem eq_of_sub_eq_zero {a b : Real} (h : a - b = 0) : b = a := by
  have v : a - b + b = 0 + b := by rw [h]
  have el : a - b + b = a := by mach_ring
  have er : (0 : Real) + b = b := by mach_ring
  rw [el, er] at v; exact v.symm

private theorem eq_zero_of_scaled_eq_zero {c z : Real} (hc : 0 < c) (h : c * z = 0) : z = 0 := by
  rcases lt_total 0 z with hz | hz | hz
  · exact absurd (h ▸ mul_pos hc hz) (lt_irrefl_ax 0)
  · exact hz.symm
  · exfalso
    have v := add_lt_add_left hz (-z)
    have l : -z + z = 0 := by mach_ring
    have r : -z + 0 = -z := by mach_ring
    rw [l, r] at v
    have hp := mul_pos hc v
    have e : c * -z = -(c * z) := by mach_ring
    rw [e, h] at hp
    have e0 : -(0 : Real) = 0 := by mach_ring
    rw [e0] at hp
    exact absurd hp (lt_irrefl_ax 0)

/-- **The tangent line exists exactly on the degree-drop locus.**

Both directions are elementary once the unit condition is cleared by `d²`; the forward direction
needs no hypothesis at all, and only the construction needs `d ≠ 0`. -/
theorem oii_tangent_line_iff (hd : 0 < d) :
    OIITangentLine d ρ ↔ d * d = (1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))) := by
  have hdne : d ≠ 0 := ne_of_gt hd
  constructor
  · rintro ⟨nx, ny, c, hunit, h0, h1, h2⟩
    -- `c = −ρ`, then `nx·d = ny·d = −2ρ`
    have hc : c = -ρ := by
      have e : nx * 0 + ny * 0 - c = -c := by mach_ring
      rw [e] at h0
      have v : -(-c) = -ρ := by rw [h0]
      have e2 : -(-c) = c := by mach_ring
      rw [e2] at v; exact v
    have hx : nx * d = -((1 + 1) * ρ) := by
      have e : nx * d + ny * 0 - c = nx * d - c := by mach_ring
      rw [e, hc] at h1
      have v : nx * d - -ρ + -ρ = -ρ + -ρ := by rw [h1]
      have el : nx * d - -ρ + -ρ = nx * d := by mach_mpoly [nx, d, ρ]
      have er : -ρ + -ρ = -((1 + 1) * ρ) := by mach_mpoly [ρ]
      rw [el, er] at v; exact v
    have hy : ny * d = -((1 + 1) * ρ) := by
      have e : nx * 0 + ny * d - c = ny * d - c := by mach_ring
      rw [e, hc] at h2
      have v : ny * d - -ρ + -ρ = -ρ + -ρ := by rw [h2]
      have el : ny * d - -ρ + -ρ = ny * d := by mach_mpoly [ny, d, ρ]
      have er : -ρ + -ρ = -((1 + 1) * ρ) := by mach_mpoly [ρ]
      rw [el, er] at v; exact v
    -- clear the unit condition by `d²`: `(nx·d)² + (ny·d)² = d²`
    have hclear : (nx * d) * (nx * d) + (ny * d) * (ny * d) = d * d := by
      have e : (nx * d) * (nx * d) + (ny * d) * (ny * d)
          = (nx * nx + ny * ny) * (d * d) := by mach_mpoly [nx, ny, d]
      rw [e, hunit]; mach_ring
    rw [hx, hy] at hclear
    have e : -((1 + 1) * ρ) * -((1 + 1) * ρ) + -((1 + 1) * ρ) * -((1 + 1) * ρ)
        = (1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))) := by mach_mpoly [ρ]
    rw [e] at hclear
    exact hclear.symm
  · intro hloc
    refine ⟨-((1 + 1) * ρ) / d, -((1 + 1) * ρ) / d, -ρ, ?_, ?_, ?_, ?_⟩
    · -- unit: multiply through by `d²` and use the locus
      refine eq_of_mul_eq_mul_right (c := d * d) (ne_of_gt (mul_pos hd hd)) ?_
      have hnd : -((1 + 1) * ρ) / d * d = -((1 + 1) * ρ) := div_mul_self hdne
      have e : (-((1 + 1) * ρ) / d * (-((1 + 1) * ρ) / d)
            + -((1 + 1) * ρ) / d * (-((1 + 1) * ρ) / d)) * (d * d)
          = (-((1 + 1) * ρ) / d * d) * (-((1 + 1) * ρ) / d * d)
            + (-((1 + 1) * ρ) / d * d) * (-((1 + 1) * ρ) / d * d) := by
        mach_mpoly [-((1 + 1) * ρ) / d, d]
      rw [e, hnd]
      have e2 : -((1 + 1) * ρ) * -((1 + 1) * ρ) + -((1 + 1) * ρ) * -((1 + 1) * ρ)
          = (1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))) := by mach_mpoly [ρ]
      rw [e2, ← hloc]; mach_ring
    · mach_mpoly [-((1 + 1) * ρ) / d, ρ]
    · have hnd : -((1 + 1) * ρ) / d * d = -((1 + 1) * ρ) := div_mul_self hdne
      have e : -((1 + 1) * ρ) / d * d + -((1 + 1) * ρ) / d * 0 - -ρ
          = -((1 + 1) * ρ) / d * d + ρ := by mach_mpoly [-((1 + 1) * ρ) / d, d, ρ]
      rw [e, hnd]; mach_ring
    · have hnd : -((1 + 1) * ρ) / d * d = -((1 + 1) * ρ) := div_mul_self hdne
      have e : -((1 + 1) * ρ) / d * 0 + -((1 + 1) * ρ) / d * d - -ρ
          = -((1 + 1) * ρ) / d * d + ρ := by mach_mpoly [-((1 + 1) * ρ) / d, d, ρ]
      rw [e, hnd]; mach_ring

/-- **The leading coefficient vanishes exactly at `d² = 8ρ²`.** -/
theorem oii_lead_zero_iff :
    QMlead d ρ classOII = 0 ↔ d * d = (1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ))) := by
  rw [classOII, QMlead_oii_factored]
  have h2 : (0 : Real) < 1 + 1 := add_pos zero_lt_one_ax zero_lt_one_ax
  constructor
  · intro h
    exact eq_of_sub_eq_zero (eq_zero_of_scaled_eq_zero h2 (eq_zero_of_scaled_eq_zero h2 h))
  · intro h; rw [← h]; mach_ring

/-- **The punchline.** The `(o,i,i)` class quadratic drops degree **if and only if** the class
admits a common tangent *line*.

So the exceptional locus is not an algebraic accident. The eighth solution has not collided with
another finite circle and disappeared; it has become a circle of infinite radius, which is a line. In
the compactified count the anomaly `8 → 7 → 8` is `8 → 8 → 8` throughout. -/
theorem oii_lead_zero_iff_tangent_line (hd : 0 < d) :
    QMlead d ρ classOII = 0 ↔ OIITangentLine d ρ := by
  rw [oii_lead_zero_iff d ρ, ← oii_tangent_line_iff d ρ hd]

/-- **A concrete witness, without square roots.** Take `ρ` with `d · d = 8ρ²`; the common tangent is
`n = (−2ρ/d, −2ρ/d)`, `c = −ρ`. For `ρ = 1` and `d² = 8` this is the line `x + y = √2`. -/
theorem oii_tangent_line_at_locus (hd : 0 < d)
    (hloc : d * d = (1 + 1) * ((1 + 1) * ((1 + 1) * (ρ * ρ)))) : OIITangentLine d ρ :=
  (oii_tangent_line_iff d ρ hd).mpr hloc

/-! ## Discrimination: the locus is class-specific

If every sign class degenerated at `d² = 8ρ²` the theorem would be about lines, not about this class.
It does not. Flipping one companion sign moves the locus to `4ρ²`, which is exactly the arithmetic
`[(s₁−s₀)² + (s₂−s₀)²] ρ² = d²` predicts. -/

/-- The `(o,i,o)` signs: opposite at `B`, aligned at `C`. -/
def OIOTangentLine : Prop :=
  ∃ nx ny c : Real,
    nx * nx + ny * ny = 1
    ∧ nx * 0 + ny * 0 - c = ρ
    ∧ nx * d + ny * 0 - c = -ρ
    ∧ nx * 0 + ny * d - c = ρ

/-- **A different class, a different locus.** `(o,i,o)` admits a common tangent line exactly at
`d² = 4ρ²` — so `8ρ²` is a fact about `(o,i,i)` and not about the configuration. -/
theorem oio_tangent_line_iff (hd : 0 < d) :
    OIOTangentLine d ρ ↔ d * d = (1 + 1) * ((1 + 1) * (ρ * ρ)) := by
  have hdne : d ≠ 0 := ne_of_gt hd
  constructor
  · rintro ⟨nx, ny, c, hunit, h0, h1, h2⟩
    have hc : c = -ρ := by
      have e : nx * 0 + ny * 0 - c = -c := by mach_ring
      rw [e] at h0
      have v : -(-c) = -ρ := by rw [h0]
      have e2 : -(-c) = c := by mach_ring
      rw [e2] at v; exact v
    have hx : nx * d = -((1 + 1) * ρ) := by
      have e : nx * d + ny * 0 - c = nx * d - c := by mach_ring
      rw [e, hc] at h1
      have v : nx * d - -ρ + -ρ = -ρ + -ρ := by rw [h1]
      have el : nx * d - -ρ + -ρ = nx * d := by mach_mpoly [nx, d, ρ]
      have er : -ρ + -ρ = -((1 + 1) * ρ) := by mach_mpoly [ρ]
      rw [el, er] at v; exact v
    have hy : ny * d = 0 := by
      have e : nx * 0 + ny * d - c = ny * d - c := by mach_ring
      rw [e, hc] at h2
      have v : ny * d - -ρ + -ρ = ρ + -ρ := by rw [h2]
      have el : ny * d - -ρ + -ρ = ny * d := by mach_mpoly [ny, d, ρ]
      have er : ρ + -ρ = (0 : Real) := by mach_ring
      rw [el, er] at v; exact v
    have hclear : (nx * d) * (nx * d) + (ny * d) * (ny * d) = d * d := by
      have e : (nx * d) * (nx * d) + (ny * d) * (ny * d)
          = (nx * nx + ny * ny) * (d * d) := by mach_mpoly [nx, ny, d]
      rw [e, hunit]; mach_ring
    rw [hx, hy] at hclear
    have e : -((1 + 1) * ρ) * -((1 + 1) * ρ) + (0 : Real) * 0
        = (1 + 1) * ((1 + 1) * (ρ * ρ)) := by mach_mpoly [ρ]
    rw [e] at hclear
    exact hclear.symm
  · intro hloc
    refine ⟨-((1 + 1) * ρ) / d, 0, -ρ, ?_, ?_, ?_, ?_⟩
    · refine eq_of_mul_eq_mul_right (c := d * d) (ne_of_gt (mul_pos hd hd)) ?_
      have hnd : -((1 + 1) * ρ) / d * d = -((1 + 1) * ρ) := div_mul_self hdne
      have e : (-((1 + 1) * ρ) / d * (-((1 + 1) * ρ) / d) + (0 : Real) * 0) * (d * d)
          = (-((1 + 1) * ρ) / d * d) * (-((1 + 1) * ρ) / d * d) := by
        mach_mpoly [-((1 + 1) * ρ) / d, d]
      rw [e, hnd]
      have e2 : -((1 + 1) * ρ) * -((1 + 1) * ρ) = (1 + 1) * ((1 + 1) * (ρ * ρ)) := by
        mach_mpoly [ρ]
      rw [e2, ← hloc]; mach_ring
    · mach_mpoly [-((1 + 1) * ρ) / d, ρ]
    · have hnd : -((1 + 1) * ρ) / d * d = -((1 + 1) * ρ) := div_mul_self hdne
      have e : -((1 + 1) * ρ) / d * d + (0 : Real) * 0 - -ρ
          = -((1 + 1) * ρ) / d * d + ρ := by mach_mpoly [-((1 + 1) * ρ) / d, ρ]
      rw [e, hnd]; mach_ring
    · mach_mpoly [-((1 + 1) * ρ) / d, ρ]

end SymmetricTriple
end Apollonius
end Geometry
end MachLib
