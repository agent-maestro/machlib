/-
`GaussianLaplaceRoute.lean` — the √π project's FINAL piece: pinning `I² = π/4` where
`I := gaussianImproperIntegral = ∫₀^∞exp(-t²)dt`.

Why (pivot, 2026-07-25): the disk/square sandwich (`GaussianDiskSandwich.lean`,
`D(R)≤S(R)≤D(R√2)`, CLOSED) doesn't close on its own — its own derivative in `R` leaves a
non-elementary residual (needs genuine 2D polar coordinates this codebase doesn't have). Pivoted
to a Laplace/Feynman parameter-differentiation route instead, verified on paper first (see the
`project_sqrtpi_laplace_route_2026_07_25` memory note for full design):

```
F(t) := gaussianI(t)²,  G(t) := ∫₀¹ exp(-t²(1+x²))/(1+x²) dx
F'(t) = 2·exp(-t²)·gaussianI(t)          (product rule + FTC1)
G'(t) = -F'(t)                            (linear substitution u=tx, no singularity)
⟹ F+G constant ⟹ I² = F(0)+G(0)-F(∞)-G(∞)... = ∫₀¹dx/(1+x²)
```
and `∫₀¹dx/(1+x²) = π/4` WITHOUT `atan` (which has zero π-connection in MachLib, would need a new
axiom) via `H(θ):=∫₀^{tanθ}dx/(1+x²)`, `H'(θ)=1` (FTC1+chain rule, pythagorean cancels exactly), so
`H(θ)=θ`, giving `H(π/4)=π/4=∫₀¹dx/(1+x²)` once `tan(π/4)=1`.

This file starts with `tan(π/4)=1` — self-contained, zero dependencies on the harder pieces, using
only `cos_add`/`sin_add` at `π/4+π/4=π/2` plus the existing `cos(π/2)=0`/`sin(π/2)=1` axioms, and
`MachLib.TanLipschitz`'s already-derived `cos_pos_of_lt_pi_div_two` (no need to re-derive `cos`
positivity from scratch). Zero new axioms.

`sorryAx`-free, no new axioms (so far).
-/
import MachLib.TanLipschitz
import MachLib.SinNotInEML
import MachLib.CosNotInEML
import MachLib.RiemannIntervalMonotone

namespace MachLib
namespace Real

/-! ## §1 — `tan(π/4) = 1` -/

private theorem eq_of_sub_eq_zero_laplace {a b : Real} (h : a - b = 0) : a = b := by
  have h2 : a - b + b = a := by mach_mpoly [a, b]
  rw [h, zero_add] at h2
  exact h2.symm

/-- `π/4 + π/4 = π/2`, using the codebase's convention `pi/(1+1)` for `π/2` and
`pi/(1+1)/(1+1)` for `π/4`. -/
theorem piQuarter_add_piQuarter :
    pi / (1 + 1) / (1 + 1) + pi / (1 + 1) / (1 + 1) = pi / (1 + 1) := by
  rw [← mul_two_eq_add_self (pi / (1 + 1) / (1 + 1))]
  exact div_mul_cancel (ne_of_gt two_pos)

theorem piQuarter_pos : 0 < pi / (1 + 1) / (1 + 1) :=
  div_pos_of_pos_pos (div_pos_of_pos_pos pi_pos two_pos) two_pos

theorem piQuarter_lt_pi_div_two : pi / (1 + 1) / (1 + 1) < pi / (1 + 1) := by
  have h1 := add_lt_add_left piQuarter_pos (pi / (1 + 1) / (1 + 1))
  rw [add_zero, piQuarter_add_piQuarter] at h1
  exact h1

theorem cos_piQuarter_pos : 0 < cos (pi / (1 + 1) / (1 + 1)) :=
  cos_pos_of_lt_pi_div_two (le_of_lt piQuarter_pos) piQuarter_lt_pi_div_two

theorem cos_piQuarter_ne_zero : cos (pi / (1 + 1) / (1 + 1)) ≠ 0 :=
  ne_of_gt cos_piQuarter_pos

/-- `cos²(π/4) = sin²(π/4)`, from `cos(π/2) = cos²(π/4) - sin²(π/4) = 0`. -/
theorem cos_sq_piQuarter_eq_sin_sq_piQuarter :
    cos (pi / (1 + 1) / (1 + 1)) * cos (pi / (1 + 1) / (1 + 1))
      = sin (pi / (1 + 1) / (1 + 1)) * sin (pi / (1 + 1) / (1 + 1)) := by
  have h1 := cos_add (pi / (1 + 1) / (1 + 1)) (pi / (1 + 1) / (1 + 1))
  rw [piQuarter_add_piQuarter, cos_pi_div_two] at h1
  exact eq_of_sub_eq_zero_laplace h1.symm

/-- `sin(π/4)·cos(π/4) = 1/2`, from `sin(π/2) = 2·sin(π/4)cos(π/4) = 1`. -/
theorem sin_mul_cos_piQuarter :
    sin (pi / (1 + 1) / (1 + 1)) * cos (pi / (1 + 1) / (1 + 1)) = 1 / (1 + 1) := by
  have h1 := sin_add (pi / (1 + 1) / (1 + 1)) (pi / (1 + 1) / (1 + 1))
  rw [piQuarter_add_piQuarter, sin_pi_div_two] at h1
  have h2 : sin (pi / (1 + 1) / (1 + 1)) * cos (pi / (1 + 1) / (1 + 1))
      + sin (pi / (1 + 1) / (1 + 1)) * cos (pi / (1 + 1) / (1 + 1)) = 1 := by
    rw [mul_comm (cos (pi / (1 + 1) / (1 + 1))) (sin (pi / (1 + 1) / (1 + 1)))] at h1
    exact h1.symm
  rw [← mul_two_eq_add_self (sin (pi / (1 + 1) / (1 + 1)) * cos (pi / (1 + 1) / (1 + 1)))] at h2
  exact eq_div_of_mul_eq (ne_of_gt two_pos) h2

theorem tan_piQuarter_pos : 0 < tan (pi / (1 + 1) / (1 + 1)) := by
  have htandef : tan (pi / (1 + 1) / (1 + 1))
      = sin (pi / (1 + 1) / (1 + 1)) / cos (pi / (1 + 1) / (1 + 1)) :=
    tan_def (pi / (1 + 1) / (1 + 1)) cos_piQuarter_ne_zero
  have hstep : tan (pi / (1 + 1) / (1 + 1)) * (cos (pi / (1 + 1) / (1 + 1))
      * cos (pi / (1 + 1) / (1 + 1))) = 1 / (1 + 1) := by
    rw [htandef, div_def (sin (pi / (1 + 1) / (1 + 1))) (cos (pi / (1 + 1) / (1 + 1)))
      cos_piQuarter_ne_zero]
    rw [show sin (pi / (1 + 1) / (1 + 1)) * (1 / cos (pi / (1 + 1) / (1 + 1)))
        * (cos (pi / (1 + 1) / (1 + 1)) * cos (pi / (1 + 1) / (1 + 1)))
        = sin (pi / (1 + 1) / (1 + 1)) * cos (pi / (1 + 1) / (1 + 1))
          * ((1 / cos (pi / (1 + 1) / (1 + 1))) * cos (pi / (1 + 1) / (1 + 1)))
        from by mach_mpoly [sin (pi / (1 + 1) / (1 + 1)), cos (pi / (1 + 1) / (1 + 1)),
          (1 / cos (pi / (1 + 1) / (1 + 1)) : Real)]]
    rw [div_mul_cancel cos_piQuarter_ne_zero, mul_one_ax]
    exact sin_mul_cos_piQuarter
  have hthird : (0 : Real) < 1 / (1 + 1) := div_pos_of_pos_pos one_pos two_pos
  rw [← hstep] at hthird
  have hcc : 0 < cos (pi / (1 + 1) / (1 + 1)) * cos (pi / (1 + 1) / (1 + 1)) :=
    mul_pos cos_piQuarter_pos cos_piQuarter_pos
  exact pos_of_mul_pos_right hthird hcc

theorem tan_piQuarter_sq_eq_one :
    tan (pi / (1 + 1) / (1 + 1)) * tan (pi / (1 + 1) / (1 + 1)) = 1 := by
  have htandef : tan (pi / (1 + 1) / (1 + 1))
      = sin (pi / (1 + 1) / (1 + 1)) / cos (pi / (1 + 1) / (1 + 1)) :=
    tan_def (pi / (1 + 1) / (1 + 1)) cos_piQuarter_ne_zero
  have hcc : cos (pi / (1 + 1) / (1 + 1)) * cos (pi / (1 + 1) / (1 + 1)) ≠ 0 :=
    mul_ne_zero cos_piQuarter_ne_zero cos_piQuarter_ne_zero
  have hstep : tan (pi / (1 + 1) / (1 + 1)) * tan (pi / (1 + 1) / (1 + 1))
      * (cos (pi / (1 + 1) / (1 + 1)) * cos (pi / (1 + 1) / (1 + 1)))
      = sin (pi / (1 + 1) / (1 + 1)) * sin (pi / (1 + 1) / (1 + 1)) := by
    rw [htandef, div_def (sin (pi / (1 + 1) / (1 + 1))) (cos (pi / (1 + 1) / (1 + 1)))
      cos_piQuarter_ne_zero]
    rw [show sin (pi / (1 + 1) / (1 + 1)) * (1 / cos (pi / (1 + 1) / (1 + 1)))
        * (sin (pi / (1 + 1) / (1 + 1)) * (1 / cos (pi / (1 + 1) / (1 + 1))))
        * (cos (pi / (1 + 1) / (1 + 1)) * cos (pi / (1 + 1) / (1 + 1)))
        = sin (pi / (1 + 1) / (1 + 1)) * sin (pi / (1 + 1) / (1 + 1))
          * ((1 / cos (pi / (1 + 1) / (1 + 1))) * cos (pi / (1 + 1) / (1 + 1))
            * ((1 / cos (pi / (1 + 1) / (1 + 1))) * cos (pi / (1 + 1) / (1 + 1))))
        from by mach_mpoly [sin (pi / (1 + 1) / (1 + 1)),
          (1 / cos (pi / (1 + 1) / (1 + 1)) : Real), cos (pi / (1 + 1) / (1 + 1))]]
    rw [div_mul_cancel cos_piQuarter_ne_zero, mul_one_ax, mul_one_ax]
  rw [← cos_sq_piQuarter_eq_sin_sq_piQuarter] at hstep
  have hstep2 : tan (pi / (1 + 1) / (1 + 1)) * tan (pi / (1 + 1) / (1 + 1))
      * (cos (pi / (1 + 1) / (1 + 1)) * cos (pi / (1 + 1) / (1 + 1)))
      = 1 * (cos (pi / (1 + 1) / (1 + 1)) * cos (pi / (1 + 1) / (1 + 1))) := by
    rw [one_mul_thm]; exact hstep
  exact mul_right_cancel' hcc hstep2

private theorem eq_one_of_pos_of_mul_self_eq_one {x : Real} (hx : 0 < x) (hxx : x * x = 1) :
    x = 1 := by
  rcases lt_total x 1 with h | h | h
  · exfalso
    have h1 : x * x < x * 1 := mul_lt_mul_of_pos_left h hx
    rw [mul_one_ax] at h1
    have h2 : x * x < 1 := lt_of_lt_of_le h1 (le_of_lt h)
    rw [hxx] at h2
    exact lt_irrefl_ax (1 : Real) h2
  · exact h
  · exfalso
    have h1 : 1 * x < x * x := mul_lt_mul_of_pos_right h hx
    rw [one_mul_thm] at h1
    have h2 : 1 < x * x := lt_of_lt_of_le h (le_of_lt h1)
    rw [hxx] at h2
    exact lt_irrefl_ax (1 : Real) h2

theorem tan_piQuarter_eq_one : tan (pi / (1 + 1) / (1 + 1)) = 1 :=
  eq_one_of_pos_of_mul_self_eq_one tan_piQuarter_pos tan_piQuarter_sq_eq_one

end Real
end MachLib
