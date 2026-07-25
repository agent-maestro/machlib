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
and `∫₀¹dx/(1+x²) = π/4`, using `atan` (its derivative `1/(1+x²)` is UNCONDITIONAL, unlike
`arcsin`'s) but WITHOUT needing `atan(1)=π/4` as a new axiom — `atan` has zero existing
π-connection in MachLib, so that value is instead DERIVED (§2 below) via the existing FTC-part-2
theorem `ftc_riemann` applied TWICE to the SAME trivial integral `∫₀^{π/4}1dθ`, once with the
identity as antiderivative (giving the value `π/4` directly) and once with `atan∘tan` as
antiderivative (giving `atan(tan(π/4))-atan(tan 0)=atan(1)`, since both `atan` and `tan`, unlike a
Riemann-integral-built total-wrapper function, are genuinely differentiable at `θ=0` with no
artificial "extend-by-0" kink to worry about) — chaining the two gives `atan(1)=π/4` as a THEOREM,
not a postulate. `π` enters as a bare trig fact, no circle/area/Jacobian/moving-domain content.

This file starts with `tan(π/4)=1` (§1) — self-contained, zero dependencies on the harder pieces,
using only `cos_add`/`sin_add` at `π/4+π/4=π/2` plus the existing `cos(π/2)=0`/`sin(π/2)=1` axioms,
and `MachLib.TanLipschitz`'s already-derived `cos_pos_of_lt_pi_div_two` (no need to re-derive `cos`
positivity from scratch). Then §2 derives `atan(1)=π/4` and `∫₀¹dx/(1+x²)=π/4` as above. Zero new
axioms throughout.

`sorryAx`-free, no new axioms (so far).
-/
import MachLib.TanLipschitz
import MachLib.SinNotInEML
import MachLib.CosNotInEML
import MachLib.RiemannIntervalMonotone
import MachLib.RiemannIntegralFTC
import MachLib.InverseTrig
import MachLib.GaussianDiskSandwich

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

/-! ## §2 — `atan(1) = π/4`, DERIVED (not axiomatized), and `∫₀¹dx/(1+x²) = π/4` -/

private theorem tan_mul_cos_eq_sin {θ : Real} (hcne : cos θ ≠ 0) : tan θ * cos θ = sin θ := by
  rw [tan_def θ hcne, div_def (sin θ) (cos θ) hcne]
  rw [show sin θ * (1 / cos θ) * cos θ = sin θ * ((1 / cos θ) * cos θ) from by
    mach_mpoly [sin θ, (1 / cos θ : Real), cos θ]]
  rw [div_mul_cancel hcne, mul_one_ax]

private theorem one_add_tan_sq_mul_cos_sq {θ : Real} (hcne : cos θ ≠ 0) :
    (1 + tan θ * tan θ) * (cos θ * cos θ) = 1 := by
  rw [show (1 + tan θ * tan θ) * (cos θ * cos θ)
      = cos θ * cos θ + (tan θ * cos θ) * (tan θ * cos θ) from by
    mach_mpoly [tan θ, cos θ]]
  rw [tan_mul_cos_eq_sin hcne]
  rw [show cos θ * cos θ + sin θ * sin θ = sin θ * sin θ + cos θ * cos θ from by
    mach_mpoly [sin θ, cos θ]]
  exact pythagorean θ

/-- `d/dθ[atan(tan θ)] = 1` for `|θ|<π/2` — the pythagorean identity cancels `tan`'s derivative
against `atan`'s exactly. Needed because `atan∘tan`, unlike a Riemann-integral-built total-wrapper
function, has NO artificial "extend by 0" kink — it is genuinely differentiable (two-sidedly) at
every point including `θ=0`, which is exactly what lets `ftc_riemann` apply on the CLOSED interval
`[0,π/4]`. -/
theorem hasDerivAt_atan_comp_tan {θ : Real} (hθ : abs θ < pi / (1 + 1)) :
    HasDerivAt (fun y => atan (tan y)) 1 θ := by
  have hcne : cos θ ≠ 0 := ne_of_gt (cos_pos_of_abs_lt_pi_div_two hθ)
  have hcc : cos θ * cos θ ≠ 0 := mul_ne_zero hcne hcne
  have hProd := one_add_tan_sq_mul_cos_sq hcne
  have htpos : 0 < 1 + tan θ * tan θ :=
    lt_of_lt_of_le zero_lt_one_ax (le_add_of_nonneg_right (mul_self_nonneg (tan θ)))
  have htne : (1 : Real) + tan θ * tan θ ≠ 0 := ne_of_gt htpos
  have hCosInv : 1 / (cos θ * cos θ) = 1 + tan θ * tan θ :=
    (eq_div_of_mul_eq hcc hProd).symm
  have hcomp := HasDerivAt_comp atan tan (1 / (cos θ * cos θ)) (1 / (1 + tan θ * tan θ)) θ
    (HasDerivAt_tan hθ) (HasDerivAt_atan (tan θ))
  rw [show (1 / (1 + tan θ * tan θ)) * (1 / (cos θ * cos θ)) = 1 from by
    rw [hCosInv, div_mul_cancel htne]] at hcomp
  exact hcomp

private theorem piQuarter_abs_lt_pi_div_two : abs (pi / (1 + 1) / (1 + 1)) < pi / (1 + 1) := by
  rw [abs_of_nonneg (le_of_lt piQuarter_pos)]
  exact piQuarter_lt_pi_div_two

/-- **`atan(1) = π/4`, DERIVED — no new axiom.** Applies `ftc_riemann` (FTC part 2) TWICE to the
SAME trivial integral `∫₀^{π/4}1dθ`: once with the identity as antiderivative (giving `π/4`
directly), once with `atan∘tan` (giving `atan(1)-atan(0)=atan(1)`). Both equal the same Riemann
integral value, so they're equal to each other. -/
theorem atan_one_eq_piQuarter : atan 1 = pi / (1 + 1) / (1 + 1) := by
  have hcont1 : ∀ z : Real, 0 ≤ z → z ≤ pi / (1 + 1) / (1 + 1) →
      ContinuousAt (fun _ : Real => (1:Real)) z :=
    fun z _ _ => continuousAt_const 1 z
  have hspec := Classical.choose_spec
    (continuous_riemann_integrable (fun _ : Real => (1:Real)) 0 (pi / (1 + 1) / (1 + 1))
      (le_of_lt piQuarter_pos) hcont1)
  have hId := ftc_riemann (fun _ : Real => (1:Real)) (fun θ : Real => θ) 0
      (pi / (1 + 1) / (1 + 1)) piQuarter_pos hcont1 (fun z _ _ => HasDerivAt_id z) _
      (fun k => (hspec.1 k).1) (fun k => (hspec.1 k).2) hspec.2
  have hAtanTan := ftc_riemann (fun _ : Real => (1:Real)) (fun y => atan (tan y)) 0
      (pi / (1 + 1) / (1 + 1)) piQuarter_pos hcont1
      (fun z hz0 hzq =>
        hasDerivAt_atan_comp_tan (by
          rw [abs_of_nonneg hz0]
          exact lt_of_le_of_lt hzq piQuarter_lt_pi_div_two))
      _ (fun k => (hspec.1 k).1) (fun k => (hspec.1 k).2) hspec.2
  have hIdVal : (fun θ : Real => θ) (pi / (1 + 1) / (1 + 1)) - (fun θ : Real => θ) 0
      = pi / (1 + 1) / (1 + 1) := by
    show pi / (1 + 1) / (1 + 1) - 0 = pi / (1 + 1) / (1 + 1)
    exact sub_zero (pi / (1 + 1) / (1 + 1))
  have hAtanVal : (fun y => atan (tan y)) (pi / (1 + 1) / (1 + 1)) - (fun y => atan (tan y)) 0
      = atan 1 := by
    show atan (tan (pi / (1 + 1) / (1 + 1))) - atan (tan 0) = atan 1
    rw [tan_piQuarter_eq_one, tan_zero, atan_zero, sub_zero]
  rw [hIdVal] at hId
  rw [hAtanVal] at hAtanTan
  exact (hId.symm.trans hAtanTan).symm

private theorem one_add_sq_pos (x : Real) : (0:Real) < 1 + x * x :=
  lt_of_lt_of_le zero_lt_one_ax (le_add_of_nonneg_right (mul_self_nonneg x))

private theorem one_add_sq_ne_zero (x : Real) : (1:Real) + x * x ≠ 0 :=
  ne_of_gt (one_add_sq_pos x)

/-- The integrand `1/(1+x²)`. -/
noncomputable def kFn (x : Real) : Real := 1 / (1 + x * x)

theorem continuousAt_kFn (x : Real) : ContinuousAt kFn x := by
  have hderiv : HasDerivAt (fun y => 1 + y * y) (0 + (1 * x + x * 1)) x :=
    HasDerivAt_add (fun _ => 1) (fun y => y * y) 0 (1 * x + x * 1) x
      (HasDerivAt_const 1 x)
      (HasDerivAt_mul (fun y => y) (fun y => y) 1 1 x (HasDerivAt_id x) (HasDerivAt_id x))
  exact hasDerivAt_continuousAt (HasDerivAt_inv (fun y => 1 + y * y) (0 + (1 * x + x * 1)) x
    (one_add_sq_ne_zero x) hderiv)

/-- **`∫₀¹dx/(1+x²) = π/4`.** Via `ftc_riemann` with `atan` as antiderivative (its derivative
`1/(1+x²)` is UNCONDITIONAL, valid at every point of `[0,1]` with no domain restriction), then
`atan(1)=π/4` (derived above, not axiomatized). -/
theorem integral_kFn_eq_piQuarter :
    Classical.choose (continuous_riemann_integrable kFn 0 1 (le_of_lt one_pos)
      (fun z _ _ => continuousAt_kFn z)) = pi / (1 + 1) / (1 + 1) := by
  have hspec := Classical.choose_spec
    (continuous_riemann_integrable kFn 0 1 (le_of_lt one_pos) (fun z _ _ => continuousAt_kFn z))
  have hE : Classical.choose (continuous_riemann_integrable kFn 0 1 (le_of_lt one_pos)
      (fun z _ _ => continuousAt_kFn z)) = atan 1 - atan 0 :=
    ftc_riemann kFn atan 0 1 one_pos (fun z _ _ => continuousAt_kFn z)
      (fun z _ _ => HasDerivAt_atan z) _ (fun k => (hspec.1 k).1) (fun k => (hspec.1 k).2) hspec.2
  rw [hE, atan_zero, sub_zero, atan_one_eq_piQuarter]

/-! ## §3 — FTC-uniqueness helpers (closed-interval and open-at-the-left-endpoint), needed for the
linear substitution lemma and, later, the final `F+G` assembly. -/

private theorem eq_of_sub_eq_sub_laplace {a b c : Real} (h : a - c = b - c) : a = b := by
  have h1 : a - c + c = a := by mach_mpoly [a, c]
  have h2 : b - c + c = b := by mach_mpoly [b, c]
  rw [← h1, ← h2, h]

/-- **Two antiderivatives of the same function that agree at the left endpoint agree
everywhere.** Combines two applications of `ftc_riemann` sharing the same (unique) Riemann
integral value. -/
theorem eq_of_hasDerivAt_eq_of_eq_at_left {f F1 F2 : Real → Real} {a b : Real} (hab : a < b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hF1 : ∀ z : Real, a ≤ z → z ≤ b → HasDerivAt F1 (f z) z)
    (hF2 : ∀ z : Real, a ≤ z → z ≤ b → HasDerivAt F2 (f z) z)
    (hstart : F1 a = F2 a) : F1 b = F2 b := by
  have hspec := Classical.choose_spec (continuous_riemann_integrable f a b (le_of_lt hab) hcont)
  have h1 := ftc_riemann f F1 a b hab hcont hF1 _ (fun k => (hspec.1 k).1) (fun k => (hspec.1 k).2)
    hspec.2
  have h2 := ftc_riemann f F2 a b hab hcont hF2 _ (fun k => (hspec.1 k).1) (fun k => (hspec.1 k).2)
    hspec.2
  have h3 : F1 b - F1 a = F2 b - F2 a := h1.symm.trans h2
  rw [hstart] at h3
  exact eq_of_sub_eq_sub_laplace h3

private theorem eq_of_forall_pos_abs_sub_lt {a b : Real} (h : ∀ ε : Real, 0 < ε → abs (a - b) < ε) :
    a = b := by
  have hab : a ≤ b := le_of_forall_pos_lt_add (fun η hη => by
    have hh := (abs_lt_split (h η hη)).1
    have h2 := add_lt_add_left hh b
    rwa [show b + (a - b) = a from by mach_mpoly [a, b]] at h2)
  have hba : b ≤ a := le_of_forall_pos_lt_add (fun η hη => by
    have hh := (abs_lt_split (h η hη)).2
    have h2 := add_lt_add_left hh (b - a)
    rw [show (b - a) + (a - b) = (0:Real) from by mach_mpoly [a, b]] at h2
    have h3 := add_lt_add_left h2 η
    rw [show η + ((b - a) + -η) = b - a from by mach_mpoly [a, b, η], add_zero] at h3
    have h4 := add_lt_add_left h3 a
    rwa [show a + (b - a) = b from by mach_mpoly [a, b]] at h4)
  exact le_antisymm hab hba

private theorem sub_sub_rearrange_laplace (p q r s : Real) : p - q - (r - s) = p - r - (q - s) := by
  mach_mpoly [p, q, r, s]

private theorem add_sub_self_laplace (p d : Real) : p + d - p = d := by mach_mpoly [p, d]

private theorem sub_eq_sub_sub_sub_laplace (X Y Q : Real) : X - Y = (X - Q) - (Y - Q) := by
  mach_mpoly [X, Y, Q]

private theorem add_neg_eq_sub_sub_laplace (X P Y Q : Real) :
    X - P + -(Y - Q) = (X - P) - (Y - Q) := by
  mach_mpoly [X, P, Y, Q]

private theorem half_add_half_laplace (X : Real) : X / (1 + 1) + X / (1 + 1) = X := by
  rw [← mul_two_eq_add_self (X / (1 + 1))]
  exact div_mul_cancel (ne_of_gt two_pos)

private theorem half_lt_self_laplace {X : Real} (hX : 0 < X) : X / (1 + 1) < X := by
  have hhalfpos : 0 < X / (1 + 1) := div_pos_of_pos_pos hX two_pos
  have h2 := add_lt_add_left hhalfpos (X / (1 + 1))
  rw [add_zero, half_add_half_laplace X] at h2
  exact h2

/-- **Two antiderivatives of the same function that agree at the left endpoint agree everywhere —
OPEN-interval version.** Only needs the derivative match on `(a,b]`, plus mere CONTINUITY (not
differentiability) of both functions at the left endpoint `a` itself. Needed because functions like
`gaussianI` (built via `if h:0≤t then ... else 0`, extended by 0 for negative inputs) are
continuous but NOT two-sidedly differentiable exactly at their extension point — the same "kink"
that broke an earlier, abandoned attempt at this project's disk-sandwich route. Proof: apply the
CLOSED-interval version on `[a+δ,b]` for every `δ>0` (safely interior, no kink there), getting
`F1(b)-F2(b) = F1(a+δ)-F2(a+δ)` exactly for every `δ`; then squeeze `δ→0⁺` using continuity of
`F1`,`F2` at `a` to conclude `F1(b)-F2(b) = F1(a)-F2(a) = 0`. -/
theorem eq_of_hasDerivAt_eq_open_of_eq_at_left {f F1 F2 : Real → Real} {a b : Real} (hab : a < b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hF1 : ∀ z : Real, a < z → z ≤ b → HasDerivAt F1 (f z) z)
    (hF2 : ∀ z : Real, a < z → z ≤ b → HasDerivAt F2 (f z) z)
    (hcontF1 : ContinuousAt F1 a) (hcontF2 : ContinuousAt F2 a)
    (hstart : F1 a = F2 a) : F1 b = F2 b := by
  have hkey : ∀ δ : Real, 0 < δ → δ < b - a → F1 b - F2 b = F1 (a + δ) - F2 (a + δ) := by
    intro δ hδ hδb
    have haδ : a < a + δ := by
      have h := add_lt_add_left hδ a
      rwa [add_zero] at h
    have haδb : a + δ < b := by
      have h := add_lt_add_left hδb a
      rwa [show a + (b - a) = b from by mach_mpoly [a, b]] at h
    have hcont' : ∀ z : Real, a + δ ≤ z → z ≤ b → ContinuousAt f z :=
      fun z hz1 hz2 => hcont z (le_of_lt (lt_of_lt_of_le haδ hz1)) hz2
    have hF1' : ∀ z : Real, a + δ ≤ z → z ≤ b → HasDerivAt F1 (f z) z :=
      fun z hz1 hz2 => hF1 z (lt_of_lt_of_le haδ hz1) hz2
    have hF2' : ∀ z : Real, a + δ ≤ z → z ≤ b → HasDerivAt F2 (f z) z :=
      fun z hz1 hz2 => hF2 z (lt_of_lt_of_le haδ hz1) hz2
    have hspec := Classical.choose_spec
      (continuous_riemann_integrable f (a + δ) b (le_of_lt haδb) hcont')
    have h1 := ftc_riemann f F1 (a + δ) b haδb hcont' hF1' _
      (fun k => (hspec.1 k).1) (fun k => (hspec.1 k).2) hspec.2
    have h2 := ftc_riemann f F2 (a + δ) b haδb hcont' hF2' _
      (fun k => (hspec.1 k).1) (fun k => (hspec.1 k).2) hspec.2
    have heq3 : F1 b - F1 (a + δ) = F2 b - F2 (a + δ) := h1.symm.trans h2
    have h4 : F1 b - F2 b - (F1 (a + δ) - F2 (a + δ))
        = F1 b - F1 (a + δ) - (F2 b - F2 (a + δ)) :=
      sub_sub_rearrange_laplace (F1 b) (F2 b) (F1 (a + δ)) (F2 (a + δ))
    have h3 : F1 b - F1 (a + δ) - (F2 b - F2 (a + δ)) = 0 := by
      rw [heq3]; exact sub_self (F2 b - F2 (a + δ))
    rw [← h4] at h3
    exact eq_of_sub_eq_zero_laplace h3
  refine eq_of_forall_pos_abs_sub_lt (fun ε hε => ?_)
  have hgap : 0 < b - a := sub_pos_of_lt hab
  have hεh : 0 < ε / (1 + 1) := div_pos_of_pos_pos hε two_pos
  obtain ⟨δg, hδgpos, hδg⟩ := hcontF1 (ε / (1 + 1)) hεh
  obtain ⟨δg2, hδg2pos, hδg2⟩ := hcontF2 (ε / (1 + 1)) hεh
  have hm1pos : 0 < min δg δg2 := lt_min_of_lt_of_lt hδgpos hδg2pos
  have hm2pos : 0 < (b - a) / (1 + 1) := div_pos_of_pos_pos hgap two_pos
  have hmpos : 0 < min (min δg δg2) ((b - a) / (1 + 1)) := lt_min_of_lt_of_lt hm1pos hm2pos
  let δ0 := min (min δg δg2) ((b - a) / (1 + 1)) / (1 + 1)
  have hδpos : 0 < δ0 := div_pos_of_pos_pos hmpos two_pos
  have hδltm : δ0 < min (min δg δg2) ((b - a) / (1 + 1)) := half_lt_self_laplace hmpos
  have hδleδg : δ0 < δg :=
    lt_of_lt_of_le hδltm (le_trans (min_le_left _ _) (min_le_left δg δg2))
  have hδleδg2 : δ0 < δg2 :=
    lt_of_lt_of_le hδltm (le_trans (min_le_left _ _) (min_le_right δg δg2))
  have hδltba : δ0 < b - a :=
    lt_of_lt_of_le hδltm (le_trans (min_le_right (min δg δg2) ((b - a) / (1 + 1)))
      (le_of_lt (half_lt_self_laplace hgap)))
  have hkeyδ := hkey δ0 hδpos hδltba
  have hd1 : abs (a + δ0 - a) < δg := by
    rw [add_sub_self_laplace a δ0]
    rwa [abs_of_nonneg (le_of_lt hδpos)]
  have hd2 : abs (a + δ0 - a) < δg2 := by
    rw [add_sub_self_laplace a δ0]
    rwa [abs_of_nonneg (le_of_lt hδpos)]
  have hb1 := hδg (a + δ0) hd1
  have hb2 := hδg2 (a + δ0) hd2
  rw [hkeyδ]
  have heq2 : F1 (a + δ0) - F2 (a + δ0) = (F1 (a + δ0) - F1 a) - (F2 (a + δ0) - F2 a) := by
    rw [hstart]
    exact sub_eq_sub_sub_sub_laplace (F1 (a + δ0)) (F2 (a + δ0)) (F2 a)
  rw [heq2]
  have htri := abs_add (F1 (a + δ0) - F1 a) (-(F2 (a + δ0) - F2 a))
  rw [add_neg_eq_sub_sub_laplace (F1 (a + δ0)) (F1 a) (F2 (a + δ0)) (F2 a)] at htri
  rw [abs_neg] at htri
  have hsum := add_lt_add_both hb1 hb2
  rw [half_add_half_laplace ε] at hsum
  exact lt_of_le_of_lt htri hsum

end Real
end MachLib
