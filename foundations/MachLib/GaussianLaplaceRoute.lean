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

/-! ## §4 — `intUpTo`: a general "`gaussianI`-shaped" total-integral wrapper, reusable for any
continuous integrand with a global upper bound and nonnegativity. Needed for the linear
substitution lemma's RHS, and again for the fixed-bounds Leibniz rule. Mirrors `gaussianI`'s own
construction in `GaussianDiskSandwich.lean` exactly, generalized. -/

noncomputable def intUpTo (g : Real → Real) (hgcont : ∀ x, ContinuousAt g x) (s : Real) : Real :=
  if h : 0 ≤ s then Classical.choose (continuous_riemann_integrable g 0 s h (fun z _ _ => hgcont z))
  else 0

theorem intUpTo_eq (g : Real → Real) (hgcont : ∀ x, ContinuousAt g x) (s : Real) (hs : 0 ≤ s) :
    intUpTo g hgcont s = Classical.choose (continuous_riemann_integrable g 0 s hs
      (fun z _ _ => hgcont z)) := by
  show (if h : 0 ≤ s then Classical.choose (continuous_riemann_integrable g 0 s h
      (fun z _ _ => hgcont z)) else 0)
      = Classical.choose (continuous_riemann_integrable g 0 s hs (fun z _ _ => hgcont z))
  rw [dif_pos hs]

theorem intUpTo_zero_eq (g : Real → Real) (hgcont : ∀ x, ContinuousAt g x) :
    intUpTo g hgcont 0 = 0 := by
  have hgspec := Classical.choose_spec (continuous_riemann_integrable g 0 0 (le_refl 0)
    (fun z _ _ => hgcont z))
  have hupz : upperSumCont g 0 0 (le_refl 0) (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0) = 0 := by
    show partialSum (maxSub g 0 0 (le_refl 0) (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0))
        (2 ^ 0) * meshWidth 0 0 (2 ^ 0) = 0
    have hw0 : meshWidth 0 0 (2 ^ 0) = 0 := by
      show ((0:Real) - 0) / natCast (2 ^ 0) = 0
      rw [sub_self, zero_div]
    rw [hw0, mul_zero]
  have hlowz : lowerSumCont g 0 0 (le_refl 0) (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0) = 0 := by
    show partialSum (minSub g 0 0 (le_refl 0) (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0))
        (2 ^ 0) * meshWidth 0 0 (2 ^ 0) = 0
    have hw0 : meshWidth 0 0 (2 ^ 0) = 0 := by
      show ((0:Real) - 0) / natCast (2 ^ 0) = 0
      rw [sub_self, zero_div]
    rw [hw0, mul_zero]
  have h1 : lowerSumCont g 0 0 (le_refl 0) (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0)
      ≤ intUpTo g hgcont 0 := by rw [intUpTo_eq g hgcont 0 (le_refl 0)]; exact (hgspec.1 0).1
  have h2 : intUpTo g hgcont 0
      ≤ upperSumCont g 0 0 (le_refl 0) (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0) := by
    rw [intUpTo_eq g hgcont 0 (le_refl 0)]; exact (hgspec.1 0).2
  rw [hupz] at h2
  rw [hlowz] at h1
  exact le_antisymm h2 h1

theorem intUpTo_le_bound_mul {g : Real → Real} (hgcont : ∀ x, ContinuousAt g x) {M : Real}
    (hgbound : ∀ x, g x ≤ M) (s : Real) (hs : 0 ≤ s) : intUpTo g hgcont s ≤ M * s := by
  have hgspec := Classical.choose_spec (continuous_riemann_integrable g 0 s hs
    (fun z _ _ => hgcont z))
  have h1 : intUpTo g hgcont s
      ≤ upperSumCont g 0 s hs (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0) := by
    rw [intUpTo_eq g hgcont s hs]; exact (hgspec.1 0).2
  have hmaxle : maxSub g 0 s hs (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0) 0 ≤ M :=
    maxSub_le_global_bound g 0 s hs (fun z _ _ => hgcont z) M (fun z _ _ => hgbound z)
      (2 ^ 0) (two_pow_pos 0) 0
  have hus : upperSumCont g 0 s hs (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0)
      = maxSub g 0 s hs (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0) 0 * meshWidth 0 s (2 ^ 0) := by
    show partialSum (maxSub g 0 s hs (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0)) (2 ^ 0)
        * meshWidth 0 s (2 ^ 0)
      = maxSub g 0 s hs (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0) 0 * meshWidth 0 s (2 ^ 0)
    rw [partialSum_one]
  rw [meshWidth_zero_one_pow] at hus
  rw [hus] at h1
  have hbound : maxSub g 0 s hs (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0) 0 * s ≤ M * s :=
    mul_le_mul_of_nonneg_right hmaxle hs
  exact le_trans h1 hbound

theorem intUpTo_nonneg {g : Real → Real} (hgcont : ∀ x, ContinuousAt g x) (hgnn : ∀ x, 0 ≤ g x)
    (s : Real) (hs : 0 ≤ s) : 0 ≤ intUpTo g hgcont s := by
  have hgspec := Classical.choose_spec (continuous_riemann_integrable g 0 s hs
    (fun z _ _ => hgcont z))
  have h1 : lowerSumCont g 0 s hs (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0)
      ≤ intUpTo g hgcont s := by rw [intUpTo_eq g hgcont s hs]; exact (hgspec.1 0).1
  have hminge : 0 ≤ minSub g 0 s hs (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0) 0 :=
    minSub_ge_global_bound g 0 s hs (fun z _ _ => hgcont z) 0 (fun z _ _ => hgnn z)
      (2 ^ 0) (two_pow_pos 0) 0
  have hls : lowerSumCont g 0 s hs (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0)
      = minSub g 0 s hs (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0) 0 * meshWidth 0 s (2 ^ 0) := by
    show partialSum (minSub g 0 s hs (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0)) (2 ^ 0)
        * meshWidth 0 s (2 ^ 0)
      = minSub g 0 s hs (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0) 0 * meshWidth 0 s (2 ^ 0)
    rw [partialSum_one]
  rw [hls] at h1
  have hbound : (0:Real) ≤ minSub g 0 s hs (fun z _ _ => hgcont z) (2 ^ 0) (two_pow_pos 0) 0
      * meshWidth 0 s (2 ^ 0) := mul_nonneg hminge (meshWidth_nonneg hs (2 ^ 0))
  exact le_trans hbound h1

theorem intUpTo_continuousAt_zero {g : Real → Real} (hgcont : ∀ x, ContinuousAt g x) {M : Real}
    (hgbound : ∀ x, g x ≤ M) (hgnn : ∀ x, 0 ≤ g x) (hMnn : 0 ≤ M) :
    ContinuousAt (intUpTo g hgcont) 0 := by
  intro ε hε
  have hM1pos : 0 < M + 1 := add_pos_of_nonneg_pos hMnn one_pos
  refine ⟨ε / (M + 1), div_pos_of_pos_pos hε hM1pos, ?_⟩
  intro y hy
  show abs (intUpTo g hgcont y - intUpTo g hgcont 0) < ε
  rw [intUpTo_zero_eq, sub_zero]
  by_cases hy0 : 0 ≤ y
  · rw [abs_of_nonneg (intUpTo_nonneg hgcont hgnn y hy0)]
    have hyabs : abs (y - 0) < ε / (M + 1) := hy
    rw [sub_zero] at hyabs
    rw [abs_of_nonneg hy0] at hyabs
    have hbound := intUpTo_le_bound_mul hgcont hgbound y hy0
    have hMy : M * y ≤ (M + 1) * y :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (le_of_lt one_pos)) hy0
    have hstep : (M + 1) * y < (M + 1) * (ε / (M + 1)) := mul_lt_mul_of_pos_left hyabs hM1pos
    rw [mul_comm (M + 1) (ε / (M + 1)), div_mul_cancel (ne_of_gt hM1pos)] at hstep
    exact lt_of_le_of_lt (le_trans hbound hMy) hstep
  · have hyneg : y < 0 := lt_of_not_le_mono hy0
    show (if h : 0 ≤ y then Classical.choose (continuous_riemann_integrable g 0 y h
      (fun z _ _ => hgcont z)) else 0).abs < ε
    rw [dif_neg hy0, abs_zero]
    exact hε

theorem intUpTo_hasDerivAt_pos {g : Real → Real} (hgcont : ∀ x, ContinuousAt g x)
    (hgnn : ∀ x, 0 ≤ g x) (s0 : Real) (hs0 : 0 < s0) :
    HasDerivAt (intUpTo g hgcont) (g s0) s0 := by
  have hc0 : (0 : Real) ≤ s0 + 1 := le_trans (le_of_lt hs0) (le_add_of_nonneg_right (le_of_lt one_pos))
  have hcont_x : ∀ x : Real, 0 ≤ x → x ≤ s0 + 1 → ∀ z : Real, 0 ≤ z → z ≤ x → ContinuousAt g z :=
    fun _ _ _ z _ _ => hgcont z
  have hIlow : ∀ x : Real, ∀ hx0 : 0 ≤ x, ∀ hxc : x ≤ s0 + 1, ∀ k : Nat,
      lowerSumCont g 0 x hx0 (hcont_x x hx0 hxc) (2 ^ k) (two_pow_pos k) ≤ intUpTo g hgcont x := by
    intro x hx0 hxc k
    rw [intUpTo_eq g hgcont x hx0]
    exact (Classical.choose_spec (continuous_riemann_integrable g 0 x hx0
      (fun z _ _ => hgcont z))).1 k |>.1
  have hIup : ∀ x : Real, ∀ hx0 : 0 ≤ x, ∀ hxc : x ≤ s0 + 1, ∀ k : Nat,
      intUpTo g hgcont x ≤ upperSumCont g 0 x hx0 (hcont_x x hx0 hxc) (2 ^ k) (two_pow_pos k) := by
    intro x hx0 hxc k
    rw [intUpTo_eq g hgcont x hx0]
    exact (Classical.choose_spec (continuous_riemann_integrable g 0 x hx0
      (fun z _ _ => hgcont z))).1 k |>.2
  have hIgap : ∀ x : Real, ∀ hx0 : 0 ≤ x, ∀ hxc : x ≤ s0 + 1, ∀ ε : Real, 0 < ε → ∃ k : Nat,
      upperSumCont g 0 x hx0 (hcont_x x hx0 hxc) (2 ^ k) (two_pow_pos k)
        - lowerSumCont g 0 x hx0 (hcont_x x hx0 hxc) (2 ^ k) (two_pow_pos k) < ε :=
    fun x hx0 _ ε hε => (Classical.choose_spec (continuous_riemann_integrable g 0 x hx0
      (fun z _ _ => hgcont z))).2 ε hε
  have hs0_lt : s0 < s0 + 1 := by
    have h := add_lt_add_left one_pos s0
    rwa [add_zero] at h
  exact ftc_part1 g (s0 + 1) hc0 (fun z _ _ => hgcont z) hcont_x (fun z _ _ => hgnn z)
    (intUpTo g hgcont) hIlow hIup hIgap s0 hs0 hs0_lt

/-! ## §5 — the linear substitution lemma: `gaussianI(t) = t·∫₀¹exp(-(tx)²)dx` -/

/-- `gaussianI` and `intUpTo` applied to the SAME gaussian kernel are definitionally the same
construction (proof irrelevance makes `Classical.choose` of two proofs of the same proposition
defeq), so `gaussianI`'s own `HasDerivAt` fact is available for free via `intUpTo_hasDerivAt_pos`. -/
theorem gaussianI_eq_intUpTo :
    gaussianI = intUpTo (fun t => Real.exp (-(t * t))) gaussian_continuous := by
  funext t
  rfl

theorem gaussianI_zero_eq : gaussianI 0 = 0 := by
  rw [gaussianI_eq_intUpTo]; exact intUpTo_zero_eq (fun t => Real.exp (-(t * t))) gaussian_continuous

theorem gaussianI_hasDerivAt_pos {t0 : Real} (ht0 : 0 < t0) :
    HasDerivAt gaussianI (Real.exp (-(t0 * t0))) t0 := by
  rw [gaussianI_eq_intUpTo]
  exact intUpTo_hasDerivAt_pos gaussian_continuous (fun z => le_of_lt (exp_pos _)) t0 ht0

theorem hasDerivAt_scaled_gaussian (t x : Real) :
    HasDerivAt (fun y => Real.exp (-((t * y) * (t * y))))
      (Real.exp (-((t * x) * (t * x))) * -(t * (t * x) + t * x * t)) x := by
  have htx : HasDerivAt (fun y => t * y) t x := by
    have h := HasDerivAt_mul (fun _ => t) (fun y => y) 0 1 x (HasDerivAt_const t x) (HasDerivAt_id x)
    rwa [show (0:Real) * x + t * 1 = t from by mach_mpoly [t, x]] at h
  have htx2 : HasDerivAt (fun y => (t * y) * (t * y)) (t * (t * x) + t * x * t) x :=
    HasDerivAt_mul (fun y => t * y) (fun y => t * y) t t x htx htx
  have hneg : HasDerivAt (fun y => -((t * y) * (t * y))) (-(t * (t * x) + t * x * t)) x :=
    HasDerivAt_neg (fun y => (t * y) * (t * y)) (t * (t * x) + t * x * t) x htx2
  exact HasDerivAt_comp Real.exp (fun y => -((t * y) * (t * y)))
    (-(t * (t * x) + t * x * t)) (Real.exp (-((t * x) * (t * x)))) x hneg
    (HasDerivAt_exp (-((t * x) * (t * x))))

theorem hcont_scaled_gaussian (t : Real) :
    ∀ x, ContinuousAt (fun y => Real.exp (-((t * y) * (t * y)))) x :=
  fun x => hasDerivAt_continuousAt (hasDerivAt_scaled_gaussian t x)

theorem scaled_gaussian_le_one (t x : Real) : Real.exp (-((t * x) * (t * x))) ≤ 1 := by
  have h1 : -((t * x) * (t * x)) ≤ 0 := neg_nonpos_of_nonneg (mul_self_nonneg (t * x))
  have h2 := exp_monotone h1
  rwa [Real.exp_zero] at h2

/-- **The linear substitution lemma.** `gaussianI(t) = t·∫₀¹exp(-(tx)²)dx` for `t>0`, via
`eq_of_hasDerivAt_eq_open_of_eq_at_left`: both sides, as functions of `s∈[0,1]` (with `t` fixed),
have derivative `t·exp(-(ts)²)` on `(0,1]` — the LHS `gaussianI(t·s)` via the chain rule (using
`gaussianI_hasDerivAt_pos` at the interior point `t·s>0`, needing NO Leibniz rule since `t·s` is
just `gaussianI`'s own moving upper limit); the RHS `t·K(s)` via `intUpTo_hasDerivAt_pos` applied
DIRECTLY to `K`'s own defining integrand (again no Leibniz rule — `s` is `K`'s own moving upper
limit, `t` is a genuinely fixed parameter throughout this lemma). Both sides are `0` at `s=0`. -/
theorem gaussianI_eq_t_mul_intUpTo (t : Real) (ht : 0 < t) :
    gaussianI t = t * intUpTo (fun x => Real.exp (-((t * x) * (t * x))))
      (hcont_scaled_gaussian t) 1 := by
  have hcontf : ∀ z : Real, 0 ≤ z → z ≤ 1 →
      ContinuousAt (fun s => t * Real.exp (-((t * s) * (t * s)))) z :=
    fun z _ _ => continuousAt_mul (continuousAt_const t z) (hcont_scaled_gaussian t z)
  have hF1 : ∀ z : Real, 0 < z → z ≤ 1 →
      HasDerivAt (fun s => gaussianI (t * s)) (t * Real.exp (-((t * z) * (t * z)))) z := by
    intro z hz0 _
    have htzpos : 0 < t * z := mul_pos ht hz0
    have htzderiv : HasDerivAt (fun y => t * y) t z := by
      have h := HasDerivAt_mul (fun _ => t) (fun y => y) 0 1 z (HasDerivAt_const t z) (HasDerivAt_id z)
      rwa [show (0:Real) * z + t * 1 = t from by mach_mpoly [t, z]] at h
    have hcomp := HasDerivAt_comp gaussianI (fun y => t * y) t
      (Real.exp (-((t * z) * (t * z)))) z htzderiv (gaussianI_hasDerivAt_pos htzpos)
    rwa [mul_comm (Real.exp (-((t * z) * (t * z)))) t] at hcomp
  have hF2 : ∀ z : Real, 0 < z → z ≤ 1 →
      HasDerivAt (fun s => t * intUpTo (fun x => Real.exp (-((t * x) * (t * x))))
        (hcont_scaled_gaussian t) s) (t * Real.exp (-((t * z) * (t * z)))) z := by
    intro z hz0 _
    have hK := intUpTo_hasDerivAt_pos (hcont_scaled_gaussian t)
      (fun x => le_of_lt (exp_pos _)) z hz0
    have hmul := HasDerivAt_mul (fun _ => t)
      (intUpTo (fun x => Real.exp (-((t * x) * (t * x)))) (hcont_scaled_gaussian t))
      0 (Real.exp (-((t * z) * (t * z)))) z (HasDerivAt_const t z) hK
    rwa [show (0:Real) * intUpTo (fun x => Real.exp (-((t * x) * (t * x))))
        (hcont_scaled_gaussian t) z + t * Real.exp (-((t * z) * (t * z)))
        = t * Real.exp (-((t * z) * (t * z))) from by
      mach_mpoly [intUpTo (fun x => Real.exp (-((t * x) * (t * x)))) (hcont_scaled_gaussian t) z,
        t, Real.exp (-((t * z) * (t * z)))]] at hmul
  have hgz : (fun y : Real => t * y) 0 = 0 := by show t * (0:Real) = 0; mach_mpoly [t]
  have hcontF1 : ContinuousAt (fun s => gaussianI (t * s)) 0 := by
    have hgcont0 : ContinuousAt (fun y => t * y) 0 := hasDerivAt_continuousAt (by
      have h := HasDerivAt_mul (fun _ => t) (fun y => y) 0 1 (0:Real) (HasDerivAt_const t 0)
        (HasDerivAt_id 0)
      rwa [show (0:Real) * (0:Real) + t * 1 = t from by mach_mpoly [t]] at h)
    have hfcont0 : ContinuousAt gaussianI (t * 0) := by
      rw [show t * (0:Real) = 0 from by mach_mpoly [t]]
      exact gaussianI_continuousAt_zero
    exact continuousAt_comp hgcont0 hfcont0
  have hcontF2 : ContinuousAt (fun s => t * intUpTo (fun x => Real.exp (-((t * x) * (t * x))))
      (hcont_scaled_gaussian t) s) 0 := by
    have hKcont0 := intUpTo_continuousAt_zero (hcont_scaled_gaussian t)
      (fun x => scaled_gaussian_le_one t x) (fun x => le_of_lt (exp_pos _)) (le_of_lt one_pos)
    exact continuousAt_mul (continuousAt_const t 0) hKcont0
  have hstart : gaussianI (t * 0) = t * intUpTo (fun x => Real.exp (-((t * x) * (t * x))))
      (hcont_scaled_gaussian t) 0 := by
    rw [show t * (0:Real) = 0 from by mach_mpoly [t], gaussianI_zero_eq,
      intUpTo_zero_eq (fun x => Real.exp (-((t * x) * (t * x)))) (hcont_scaled_gaussian t),
      mul_zero]
  have hconcl := eq_of_hasDerivAt_eq_open_of_eq_at_left one_pos hcontf hF1 hF2 hcontF1 hcontF2 hstart
  rwa [mul_one_ax] at hconcl

/-! ## §6 — one-directional Darboux-sum additivity, and constant-function integrals

Needed for the Leibniz rule below: general "`∫(f+g)=∫f+∫g`" additivity for Riemann integrals is
NOT available and would be genuinely hard to build (comparable to `riemann_integral_additivity`'s
domain-additivity — the natural termwise Darboux bound only gives ONE direction). But the Leibniz
bound only needs that ONE direction (an inequality, not an equality), which is easy: at `f+g`'s own
extremum point, each of `f`,`g` individually is bounded by ITS OWN `maxSub`/`minSub`, so their sum
bounds `f+g`'s extremum too. -/

private theorem distrib_mul_local_laplace (X Y q : Real) : (X + Y) * q = X * q + Y * q := by
  mach_mpoly [X, Y, q]

private theorem partialSum_add_termwise (f g : Nat → Real) :
    ∀ n, partialSum (fun i => f i + g i) n = partialSum f n + partialSum g n
  | 0 => by show (0 : Real) = 0 + 0; mach_ring
  | n + 1 => by
      rw [partialSum_succ, partialSum_succ, partialSum_succ, partialSum_add_termwise f g n]
      show (partialSum f n + partialSum g n) + (f n + g n)
        = (partialSum f n + f n) + (partialSum g n + g n)
      mach_ring

private theorem partialSum_const_laplace (c : Real) :
    ∀ n, partialSum (fun _ : Nat => c) n = natCast n * c
  | 0 => by show (0 : Real) = natCast 0 * c; rw [natCast_zero, zero_mul]
  | k + 1 => by
      show partialSum (fun _ : Nat => c) k + c = natCast (k + 1) * c
      rw [partialSum_const_laplace c k, natCast_succ]
      mach_mpoly [natCast k, c]

theorem upperSumCont_add_le {f g : Real → Real} {a b : Real} (hab : a ≤ b)
    (hfcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hgcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt g z)
    (hfgcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt (fun x => f x + g x) z)
    (n : Nat) (hn : 0 < n) :
    upperSumCont (fun x => f x + g x) a b hab hfgcont n hn
      ≤ upperSumCont f a b hab hfcont n hn + upperSumCont g a b hab hgcont n hn := by
  show partialSum (maxSub (fun x => f x + g x) a b hab hfgcont n hn) n * meshWidth a b n
      ≤ partialSum (maxSub f a b hab hfcont n hn) n * meshWidth a b n
        + partialSum (maxSub g a b hab hgcont n hn) n * meshWidth a b n
  have hterm : ∀ i, i < n →
      maxSub (fun x => f x + g x) a b hab hfgcont n hn i
        ≤ (fun j => maxSub f a b hab hfcont n hn j + maxSub g a b hab hgcont n hn j) i := by
    intro i hi
    rw [maxSub_eq (fun x => f x + g x) a b hab hfgcont n hn i hi]
    obtain ⟨h1lo, h1hi, _⟩ := Classical.choose_spec
      (evt_exists_max (fun x => f x + g x) a b hab hfgcont n hn i hi)
    have hf := maxSub_spec f a b hab hfcont n hn i hi _ h1lo h1hi
    have hg := maxSub_spec g a b hab hgcont n hn i hi _ h1lo h1hi
    exact add_le_add_both hf hg
  have hsum := partialSum_le_of_termwise_le n hterm
  rw [partialSum_add_termwise (maxSub f a b hab hfcont n hn) (maxSub g a b hab hgcont n hn) n]
    at hsum
  have hbound : partialSum (maxSub (fun x => f x + g x) a b hab hfgcont n hn) n * meshWidth a b n
      ≤ (partialSum (maxSub f a b hab hfcont n hn) n + partialSum (maxSub g a b hab hgcont n hn) n)
        * meshWidth a b n :=
    mul_le_mul_of_nonneg_right hsum (meshWidth_nonneg hab n)
  rwa [distrib_mul_local_laplace (partialSum (maxSub f a b hab hfcont n hn) n)
    (partialSum (maxSub g a b hab hgcont n hn) n) (meshWidth a b n)] at hbound

theorem lowerSumCont_add_ge {f g : Real → Real} {a b : Real} (hab : a ≤ b)
    (hfcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hgcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt g z)
    (hfgcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt (fun x => f x + g x) z)
    (n : Nat) (hn : 0 < n) :
    lowerSumCont f a b hab hfcont n hn + lowerSumCont g a b hab hgcont n hn
      ≤ lowerSumCont (fun x => f x + g x) a b hab hfgcont n hn := by
  show partialSum (minSub f a b hab hfcont n hn) n * meshWidth a b n
      + partialSum (minSub g a b hab hgcont n hn) n * meshWidth a b n
      ≤ partialSum (minSub (fun x => f x + g x) a b hab hfgcont n hn) n * meshWidth a b n
  have hterm : ∀ i, i < n →
      (fun j => minSub f a b hab hfcont n hn j + minSub g a b hab hgcont n hn j) i
        ≤ minSub (fun x => f x + g x) a b hab hfgcont n hn i := by
    intro i hi
    rw [minSub_eq (fun x => f x + g x) a b hab hfgcont n hn i hi]
    obtain ⟨h1lo, h1hi, _⟩ := Classical.choose_spec
      (evt_exists_min (fun x => f x + g x) a b hab hfgcont n hn i hi)
    have hf := minSub_spec f a b hab hfcont n hn i hi _ h1lo h1hi
    have hg := minSub_spec g a b hab hgcont n hn i hi _ h1lo h1hi
    exact add_le_add_both hf hg
  have hsum := partialSum_le_of_termwise_le n hterm
  rw [partialSum_add_termwise (minSub f a b hab hfcont n hn) (minSub g a b hab hgcont n hn) n]
    at hsum
  have hbound : (partialSum (minSub f a b hab hfcont n hn) n + partialSum (minSub g a b hab hgcont n hn) n)
      * meshWidth a b n
      ≤ partialSum (minSub (fun x => f x + g x) a b hab hfgcont n hn) n * meshWidth a b n :=
    mul_le_mul_of_nonneg_right hsum (meshWidth_nonneg hab n)
  rwa [distrib_mul_local_laplace (partialSum (minSub f a b hab hfcont n hn) n)
    (partialSum (minSub g a b hab hgcont n hn) n) (meshWidth a b n)] at hbound

theorem upperSumCont_const_eq (c a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt (fun _ : Real => c) z) (n : Nat) (hn : 0 < n) :
    upperSumCont (fun _ : Real => c) a b hab hcont n hn = c * (b - a) := by
  show partialSum (maxSub (fun _ : Real => c) a b hab hcont n hn) n * meshWidth a b n = c * (b - a)
  have hmax : ∀ i, maxSub (fun _ : Real => c) a b hab hcont n hn i = (fun _ : Nat => c) i := by
    intro i
    by_cases hi : i < n
    · rw [maxSub_eq (fun _ : Real => c) a b hab hcont n hn i hi]
    · unfold maxSub
      rw [dif_neg hi]
  rw [partialSum_congr hmax n, partialSum_const_laplace c n]
  rw [show natCast n * c * meshWidth a b n = c * (natCast n * meshWidth a b n) from by
    mach_mpoly [natCast n, c, meshWidth a b n]]
  rw [natCast_mul_meshWidth a b n hn]

theorem lowerSumCont_const_eq (c a b : Real) (hab : a ≤ b)
    (hcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt (fun _ : Real => c) z) (n : Nat) (hn : 0 < n) :
    lowerSumCont (fun _ : Real => c) a b hab hcont n hn = c * (b - a) := by
  show partialSum (minSub (fun _ : Real => c) a b hab hcont n hn) n * meshWidth a b n = c * (b - a)
  have hmin : ∀ i, minSub (fun _ : Real => c) a b hab hcont n hn i = (fun _ : Nat => c) i := by
    intro i
    by_cases hi : i < n
    · rw [minSub_eq (fun _ : Real => c) a b hab hcont n hn i hi]
    · unfold minSub
      rw [dif_neg hi]
  rw [partialSum_congr hmin n, partialSum_const_laplace c n]
  rw [show natCast n * c * meshWidth a b n = c * (natCast n * meshWidth a b n) from by
    mach_mpoly [natCast n, c, meshWidth a b n]]
  rw [natCast_mul_meshWidth a b n hn]

/-! ## §7 — `q(t,x) := ∂p/∂t` is Lipschitz in `t`, uniformly in `x∈[0,1]`

The MVT+Lipschitz ingredient the Leibniz bound needs — built via `q`'s OWN `t`-derivative (the
integrand's SECOND `t`-derivative) plus an explicit magnitude bound on it. -/

private theorem hasDerivAt_qFn_t (c t : Real) :
    HasDerivAt (fun s => -(1+1) * s * Real.exp (-(s * s * c)))
      (-(1+1) * Real.exp (-(t * t * c)) + (1+1+1+1) * t * t * c * Real.exp (-(t * t * c))) t := by
  have h1 : HasDerivAt (fun s => s * s) (1 * t + t * 1) t :=
    HasDerivAt_mul (fun s => s) (fun s => s) 1 1 t (HasDerivAt_id t) (HasDerivAt_id t)
  have h2 : HasDerivAt (fun s => s * s * c) ((1 * t + t * 1) * c + t * t * 0) t :=
    HasDerivAt_mul (fun s => s * s) (fun _ => c) (1 * t + t * 1) 0 t h1 (HasDerivAt_const c t)
  have h3 : HasDerivAt (fun s => -(s * s * c)) (-((1 * t + t * 1) * c + t * t * 0)) t :=
    HasDerivAt_neg (fun s => s * s * c) ((1 * t + t * 1) * c + t * t * 0) t h2
  have h4 : HasDerivAt (fun s => Real.exp (-(s * s * c)))
      (Real.exp (-(t * t * c)) * -((1 * t + t * 1) * c + t * t * 0)) t :=
    HasDerivAt_comp Real.exp (fun s => -(s * s * c)) (-((1 * t + t * 1) * c + t * t * 0))
      (Real.exp (-(t * t * c))) t h3 (HasDerivAt_exp (-(t * t * c)))
  have h5 : HasDerivAt (fun s => -(1+1) * s) (0 * t + -(1+1) * 1) t :=
    HasDerivAt_mul (fun _ => (-(1+1):Real)) (fun s => s) 0 1 t (HasDerivAt_const (-(1+1)) t) (HasDerivAt_id t)
  have h6 := HasDerivAt_mul (fun s => -(1+1) * s) (fun s => Real.exp (-(s * s * c)))
    (0 * t + -(1+1) * 1) (Real.exp (-(t * t * c)) * -((1 * t + t * 1) * c + t * t * 0)) t h5 h4
  rwa [show (0 * t + -(1+1) * 1) * Real.exp (-(t * t * c))
      + (-(1+1) * t) * (Real.exp (-(t * t * c)) * -((1 * t + t * 1) * c + t * t * 0))
      = -(1+1) * Real.exp (-(t * t * c)) + (1+1+1+1) * t * t * c * Real.exp (-(t * t * c))
      from by mach_mpoly [t, c, Real.exp (-(t * t * c))]] at h6

private theorem four_pos_laplace : (0:Real) < 1 + 1 + 1 + 1 := by
  have h1 : (0:Real) < 1 + 1 := two_pos
  have h2 := add_lt_add_both h1 h1
  rw [add_zero] at h2
  rwa [show (1 + 1 : Real) + (1 + 1) = 1 + 1 + 1 + 1 from by mach_mpoly [(1:Real)]] at h2

private theorem eight_pos_laplace : (0:Real) < 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by
  have h1 := four_pos_laplace
  have h2 := add_lt_add_both h1 h1
  rw [add_zero] at h2
  rwa [show (1 + 1 + 1 + 1 : Real) + (1 + 1 + 1 + 1) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1
      from by mach_mpoly [(1:Real)]] at h2

private theorem abs_neg_two_local : abs (-(1+1) : Real) = (1+1) := by
  rw [abs_of_nonpos (neg_nonpos_of_nonneg (le_of_lt two_pos))]; mach_ring

private theorem qFn_deriv_bound {c t T : Real} (hc0 : 0 ≤ c) (hc2 : c ≤ (1+1)) (hT : 0 ≤ T)
    (htT : abs t ≤ T) :
    abs (-(1+1) * Real.exp (-(t * t * c)) + (1+1+1+1) * t * t * c * Real.exp (-(t * t * c)))
      ≤ (1+1) + (1+1+1+1+1+1+1+1) * T * T := by
  have hE0 : 0 ≤ Real.exp (-(t * t * c)) := le_of_lt (exp_pos _)
  have hE1 : Real.exp (-(t * t * c)) ≤ 1 := by
    have h1 : -(t * t * c) ≤ 0 := neg_nonpos_of_nonneg (mul_nonneg (mul_self_nonneg t) hc0)
    have h2 := exp_monotone h1
    rwa [Real.exp_zero] at h2
  have httT : t * t ≤ T * T := by
    have h1 : t * t = abs t * abs t := by
      rw [← abs_mul]; exact (abs_of_nonneg (mul_self_nonneg t)).symm
    rw [h1]
    exact mul_le_mul' (abs_nonneg t) htT (abs_nonneg t) htT
  have htri := abs_add ((-(1+1):Real) * Real.exp (-(t * t * c)))
    ((1+1+1+1) * t * t * c * Real.exp (-(t * t * c)))
  have hb1 : abs ((-(1+1):Real) * Real.exp (-(t * t * c))) ≤ (1+1) := by
    rw [abs_mul, abs_neg_two_local, abs_of_nonneg hE0]
    have h := mul_le_mul_of_nonneg_left hE1 (le_of_lt two_pos)
    rwa [mul_one_ax] at h
  have hb2 : abs ((1+1+1+1) * t * t * c * Real.exp (-(t * t * c))) ≤ (1+1+1+1+1+1+1+1) * T * T := by
    rw [show (1+1+1+1:Real) * t * t * c * Real.exp (-(t * t * c))
        = (1+1+1+1) * (t * t * (c * Real.exp (-(t * t * c)))) from by
      mach_mpoly [t, c, Real.exp (-(t * t * c))]]
    have hcE : c * Real.exp (-(t * t * c)) ≤ (1+1) := by
      have h := mul_le_mul' hc0 hc2 hE0 hE1
      rwa [mul_one_ax] at h
    have hcEnn : 0 ≤ c * Real.exp (-(t * t * c)) := mul_nonneg hc0 hE0
    have httTc : t * t * (c * Real.exp (-(t * t * c))) ≤ T * T * (1+1) :=
      mul_le_mul' (mul_self_nonneg t) httT hcEnn hcE
    have httTcnn : 0 ≤ t * t * (c * Real.exp (-(t * t * c))) :=
      mul_nonneg (mul_self_nonneg t) hcEnn
    rw [abs_of_nonneg (mul_nonneg (le_of_lt four_pos_laplace) httTcnn)]
    have h := mul_le_mul_of_nonneg_left httTc (le_of_lt four_pos_laplace)
    rwa [show (1+1+1+1:Real) * (T * T * (1+1)) = (1+1+1+1+1+1+1+1) * T * T from by mach_mpoly [T]] at h
  have hsum := add_le_add_both hb1 hb2
  rw [show ((1+1):Real) + (1+1+1+1+1+1+1+1) * T * T = (1+1) + (1+1+1+1+1+1+1+1) * T * T from rfl] at hsum
  exact le_trans htri hsum

/-- **`q(t,x)` is Lipschitz in `t` on `[-T,T]`, uniformly in `x`, with constant `(1+1)+8T²`.** -/
theorem qFn_lipschitz_in_t {c t1 t2 T : Real} (hc0 : 0 ≤ c) (hc2 : c ≤ (1+1)) (hT : 0 ≤ T)
    (ht1 : abs t1 ≤ T) (ht2 : abs t2 ≤ T) :
    abs (-(1+1) * t1 * Real.exp (-(t1 * t1 * c)) - -(1+1) * t2 * Real.exp (-(t2 * t2 * c)))
      ≤ ((1+1) + (1+1+1+1+1+1+1+1) * T * T) * abs (t1 - t2) := by
  have hstep : ∀ p q : Real, p < q → abs p ≤ T → abs q ≤ T →
      abs (-(1+1) * q * Real.exp (-(q * q * c)) - -(1+1) * p * Real.exp (-(p * p * c)))
        ≤ ((1+1) + (1+1+1+1+1+1+1+1) * T * T) * (q - p) := by
    intro p q hpq hpT hqT
    obtain ⟨cc, f', hc1, hc2', hderiv, heqv⟩ :=
      mean_value_theorem_ct (fun s => -(1+1) * s * Real.exp (-(s * s * c))) p q hpq
        (fun z _ _ => ⟨-(1+1) * Real.exp (-(z * z * c)) + (1+1+1+1) * z * z * c * Real.exp (-(z * z * c)),
          hasDerivAt_qFn_t c z⟩)
    rw [HasDerivAt_unique (fun s => -(1+1) * s * Real.exp (-(s * s * c))) f'
      (-(1+1) * Real.exp (-(cc * cc * c)) + (1+1+1+1) * cc * cc * c * Real.exp (-(cc * cc * c))) cc hderiv
      (hasDerivAt_qFn_t c cc)] at heqv
    have hccT : abs cc ≤ T := by
      have hp1 := (abs_le_iff.mp hpT).1
      have hq2 := (abs_le_iff.mp hqT).2
      exact abs_le_iff.mpr ⟨le_trans hp1 (le_of_lt hc1), le_of_lt (lt_of_lt_of_le hc2' hq2)⟩
    have hbound := qFn_deriv_bound hc0 hc2 hT hccT
    have hqpnn : 0 ≤ q - p := sub_nonneg_of_le (le_of_lt hpq)
    have hgoal : abs ((-(1+1) * Real.exp (-(cc * cc * c)) + (1+1+1+1) * cc * cc * c * Real.exp (-(cc * cc * c)))
        * (q - p)) ≤ ((1+1) + (1+1+1+1+1+1+1+1) * T * T) * (q - p) := by
      rw [abs_mul, abs_of_nonneg hqpnn]
      exact mul_le_mul_of_nonneg_right hbound hqpnn
    show abs (-(1+1) * q * Real.exp (-(q * q * c)) - -(1+1) * p * Real.exp (-(p * p * c))) ≤ _
    rw [heqv]
    exact hgoal
  rcases lt_total t1 t2 with hlt | heqv | hlt
  · have h := hstep t1 t2 hlt ht1 ht2
    rw [show -(1+1) * t1 * Real.exp (-(t1 * t1 * c)) - -(1+1) * t2 * Real.exp (-(t2 * t2 * c))
        = -(-(1+1) * t2 * Real.exp (-(t2 * t2 * c)) - -(1+1) * t1 * Real.exp (-(t1 * t1 * c)))
        from by mach_mpoly [t1, t2, Real.exp (-(t1 * t1 * c)), Real.exp (-(t2 * t2 * c))]]
    rw [abs_neg]
    rw [show abs (t1 - t2) = t2 - t1 from by
      rw [show t1 - t2 = -(t2 - t1) from by mach_mpoly [t1, t2], abs_neg,
        abs_of_nonneg (sub_nonneg_of_le (le_of_lt hlt))]]
    exact h
  · rw [heqv]
    rw [show -(1+1) * t2 * Real.exp (-(t2 * t2 * c)) - -(1+1) * t2 * Real.exp (-(t2 * t2 * c)) = (0:Real)
      from by mach_mpoly [t2, Real.exp (-(t2 * t2 * c))]]
    rw [abs_zero, show t2 - t2 = (0:Real) from by mach_mpoly [t2], abs_zero, mul_zero]
    exact le_refl 0
  · have h := hstep t2 t1 hlt ht2 ht1
    rwa [show abs (t1 - t2) = t1 - t2 from abs_of_nonneg (sub_nonneg_of_le (le_of_lt hlt))]

/-! ## §8 — `G(t) := ∫₀¹p(t,x)dx`, `Gderiv(t) := ∫₀¹q(t,x)dx`, well-posed for EVERY real `t` (no
boundary-kink construction needed — `p`,`q` are honestly defined for all `t`, positive or
negative, unlike `gaussianI`'s total-wrapper). -/

private theorem hasDerivAt_p_exp_x (t x : Real) :
    HasDerivAt (fun y => Real.exp (-(t * t * (1 + y * y))))
      (Real.exp (-(t * t * (1 + x * x))) * -(t * t * (0 + (1 * x + x * 1)))) x := by
  have h1 : HasDerivAt (fun y => y * y) (1 * x + x * 1) x :=
    HasDerivAt_mul (fun y => y) (fun y => y) 1 1 x (HasDerivAt_id x) (HasDerivAt_id x)
  have h2 : HasDerivAt (fun y => 1 + y * y) (0 + (1 * x + x * 1)) x :=
    HasDerivAt_add (fun _ => 1) (fun y => y * y) 0 (1 * x + x * 1) x (HasDerivAt_const 1 x) h1
  have h3 : HasDerivAt (fun y => t * t * (1 + y * y))
      (0 * (1 + x * x) + t * t * (0 + (1 * x + x * 1))) x :=
    HasDerivAt_mul (fun _ => t * t) (fun y => 1 + y * y) 0 (0 + (1 * x + x * 1)) x
      (HasDerivAt_const (t * t) x) h2
  have h4 : HasDerivAt (fun y => -(t * t * (1 + y * y)))
      (-(0 * (1 + x * x) + t * t * (0 + (1 * x + x * 1)))) x :=
    HasDerivAt_neg (fun y => t * t * (1 + y * y)) (0 * (1 + x * x) + t * t * (0 + (1 * x + x * 1))) x h3
  have h5 := HasDerivAt_comp Real.exp (fun y => -(t * t * (1 + y * y)))
    (-(0 * (1 + x * x) + t * t * (0 + (1 * x + x * 1)))) (Real.exp (-(t * t * (1 + x * x)))) x h4
    (HasDerivAt_exp (-(t * t * (1 + x * x))))
  rwa [show Real.exp (-(t * t * (1 + x * x))) * -(0 * (1 + x * x) + t * t * (0 + (1 * x + x * 1)))
      = Real.exp (-(t * t * (1 + x * x))) * -(t * t * (0 + (1 * x + x * 1))) from by
    mach_mpoly [Real.exp (-(t * t * (1 + x * x))), t, x]] at h5

private theorem hcont_p_exp (t : Real) :
    ∀ x, ContinuousAt (fun y => Real.exp (-(t * t * (1 + y * y)))) x :=
  fun x => hasDerivAt_continuousAt (hasDerivAt_p_exp_x t x)

private theorem hcont_p (t : Real) :
    ∀ x, ContinuousAt (fun y => Real.exp (-(t * t * (1 + y * y))) * kFn y) x :=
  fun x => continuousAt_mul (hcont_p_exp t x) (continuousAt_kFn x)

private theorem hcont_q (t : Real) :
    ∀ x, ContinuousAt (fun y => -(1 + 1) * t * Real.exp (-(t * t * (1 + y * y)))) x :=
  fun x => continuousAt_mul (continuousAt_const (-(1 + 1) * t) x) (hcont_p_exp t x)

/-- `G(t) := ∫₀¹ exp(-t²(1+x²))/(1+x²) dx`. Well-defined for EVERY real `t` — no total-wrapper
extension needed, since the integrand is honestly defined for all `t`. -/
noncomputable def GFn (t : Real) : Real :=
  Classical.choose (continuous_riemann_integrable
    (fun x => Real.exp (-(t * t * (1 + x * x))) * kFn x) 0 1 (le_of_lt one_pos) (fun z _ _ => hcont_p t z))

/-- `Gderiv(t) := ∫₀¹ q(t,x) dx = ∫₀¹ -2t·exp(-t²(1+x²)) dx` — the pointwise-in-`t`-derivative's
own integral, the target for `G`'s FTC-derivative. -/
noncomputable def GderivFn (t : Real) : Real :=
  Classical.choose (continuous_riemann_integrable
    (fun x => -(1 + 1) * t * Real.exp (-(t * t * (1 + x * x)))) 0 1 (le_of_lt one_pos)
    (fun z _ _ => hcont_q t z))

/-! ## §9 — `p(t,x)`'s pointwise `t`-derivative is `q(t,x)` exactly

The `(1+x²)` from differentiating the exponential cancels EXACTLY against `kFn(x)=1/(1+x²)` — this
cancellation is the whole reason `p`'s `x`-integral against `kFn` was worth building in the first
place (a bare `exp(-t²(1+x²))` integrand would carry an un-cancelled `(1+x²)` factor in its
`t`-derivative, breaking the match against `qFn_lipschitz_in_t`, which is stated for the bare
`-2t·exp(...)` form). -/

private theorem hasDerivAt_exp_neg_sq_mul_c (c t : Real) :
    HasDerivAt (fun s => Real.exp (-(s * s * c)))
      (Real.exp (-(t * t * c)) * -((1 * t + t * 1) * c + t * t * 0)) t := by
  have h1 : HasDerivAt (fun s => s * s) (1 * t + t * 1) t :=
    HasDerivAt_mul (fun s => s) (fun s => s) 1 1 t (HasDerivAt_id t) (HasDerivAt_id t)
  have h2 : HasDerivAt (fun s => s * s * c) ((1 * t + t * 1) * c + t * t * 0) t :=
    HasDerivAt_mul (fun s => s * s) (fun _ => c) (1 * t + t * 1) 0 t h1 (HasDerivAt_const c t)
  have h3 : HasDerivAt (fun s => -(s * s * c)) (-((1 * t + t * 1) * c + t * t * 0)) t :=
    HasDerivAt_neg (fun s => s * s * c) ((1 * t + t * 1) * c + t * t * 0) t h2
  exact HasDerivAt_comp Real.exp (fun s => -(s * s * c)) (-((1 * t + t * 1) * c + t * t * 0))
    (Real.exp (-(t * t * c))) t h3 (HasDerivAt_exp (-(t * t * c)))

private theorem cancel_one_add_xx (x A : Real) : A * (1 + x * x) * (1 / (1 + x * x)) = A := by
  rw [show A * (1 + x * x) * (1 / (1 + x * x)) = A * ((1 / (1 + x * x)) * (1 + x * x)) from by
    mach_mpoly [A, (1 + x * x : Real), (1 / (1 + x * x) : Real)]]
  rw [div_mul_cancel (ne_of_gt (one_add_sq_pos x)), mul_one_ax]

theorem hasDerivAt_p_t (t x : Real) :
    HasDerivAt (fun s => Real.exp (-(s * s * (1 + x * x))) * kFn x)
      (-(1 + 1) * t * Real.exp (-(t * t * (1 + x * x)))) t := by
  have h1 := hasDerivAt_exp_neg_sq_mul_c (1 + x * x) t
  have h2 := HasDerivAt_mul (fun s => Real.exp (-(s * s * (1 + x * x)))) (fun _ => kFn x)
    (Real.exp (-(t * t * (1 + x * x))) * -((1 * t + t * 1) * (1 + x * x) + t * t * 0)) 0 t h1
    (HasDerivAt_const (kFn x) t)
  have hval : (Real.exp (-(t * t * (1 + x * x))) * -((1 * t + t * 1) * (1 + x * x) + t * t * 0))
      * kFn x + Real.exp (-(t * t * (1 + x * x))) * 0
      = -(1 + 1) * t * Real.exp (-(t * t * (1 + x * x))) := by
    show (Real.exp (-(t * t * (1 + x * x))) * -((1 * t + t * 1) * (1 + x * x) + t * t * 0))
        * (1 / (1 + x * x)) + Real.exp (-(t * t * (1 + x * x))) * 0
        = -(1 + 1) * t * Real.exp (-(t * t * (1 + x * x)))
    rw [show (Real.exp (-(t * t * (1 + x * x))) * -((1 * t + t * 1) * (1 + x * x) + t * t * 0))
        * (1 / (1 + x * x)) + Real.exp (-(t * t * (1 + x * x))) * 0
        = (Real.exp (-(t * t * (1 + x * x))) * (-(1 + 1) * t)) * (1 + x * x) * (1 / (1 + x * x))
        from by
      mach_mpoly [Real.exp (-(t * t * (1 + x * x))), t, (1 + x * x : Real), (1 / (1 + x * x) : Real)]]
    rw [cancel_one_add_xx x (Real.exp (-(t * t * (1 + x * x))) * (-(1 + 1) * t))]
    mach_mpoly [Real.exp (-(t * t * (1 + x * x))), t]
  rwa [hval] at h2

end Real
end MachLib
