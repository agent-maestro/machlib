import MachLib.Rolle
import MachLib.Differentiation
import MachLib.Ring

/-!
# Bivariate differentiation + the implicit function derivative (Gate 2d, IFT gate — brick 1.c)

The last piece of the IFT/parametrization gate. The model's single-variable `HasDerivAt` is entirely
axiomatized (`HasDerivAt_exp`, `_comp`, `_add`, …); this file adds the **bivariate analogs** in the same
style — an opaque `HasDerivAt2 f fx fy x y` (joint/Fréchet differentiability with partials `fx, fy`), the
**curve chain rule**, and the **implicit function derivative**. All three are standard, witnessable facts
(mirroring Mathlib's `HasFDerivAt`/`HasDerivAt.comp`/`ImplicitFunction`), the bivariate counterparts of the
single-variable axioms already trusted.

From them, `curve_tangent_and_chain` DERIVES exactly what the parametrized Khovanskii–Rolle step
(`TwoExp.khovanskii_rolle_count`) takes as hypotheses: the tangent condition `fₓ + fᵧ·yc' = 0` (algebra,
`yc' = −fₓ/fᵧ`) and the chain rule `HasDerivAt (g along the curve) (gₓ + gᵧ·yc')`. This closes the
parametrization for a general nonlinear curve — the arc `yc` exists and is unique in-model
(`exists_unique_root`, from `sup_exists`), and is differentiable with the right derivative by these bridges.
-/

namespace MachLib
namespace Real

/-- **Joint (Fréchet) differentiability** of a bivariate function: `f` has partials `fx, fy` at `(x, y)`.
Opaque, like the single-variable `HasDerivAt`; pinned by the rules below. -/
axiom HasDerivAt2 : (Real → Real → Real) → Real → Real → Real → Real → Prop

/-- **Curve chain rule** (bivariate analog of `HasDerivAt_comp`). Along a differentiable curve
`s ↦ (γ₁ s, γ₂ s)` through `(γ₁ t, γ₂ t)`, the composition `s ↦ f (γ₁ s) (γ₂ s)` has derivative
`fx·γ₁' + fy·γ₂'`. -/
axiom HasDerivAt2_comp (f : Real → Real → Real) (fx fy : Real) (γ₁ γ₂ : Real → Real) (d₁ d₂ t : Real) :
    HasDerivAt2 f fx fy (γ₁ t) (γ₂ t) → HasDerivAt γ₁ d₁ t → HasDerivAt γ₂ d₂ t →
    HasDerivAt (fun s => f (γ₁ s) (γ₂ s)) (fx * d₁ + fy * d₂) t

/-- **Implicit function derivative** (the IFT bridge). If `f (s, yc s) = 0` along the arc, `f` is jointly
differentiable at `(x, yc x)` with `fᵧ ≠ 0`, then the implicit function `yc` is differentiable with
`yc'(x) = −fₓ/fᵧ`. (Existence + uniqueness of `yc` are in-model via `exists_unique_root`; this axiom is only
the derivative.) -/
axiom hasDerivAt_implicit (f : Real → Real → Real) (fx fy : Real) (yc : Real → Real) (x : Real) :
    HasDerivAt2 f fx fy x (yc x) → fy ≠ 0 → (∀ s : Real, f s (yc s) = 0) →
    HasDerivAt yc (-fx / fy) x

/-- **The parametrization discharges the Khovanskii–Rolle hypotheses.** Given a curve `{f = 0}`
parametrized by `y = yc x` (jointly differentiable `f, g` at `(x, yc x)`, `fᵧ ≠ 0`, `f ≡ 0` along the arc),
the implicit function `yc` yields: (1) the **tangent condition** `fₓ + fᵧ·yc' = 0` and (2) the **chain rule**
`HasDerivAt (g along the curve) (gₓ·1 + gᵧ·yc')` — exactly `khovanskii_rolle_count`'s `hcurve` and
`hGderiv` (with `yc' = −fₓ/fᵧ`). -/
theorem curve_tangent_and_chain (f g : Real → Real → Real) (fx fy gx gy : Real) (yc : Real → Real)
    (x : Real) (hf2 : HasDerivAt2 f fx fy x (yc x)) (hg2 : HasDerivAt2 g gx gy x (yc x))
    (hfy : fy ≠ 0) (hid : ∀ s : Real, f s (yc s) = 0) :
    HasDerivAt yc (-fx / fy) x
      ∧ fx + fy * (-fx / fy) = 0
      ∧ HasDerivAt (fun s => g s (yc s)) (gx * 1 + gy * (-fx / fy)) x := by
  have hyc : HasDerivAt yc (-fx / fy) x := hasDerivAt_implicit f fx fy yc x hf2 hfy hid
  refine ⟨hyc, ?_, ?_⟩
  · have h : fy * (-fx / fy) = -fx := by
      rw [div_def (-fx) fy hfy, ← mul_assoc, mul_comm fy (-fx), mul_assoc, mul_inv fy hfy, mul_one_ax]
    rw [h]; exact add_neg fx
  · exact HasDerivAt2_comp g gx gy (fun s => s) yc 1 (-fx / fy) x hg2 (HasDerivAt_id x) hyc

end Real
end MachLib
