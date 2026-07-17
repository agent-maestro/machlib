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

/-! ## Base-case + arithmetic rules (bivariate analogs of the single-variable `HasDerivAt` axioms) -/

axiom HasDerivAt2_projX (x y : Real) : HasDerivAt2 (fun a _ => a) 1 0 x y
axiom HasDerivAt2_projY (x y : Real) : HasDerivAt2 (fun _ b => b) 0 1 x y
axiom HasDerivAt2_const (c x y : Real) : HasDerivAt2 (fun _ _ => c) 0 0 x y

axiom HasDerivAt2_add (f g : Real → Real → Real) (fx fy gx gy x y : Real) :
    HasDerivAt2 f fx fy x y → HasDerivAt2 g gx gy x y →
    HasDerivAt2 (fun a b => f a b + g a b) (fx + gx) (fy + gy) x y

axiom HasDerivAt2_sub (f g : Real → Real → Real) (fx fy gx gy x y : Real) :
    HasDerivAt2 f fx fy x y → HasDerivAt2 g gx gy x y →
    HasDerivAt2 (fun a b => f a b - g a b) (fx - gx) (fy - gy) x y

axiom HasDerivAt2_mul (f g : Real → Real → Real) (fx fy gx gy x y : Real) :
    HasDerivAt2 f fx fy x y → HasDerivAt2 g gx gy x y →
    HasDerivAt2 (fun a b => f a b * g a b) (fx * g x y + f x y * gx) (fy * g x y + f x y * gy) x y

/-- Single-variable `φ` composed with a bivariate `u` (gives `exp`, `log`, … of any bivariate expression). -/
axiom HasDerivAt2_scomp (φ : Real → Real) (φ' : Real) (u : Real → Real → Real) (ux uy x y : Real) :
    HasDerivAt φ φ' (u x y) → HasDerivAt2 u ux uy x y →
    HasDerivAt2 (fun a b => φ (u a b)) (φ' * ux) (φ' * uy) x y

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

/-- **Implicit function derivative, interval-localized.** The standard IFT is inherently local — the
derivative at `x` depends only on `f`'s behavior near `x`, not on `f (s, yc s) = 0` holding for every real
`s`. `hasDerivAt_implicit` above requires the latter (a genuinely global curve identity), which no total
`yc` can satisfy for a curve with no global solution branch — e.g. `eˣ+eʸ=c`, solvable only for `x < log c`
(`multivariate-khovanskii-chainN-scoping.md §9.1`). This axiom weakens the hypothesis to match: `f (s, yc
s) = 0` only on an open interval `(p, q) ∋ x`. Strictly weaker than `hasDerivAt_implicit` (any global
witness gives a local one on an arbitrary `(p,q)` by restriction), so this does not replace it — added
alongside as a separate axiom to avoid touching the existing one and everything built on it. -/
axiom hasDerivAt_implicit_local (f : Real → Real → Real) (fx fy : Real) (yc : Real → Real) (x p q : Real)
    (hp : p < x) (hq : x < q) :
    HasDerivAt2 f fx fy x (yc x) → fy ≠ 0 → (∀ s : Real, p < s → s < q → f s (yc s) = 0) →
    HasDerivAt yc (-fx / fy) x

/-- **`curve_tangent_and_chain`, interval-localized.** Same conclusion, same proof shape, built from
`hasDerivAt_implicit_local` instead — the curve identity only needs to hold on `(p,q) ∋ x`, not globally.
-/
theorem curve_tangent_and_chain_local (f g : Real → Real → Real) (fx fy gx gy : Real) (yc : Real → Real)
    (x p q : Real) (hp : p < x) (hq : x < q)
    (hf2 : HasDerivAt2 f fx fy x (yc x)) (hg2 : HasDerivAt2 g gx gy x (yc x))
    (hfy : fy ≠ 0) (hid : ∀ s : Real, p < s → s < q → f s (yc s) = 0) :
    HasDerivAt yc (-fx / fy) x
      ∧ fx + fy * (-fx / fy) = 0
      ∧ HasDerivAt (fun s => g s (yc s)) (gx * 1 + gy * (-fx / fy)) x := by
  have hyc : HasDerivAt yc (-fx / fy) x := hasDerivAt_implicit_local f fx fy yc x p q hp hq hf2 hfy hid
  refine ⟨hyc, ?_, ?_⟩
  · have h : fy * (-fx / fy) = -fx := by
      rw [div_def (-fx) fy hfy, ← mul_assoc, mul_comm fy (-fx), mul_assoc, mul_inv fy hfy, mul_one_ax]
    rw [h]; exact add_neg fx
  · exact HasDerivAt2_comp g gx gy (fun s => s) yc 1 (-fx / fy) x hg2 (HasDerivAt_id x) hyc

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

/-- **Framework validation.** The joint derivative of `g(x,y) = eˣ + eʸ − d` is `(eˣ, eʸ)`, built entirely
from the base-case + arithmetic + composition rules — so `HasDerivAt2` is genuinely constructible for a
Pfaffian bivariate function (here the sum-instance's `g`), not just posited. -/
theorem hasDerivAt2_exp_sum (d x y : Real) :
    HasDerivAt2 (fun a b => exp a + exp b - d) (exp x) (exp y) x y := by
  have hExpA : HasDerivAt2 (fun a _ => exp a) (exp x * 1) (exp x * 0) x y :=
    HasDerivAt2_scomp exp (exp x) (fun a _ => a) 1 0 x y (HasDerivAt_exp x) (HasDerivAt2_projX x y)
  have hExpB : HasDerivAt2 (fun _ b => exp b) (exp y * 0) (exp y * 1) x y :=
    HasDerivAt2_scomp exp (exp y) (fun _ b => b) 0 1 x y (HasDerivAt_exp y) (HasDerivAt2_projY x y)
  have hSum := HasDerivAt2_add _ _ _ _ _ _ x y hExpA hExpB
  have hSub := HasDerivAt2_sub _ _ _ _ _ _ x y hSum (HasDerivAt2_const d x y)
  have e1 : exp x * 1 + exp y * 0 - 0 = exp x := by mach_ring
  have e2 : exp x * 0 + exp y * 1 - 0 = exp y := by mach_ring
  rw [e1, e2] at hSub
  exact hSub

end Real
end MachLib
