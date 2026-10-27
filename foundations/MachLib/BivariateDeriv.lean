import MachLib.Rolle
import MachLib.Differentiation
import MachLib.Ring
import MachLib.IntermediateValue

/-!
# Bivariate differentiation + the implicit function derivative (Gate 2d, IFT gate — brick 1.c)

The last piece of the IFT/parametrization gate. The model's single-variable `HasDerivAt` is entirely
axiomatized (`HasDerivAt_exp`, `_comp`, `_add`, …); this file adds the **bivariate analogs** in the same
style — an opaque `HasDerivAt2 f fx fy x y` (joint/Fréchet differentiability with partials `fx, fy`), the
**curve chain rule**, and the **implicit function derivative**. All three are standard, witnessable facts
(mirroring Mathlib's `HasFDerivAt`/`HasDerivAt.comp`/`ImplicitFunction`), the bivariate counterparts of the
single-variable axioms already trusted. Since 2026-10-27 they are witnessed in `monogate-lean` and trusted;
`HasDerivAt2_sub` and the global `hasDerivAt_implicit` are theorems here, of the other rules.

From them, `curve_tangent_and_chain` DERIVES exactly what the parametrized Khovanskii–Rolle step
(`TwoExp.khovanskii_rolle_count`) takes as hypotheses: the tangent condition `fₓ + fᵧ·yc' = 0` (algebra,
`yc' = −fₓ/fᵧ`) and the chain rule `HasDerivAt (g along the curve) (gₓ + gᵧ·yc')`, for a curve `yc` that solves
`f = 0` and is continuous where it is used. A root `yc x` exists and is unique in-model for each `x` where `f`
is monotone in `y` (`exists_unique_root`, from `sup_exists`); nothing in the corpus proves the resulting curve
continuous, so every caller supplies that hypothesis itself.
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

axiom HasDerivAt2_mul (f g : Real → Real → Real) (fx fy gx gy x y : Real) :
    HasDerivAt2 f fx fy x y → HasDerivAt2 g gx gy x y →
    HasDerivAt2 (fun a b => f a b * g a b) (fx * g x y + f x y * gx) (fy * g x y + f x y * gy) x y

/-- The difference rule. An axiom until 2026-10-27, when the independent review of that day's rebaseline found it
derivable (owner's ruling: convert it): `f − g = f + (−1)·g`, so the product rule with a constant and the sum rule
give it, and field algebra fixes the partials. -/
theorem HasDerivAt2_sub (f g : Real → Real → Real) (fx fy gx gy x y : Real) :
    HasDerivAt2 f fx fy x y → HasDerivAt2 g gx gy x y →
    HasDerivAt2 (fun a b => f a b - g a b) (fx - gx) (fy - gy) x y := by
  intro hf hg
  have hm := HasDerivAt2_mul (fun _ _ => -(1 : Real)) g 0 0 gx gy x y (HasDerivAt2_const (-1) x y) hg
  have ha := HasDerivAt2_add f (fun a b => (fun _ _ => -(1 : Real)) a b * g a b) fx fy _ _ x y hf hm
  have e1 : fx + (0 * g x y + -(1 : Real) * gx) = fx - gx := by mach_ring
  have e2 : fy + (0 * g x y + -(1 : Real) * gy) = fy - gy := by mach_ring
  have ef : (fun a b => f a b + (fun _ _ => -(1 : Real)) a b * g a b) = (fun a b => f a b - g a b) := by
    funext a b
    show f a b + -(1 : Real) * g a b = f a b - g a b
    mach_ring
  rw [e1, e2] at ha
  exact ef ▸ ha

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

/-- **Implicit function derivative** (the IFT bridge), interval-localized. If `f (s, yc s) = 0` for `s` in an
open interval `(p, q) ∋ x`, `f` is jointly differentiable at `(x, yc x)` with `fᵧ ≠ 0`, and the curve `yc` is
CONTINUOUS at `x`, then `yc` is differentiable at `x` with `yc'(x) = −fₓ/fᵧ`. The derivative at `x` depends only on
`f` near `x`, which is why the identity is asked for on `(p, q)` only: a curve with no global solution branch, such as
`eˣ + eʸ = c` (solvable only for `x < log c`, `multivariate-khovanskii-chainN-scoping.md §9.1`), satisfies it.
Asking less of the curve, it is the STRONGER of the two statements, and the global `hasDerivAt_implicit` below is a
theorem of it.

**The continuity hypothesis was missing until 2026-10-27, and without it this axiom and its global form were FALSE
and inconsistent with the trusted ones.** Nothing stopped `yc` from jumping between solution branches: for
`f a b = b (b − 1)` a step function from `0` to `1` satisfies the curve identity everywhere with `fᵧ = ±1`, so the
old statements gave it derivative `0` at every point, and the mean value theorem then gives `1 = 0`.
`BivariateImplicitControls` derives `False` from each old statement and refutes the old
`khovanskii_rolle_count_curve`. The implicit function theorem's derivative needs exactly this much: Fréchet
differentiability at the one point (`HasDerivAt2`), `fᵧ ≠ 0`, and a solution curve continuous there. Witnessed in
`monogate-lean` against Mathlib's `HasFDerivAt` (`implicit_deriv_core`). -/
axiom hasDerivAt_implicit_local (f : Real → Real → Real) (fx fy : Real) (yc : Real → Real) (x p q : Real)
    (hp : p < x) (hq : x < q) :
    HasDerivAt2 f fx fy x (yc x) → fy ≠ 0 → ContinuousAt yc x →
    (∀ s : Real, p < s → s < q → f s (yc s) = 0) →
    HasDerivAt yc (-fx / fy) x

/-- **Implicit function derivative, global form.** The curve identity for every real `s` restricts to the interval
`(x − 1, x + 1)`. An axiom until 2026-10-27 (restated that day with `ContinuousAt yc x`, see
`hasDerivAt_implicit_local`); the independent review of the rebaseline found it derivable, and the owner ruled to
convert it. -/
theorem hasDerivAt_implicit (f : Real → Real → Real) (fx fy : Real) (yc : Real → Real) (x : Real) :
    HasDerivAt2 f fx fy x (yc x) → fy ≠ 0 → ContinuousAt yc x → (∀ s : Real, f s (yc s) = 0) →
    HasDerivAt yc (-fx / fy) x := by
  intro h2 hfy hc hid
  have hlt : x < x + 1 := by
    have v := add_lt_add_left zero_lt_one_ax x
    rw [add_zero] at v
    exact v
  have hgt : x + -1 < x := by
    have hn : -(1 : Real) < 0 := by
      have v := add_lt_add_left zero_lt_one_ax (-(1 : Real))
      rw [add_zero, neg_add_self] at v
      exact v
    have v := add_lt_add_left hn x
    rw [add_zero] at v
    exact v
  exact hasDerivAt_implicit_local f fx fy yc x (x + -1) (x + 1) hgt hlt h2 hfy hc (fun s _ _ => hid s)

/-- **`curve_tangent_and_chain`, interval-localized.** Same conclusion, same proof shape, built from
`hasDerivAt_implicit_local` instead — the curve identity only needs to hold on `(p,q) ∋ x`, not globally.
-/
theorem curve_tangent_and_chain_local (f g : Real → Real → Real) (fx fy gx gy : Real) (yc : Real → Real)
    (x p q : Real) (hp : p < x) (hq : x < q)
    (hf2 : HasDerivAt2 f fx fy x (yc x)) (hg2 : HasDerivAt2 g gx gy x (yc x))
    (hfy : fy ≠ 0) (hcont : ContinuousAt yc x) (hid : ∀ s : Real, p < s → s < q → f s (yc s) = 0) :
    HasDerivAt yc (-fx / fy) x
      ∧ fx + fy * (-fx / fy) = 0
      ∧ HasDerivAt (fun s => g s (yc s)) (gx * 1 + gy * (-fx / fy)) x := by
  have hyc : HasDerivAt yc (-fx / fy) x :=
    hasDerivAt_implicit_local f fx fy yc x p q hp hq hf2 hfy hcont hid
  refine ⟨hyc, ?_, ?_⟩
  · have h : fy * (-fx / fy) = -fx := by
      rw [div_def (-fx) fy hfy, ← mul_assoc, mul_comm fy (-fx), mul_assoc, mul_inv fy hfy, mul_one_ax]
    rw [h]; exact add_neg fx
  · exact HasDerivAt2_comp g gx gy (fun s => s) yc 1 (-fx / fy) x hg2 (HasDerivAt_id x) hyc

/-- **The parametrization discharges the Khovanskii–Rolle hypotheses.** Given a curve `{f = 0}`
parametrized by `y = yc x` (jointly differentiable `f, g` at `(x, yc x)`, `fᵧ ≠ 0`, `f ≡ 0` along the arc),
the implicit function `yc`, continuous at `x`, yields: (1) the **tangent condition** `fₓ + fᵧ·yc' = 0` and (2) the **chain rule**
`HasDerivAt (g along the curve) (gₓ·1 + gᵧ·yc')` — exactly `khovanskii_rolle_count`'s `hcurve` and
`hGderiv` (with `yc' = −fₓ/fᵧ`). -/
theorem curve_tangent_and_chain (f g : Real → Real → Real) (fx fy gx gy : Real) (yc : Real → Real)
    (x : Real) (hf2 : HasDerivAt2 f fx fy x (yc x)) (hg2 : HasDerivAt2 g gx gy x (yc x))
    (hfy : fy ≠ 0) (hcont : ContinuousAt yc x) (hid : ∀ s : Real, f s (yc s) = 0) :
    HasDerivAt yc (-fx / fy) x
      ∧ fx + fy * (-fx / fy) = 0
      ∧ HasDerivAt (fun s => g s (yc s)) (gx * 1 + gy * (-fx / fy)) x := by
  have hyc : HasDerivAt yc (-fx / fy) x := hasDerivAt_implicit f fx fy yc x hf2 hfy hcont hid
  refine ⟨hyc, ?_, ?_⟩
  · have h : fy * (-fx / fy) = -fx := by
      rw [div_def (-fx) fy hfy, ← mul_assoc, mul_comm fy (-fx), mul_assoc, mul_inv fy hfy, mul_one_ax]
    rw [h]; exact add_neg fx
  · exact HasDerivAt2_comp g gx gy (fun s => s) yc 1 (-fx / fy) x hg2 (HasDerivAt_id x) hyc

/-- **The line `x ↦ c − x` is continuous everywhere**, being differentiable (`hasDerivAt_continuousAt`). The
implicit-derivative instances over a line curve discharge their continuity hypothesis with it. -/
theorem continuousAt_const_sub (c z : Real) : ContinuousAt (fun x => c - x) z :=
  hasDerivAt_continuousAt
    (HasDerivAt_sub (fun _ => c) (fun x => x) 0 1 z (HasDerivAt_const c z) (HasDerivAt_id z))

/-- Continuity carries over to a function equal to a continuous one at every point. -/
theorem continuousAt_congr_fun {f g : Real → Real} (h : ∀ t, f t = g t) (z : Real)
    (hf : ContinuousAt f z) : ContinuousAt g z := by
  rw [show g = f from funext (fun t => (h t).symm)]
  exact hf

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
