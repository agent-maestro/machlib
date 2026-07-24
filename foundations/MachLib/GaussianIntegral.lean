import MachLib.RiemannIntegralContinuous
import MachLib.Differentiation

/-!
# The Gaussian kernel's Riemann integral exists

`erf` is axiomatized in `MachLib.Trig` completely opaquely — `axiom erf : Real → Real`, with only
the bound properties `-1 ≤ erf x ≤ 1`. Its actual definition is
`erf x = (2/√π) · ∫₀ˣ exp(-t²) dt`. This file connects the RIGHT-HAND SIDE — the integral itself —
to something real for the first time: `exp(-t²)` is continuous everywhere, so
`RiemannIntegralContinuous.lean`'s `continuous_riemann_integrable` applies directly, and the
Gaussian integral genuinely EXISTS as a Riemann integral in MachLib.

**What this file does NOT do, and why**: it does not derive the Gaussian normalization constant
`√π` (equivalently, does not prove `∫₀^∞ exp(-t²)dt = √π/2`), and it does not connect this integral
back to the `erf` axiom via an equation. Both would need machinery genuinely beyond what exists or
is being added here:

- The constant `√π` is one of the harder classical integrals — the standard proof (Poisson's
  trick: square the integral, convert to polar coordinates, evaluate the resulting 2D integral)
  needs multivariable/improper integration MachLib has none of. Alternative routes (Gamma/Beta
  function identities, Wallis product, Laplace's method) all need comparable machinery MachLib
  also doesn't have. This is a substantially bigger undertaking than either Riemann integral file.
- Connecting `erf x = (2/√π) · gaussianIntegral x` to the existing opaque `erf` axiom would itself
  be a NEW axiom (asserting a specific numerical relationship between two independently-axiomatized
  objects) — the kind of decision this project's discipline routes through explicit user sign-off
  (see `HasDerivAt_of_eps_delta`'s `AskUserQuestion` in the derivative arc), not something to add
  unilaterally.

So the honest, complete claim here is narrower but real: `∫₀ˣ exp(-t²) dt` — the object `erf` is
DEFINED in terms of — is no longer just informal notation; it is a Lean object with a machine
verified existence proof, for the first time in MachLib.

`sorryAx`-free, no new axioms.
-/

namespace MachLib
namespace Real

/-! ## §1 — The Gaussian kernel is continuous everywhere -/

/-- `(t·t)' = t + t`, via the product rule applied to the identity function twice. -/
theorem hasDerivAt_sq (x : Real) : HasDerivAt (fun t => t * t) (x + x) x := by
  have h := HasDerivAt_mul (fun t => t) (fun t => t) 1 1 x (HasDerivAt_id x) (HasDerivAt_id x)
  rwa [show (1:Real) * x + x * 1 = x + x from by mach_ring] at h

/-- `(-(t·t))' = -(x+x)`. -/
theorem hasDerivAt_neg_sq (x : Real) : HasDerivAt (fun t => -(t * t)) (-(x + x)) x :=
  HasDerivAt_neg (fun t => t * t) (x + x) x (hasDerivAt_sq x)

/-- `(exp(-(t·t)))' = exp(-(x·x)) · (-(x+x))`, via the chain rule. -/
theorem hasDerivAt_gaussian (x : Real) :
    HasDerivAt (fun t => Real.exp (-(t * t))) (Real.exp (-(x * x)) * (-(x + x))) x :=
  HasDerivAt_comp Real.exp (fun t => -(t * t)) (-(x + x)) (Real.exp (-(x * x))) x
    (hasDerivAt_neg_sq x) (HasDerivAt_exp (-(x * x)))

/-- The Gaussian kernel `exp(-t²)` is continuous at every point. -/
theorem gaussian_continuous (x : Real) : ContinuousAt (fun t => Real.exp (-(t * t))) x :=
  hasDerivAt_continuousAt (hasDerivAt_gaussian x)

/-! ## §2 — The Gaussian integral exists -/

/-- **`erf`'s defining integral genuinely exists.** `∫₀ˣ exp(-t²) dt` — for any `x ≥ 0` — is a
well-defined Riemann integral: there is a value `I` sandwiched between every dyadic lower and
upper Darboux sum, with the gap shrinking below any `ε > 0`. Instantiates
`RiemannIntegralContinuous.continuous_riemann_integrable` at the Gaussian kernel. -/
theorem gaussian_integral_exists (x : Real) (hx : 0 ≤ x) :
    ∃ I : Real,
      (∀ k, lowerSumCont (fun t => Real.exp (-(t * t))) 0 x hx (fun z _ _ => gaussian_continuous z)
          (2 ^ k) (two_pow_pos k) ≤ I ∧
        I ≤ upperSumCont (fun t => Real.exp (-(t * t))) 0 x hx
          (fun z _ _ => gaussian_continuous z) (2 ^ k) (two_pow_pos k)) ∧
      (∀ ε : Real, 0 < ε → ∃ k,
        upperSumCont (fun t => Real.exp (-(t * t))) 0 x hx (fun z _ _ => gaussian_continuous z)
            (2 ^ k) (two_pow_pos k)
          - lowerSumCont (fun t => Real.exp (-(t * t))) 0 x hx
              (fun z _ _ => gaussian_continuous z) (2 ^ k) (two_pow_pos k) < ε) :=
  continuous_riemann_integrable (fun t => Real.exp (-(t * t))) 0 x hx
    (fun z _ _ => gaussian_continuous z)

/-- The genuine Riemann-integral value of `∫₀ˣ exp(-t²) dt`, for `x ≥ 0`. This is the object
`erf x` is defined in terms of (up to the `2/√π` normalization — see this file's header for why
that constant is not derived here). -/
noncomputable def gaussianIntegral (x : Real) (hx : 0 ≤ x) : Real :=
  Classical.choose (gaussian_integral_exists x hx)

end Real
end MachLib
