import MachLib.TwoExpCurveCount
import MachLib.MultiVarTwoExpSum
import MachLib.BivariateDeriv

/-!
# End-to-end validation of the IFT-gate closure (Gate 2d, two-exp)

Re-derives the sum-instance count `{x+y=c, eˣ+eʸ=d} ≤ 2` through the **general-curve pipeline**
`khovanskii_rolle_count_curve` — exercising the bivariate framework (`HasDerivAt2` built from base cases),
the implicit-derivative bridge (`hasDerivAt_implicit`, via `curve_tangent_and_chain`), and the
Khovanskii–Rolle counting, all at once. Unlike the direct `MultiVarTwoExpSum` proof (which hand-supplies
`yc'` and the derivative/tangent hypotheses to T.1), this drives the count entirely through the IFT gate:
the tangent condition and the `g`-along-curve chain rule are DERIVED from the joint derivatives. So the
whole IFT-gate closure is validated end-to-end on a real two-exponential system.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real

/-- **`{x+y=c, eˣ+eʸ=d} ≤ 2`, via the general-curve pipeline.** `f = x+y−c` (line, `fᵧ = 1 ≠ 0`,
parametrized by `yc = c−x`), `g = eˣ+eʸ−d`; both joint derivatives are built from the bivariate framework.
The count runs through `khovanskii_rolle_count_curve`, whose parametrization hypotheses are discharged by
the implicit-function bridge — validating the IFT gate end-to-end. -/
theorem curve_exp_sum_le_two (c d a b : Real) (hab : a < b) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (fun s => exp s + exp ((fun x => c - x) s) - d) z = 0) →
      zeros.length ≤ 1 + 1 :=
  khovanskii_rolle_count_curve
    (fun a b => a + b - c) (fun a b => exp a + exp b - d)
    (fun _ => 1) (fun _ => 1) (fun z => exp z) (fun z => exp (c - z)) (fun x => c - x) a b hab
    -- hf2 : joint derivative of the line f = x+y-c is (1,1)
    (fun z _ _ => by
      have hadd := HasDerivAt2_add (fun a _ => a) (fun _ b => b) 1 0 0 1 z (c - z)
        (HasDerivAt2_projX z (c - z)) (HasDerivAt2_projY z (c - z))
      have hsub := HasDerivAt2_sub _ _ _ _ _ _ z (c - z) hadd (HasDerivAt2_const c z (c - z))
      rw [show (1 : Real) + 0 - 0 = 1 from by mach_ring,
          show (0 : Real) + 1 - 0 = 1 from by mach_ring] at hsub
      exact hsub)
    -- hg2 : joint derivative of g = eˣ+eʸ-d is (eˣ, e^{c-z}) at (z, c-z)
    (fun z _ _ => hasDerivAt2_exp_sum d z (c - z))
    -- fy = 1 ≠ 0
    (fun _ _ _ => one_ne_zero)
    -- curve identity: f(s, c-s) = 0
    (fun s => by show s + (c - s) - c = 0; mach_ring)
    1
    -- Jacobian bound N = 1: J = eᶜ⁻ᶻ - eᶻ is strictly antitone, so ≤ 1 zero
    (fun zeros_J hnd hJ =>
      inj_zeros_le_one (fun z => exp (c - z) - exp z)
        (injective_of_antitone _ (sumJac_antitone c)) zeros_J hnd
        (fun z hz => by
          obtain ⟨_, _, hjz⟩ := hJ z hz
          show exp (c - z) - exp z = 0
          rw [show exp (c - z) - exp z = 1 * exp (c - z) - 1 * exp z from by mach_ring]
          exact hjz))

end TwoExp
end MultiVarMod
end MachLib
