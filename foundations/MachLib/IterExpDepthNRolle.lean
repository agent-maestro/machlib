import MachLib.IterExpDepthNVehicle

/-!
# Phase D (D2) — the ∀N Rolle bridge: at `V' = 0`, the reduce value vanishes

The counting content of the "+1 zero per reduce" step. At a point `z` where the vehicle's derivative is
`0` (Rolle's gift between consecutive zeros of `f`), the reduce value `f' − reductMult·f` is `0`. Derived
from `hasDerivAt_vehicleN` (`V'` is the product/chain-rule value), `HasDerivAt_unique`, the factoring
`f'·E + f·(E·(−R)) = E·(f' − R·f)`, and `exp ≠ 0`. Mirrors the depth-3 `polyMultReduce3_eval_zero_of_
vehicle_deriv_zero`, ∀N. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.IterExpChainMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn

private theorem vehicle_deriv_factor (f' E fv R : Real) :
    f' * E + fv * (E * (-R)) = E * (f' - R * fv) := by mach_mpoly [f', E, fv, R]

/-- **The Rolle bridge, ∀N.** At `z` where the vehicle's derivative is `0`, the reduce value
`f' − reductMult·f` is `0`. -/
theorem vehicleN_reduct_zero_of_deriv_zero (f : PfaffianFn) (d : Nat → Nat) (c : Real) (m : Nat)
    (z : Real) (hf : HasDerivAt f.eval (f.chainTotalDerivative.eval z) z)
    (g'' : Real) (hg''_deriv : HasDerivAt (vehicleN f d c m) g'' z) (hg''_zero : g'' = 0) :
    f.chainTotalDerivative.eval z - reductMult d c z m * f.eval z = 0 := by
  have hcanon := hasDerivAt_vehicleN f d c m z hf
  have huniq := HasDerivAt_unique (vehicleN f d c m) g''
    (f.chainTotalDerivative.eval z * Real.exp (vehExpo d c m z)
      + f.eval z * (Real.exp (vehExpo d c m z) * vehExpoDeriv d c z m)) z hg''_deriv hcanon
  have hraw : f.chainTotalDerivative.eval z * Real.exp (vehExpo d c m z)
      + f.eval z * (Real.exp (vehExpo d c m z) * vehExpoDeriv d c z m) = 0 := by
    rw [← huniq]; exact hg''_zero
  rw [vehExpoDeriv_eq_neg_reductMult] at hraw
  rw [vehicle_deriv_factor (f.chainTotalDerivative.eval z) (Real.exp (vehExpo d c m z))
        (f.eval z) (reductMult d c z m)] at hraw
  exact mul_eq_zero_of_factor_ne_zero (exp_ne_zero _) hraw

end MachLib.IterExpDepthN
