import MachLib.IterExpDepthNVehicleExpo
import MachLib.ChainExp2NoZeros

/-!
# Phase D (D1) — the ∀N Rolle vehicle `V = f · exp(vehExpo)` and its calculus

The integrating-factor vehicle for the depth-`N` reduce, generic in the level-degrees `d` and the
constant `c` (the coupling to the actual `fullMult` multiplier is deferred to D3):

* `vehicleN f d c m x = f.eval x · exp(vehExpo d c m x)` — same zero set as `f` (`exp ≠ 0`);
* `hasDerivAt_vehicleN` — its derivative by the product/chain rules, from `HasDerivAt_vehExpo`;
* `reductMult d c x m = Σ_{k<m} dₖ·prodExp x k + c`, with `vehExpoDeriv = − reductMult`, so the vehicle's
  derivative factors as `exp(vehExpo)·(f' − reductMult·f)` — the reduce value the Rolle step (D2) counts.

No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.IterExpChainMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn

/-- The ∀N Rolle vehicle: `f.eval x · exp(vehExpo d c m x)` (the sign is folded into `vehExpo`). -/
noncomputable def vehicleN (f : PfaffianFn) (d : Nat → Nat) (c : Real) (m : Nat) : Real → Real :=
  fun x => f.eval x * Real.exp (vehExpo d c m x)

/-- **Same-zero-set:** the vehicle vanishes exactly where `f` does. -/
theorem vehicleN_zero_iff (f : PfaffianFn) (d : Nat → Nat) (c : Real) (m : Nat) (x : Real) :
    vehicleN f d c m x = 0 ↔ f.eval x = 0 := by
  show f.eval x * Real.exp (vehExpo d c m x) = 0 ↔ f.eval x = 0
  constructor
  · intro h
    rw [mul_comm] at h
    exact mul_eq_zero_of_factor_ne_zero (exp_ne_zero _) h
  · intro h; rw [h, zero_mul]

/-- **HasDerivAt for the vehicle** (raw product-rule form). -/
theorem hasDerivAt_vehicleN (f : PfaffianFn) (d : Nat → Nat) (c : Real) (m : Nat) (x : Real)
    (hf : HasDerivAt f.eval (f.chainTotalDerivative.eval x) x) :
    HasDerivAt (vehicleN f d c m)
      (f.chainTotalDerivative.eval x * Real.exp (vehExpo d c m x)
        + f.eval x * (Real.exp (vehExpo d c m x) * vehExpoDeriv d c x m)) x := by
  have hE := HasDerivAt_comp Real.exp (vehExpo d c m) (vehExpoDeriv d c x m)
    (Real.exp (vehExpo d c m x)) x (HasDerivAt_vehExpo d c x m) (HasDerivAt_exp _)
  exact HasDerivAt_mul f.eval (fun y => Real.exp (vehExpo d c m y))
    (f.chainTotalDerivative.eval x) (Real.exp (vehExpo d c m x) * vehExpoDeriv d c x m) x hf hE

/-- The reduce multiplier value along the chain: `Σ_{k<m} dₖ·prodExp x k + c`. -/
noncomputable def reductMult (d : Nat → Nat) (c : Real) (x : Real) : Nat → Real
  | 0 => c
  | m + 1 => MachLib.Real.natCast (d m) * prodExp x m + reductMult d c x m

private theorem neg_reduct_ring (a b r : Real) : (-a) * b + (-r) = -(a * b + r) := by
  mach_mpoly [a, b, r]

/-- The vehicle-exponent derivative is `−` the reduce multiplier. -/
theorem vehExpoDeriv_eq_neg_reductMult (d : Nat → Nat) (c : Real) (x : Real) (m : Nat) :
    vehExpoDeriv d c x m = - reductMult d c x m := by
  induction m with
  | zero => show (-c : Real) = -c; rfl
  | succ m ih =>
      show (-MachLib.Real.natCast (d m)) * prodExp x m + vehExpoDeriv d c x m
        = -(MachLib.Real.natCast (d m) * prodExp x m + reductMult d c x m)
      rw [ih]
      exact neg_reduct_ring (MachLib.Real.natCast (d m)) (prodExp x m) (reductMult d c x m)

end MachLib.IterExpDepthN
