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

/-- **Raw zero-count transfer** (in terms of zeros of the vehicle's derivative). -/
theorem zero_count_vehicleN_transfer_raw (f : PfaffianFn) (d : Nat → Nat) (c : Real) (m : Nat)
    (a b : Real) (hab : a < b) (hcoherent : f.chain.IsCoherentOn a b) (N : Nat)
    (h_reduced_bound : ∀ zeros' : List Real, zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          ∃ f'' : Real, HasDerivAt (vehicleN f d c m) f'' z ∧ f'' = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real, zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  intro zeros_f hnodup hzeros
  have hzeros_g : ∀ z ∈ zeros_f, a < z ∧ z < b ∧ vehicleN f d c m z = 0 := by
    intro z hz
    obtain ⟨haz, hzb, hfz⟩ := hzeros z hz
    exact ⟨haz, hzb, (vehicleN_zero_iff f d c m z).mpr hfz⟩
  have hdiff : ∀ x : Real, a < x → x < b →
                ∃ f' : Real, HasDerivAt (vehicleN f d c m) f' x := by
    intro x hax hxb
    exact ⟨_, hasDerivAt_vehicleN f d c m x (hasDerivAt_eval_natural f x (hcoherent x hax hxb))⟩
  exact zero_count_bound_by_deriv (vehicleN f d c m) a b hab hdiff N
          h_reduced_bound zeros_f hnodup hzeros_g

/-- **Zero-count transfer (eval form).** If the reduce value `f' − reductMult·f` has at most `N` zeros on
`(a,b)`, then `f` has at most `N + 1`. The constructive Rolle step, ∀N. -/
theorem zero_count_vehicleN_transfer (f : PfaffianFn) (d : Nat → Nat) (c : Real) (m : Nat)
    (a b : Real) (hab : a < b) (hcoherent : f.chain.IsCoherentOn a b) (N : Nat)
    (h_reduced_bound_eval : ∀ zeros' : List Real, zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          f.chainTotalDerivative.eval z - reductMult d c z m * f.eval z = 0) →
        zeros'.length ≤ N) :
    ∀ zeros_f : List Real, zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ f.eval z = 0) →
      zeros_f.length ≤ N + 1 := by
  apply zero_count_vehicleN_transfer_raw f d c m a b hab hcoherent N
  intro zeros' hnodup' hzeros'_prop
  apply h_reduced_bound_eval zeros' hnodup'
  intro z hz
  obtain ⟨haz, hzb, g'', hg''_deriv, hg''_zero⟩ := hzeros'_prop z hz
  exact ⟨haz, hzb, vehicleN_reduct_zero_of_deriv_zero f d c m z
    (hasDerivAt_eval_natural f z (hcoherent z haz hzb)) g'' hg''_deriv hg''_zero⟩

end MachLib.IterExpDepthN
