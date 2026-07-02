import MachLib.IterExpProdDeriv

/-!
# Phase D (D1) — the ∀N Rolle-vehicle exponent and its derivative

The depth-`N` integrating-factor vehicle is `V(x) = f(x)·exp(−E(x))` with exponent
`E(x) = Σ_{k<m} dₖ·iterExp k x + c·x` (`m = N−1` levels). This file builds that exponent as a level-sum
and proves its `HasDerivAt` — the analytic heart of Phase D — from the bound-free iterated-exp derivative
`HasDerivAt_iterExp_prodExp`.

* `vehExpo d c m` — the (sign-folded) exponent `Σ_{k<m} (−dₖ)·iterExp k x + (−c)·x`;
* `vehExpoDeriv d c x m` — its derivative `Σ_{k<m} (−dₖ)·prodExp x k + (−c)`;
* `HasDerivAt_vehExpo` — `HasDerivAt (vehExpo d c m) (vehExpoDeriv d c x m) x`, by induction on the number
  of levels `m` (summing `HasDerivAt_mul`/`HasDerivAt_iterExp_prodExp` per level). No depth bound; no `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.IterExpChainMod

/-- The sign-folded vehicle exponent with `m` levels: `Σ_{k<m} (−dₖ)·iterExp k x + (−c)·x`. -/
noncomputable def vehExpo (d : Nat → Nat) (c : Real) : Nat → Real → Real
  | 0 => fun x => (-c) * x
  | m + 1 => fun x => (-MachLib.Real.natCast (d m)) * iterExp m x + vehExpo d c m x

/-- The derivative of `vehExpo d c m`: `Σ_{k<m} (−dₖ)·prodExp x k + (−c)`. -/
noncomputable def vehExpoDeriv (d : Nat → Nat) (c : Real) (x : Real) : Nat → Real
  | 0 => -c
  | m + 1 => (-MachLib.Real.natCast (d m)) * prodExp x m + vehExpoDeriv d c x m

/-- **`HasDerivAt` for the vehicle exponent, `∀ m`.** By induction on the number of levels. -/
theorem HasDerivAt_vehExpo (d : Nat → Nat) (c : Real) (x : Real) :
    ∀ m, HasDerivAt (vehExpo d c m) (vehExpoDeriv d c x m) x := by
  intro m
  induction m with
  | zero =>
      show HasDerivAt (fun x => (-c) * x) (-c) x
      have h := HasDerivAt_mul (fun _ => -c) (fun x => x) 0 1 x (HasDerivAt_const _ x) (HasDerivAt_id x)
      rw [zero_mul, zero_add, mul_one_ax] at h
      exact h
  | succ m ih =>
      show HasDerivAt (fun x => (-MachLib.Real.natCast (d m)) * iterExp m x + vehExpo d c m x)
        ((-MachLib.Real.natCast (d m)) * prodExp x m + vehExpoDeriv d c x m) x
      have hlvl := HasDerivAt_mul (fun _ => -MachLib.Real.natCast (d m)) (iterExp m)
        0 (prodExp x m) x (HasDerivAt_const _ x) (HasDerivAt_iterExp_prodExp m x)
      rw [zero_mul, zero_add] at hlvl
      exact HasDerivAt_add (fun y => (-MachLib.Real.natCast (d m)) * iterExp m y) (vehExpo d c m)
        ((-MachLib.Real.natCast (d m)) * prodExp x m) (vehExpoDeriv d c x m) x hlvl ih

end MachLib.IterExpDepthN
