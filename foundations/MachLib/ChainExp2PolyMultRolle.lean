import MachLib.KhovanskiiReduction

/-!
# Piece 2 — the Rolle bridge for the polynomial-multiplier reduce

The correct chain-2 reduce is `R(P) = P' − m·P` with the **polynomial** multiplier `m = d·y₀ + c`
(`ChainExp2Reducer.chain2Reduce`). Its soundness (`#zeros(P) ≤ #zeros(R P) + 1`) is a Rolle argument on
the integrating-factor vehicle `g(x) = P(x)·e^{−∫m}`. Here `∫m = d·∫y₀ + c·x = d·e^x + c·x` (since
`y₀ = e^x`), so the factor is

  `e^{−∫m} = e^{−(d·e^x + c·x)} = e^{−d·e^x}·e^{−cx} = y₁^{−d}·e^{−cx}`   (because `y₁ = e^{e^x}`),

never zero along the chain. This file builds the **analytic heart**: the vehicle has the same zeros as
`P` (factor ≠ 0), and its derivative *factors* as `e^{−∫m}·(P' − m·P)` — so a zero of the vehicle's
derivative (which Rolle hands us between consecutive zeros of `P`) is exactly a zero of `R(P)`. This is
the polynomial-multiplier analog of `mulNegExpX_aux` / `scaledReduction_eval_zero_of_g_deriv_zero`, with
the only change being `exp(−cx) ⤳ exp(−(d·e^x + c·x))`.

The multiplier value `d` is an arbitrary `Nat` parameter here — the bridge holds for every `(d, c)`; the
specialisation `d = degreeY₁ P` (needed for the *descent*) is Piece 3, not soundness. Wiring this bridge
into a `reduce`-style constructor of `IsKhovanskiiReducible` (the zero-count bookkeeping) is the remaining
Piece-2 step; the novel analysis is done here. Single-exp framework untouched (Path B).
-/

namespace MachLib.ChainExp2PolyMultRolle

open MachLib.Real
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn

/-- The Rolle vehicle for the polynomial-multiplier reduce: `f.eval x · exp(−(d·eˣ + c·x))`. The
integrating factor `exp(−(d·eˣ + c·x)) = y₁^{−d}·e^{−cx}` is never zero. (Written with the sign folded
in — `(−d)·eˣ + (−c)·x` — to keep the `HasDerivAt` assembly free of a separate negation step.) -/
noncomputable def vehicleM (f : PfaffianFn) (d : Nat) (c : Real) : Real → Real :=
  fun x => f.eval x * Real.exp ((-MachLib.Real.natCast d) * Real.exp x + (-c) * x)

/-- **Same-zero-set:** the vehicle vanishes exactly where `f` does (the factor `exp(…)` is never 0). -/
theorem vehicleM_zero_iff (f : PfaffianFn) (d : Nat) (c : Real) (x : Real) :
    vehicleM f d c x = 0 ↔ f.eval x = 0 := by
  show f.eval x * Real.exp ((-MachLib.Real.natCast d) * Real.exp x + (-c) * x) = 0 ↔ f.eval x = 0
  constructor
  · intro h
    have hexp_ne : Real.exp ((-MachLib.Real.natCast d) * Real.exp x + (-c) * x) ≠ 0 := exp_ne_zero _
    rw [mul_comm] at h
    exact mul_eq_zero_of_factor_ne_zero hexp_ne h
  · intro h
    rw [h, zero_mul]

/-- **HasDerivAt for the vehicle (raw product-rule form).** Derivative
`f' · E + f · (E · ((−d)·eˣ + (−c)))`, `E = exp(−(d·eˣ + c·x))`. Assembled from the chain/product/sum
rules, exactly like `hasDerivAt_mulNegExpX_aux_raw`. -/
theorem hasDerivAt_vehicleM (f : PfaffianFn) (d : Nat) (c : Real) (z : Real)
    (hf : HasDerivAt f.eval (f.chainTotalDerivative.eval z) z) :
    HasDerivAt (vehicleM f d c)
      (f.chainTotalDerivative.eval z
          * Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z)
        + f.eval z
          * (Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z)
             * ((-MachLib.Real.natCast d) * Real.exp z + (-c))))
      z := by
  -- inner u(x) = (−d)·eˣ + (−c)·x, with derivative (−d)·eᶻ + (−c).
  have hA := HasDerivAt_mul (fun _ => -MachLib.Real.natCast d) Real.exp 0 (Real.exp z) z
              (HasDerivAt_const _ z) (HasDerivAt_exp z)
  have hB := HasDerivAt_mul (fun _ => -c) (fun x => x) 0 1 z
              (HasDerivAt_const _ z) (HasDerivAt_id z)
  have hu := HasDerivAt_add (fun y => (-MachLib.Real.natCast d) * Real.exp y)
              (fun y => (-c) * y) _ _ z hA hB
  have hu_eq :
      (0 * Real.exp z + (-MachLib.Real.natCast d) * Real.exp z) + (0 * z + (-c) * 1)
      = (-MachLib.Real.natCast d) * Real.exp z + (-c) := by mach_ring
  rw [hu_eq] at hu
  -- E(x) = exp(u(x)), derivative E·u'.
  have hE := HasDerivAt_comp Real.exp
              (fun x => (-MachLib.Real.natCast d) * Real.exp x + (-c) * x)
              ((-MachLib.Real.natCast d) * Real.exp z + (-c))
              (Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z))
              z hu (HasDerivAt_exp _)
  -- g = f.eval · E, product rule.
  exact HasDerivAt_mul f.eval
          (fun x => Real.exp ((-MachLib.Real.natCast d) * Real.exp x + (-c) * x))
          (f.chainTotalDerivative.eval z)
          (Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z)
            * ((-MachLib.Real.natCast d) * Real.exp z + (-c)))
          z hf hE

/-- **Algebraic factoring** of the raw derivative: `f'·E + f·(E·((−d)·eᶻ+(−c))) = E·(f' − (d·eᶻ+c)·f)`.
Pure ring identity (the `mulNegExpX_derivative_factored` analog). -/
theorem vehicleM_derivative_factored (f' E fv dr c expz : Real) :
    f' * E + fv * (E * ((-dr) * expz + (-c)))
    = E * (f' - (dr * expz + c) * fv) := by mach_mpoly [f', E, fv, dr, c, expz]

/-- **The Rolle bridge.** At a point `z` where the vehicle's derivative is 0 (Rolle's gift between
consecutive zeros of `f`), the polynomial-multiplier reduce value `f' − (d·eᶻ + c)·f` is 0. This is the
soundness core of the chain-2 reduce `R(P) = P' − (d·y₀ + c)·P`. -/
theorem polyMultReduce_eval_zero_of_vehicle_deriv_zero
    (f : PfaffianFn) (d : Nat) (c : Real) (z : Real)
    (hf : HasDerivAt f.eval (f.chainTotalDerivative.eval z) z)
    (g'' : Real)
    (hg''_deriv : HasDerivAt (vehicleM f d c) g'' z)
    (hg''_zero : g'' = 0) :
    f.chainTotalDerivative.eval z
      - (MachLib.Real.natCast d * Real.exp z + c) * f.eval z = 0 := by
  have hcanonical := hasDerivAt_vehicleM f d c z hf
  have huniq := HasDerivAt_unique (vehicleM f d c) g''
                  (f.chainTotalDerivative.eval z
                      * Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z)
                    + f.eval z
                      * (Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z)
                         * ((-MachLib.Real.natCast d) * Real.exp z + (-c))))
                  z hg''_deriv hcanonical
  have hraw_zero :
      f.chainTotalDerivative.eval z
          * Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z)
        + f.eval z
          * (Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z)
             * ((-MachLib.Real.natCast d) * Real.exp z + (-c))) = 0 := by
    rw [← huniq]; exact hg''_zero
  rw [vehicleM_derivative_factored
        (f.chainTotalDerivative.eval z)
        (Real.exp ((-MachLib.Real.natCast d) * Real.exp z + (-c) * z))
        (f.eval z) (MachLib.Real.natCast d) c (Real.exp z)] at hraw_zero
  exact mul_eq_zero_of_factor_ne_zero (exp_ne_zero _) hraw_zero

end MachLib.ChainExp2PolyMultRolle
