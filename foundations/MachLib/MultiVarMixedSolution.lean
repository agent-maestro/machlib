import MachLib.MultiVarMixedCount
import MachLib.MultiVarBezoutFiber

/-!
# Mixed-exponential FULL solution count (Gate 2d, M.3)

Lifts the w-coordinate count (`mixed_wcoord_bound`, M.2) to the full solution count for a plane system with
one exponential of a polynomial, exactly as `bezout_general_fibered` lifted the polynomial x-count. The
solution set is fibered by w-coordinate (`= g(x,y)` value); at a fixed `w₀` the exponential is a constant
`u = e^{w₀}`, so the `(x,y)`-fiber `{P(·,·,e^{w₀}) = 0, Q(·,·,e^{w₀}) = 0, g = w₀}` is an ordinary
polynomial system whose point count is `≤ B` (the polynomial Bezout bound, supplied by the caller and
discharged via `bezout_general_fibered` at fixed `u`).

`mixed_solution_bound`: `#solutions ≤ (ExpPoly w-count) · B`, where the ExpPoly is `w ↦ R(w, e^w)`. Fibered
form (the fibration supplied), as in the polynomial layer. `rolle_ct` + Classical + exp — no multivariate
Rolle. This completes the mixed-exponential arc: M.0 (engine) + M.1 (elimination) + M.2 (substitution +
w-count) + M.3 (fiber → full count).
-/

namespace MachLib
namespace MultiVarMod
namespace ElimK

open MachLib.MultiVarMod.MultiVar
open MachLib.SingleExpKhovanskii (ExpPoly)
open MachLib.SingleExpKhovanskii.ExpPoly
open MachLib.Real

/-- **Mixed-exponential full solution count (fibered).** Given a fibration of the solution set of
`{P, Q, w−g}` (along `u = e^w`) by w-coordinate — distinct w-values (`hfib_nd`), each fiber a list of
`(x,y)` solution points of size `≤ B`, each carrying a common-zero witness with `u = e^w` — the total
solution count is `≤ (|coeffs| + Σ simplified-deg of R(w, e^w)) · B`. The complete
multivariate-transcendental bound for one exponential of a polynomial; no multivariate Rolle. -/
theorem mixed_solution_bound (P Q wg : MultiVar 4) (a b : Real) (hab : a < b)
    (hne : ∃ w : Real, a < w ∧ w < b
      ∧ (toExpPoly (restrict24 (mixedResultant P Q wg))).eval w ≠ 0)
    (B : Nat)
    (fibers : List (Real × List (Real × Real)))
    (hfib_nd : (fibers.map (fun f => f.1)).Nodup)
    (hfib : ∀ f ∈ fibers, f.2.length ≤ B ∧ a < f.1 ∧ f.1 < b ∧
      ∃ env4 : Fin 4 → Real, env4 2 = f.1 ∧ env4 3 = exp f.1 ∧
        MultiVar.eval P env4 = 0 ∧ MultiVar.eval Q env4 = 0 ∧ MultiVar.eval wg env4 = 0) :
    (fibers.flatMap (fun f => f.2)).length
      ≤ ((toExpPoly (restrict24 (mixedResultant P Q wg))).coeffs.length
          + sumSimplifiedDegrees (toExpPoly (restrict24 (mixedResultant P Q wg))).coeffs) * B := by
  have hN : fibers.length
      ≤ (toExpPoly (restrict24 (mixedResultant P Q wg))).coeffs.length
        + sumSimplifiedDegrees (toExpPoly (restrict24 (mixedResultant P Q wg))).coeffs := by
    have h := mixed_wcoord_bound P Q wg a b hab hne (fibers.map (fun f => f.1)) hfib_nd
      (fun w₀ hw₀ => by
        rw [List.mem_map] at hw₀
        obtain ⟨f, hf, rfl⟩ := hw₀
        obtain ⟨_, ha, hb, henv⟩ := hfib f hf
        exact ⟨ha, hb, henv⟩)
    rwa [List.length_map] at h
  exact Nat.le_trans
    (length_flatMap_le' B fibers (fun f hf => (hfib f hf).1))
    (Nat.mul_le_mul hN (Nat.le_refl B))

end ElimK
end MultiVarMod
end MachLib
