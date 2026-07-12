import MachLib.MultiVarRung1
import MachLib.MultiVarBezoutFiber

/-!
# Rung 1 full solution count (Gate 2d) — x-coordinate count × y-fiber size

Lifts `rung1_one_exp_xcoord_bound` (distinct x-coordinates) to the **full solution count** for a plane
system with one exponential, exactly as `bezout_general_fibered` lifted the polynomial x-count. At a fixed
x-coordinate `x₀` the exponential is a constant `u = e^{x₀}`, so `P(x₀, y, e^{x₀})` is an ordinary
polynomial in `y` — its roots number `≤ deg_y P` (`fiber_count`, which is `{k}`-generic and applies to the
`MultiVar 3` y-slice). Fibering the solution set by x-coordinate:

  #solutions ≤ #{x-coordinates} · deg_y P ≤ (|coeffs| + Σ simplified-deg of R(x,eˣ)) · deg_y P.

Fibered form (fibration supplied), sidestepping the Mathlib-free `List.dedup` gap as in the polynomial
layer. `rolle_ct` + Classical + exp — no multivariate Rolle.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar
open MachLib.SingleExpKhovanskii (ExpPoly)
open MachLib.SingleExpKhovanskii.ExpPoly
open MachLib.Real

/-- The y-slice environment at x-coordinate `x₀`: freeze `x = x₀` and `u = e^{x₀}` (index 1, `y`, is the
live variable and overrides its entry here). -/
noncomputable def fiberEnv (x₀ : Real) : Fin 3 → Real := fun j => if j = (0 : Fin 3) then x₀ else exp x₀

/-- **y-fibration bound for a `MultiVar 3` system along `u = eˣ`.** Given a fibration of the solution set by
x-coordinate (`≤ A` fibers, each a `Nodup` list of `P`-roots on the y-slice at that `x` with `u = e^x`),
the total count is `≤ A · deg_y P`. The `MultiVar 3` analogue of `bezout_of_fibration`, via the `{k}`-generic
`fiber_count` at `live = 1`. -/
theorem bezout_of_fibration3 (P : MultiVar 3) (a b : Real) (hab : a < b)
    (fibers : List (Real × List Real)) (A : Nat) (hA : fibers.length ≤ A)
    (hfib : ∀ f ∈ fibers,
      (∃ t, MultiVar.eval P (fun j => if j = (1 : Fin 3) then t else fiberEnv f.1 j) ≠ 0)
      ∧ f.2.Nodup
      ∧ (∀ y ∈ f.2, a < y ∧ y < b
          ∧ MultiVar.eval P (fun j => if j = (1 : Fin 3) then y else fiberEnv f.1 j) = 0)) :
    (fibers.flatMap (fun f => f.2)).length ≤ A * MultiVar.degVar (1 : Fin 3) P := by
  refine Nat.le_trans
    (length_flatMap_le' (MultiVar.degVar (1 : Fin 3) P) fibers ?_)
    (Nat.mul_le_mul hA (Nat.le_refl _))
  intro f hf
  obtain ⟨hne, hnd, hys⟩ := hfib f hf
  exact fiber_count (1 : Fin 3) (fiberEnv f.1) P a b hab hne f.2 hnd hys

/-- **Rung 1 — full solution count for a plane system with one exponential.** Given a fibration of the
solution set of `{P, Q}` (along `u = eˣ`) by x-coordinate — distinct x-values (`hfib_nd`), each fiber a
`Nodup` list of `P`-roots on the y-slice `(x₀, ·, e^{x₀})`, each x-slice non-degenerate and carrying a
common-zero witness — the total number of solution points is
`≤ (|coeffs| + Σ simplified-deg of R(x,eˣ)) · deg_y P`, where `R = Res_y(P,Q)`. The complete
multivariate-transcendental Bezout/Khovanskii bound for one exponential; `rolle_ct` + Classical, no
multivariate Rolle. -/
theorem rung1_one_exp_solution_bound (P Q : MultiVar 3) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, a < x ∧ x < b
      ∧ (toExpPoly (prsResultant3 P Q (prsFuel3 P Q))).eval x ≠ 0)
    (fibers : List (Real × List Real))
    (hfib_nd : (fibers.map (fun f => f.1)).Nodup)
    (hfib : ∀ f ∈ fibers,
      (∃ t, MultiVar.eval P (fun j => if j = (1 : Fin 3) then t else fiberEnv f.1 j) ≠ 0)
      ∧ f.2.Nodup
      ∧ (∀ y ∈ f.2, a < y ∧ y < b
          ∧ MultiVar.eval P (fun j => if j = (1 : Fin 3) then y else fiberEnv f.1 j) = 0)
      ∧ a < f.1 ∧ f.1 < b
      ∧ ∃ env3 : Fin 3 → Real, env3 0 = f.1 ∧ env3 2 = exp f.1
          ∧ MultiVar.eval P env3 = 0 ∧ MultiVar.eval Q env3 = 0) :
    (fibers.flatMap (fun f => f.2)).length
      ≤ ((toExpPoly (prsResultant3 P Q (prsFuel3 P Q))).coeffs.length
          + sumSimplifiedDegrees (toExpPoly (prsResultant3 P Q (prsFuel3 P Q))).coeffs)
        * MultiVar.degVar (1 : Fin 3) P := by
  have hA : fibers.length
      ≤ (toExpPoly (prsResultant3 P Q (prsFuel3 P Q))).coeffs.length
        + sumSimplifiedDegrees (toExpPoly (prsResultant3 P Q (prsFuel3 P Q))).coeffs := by
    have hx := rung1_one_exp_xcoord_bound P Q a b hab hne (fibers.map (fun f => f.1)) hfib_nd
      (fun x₀ hx₀ => by
        rw [List.mem_map] at hx₀
        obtain ⟨f, hf, rfl⟩ := hx₀
        obtain ⟨_, _, _, ha1, hb1, henv⟩ := hfib f hf
        exact ⟨ha1, hb1, henv⟩)
    rwa [List.length_map] at hx
  exact bezout_of_fibration3 P a b hab fibers _ hA
    (fun f hf => ⟨(hfib f hf).1, (hfib f hf).2.1, (hfib f hf).2.2.1⟩)

end MultiVarMod
end MachLib
