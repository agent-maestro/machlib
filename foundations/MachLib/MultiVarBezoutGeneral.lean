import MachLib.MultiVarBezoutFiber
import MachLib.MultiVarResultant

/-!
# Full multivariate Bezout for a general system (Gate 2d — the solution-count capstone)

Combines the two halves into the **full solution count** for an arbitrary system `{p, q}` in `MultiVar 2`,
in fibered form (the fibration given, as in `bezout_of_fibration` — which sidesteps the Mathlib-free
`List.dedup`/`Nodup.map_on` gap entirely):

* `prsResultant_xbound` bounds the number of vertical fibers (distinct x-coordinates of common zeros) by
  `deg_x (resultant)`;
* `bezout_of_fibration` bounds each fiber by `deg_y p`.

`bezout_general_fibered`: the total number of solution points is `≤ deg_x(resultant) · deg_y p`. This is
the multivariate polynomial Bezout bound in full — the solution *count*, not just the x-coordinate count
— modulo the PRS terminating (`hterm`) and non-degeneracy (`hRne`), and with the caller supplying the
fibration of the solution set. `rolle_ct` + Classical, no new axiom.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

/-- **Full multivariate Bezout (solution count), fibered.** For a general system `{p, q}`, given a
fibration of the solution set by x-coordinate (`fibers`, with distinct x-values `hfib_nd`, each fiber a
`Nodup` list of `p`-roots on that vertical line, each line non-degenerate, and each carrying a common-zero
witness), the total solution count is `≤ deg_x(resultant) · deg_y p`. -/
theorem bezout_general_fibered (p q : MultiVar 2) (fuel : Nat)
    (hterm : (prsLoop fuel (coeffsY p) (coeffsY q)).length ≤ 1)
    (a b : Real) (hab : a < b) (env0 : Fin 2 → Real)
    (hRne : ∃ x, MultiVar.eval (prsResultant p q fuel)
      (fun j => if j = (0 : Fin 2) then x else env0 j) ≠ 0)
    (fibers : List (Real × List Real))
    (hfib_nd : (fibers.map (fun f => f.1)).Nodup)
    (hfib : ∀ f ∈ fibers,
      (∃ t, MultiVar.eval p (fun j => if j = (1 : Fin 2) then t else f.1) ≠ 0)
      ∧ f.2.Nodup
      ∧ (∀ y ∈ f.2, a < y ∧ y < b
          ∧ MultiVar.eval p (fun j => if j = (1 : Fin 2) then y else f.1) = 0)
      ∧ a < f.1 ∧ f.1 < b
      ∧ ∃ envc : Fin 2 → Real, envc 0 = f.1 ∧ MultiVar.eval p envc = 0 ∧ MultiVar.eval q envc = 0) :
    (fibers.flatMap (fun f => f.2)).length
      ≤ MultiVar.degVar (0 : Fin 2) (prsResultant p q fuel) * MultiVar.degVar (1 : Fin 2) p := by
  have hA : fibers.length ≤ MultiVar.degVar (0 : Fin 2) (prsResultant p q fuel) := by
    have hx := prsResultant_xbound p q fuel hterm a b hab env0 hRne (fibers.map (fun f => f.1))
      hfib_nd (fun x₀ hx₀ => by
        rw [List.mem_map] at hx₀
        obtain ⟨f, hf, rfl⟩ := hx₀
        obtain ⟨_, _, _, ha1, hb1, henvc⟩ := hfib f hf
        exact ⟨ha1, hb1, henvc⟩)
    rwa [List.length_map] at hx
  exact bezout_of_fibration p a b hab fibers
    (MultiVar.degVar (0 : Fin 2) (prsResultant p q fuel)) hA
    (fun f hf => ⟨(hfib f hf).1, (hfib f hf).2.1, (hfib f hf).2.2.1⟩)

/-- **Full multivariate Bezout, UNCONDITIONAL** (no `hterm`): at the canonical fuel `prsFuel`, the PRS
provably eliminates `y`, so the total solution count is `≤ deg_x(resultant) · deg_y p` — modulo only the
non-degeneracy `hRne`. This is the complete multivariate polynomial Bezout bound. -/
theorem bezout_general_fibered_uncond (p q : MultiVar 2)
    (a b : Real) (hab : a < b) (env0 : Fin 2 → Real)
    (hRne : ∃ x, MultiVar.eval (prsResultant p q (prsFuel p q))
      (fun j => if j = (0 : Fin 2) then x else env0 j) ≠ 0)
    (fibers : List (Real × List Real))
    (hfib_nd : (fibers.map (fun f => f.1)).Nodup)
    (hfib : ∀ f ∈ fibers,
      (∃ t, MultiVar.eval p (fun j => if j = (1 : Fin 2) then t else f.1) ≠ 0)
      ∧ f.2.Nodup
      ∧ (∀ y ∈ f.2, a < y ∧ y < b
          ∧ MultiVar.eval p (fun j => if j = (1 : Fin 2) then y else f.1) = 0)
      ∧ a < f.1 ∧ f.1 < b
      ∧ ∃ envc : Fin 2 → Real, envc 0 = f.1 ∧ MultiVar.eval p envc = 0 ∧ MultiVar.eval q envc = 0) :
    (fibers.flatMap (fun f => f.2)).length
      ≤ MultiVar.degVar (0 : Fin 2) (prsResultant p q (prsFuel p q)) * MultiVar.degVar (1 : Fin 2) p :=
  bezout_general_fibered p q (prsFuel p q) (prsFuel_hterm p q) a b hab env0 hRne fibers hfib_nd hfib

end MultiVarMod
end MachLib
