import MachLib.MultiVarElimPreserve

/-!
# Iterated elimination for the mixed-exponential system (Gate 2d, M.1)

Realises the polynomial half of the mixed-exponential reduction. Working in `MultiVar 4`
`(x = 0, y = 1, w = 2, u = 3)`, a system `{P(x,y,u) = 0, Q(x,y,u) = 0, w − g(x,y) = 0}` (the third equation
`wg` ties the new variable `w` to the polynomial `g`) is reduced to a single relation `R(w, u)` by
eliminating `x` then `y`:

* `elimX P wg = Res_x(P, wg)` — eliminate `x` between `P` and `w − g`;
* `mixedResultant P Q wg = Res_y(elimX P wg, elimX Q wg)` — then eliminate `y`.

`mixedResultant_vanish`: `R` vanishes at every common zero of `{P, Q, wg}` (two applications of
`resultantElim_vanish_uncond`). `mixedResultant_xfree` / `_yfree`: `R` is a genuine polynomial in `(w, u)`
only — `y`-free directly (`resultantElim_ifree`), `x`-free because eliminating `y` preserves the
`x`-freeness that eliminating `x` produced (`resultantElim_pres_free`). No multivariate Rolle; pure
polynomial algebra. The next brick (M.2) substitutes `u = e^w` into `R(w, u)` (reusing the Rung 1.1 bridge,
in the variable `w`) to count `w`-values by the single-variable Khovanskii bound.
-/

namespace MachLib
namespace MultiVarMod
namespace ElimK

open MachLib.MultiVarMod.MultiVar

/-- Eliminate `x` (index 0) between `P` and the tie `wg = w − g`. -/
noncomputable def elimX (P wg : MultiVar 4) : MultiVar 4 :=
  resultantElim (0 : Fin 4) P wg (prsFuelElim (0 : Fin 4) P wg)

theorem elimX_vanish (P wg : MultiVar 4) (env : Fin 4 → Real)
    (hP : MultiVar.eval P env = 0) (hwg : MultiVar.eval wg env = 0) :
    MultiVar.eval (elimX P wg) env = 0 :=
  resultantElim_vanish_uncond (0 : Fin 4) P wg env hP hwg

theorem elimX_xfree (P wg : MultiVar 4) : MultiVar.degVar (0 : Fin 4) (elimX P wg) = 0 :=
  resultantElim_ifree (0 : Fin 4) P wg _

/-- Eliminate `x` then `y` from `{P, Q, wg}` → the relation `R(w, u)`. -/
noncomputable def mixedResultant (P Q wg : MultiVar 4) : MultiVar 4 :=
  resultantElim (1 : Fin 4) (elimX P wg) (elimX Q wg)
    (prsFuelElim (1 : Fin 4) (elimX P wg) (elimX Q wg))

/-- **The mixed resultant vanishes at every common zero** of `{P, Q, wg}`. -/
theorem mixedResultant_vanish (P Q wg : MultiVar 4) (env : Fin 4 → Real)
    (hP : MultiVar.eval P env = 0) (hQ : MultiVar.eval Q env = 0) (hwg : MultiVar.eval wg env = 0) :
    MultiVar.eval (mixedResultant P Q wg) env = 0 :=
  resultantElim_vanish_uncond (1 : Fin 4) (elimX P wg) (elimX Q wg) env
    (elimX_vanish P wg env hP hwg) (elimX_vanish Q wg env hQ hwg)

/-- The mixed resultant is `y`-free. -/
theorem mixedResultant_yfree (P Q wg : MultiVar 4) :
    MultiVar.degVar (1 : Fin 4) (mixedResultant P Q wg) = 0 :=
  resultantElim_ifree (1 : Fin 4) (elimX P wg) (elimX Q wg) _

/-- The mixed resultant is `x`-free (eliminating `y` preserves the `x`-freeness from eliminating `x`). So
`R` is a genuine polynomial in `(w, u)` only. -/
theorem mixedResultant_xfree (P Q wg : MultiVar 4) :
    MultiVar.degVar (0 : Fin 4) (mixedResultant P Q wg) = 0 :=
  resultantElim_pres_free (1 : Fin 4) (0 : Fin 4) (elimX P wg) (elimX Q wg) _
    (elimX_xfree P wg) (elimX_xfree Q wg)

end ElimK
end MultiVarMod
end MachLib
