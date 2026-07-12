import MachLib.MultiVarEvalAt

/-!
# `y`-coefficients of a `MultiVar 3` as `(x,u)`-polynomials (Gate 2d, Rung 1 brick 1.0-d)

The Rung-1 front door. A system `{P, Q}` in `MultiVar 3` `(x = 0, y = 1, u = 2)` is written as a polynomial
in `y` with coefficients in `ℝ[x, u]`: `P = Σₖ cₖ(x,u)·yᵏ`. `coeffsY3 P` extracts that list, each `cₖ` a
**`MultiVar 2`** in `(x = 0, u = 1)` — the `y` variable is *dropped* and `u` reindexed from `2` to `1`.
The remainder therefore lands in `(x, u)` automatically `y`-free (no `y`-freeness to track), and the
existing `List (MultiVar 2)` PRS applies verbatim.

`eval_coeffsY3` is faithfulness against `evalCoeffsAt` (Horner variable `y = env3 1` supplied externally,
coefficients read at `env2` with `env2 0 = x = env3 0`, `env2 1 = u = env3 2`). The `mul` case is the
convolution law `evalCoeffsAt_mulCoeffs`.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

/-- The `y`-coefficient list of a `MultiVar 3` `(x = 0, y = 1, u = 2)`, as `MultiVar 2` in `(x = 0,
u = 1)`: drop `y`, reindex `u : 2 ↦ 1`. -/
noncomputable def coeffsY3 : MultiVar 3 → List (MultiVar 2)
  | .const c => [MultiVar.const c]
  | .var j   =>
      if j = 1 then [MultiVar.const 0, MultiVar.const 1]
      else if j = 0 then [MultiVar.var 0]
      else [MultiVar.var 1]
  | .add p q => addCoeffs (coeffsY3 p) (coeffsY3 q)
  | .sub p q => subCoeffs (coeffsY3 p) (coeffsY3 q)
  | .mul p q => mulCoeffs (coeffsY3 p) (coeffsY3 q)

/-- **The `MultiVar 3` coefficient representation is faithful.** With `y = env3 1` supplied as the external
Horner value and `env2 0 = env3 0` (x), `env2 1 = env3 2` (u), evaluating `P` at `env3` equals the Horner
sum of its `(x,u)`-coefficients. The `mul` case is the convolution law. -/
theorem eval_coeffsY3 (env3 : Fin 3 → Real) (env2 : Fin 2 → Real) (yv : Real)
    (h0 : env2 0 = env3 0) (h2 : env2 1 = env3 2) (hy : yv = env3 1) :
    ∀ P : MultiVar 3, MultiVar.eval P env3 = evalCoeffsAt (coeffsY3 P) env2 yv
  | .const c => by
      show MultiVar.eval (MultiVar.const c) env3 = evalCoeffsAt [MultiVar.const c] env2 yv
      simp only [evalCoeffsAt_cons, evalCoeffsAt_nil, MultiVar.eval_const]
      mach_ring
  | .var j => by
      by_cases hj0 : j = 0
      · subst hj0
        have hc : coeffsY3 (MultiVar.var (0 : Fin 3)) = [MultiVar.var (0 : Fin 2)] := by
          show (if (0 : Fin 3) = 1 then [MultiVar.const 0, MultiVar.const 1]
              else if (0 : Fin 3) = 0 then [MultiVar.var (0 : Fin 2)] else [MultiVar.var 1])
              = [MultiVar.var (0 : Fin 2)]
          rw [if_neg (by decide), if_pos (by decide)]
        rw [hc]
        simp only [evalCoeffsAt_cons, evalCoeffsAt_nil, MultiVar.eval_var]
        rw [h0]; mach_ring
      · by_cases hj1 : j = 1
        · subst hj1
          have hc : coeffsY3 (MultiVar.var (1 : Fin 3)) = [MultiVar.const 0, MultiVar.const 1] := by
            show (if (1 : Fin 3) = 1 then [MultiVar.const 0, MultiVar.const 1]
                else if (1 : Fin 3) = 0 then [MultiVar.var (0 : Fin 2)] else [MultiVar.var 1])
                = [MultiVar.const 0, MultiVar.const 1]
            rw [if_pos (by decide)]
          rw [hc]
          simp only [evalCoeffsAt_cons, evalCoeffsAt_nil, MultiVar.eval_var, MultiVar.eval_const]
          rw [hy]; mach_ring
        · have hj2 : j = 2 := by
            apply Fin.ext
            have hv0 : j.val ≠ 0 := fun hv => hj0 (Fin.ext hv)
            have hv1 : j.val ≠ 1 := fun hv => hj1 (Fin.ext hv)
            have := j.isLt; omega
          subst hj2
          have hc : coeffsY3 (MultiVar.var (2 : Fin 3)) = [MultiVar.var (1 : Fin 2)] := by
            show (if (2 : Fin 3) = 1 then [MultiVar.const 0, MultiVar.const 1]
                else if (2 : Fin 3) = 0 then [MultiVar.var (0 : Fin 2)] else [MultiVar.var 1])
                = [MultiVar.var (1 : Fin 2)]
            rw [if_neg (by decide), if_neg (by decide)]
          rw [hc]
          simp only [evalCoeffsAt_cons, evalCoeffsAt_nil, MultiVar.eval_var]
          rw [h2]; mach_ring
  | .add p q => by
      rw [MultiVar.eval_add, eval_coeffsY3 env3 env2 yv h0 h2 hy p,
        eval_coeffsY3 env3 env2 yv h0 h2 hy q]
      exact (evalCoeffsAt_addCoeffs env2 yv (coeffsY3 p) (coeffsY3 q)).symm
  | .sub p q => by
      rw [MultiVar.eval_sub, eval_coeffsY3 env3 env2 yv h0 h2 hy p,
        eval_coeffsY3 env3 env2 yv h0 h2 hy q]
      exact (evalCoeffsAt_subCoeffs env2 yv (coeffsY3 p) (coeffsY3 q)).symm
  | .mul p q => by
      rw [MultiVar.eval_mul, eval_coeffsY3 env3 env2 yv h0 h2 hy p,
        eval_coeffsY3 env3 env2 yv h0 h2 hy q]
      exact (evalCoeffsAt_mulCoeffs env2 yv (coeffsY3 p) (coeffsY3 q)).symm

end MultiVarMod
end MachLib
