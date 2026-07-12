import MachLib.MultiVarShift

/-!
# Coefficient-list split + the reduction step's eval scaffolding (Gate 2d, resultant brick 3c-2)

The pseudo-division reduction step drops the (eval-zero, formally-present) top coefficient via `dropLast`,
which is justified by the **polynomial-split** law: `evalCoeffs (as ++ bs) = evalCoeffs as + yᵃˢ ·
evalCoeffs bs` (`as` is the low-degree part, `bs` shifted up by `|as|`). Specialized to `bs = [b]` and the
decomposition `l = l.dropLast ++ [l.getLast]`, it gives `evalCoeffs l = evalCoeffs l.dropLast +
eval(l.getLast)·y^{|l|−1}` — so dropping an eval-zero last coefficient preserves eval. This file proves
the split law; `reduceOnce` (scale + shift + subCoeffs + dropLast) and its eval identity build on it.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

/-- **Polynomial split.** `evalCoeffs (as ++ bs) = evalCoeffs as + y^{|as|} · evalCoeffs bs` — appending
coefficient lists is adding the second, shifted up by `|as|` powers of `y`. -/
theorem evalCoeffs_append (env : Fin 2 → Real) :
    ∀ (as bs : List (MultiVar 2)),
      evalCoeffs (as ++ bs) env
        = evalCoeffs as env
          + MultiVar.eval (MultiVar.pow (MultiVar.var (1 : Fin 2)) as.length) env * evalCoeffs bs env
  | [], bs => by
      show evalCoeffs bs env
          = evalCoeffs [] env
            + MultiVar.eval (MultiVar.pow (MultiVar.var (1 : Fin 2)) 0) env * evalCoeffs bs env
      rw [eval_pow_zero, evalCoeffs_nil]; mach_ring
  | a :: as, bs => by
      show evalCoeffs (a :: (as ++ bs)) env
          = evalCoeffs (a :: as) env
            + MultiVar.eval (MultiVar.pow (MultiVar.var (1 : Fin 2)) (as.length + 1)) env
              * evalCoeffs bs env
      rw [evalCoeffs_cons, evalCoeffs_cons, evalCoeffs_append env as bs, eval_pow_succ,
        MultiVar.eval_var]
      mach_ring

/-- **Dropping an eval-zero top coefficient preserves eval.** `evalCoeffs (as ++ [b]) = evalCoeffs as`
when `b` evaluates to `0`. This is the dropLast-preservation the reduction step needs: the cancelled top
coefficient of a reduction is eval-zero, so removing it leaves the evaluation unchanged (only the formal
length drops). No identically-zero detection — just this eval fact. -/
theorem evalCoeffs_append_singleton_zero (env : Fin 2 → Real) (as : List (MultiVar 2)) (b : MultiVar 2)
    (hb : MultiVar.eval b env = 0) :
    evalCoeffs (as ++ [b]) env = evalCoeffs as env := by
  rw [evalCoeffs_append env as [b], evalCoeffs_cons, evalCoeffs_nil, hb]
  mach_ring

end MultiVarMod
end MachLib
