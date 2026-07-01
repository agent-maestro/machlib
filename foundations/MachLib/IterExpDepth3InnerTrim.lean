import MachLib.ChainExp2Trim

/-!
# Depth-3 inner-trim — dropping a phantom leading `y₁`-term of the leading `y₂`-coefficient

The depth-3 WF assembly's one remaining shrinking move. When the inner `q := dropLastY(lcY₂ p)` is
*phantom* (its syntactic leading `y₁`-coefficient vanishes on the chain) with `degreeY₁ q > 0`, the
reduce cannot make progress (it targets the dead coefficient). The fix: drop that phantom `y₁`-term
from `lcY₂ p` — reflected into `p` by rebuilding its `y₂`-coefficient list with the last (leading)
entry replaced by its `dropLeadingYAt ⟨1⟩`.

This file builds the operation `innerTrim3` and its **eval-preservation** (`eval_innerTrim3`): when the
leading `y₁`-term of the leading `y₂`-coefficient vanishes on every environment, `innerTrim3 p` agrees
with `p` everywhere. The measure/degree facts and the WF assembly follow in later phases.

Foundation: `eval_reconstructY_last_swap` — swapping the last coefficient of a `reconstructY` list for
an eval-equal one preserves the evaluation (`reconstructY` is `Σ cₖ·yᵏ`, linear in each `cₖ`). Path B; no `sorry`.
-/

namespace MachLib.IterExpDepth3InnerTrim

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct

/-- **Last-coefficient swap preserves eval.** Replacing the final entry of a `reconstructY` coefficient
list by an eval-equal polynomial does not change the evaluation — `reconstructY` is a sum `Σ cₖ·yᵢᵏ`
linear in each coefficient, and only the last coefficient changes. -/
theorem eval_reconstructY_last_swap {n : Nat} (i : Fin n) (a b : MultiPoly n)
    (x : Real) (env : Fin n → Real) (hab : MultiPoly.eval a x env = MultiPoly.eval b x env) :
    ∀ (pre : List (MultiPoly n)) (k : Nat),
      MultiPoly.eval (reconstructY i (pre ++ [a]) k) x env
        = MultiPoly.eval (reconstructY i (pre ++ [b]) k) x env := by
  intro pre
  induction pre with
  | nil =>
    intro k
    simp only [List.nil_append]
    rw [reconstructY_cons, reconstructY_cons, MultiPoly.eval_add, MultiPoly.eval_add,
        MultiPoly.eval_mul, MultiPoly.eval_mul, hab]
  | cons c cs ih =>
    intro k
    show MultiPoly.eval (reconstructY i (c :: (cs ++ [a])) k) x env
       = MultiPoly.eval (reconstructY i (c :: (cs ++ [b])) k) x env
    rw [reconstructY_cons, reconstructY_cons, MultiPoly.eval_add, MultiPoly.eval_add, ih (k + 1)]

/-- **The inner-trim operation.** Rebuild `p`'s `y₂`-coefficient list with the leading (last) entry —
the leading `y₂`-coefficient `lcY₂ p` — replaced by its `dropLeadingYAt ⟨1⟩` (its own leading `y₁`-term
dropped). All other `y₂`-coefficients are untouched. -/
noncomputable def innerTrim3 (p : MultiPoly 3) : MultiPoly 3 :=
  reconstructY (⟨2, by omega⟩ : Fin 3)
    ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).dropLast ++
      [MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 3)
        ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p))]) 0

/-- **Eval-preservation.** When the leading `y₁`-term of the leading `y₂`-coefficient of `p` vanishes on
every environment (the phantom condition), `innerTrim3 p` evaluates identically to `p` at every point:
the swapped-in `dropLeadingYAt ⟨1⟩ (lcY₂ p)` is eval-equal to `lcY₂ p`, so the reconstructed polynomial
is eval-equal to the `yCoeffsAt`-round-trip, i.e. `p` itself. -/
theorem eval_innerTrim3 (p : MultiPoly 3)
    (h_phantom : ∀ (x : Real) (env : Fin 3 → Real),
      MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨1, by omega⟩ : Fin 3)
        ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p))).getLast
        (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 3)
          ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
            (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p)))) x env = 0)
    (x : Real) (env : Fin 3 → Real) :
    MultiPoly.eval (innerTrim3 p) x env = MultiPoly.eval p x env := by
  have hswap_eval : MultiPoly.eval (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 3)
        ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p))) x env
      = MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p)) x env :=
    MachLib.ChainExp2Trim.eval_dropLeadingYAt_of_last_canonically_zero (⟨1, by omega⟩ : Fin 3)
      ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
        (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p))
      (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 3)
        ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p)))
      h_phantom x env
  unfold innerTrim3
  rw [eval_reconstructY_last_swap (⟨2, by omega⟩ : Fin 3)
        (MachLib.ChainExp2Trim.dropLeadingYAt (⟨1, by omega⟩ : Fin 3)
          ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
            (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p)))
        ((MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).getLast
          (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p))
        x env hswap_eval (MultiPoly.yCoeffsAt (⟨2, by omega⟩ : Fin 3) p).dropLast 0,
      List.dropLast_concat_getLast (MultiPoly.yCoeffsAt_nonempty (⟨2, by omega⟩ : Fin 3) p)]
  exact eval_reconstructY_yCoeffsAt (⟨2, by omega⟩ : Fin 3) p x env

end MachLib.IterExpDepth3InnerTrim
