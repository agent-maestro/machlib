import MachLib.MultiPoly
import MachLib.Differentiation

/-!
# General formal partial derivatives — foundation for the log Khovanskii step

`log_hard`'s L2 inductive cases need `cTD` to respect eval-equality
(`eval_cTD_congr`), which exists only in `Fin 2`/`y1free` form
(`ChainExp2CTDCongr.lean`). Lifting it to a general chain rests on general
partial-derivative machinery, built here: the formal partials `partialY i` (any
index) and `partialX`, and their eval-correctness (each is the `HasDerivAt`
derivative of `eval r` in that coordinate). Direct ports of the `Fin 2` templates
`partialY0`/`partialX` to a general index/`N`. Next: the general `cTD`
sum-decomposition (`cTD r = partialX r + Σᵢ relationsᵢ · partialY i r`), then the
eval-zero lemma, then `eval_cTD_congr_gen`.
-/
namespace MachLib
namespace MultiPolyMod
namespace MultiPoly
open MachLib.Real

/-- Formal partial derivative w.r.t. `y_i` (general index). -/
noncomputable def partialY {n : Nat} (i : Fin n) : MultiPoly n → MultiPoly n
  | .const _ => .const 0
  | .varX => .const 0
  | .varY j => if j = i then .const 1 else .const 0
  | .add p q => .add (partialY i p) (partialY i q)
  | .sub p q => .sub (partialY i p) (partialY i q)
  | .mul p q => .add (.mul (partialY i p) q) (.mul p (partialY i q))

/-- Formal partial derivative w.r.t. `x` (general). -/
noncomputable def partialX {n : Nat} : MultiPoly n → MultiPoly n
  | .const _ => .const 0
  | .varX => .const 1
  | .varY _ => .const 0
  | .add p q => .add (partialX p) (partialX q)
  | .sub p q => .sub (partialX p) (partialX q)
  | .mul p q => .add (.mul (partialX p) q) (.mul p (partialX q))

theorem upd_self {n : Nat} (i : Fin n) (env : Fin n → Real) :
    (fun j => if j = i then env i else env j) = env := by
  funext j; by_cases h : j = i
  · rw [if_pos h, h]
  · rw [if_neg h]

/-- **`partialY i` is eval-correct**: the derivative of `eval r` in coordinate `i`. -/
theorem hasDerivAt_eval_partialY {n : Nat} (i : Fin n) (r : MultiPoly n) (x : Real) (env : Fin n → Real) :
    HasDerivAt (fun v => MultiPoly.eval r x (fun j => if j = i then v else env j))
      (MultiPoly.eval (partialY i r) x env) (env i) := by
  induction r with
  | const c => exact HasDerivAt_const c _
  | varX =>
    show HasDerivAt (fun _ => x) (0 : Real) (env i)
    exact HasDerivAt_const x (env i)
  | varY j =>
    by_cases hj : j = i
    · have hf : (fun v => MultiPoly.eval (MultiPoly.varY j) x (fun j' => if j' = i then v else env j'))
          = fun v => v := by
        funext v; show (if j = i then v else env j) = v; rw [if_pos hj]
      have hd : MultiPoly.eval (partialY i (MultiPoly.varY j)) x env = 1 := by
        rw [show partialY i (MultiPoly.varY j) = MultiPoly.const 1 from if_pos hj]; rfl
      rw [hf, hd]; exact HasDerivAt_id (env i)
    · have hf : (fun v => MultiPoly.eval (MultiPoly.varY j) x (fun j' => if j' = i then v else env j'))
          = fun _ => env j := by
        funext v; show (if j = i then v else env j) = env j; rw [if_neg hj]
      have hd : MultiPoly.eval (partialY i (MultiPoly.varY j)) x env = 0 := by
        rw [show partialY i (MultiPoly.varY j) = MultiPoly.const 0 from if_neg hj]; rfl
      rw [hf, hd]; exact HasDerivAt_const (env j) (env i)
  | add p q ihp ihq =>
    exact HasDerivAt_add _ _ _ _ _ ihp ihq
  | sub p q ihp ihq =>
    exact HasDerivAt_sub _ _ _ _ _ ihp ihq
  | mul p q ihp ihq =>
    have h := HasDerivAt_mul _ _ _ _ _ ihp ihq
    have hqself : MultiPoly.eval q x (fun j => if j = i then env i else env j) = MultiPoly.eval q x env := by
      rw [upd_self]
    have hpself : MultiPoly.eval p x (fun j => if j = i then env i else env j) = MultiPoly.eval p x env := by
      rw [upd_self]
    rw [hqself, hpself] at h
    exact h

/-- **`partialX` is eval-correct**: the derivative of `eval r` in the `x` coordinate. -/
theorem hasDerivAt_eval_partialX {n : Nat} (r : MultiPoly n) (env : Fin n → Real) (x : Real) :
    HasDerivAt (fun t => MultiPoly.eval r t env) (MultiPoly.eval (partialX r) x env) x := by
  induction r with
  | const c => exact HasDerivAt_const c _
  | varX => exact HasDerivAt_id _
  | varY j => exact HasDerivAt_const (env j) _
  | add p q ihp ihq => exact HasDerivAt_add _ _ _ _ _ ihp ihq
  | sub p q ihp ihq => exact HasDerivAt_sub _ _ _ _ _ ihp ihq
  | mul p q ihp ihq => exact HasDerivAt_mul _ _ _ _ _ ihp ihq

end MultiPoly
end MultiPolyMod
end MachLib
