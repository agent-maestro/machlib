import MachLib.MultiVar
import MachLib.Ring

/-!
# y-coefficient representation of `MultiVar 2` — the resultant's foundation (Gate 2d, resultant Rung)

The resultant `Res_y(p,q)` (Bezout obligation A) is built from `p, q` written as polynomials in `y` with
coefficients in `ℝ[x]`: `p = Σᵢ cᵢ(x)·yⁱ`. `coeffsY p` extracts that coefficient list (each `cᵢ` a
`MultiVar 2` in the `x` variable, `y`-free); `evalCoeffs` evaluates a coefficient list back by Horner in
`y = env 1`. The load-bearing correctness is `eval_coeffsY` — the representation is faithful — whose crux
is `evalCoeffs_mulCoeffs`: the **convolution** of coefficient lists corresponds to polynomial
multiplication (the fact that makes the coefficient view a ring homomorphism).

This is the first brick of the resultant subsystem (both the Sylvester and the Euclid/subresultant routes
sit on this representation). Mathlib-free; `mach_ring` discharges the `MachLib.Real` arithmetic.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

/-- Horner evaluation of a `y`-coefficient list at `env` (`y := env 1`): `[c₀,c₁,…] ↦ c₀ + y·(c₁ + …)`. -/
noncomputable def evalCoeffs : List (MultiVar 2) → (Fin 2 → Real) → Real
  | [], _ => 0
  | c :: cs, env => MultiVar.eval c env + env 1 * evalCoeffs cs env

@[simp] theorem evalCoeffs_nil (env : Fin 2 → Real) : evalCoeffs [] env = 0 := rfl
@[simp] theorem evalCoeffs_cons (c : MultiVar 2) (cs : List (MultiVar 2)) (env : Fin 2 → Real) :
    evalCoeffs (c :: cs) env = MultiVar.eval c env + env 1 * evalCoeffs cs env := rfl

/-- Pointwise sum of coefficient lists (the longer tail carries through). -/
def addCoeffs : List (MultiVar 2) → List (MultiVar 2) → List (MultiVar 2)
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => MultiVar.add a b :: addCoeffs as bs

/-- Negate a coefficient list (`0 - ·` on each). -/
noncomputable def negCoeffs (bs : List (MultiVar 2)) : List (MultiVar 2) :=
  bs.map (fun b => MultiVar.sub (MultiVar.const 0) b)

/-- Pointwise difference of coefficient lists, via `addCoeffs ∘ negCoeffs`. -/
noncomputable def subCoeffs (as bs : List (MultiVar 2)) : List (MultiVar 2) :=
  addCoeffs as (negCoeffs bs)

/-- Convolution of coefficient lists — polynomial multiplication in `y`. -/
noncomputable def mulCoeffs : List (MultiVar 2) → List (MultiVar 2) → List (MultiVar 2)
  | [], _ => []
  | a :: as, bs =>
      addCoeffs (bs.map (fun b => MultiVar.mul a b)) (MultiVar.const 0 :: mulCoeffs as bs)

/-- The `y`-coefficient list of a `MultiVar 2` (variable `0` = `x`, variable `1` = `y`). -/
noncomputable def coeffsY : MultiVar 2 → List (MultiVar 2)
  | .const c => [MultiVar.const c]
  | .var j   => if j = 0 then [MultiVar.var 0] else [MultiVar.const 0, MultiVar.const 1]
  | .add p q => addCoeffs (coeffsY p) (coeffsY q)
  | .sub p q => subCoeffs (coeffsY p) (coeffsY q)
  | .mul p q => mulCoeffs (coeffsY p) (coeffsY q)

/-! ## Homomorphism laws for the coefficient arithmetic -/

theorem evalCoeffs_addCoeffs (env : Fin 2 → Real) :
    ∀ as bs : List (MultiVar 2),
      evalCoeffs (addCoeffs as bs) env = evalCoeffs as env + evalCoeffs bs env
  | [], bs => by simp only [addCoeffs, evalCoeffs_nil]; mach_ring
  | a :: as, [] => by simp only [addCoeffs, evalCoeffs_nil]; mach_ring
  | a :: as, b :: bs => by
      simp only [addCoeffs, evalCoeffs_cons, MultiVar.eval_add, evalCoeffs_addCoeffs env as bs]
      mach_ring

theorem evalCoeffs_mapMul (env : Fin 2 → Real) (c : MultiVar 2) :
    ∀ cs : List (MultiVar 2),
      evalCoeffs (cs.map (fun b => MultiVar.mul c b)) env = MultiVar.eval c env * evalCoeffs cs env
  | [] => by simp only [List.map_nil, evalCoeffs_nil]; mach_ring
  | d :: ds => by
      simp only [List.map_cons, evalCoeffs_cons, MultiVar.eval_mul, evalCoeffs_mapMul env c ds]
      mach_ring

theorem evalCoeffs_mulCoeffs (env : Fin 2 → Real) :
    ∀ as bs : List (MultiVar 2),
      evalCoeffs (mulCoeffs as bs) env = evalCoeffs as env * evalCoeffs bs env
  | [], bs => by simp only [mulCoeffs, evalCoeffs_nil]; mach_ring
  | a :: as, bs => by
      simp only [mulCoeffs, evalCoeffs_addCoeffs, evalCoeffs_mapMul, evalCoeffs_cons,
        MultiVar.eval_const, evalCoeffs_mulCoeffs env as bs]
      mach_ring

theorem evalCoeffs_negCoeffs (env : Fin 2 → Real) :
    ∀ bs : List (MultiVar 2), evalCoeffs (negCoeffs bs) env = 0 - evalCoeffs bs env
  | [] => by simp only [negCoeffs, List.map_nil, evalCoeffs_nil]; mach_ring
  | b :: bs => by
      show evalCoeffs (MultiVar.sub (MultiVar.const 0) b :: negCoeffs bs) env
          = 0 - evalCoeffs (b :: bs) env
      rw [evalCoeffs_cons, evalCoeffs_cons, MultiVar.eval_sub, MultiVar.eval_const,
        evalCoeffs_negCoeffs env bs]
      mach_ring

theorem evalCoeffs_subCoeffs (env : Fin 2 → Real) (as bs : List (MultiVar 2)) :
    evalCoeffs (subCoeffs as bs) env = evalCoeffs as env - evalCoeffs bs env := by
  show evalCoeffs (addCoeffs as (negCoeffs bs)) env = _
  rw [evalCoeffs_addCoeffs, evalCoeffs_negCoeffs]
  mach_ring

/-! ## Faithfulness of the representation -/

/-- **The coefficient representation is faithful.** Evaluating `p` equals evaluating its `y`-coefficient
list by Horner in `y = env 1`. The `mul` case is the convolution law `evalCoeffs_mulCoeffs`. -/
theorem eval_coeffsY (env : Fin 2 → Real) :
    ∀ p : MultiVar 2, MultiVar.eval p env = evalCoeffs (coeffsY p) env
  | .const c => by
      show MultiVar.eval (MultiVar.const c) env = evalCoeffs [MultiVar.const c] env
      simp only [evalCoeffs_cons, evalCoeffs_nil]
      mach_ring
  | .var j   => by
      by_cases h : j = 0
      · rw [coeffsY, if_pos h, h]
        simp only [evalCoeffs_cons, evalCoeffs_nil, MultiVar.eval_var]
        mach_ring
      · have hj1 : j = (1 : Fin 2) := by
          apply Fin.ext
          have hv : j.val ≠ 0 := fun hv => h (Fin.ext hv)
          have := j.isLt; omega
        rw [coeffsY, if_neg h, hj1]
        simp only [evalCoeffs_cons, evalCoeffs_nil, MultiVar.eval_var, MultiVar.eval_const]
        mach_ring
  | .add p q => by
      rw [MultiVar.eval_add, eval_coeffsY env p, eval_coeffsY env q]
      exact (evalCoeffs_addCoeffs env (coeffsY p) (coeffsY q)).symm
  | .sub p q => by
      rw [MultiVar.eval_sub, eval_coeffsY env p, eval_coeffsY env q]
      exact (evalCoeffs_subCoeffs env (coeffsY p) (coeffsY q)).symm
  | .mul p q => by
      rw [MultiVar.eval_mul, eval_coeffsY env p, eval_coeffsY env q]
      exact (evalCoeffs_mulCoeffs env (coeffsY p) (coeffsY q)).symm

end MultiVarMod
end MachLib
