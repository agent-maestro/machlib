import MachLib.MultiVarReduce

/-!
# Horner evaluation at an EXTERNAL point — `evalCoeffsAt` (Gate 2d, Rung 1 brick 1.0-a)

For Rung 1 (one exponential), a system `{P, Q}` in `MultiVar 3` `(x, y, u)` is eliminated in `y`, and the
`y`-coefficients are polynomials in `(x, u)` — `MultiVar 2` elements whose index `1` is now **`u`**, not
`y`. The Horner variable (`y`) must therefore be **external** to the coefficient environment, unlike the
polynomial-Bezout `evalCoeffs` (which reads the Horner variable off `env 1`).

`evalCoeffsAt cs env yv = Σₖ eval(cs[k]) env · yvᵏ` is that external-Horner evaluator. This file mirrors
the `evalCoeffs` homomorphism/scale/shift/append laws with `env 1 ↦ yv` and the shift factor `yᵏ ↦
ypow yv k` (a plain real Nat-power). The `getLast`/length/`_ne_nil` machinery and
`reduceFull_getLast_eval_zero` are coefficient-eval (env-based, no Horner) and are reused verbatim from the
polynomial layer. `mach_ring` discharges the `MachLib.Real` arithmetic.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

/-- Real Nat-power (the external Horner power). `MachLib.Real`'s `^` is analytic, so we recurse. -/
noncomputable def ypow (y : Real) : Nat → Real
  | 0 => 1
  | k + 1 => y * ypow y k

@[simp] theorem ypow_zero (y : Real) : ypow y 0 = 1 := rfl
@[simp] theorem ypow_succ (y : Real) (k : Nat) : ypow y (k + 1) = y * ypow y k := rfl

/-- Horner evaluation of a coefficient list at an **external** Horner value `yv` (coefficients evaluated
at `env`): `[c₀,c₁,…] ↦ c₀(env) + yv·(c₁(env) + …)`. -/
noncomputable def evalCoeffsAt : List (MultiVar 2) → (Fin 2 → Real) → Real → Real
  | [], _, _ => 0
  | c :: cs, env, yv => MultiVar.eval c env + yv * evalCoeffsAt cs env yv

@[simp] theorem evalCoeffsAt_nil (env : Fin 2 → Real) (yv : Real) : evalCoeffsAt [] env yv = 0 := rfl
@[simp] theorem evalCoeffsAt_cons (c : MultiVar 2) (cs : List (MultiVar 2)) (env : Fin 2 → Real)
    (yv : Real) :
    evalCoeffsAt (c :: cs) env yv = MultiVar.eval c env + yv * evalCoeffsAt cs env yv := rfl

/-! ## Homomorphism laws (external Horner) -/

theorem evalCoeffsAt_addCoeffs (env : Fin 2 → Real) (yv : Real) :
    ∀ as bs : List (MultiVar 2),
      evalCoeffsAt (addCoeffs as bs) env yv = evalCoeffsAt as env yv + evalCoeffsAt bs env yv
  | [], bs => by simp only [addCoeffs, evalCoeffsAt_nil]; mach_ring
  | a :: as, [] => by simp only [addCoeffs, evalCoeffsAt_nil]; mach_ring
  | a :: as, b :: bs => by
      simp only [addCoeffs, evalCoeffsAt_cons, MultiVar.eval_add, evalCoeffsAt_addCoeffs env yv as bs]
      mach_ring

theorem evalCoeffsAt_mapMul (env : Fin 2 → Real) (yv : Real) (c : MultiVar 2) :
    ∀ cs : List (MultiVar 2),
      evalCoeffsAt (cs.map (fun b => MultiVar.mul c b)) env yv = MultiVar.eval c env * evalCoeffsAt cs env yv
  | [] => by simp only [List.map_nil, evalCoeffsAt_nil]; mach_ring
  | d :: ds => by
      simp only [List.map_cons, evalCoeffsAt_cons, MultiVar.eval_mul, evalCoeffsAt_mapMul env yv c ds]
      mach_ring

theorem evalCoeffsAt_mulCoeffs (env : Fin 2 → Real) (yv : Real) :
    ∀ as bs : List (MultiVar 2),
      evalCoeffsAt (mulCoeffs as bs) env yv = evalCoeffsAt as env yv * evalCoeffsAt bs env yv
  | [], bs => by simp only [mulCoeffs, evalCoeffsAt_nil]; mach_ring
  | a :: as, bs => by
      simp only [mulCoeffs, evalCoeffsAt_addCoeffs, evalCoeffsAt_mapMul, evalCoeffsAt_cons,
        MultiVar.eval_const, evalCoeffsAt_mulCoeffs env yv as bs]
      mach_ring

theorem evalCoeffsAt_negCoeffs (env : Fin 2 → Real) (yv : Real) :
    ∀ bs : List (MultiVar 2), evalCoeffsAt (negCoeffs bs) env yv = 0 - evalCoeffsAt bs env yv
  | [] => by simp only [negCoeffs, List.map_nil, evalCoeffsAt_nil]; mach_ring
  | b :: bs => by
      show evalCoeffsAt (MultiVar.sub (MultiVar.const 0) b :: negCoeffs bs) env yv
          = 0 - evalCoeffsAt (b :: bs) env yv
      rw [evalCoeffsAt_cons, evalCoeffsAt_cons, MultiVar.eval_sub, MultiVar.eval_const,
        evalCoeffsAt_negCoeffs env yv bs]
      mach_ring

theorem evalCoeffsAt_subCoeffs (env : Fin 2 → Real) (yv : Real) (as bs : List (MultiVar 2)) :
    evalCoeffsAt (subCoeffs as bs) env yv = evalCoeffsAt as env yv - evalCoeffsAt bs env yv := by
  show evalCoeffsAt (addCoeffs as (negCoeffs bs)) env yv = _
  rw [evalCoeffsAt_addCoeffs, evalCoeffsAt_negCoeffs]
  mach_ring

theorem evalCoeffsAt_scaleCoeffs (env : Fin 2 → Real) (yv : Real) (c : MultiVar 2)
    (as : List (MultiVar 2)) :
    evalCoeffsAt (scaleCoeffs c as) env yv = MultiVar.eval c env * evalCoeffsAt as env yv :=
  evalCoeffsAt_mapMul env yv c as

/-! ## Shift + append (external Horner, factor `ypow yv k`) -/

theorem evalCoeffsAt_shiftCoeffs (as : List (MultiVar 2)) (env : Fin 2 → Real) (yv : Real) :
    ∀ k : Nat, evalCoeffsAt (shiftCoeffs k as) env yv = ypow yv k * evalCoeffsAt as env yv
  | 0 => by
      show evalCoeffsAt (List.replicate 0 (MultiVar.const 0) ++ as) env yv
          = ypow yv 0 * evalCoeffsAt as env yv
      simp only [List.replicate, List.nil_append, ypow_zero]
      mach_ring
  | k + 1 => by
      show evalCoeffsAt (List.replicate (k + 1) (MultiVar.const 0) ++ as) env yv
          = ypow yv (k + 1) * evalCoeffsAt as env yv
      rw [ypow_succ,
        show List.replicate (k + 1) (MultiVar.const 0) ++ as
            = MultiVar.const 0 :: (List.replicate k (MultiVar.const 0) ++ as) from rfl,
        evalCoeffsAt_cons, MultiVar.eval_const,
        show List.replicate k (MultiVar.const 0) ++ as = shiftCoeffs k as from rfl,
        evalCoeffsAt_shiftCoeffs as env yv k]
      mach_ring

/-- **Polynomial split (external Horner).** `evalCoeffsAt (as ++ bs) = evalCoeffsAt as + yvᵃˢ ·
evalCoeffsAt bs`. -/
theorem evalCoeffsAt_append (env : Fin 2 → Real) (yv : Real) :
    ∀ (as bs : List (MultiVar 2)),
      evalCoeffsAt (as ++ bs) env yv
        = evalCoeffsAt as env yv + ypow yv as.length * evalCoeffsAt bs env yv
  | [], bs => by
      show evalCoeffsAt bs env yv = evalCoeffsAt [] env yv + ypow yv 0 * evalCoeffsAt bs env yv
      simp only [evalCoeffsAt_nil, ypow_zero]; mach_ring
  | a :: as, bs => by
      show evalCoeffsAt (a :: (as ++ bs)) env yv
          = evalCoeffsAt (a :: as) env yv + ypow yv (as.length + 1) * evalCoeffsAt bs env yv
      rw [evalCoeffsAt_cons, evalCoeffsAt_cons, evalCoeffsAt_append env yv as bs, ypow_succ]
      mach_ring

/-- **Dropping an eval-zero top coefficient preserves eval** (external Horner). -/
theorem evalCoeffsAt_append_singleton_zero (env : Fin 2 → Real) (yv : Real) (as : List (MultiVar 2))
    (b : MultiVar 2) (hb : MultiVar.eval b env = 0) :
    evalCoeffsAt (as ++ [b]) env yv = evalCoeffsAt as env yv := by
  rw [evalCoeffsAt_append env yv as [b], evalCoeffsAt_cons, evalCoeffsAt_nil, hb]
  mach_ring

end MultiVarMod
end MachLib
