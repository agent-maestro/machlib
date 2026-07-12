import MachLib.MultiVar
import MachLib.Ring

/-!
# `MultiVar k` coefficient elimination — generic in arity and eliminated index (Gate 2d, M.0-a)

Generalizes the polynomial-Bezout coefficient representation (`coeffsY`/`evalCoeffs`, hardwired to
`MultiVar 2` eliminating index `1`) to **arbitrary arity `k` and any eliminated index `i`**. This is the
machinery the mixed-exponential reduction needs: `e^{g(x,y)}` becomes a one-variable exponential of a new
variable `w = g`, at the cost of eliminating TWO variables from a polynomial system — iterated resultants,
which need the resultant polymorphic in variable count.

`coeffsElim i p` writes `p ∈ MultiVar k` as a polynomial in the `i`-th variable with coefficients that are
`i`-free (`MultiVar k` with `degVar i = 0` — polynomials in the *other* `k−1` variables). Unlike Rung 1.0
(which reindexed to a smaller arity and threaded the Horner value externally), here the coefficients stay
in `MultiVar k` and the Horner variable is simply `env i` — a direct mirror of the original, no
reindexing. `evalC i` is the Horner evaluator; `eval_coeffsElim` is faithfulness. Mathlib-free, `mach_ring`.
-/

namespace MachLib
namespace MultiVarMod
namespace ElimK

open MachLib.MultiVarMod.MultiVar

/-- Horner evaluation of an `i`-coefficient list (`x_i := env i`). -/
noncomputable def evalC {k : Nat} (i : Fin k) : List (MultiVar k) → (Fin k → Real) → Real
  | [], _ => 0
  | c :: cs, env => MultiVar.eval c env + env i * evalC i cs env

@[simp] theorem evalC_nil {k : Nat} (i : Fin k) (env : Fin k → Real) : evalC i [] env = 0 := rfl
@[simp] theorem evalC_cons {k : Nat} (i : Fin k) (c : MultiVar k) (cs : List (MultiVar k))
    (env : Fin k → Real) :
    evalC i (c :: cs) env = MultiVar.eval c env + env i * evalC i cs env := rfl

/-- Pointwise sum of coefficient lists (longer tail carries through). -/
def addC {k : Nat} : List (MultiVar k) → List (MultiVar k) → List (MultiVar k)
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => MultiVar.add a b :: addC as bs

/-- Negate a coefficient list. -/
noncomputable def negC {k : Nat} (bs : List (MultiVar k)) : List (MultiVar k) :=
  bs.map (fun b => MultiVar.sub (MultiVar.const 0) b)

/-- Pointwise difference. -/
noncomputable def subC {k : Nat} (as bs : List (MultiVar k)) : List (MultiVar k) := addC as (negC bs)

/-- Convolution — polynomial multiplication in `x_i`. -/
noncomputable def mulC {k : Nat} : List (MultiVar k) → List (MultiVar k) → List (MultiVar k)
  | [], _ => []
  | a :: as, bs => addC (bs.map (fun b => MultiVar.mul a b)) (MultiVar.const 0 :: mulC as bs)

/-- The `x_i`-coefficient list of a `MultiVar k`: eliminate variable `i`, coefficients `i`-free. -/
noncomputable def coeffsElim {k : Nat} (i : Fin k) : MultiVar k → List (MultiVar k)
  | .const c => [MultiVar.const c]
  | .var j   => if j = i then [MultiVar.const 0, MultiVar.const 1] else [MultiVar.var j]
  | .add p q => addC (coeffsElim i p) (coeffsElim i q)
  | .sub p q => subC (coeffsElim i p) (coeffsElim i q)
  | .mul p q => mulC (coeffsElim i p) (coeffsElim i q)

/-! ## Homomorphism laws -/

theorem evalC_addC {k : Nat} (i : Fin k) (env : Fin k → Real) :
    ∀ as bs : List (MultiVar k), evalC i (addC as bs) env = evalC i as env + evalC i bs env
  | [], bs => by simp only [addC, evalC_nil]; mach_ring
  | a :: as, [] => by simp only [addC, evalC_nil]; mach_ring
  | a :: as, b :: bs => by
      simp only [addC, evalC_cons, MultiVar.eval_add, evalC_addC i env as bs]; mach_ring

theorem evalC_mapMul {k : Nat} (i : Fin k) (env : Fin k → Real) (c : MultiVar k) :
    ∀ cs : List (MultiVar k),
      evalC i (cs.map (fun b => MultiVar.mul c b)) env = MultiVar.eval c env * evalC i cs env
  | [] => by simp only [List.map_nil, evalC_nil]; mach_ring
  | d :: ds => by
      simp only [List.map_cons, evalC_cons, MultiVar.eval_mul, evalC_mapMul i env c ds]; mach_ring

theorem evalC_mulC {k : Nat} (i : Fin k) (env : Fin k → Real) :
    ∀ as bs : List (MultiVar k), evalC i (mulC as bs) env = evalC i as env * evalC i bs env
  | [], bs => by simp only [mulC, evalC_nil]; mach_ring
  | a :: as, bs => by
      simp only [mulC, evalC_addC, evalC_mapMul, evalC_cons, MultiVar.eval_const,
        evalC_mulC i env as bs]; mach_ring

theorem evalC_negC {k : Nat} (i : Fin k) (env : Fin k → Real) :
    ∀ bs : List (MultiVar k), evalC i (negC bs) env = 0 - evalC i bs env
  | [] => by simp only [negC, List.map_nil, evalC_nil]; mach_ring
  | b :: bs => by
      show evalC i (MultiVar.sub (MultiVar.const 0) b :: negC bs) env = 0 - evalC i (b :: bs) env
      rw [evalC_cons, evalC_cons, MultiVar.eval_sub, MultiVar.eval_const, evalC_negC i env bs]
      mach_ring

theorem evalC_subC {k : Nat} (i : Fin k) (env : Fin k → Real) (as bs : List (MultiVar k)) :
    evalC i (subC as bs) env = evalC i as env - evalC i bs env := by
  show evalC i (addC as (negC bs)) env = _
  rw [evalC_addC, evalC_negC]; mach_ring

/-! ## Faithfulness -/

/-- **The coefficient representation is faithful** for arbitrary arity and eliminated index. -/
theorem eval_coeffsElim {k : Nat} (i : Fin k) (env : Fin k → Real) :
    ∀ p : MultiVar k, MultiVar.eval p env = evalC i (coeffsElim i p) env
  | .const c => by
      show MultiVar.eval (MultiVar.const c) env = evalC i [MultiVar.const c] env
      simp only [evalC_cons, evalC_nil]; mach_ring
  | .var j => by
      by_cases h : j = i
      · have hc : coeffsElim i (MultiVar.var j) = [MultiVar.const 0, MultiVar.const 1] := by
          show (if j = i then [MultiVar.const 0, MultiVar.const 1] else [MultiVar.var j]) = _
          rw [if_pos h]
        rw [hc]
        simp only [evalC_cons, evalC_nil, MultiVar.eval_var, MultiVar.eval_const]
        rw [h]; mach_ring
      · have hc : coeffsElim i (MultiVar.var j) = [MultiVar.var j] := by
          show (if j = i then [MultiVar.const 0, MultiVar.const 1] else [MultiVar.var j]) = _
          rw [if_neg h]
        rw [hc]
        simp only [evalC_cons, evalC_nil, MultiVar.eval_var]; mach_ring
  | .add p q => by
      rw [MultiVar.eval_add, eval_coeffsElim i env p, eval_coeffsElim i env q]
      exact (evalC_addC i env (coeffsElim i p) (coeffsElim i q)).symm
  | .sub p q => by
      rw [MultiVar.eval_sub, eval_coeffsElim i env p, eval_coeffsElim i env q]
      exact (evalC_subC i env (coeffsElim i p) (coeffsElim i q)).symm
  | .mul p q => by
      rw [MultiVar.eval_mul, eval_coeffsElim i env p, eval_coeffsElim i env q]
      exact (evalC_mulC i env (coeffsElim i p) (coeffsElim i q)).symm

end ElimK
end MultiVarMod
end MachLib
