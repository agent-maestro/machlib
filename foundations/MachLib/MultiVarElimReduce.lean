import MachLib.MultiVarElimCoeff

/-!
# `MultiVar k` shift + reduction step (Gate 2d, M.0-b)

The k-generic analogue of `MultiVarShift` + `MultiVarReduce`: `shiftC n` multiplies an `x_i`-coefficient
list by `x_iⁿ` (prepend `n` zeros); `reduceFullK` is the pseudo-division combination
`q_lead·p − p_lead·x_iⁿ·q`, whose cancelled top coefficient is dropped by `reduceOnceK` (`= .dropLast`).
Direct mirror of the `MultiVar 2` proofs with `2 ↦ k`, `1 ↦ i`. Mathlib-free, `mach_ring`.
-/

namespace MachLib
namespace MultiVarMod
namespace ElimK

open MachLib.MultiVarMod.MultiVar

theorem eval_powK_zero {k : Nat} (p : MultiVar k) (env : Fin k → Real) :
    MultiVar.eval (MultiVar.pow p 0) env = 1 := rfl
theorem eval_powK_succ {k : Nat} (p : MultiVar k) (n : Nat) (env : Fin k → Real) :
    MultiVar.eval (MultiVar.pow p (n + 1)) env
      = MultiVar.eval (MultiVar.pow p n) env * MultiVar.eval p env := rfl

/-- Multiply an `x_i`-coefficient list by `x_iⁿ`: prepend `n` zero coefficients. -/
noncomputable def shiftC {k : Nat} (n : Nat) (as : List (MultiVar k)) : List (MultiVar k) :=
  List.replicate n (MultiVar.const 0) ++ as

theorem evalC_shiftC {k : Nat} (i : Fin k) (as : List (MultiVar k)) (env : Fin k → Real) :
    ∀ n : Nat,
      evalC i (shiftC n as) env
        = MultiVar.eval (MultiVar.pow (MultiVar.var i) n) env * evalC i as env
  | 0 => by
      show evalC i (List.replicate 0 (MultiVar.const 0) ++ as) env
          = MultiVar.eval (MultiVar.pow (MultiVar.var i) 0) env * evalC i as env
      rw [eval_powK_zero]; simp only [List.replicate, List.nil_append]; mach_ring
  | n + 1 => by
      show evalC i (List.replicate (n + 1) (MultiVar.const 0) ++ as) env
          = MultiVar.eval (MultiVar.pow (MultiVar.var i) (n + 1)) env * evalC i as env
      rw [eval_powK_succ,
        show List.replicate (n + 1) (MultiVar.const 0) ++ as
            = MultiVar.const 0 :: (List.replicate n (MultiVar.const 0) ++ as) from rfl,
        evalC_cons, MultiVar.eval_var, MultiVar.eval_const,
        show List.replicate n (MultiVar.const 0) ++ as = shiftC n as from rfl,
        evalC_shiftC i as env n]
      mach_ring

/-- **Polynomial split.** `evalC (as ++ bs) = evalC as + x_i^{|as|} · evalC bs`. -/
theorem evalC_append {k : Nat} (i : Fin k) (env : Fin k → Real) :
    ∀ (as bs : List (MultiVar k)),
      evalC i (as ++ bs) env
        = evalC i as env
          + MultiVar.eval (MultiVar.pow (MultiVar.var i) as.length) env * evalC i bs env
  | [], bs => by
      show evalC i bs env
          = evalC i [] env
            + MultiVar.eval (MultiVar.pow (MultiVar.var i) 0) env * evalC i bs env
      rw [eval_powK_zero, evalC_nil]; mach_ring
  | a :: as, bs => by
      show evalC i (a :: (as ++ bs)) env
          = evalC i (a :: as) env
            + MultiVar.eval (MultiVar.pow (MultiVar.var i) (as.length + 1)) env * evalC i bs env
      rw [evalC_cons, evalC_cons, evalC_append i env as bs, eval_powK_succ, MultiVar.eval_var]
      mach_ring

theorem evalC_append_singleton_zero {k : Nat} (i : Fin k) (env : Fin k → Real)
    (as : List (MultiVar k)) (b : MultiVar k) (hb : MultiVar.eval b env = 0) :
    evalC i (as ++ [b]) env = evalC i as env := by
  rw [evalC_append i env as [b], evalC_cons, evalC_nil, hb]; mach_ring

/-- Scale a coefficient list by a single coefficient. -/
noncomputable def scaleC {k : Nat} (c : MultiVar k) (as : List (MultiVar k)) : List (MultiVar k) :=
  as.map (fun b => MultiVar.mul c b)

theorem evalC_scaleC {k : Nat} (i : Fin k) (env : Fin k → Real) (c : MultiVar k)
    (as : List (MultiVar k)) :
    evalC i (scaleC c as) env = MultiVar.eval c env * evalC i as env :=
  evalC_mapMul i env c as

/-- The pseudo-division reduction `q_lead·p − p_lead·x_iⁿ·q` as coefficient lists. -/
noncomputable def reduceFullK {k : Nat} (q_lead p_lead : MultiVar k) (n : Nat)
    (ps qs : List (MultiVar k)) : List (MultiVar k) :=
  subC (scaleC q_lead ps) (shiftC n (scaleC p_lead qs))

theorem evalC_reduceFullK {k : Nat} (i : Fin k) (env : Fin k → Real) (q_lead p_lead : MultiVar k)
    (n : Nat) (ps qs : List (MultiVar k)) :
    evalC i (reduceFullK q_lead p_lead n ps qs) env
      = MultiVar.eval q_lead env * evalC i ps env
        - MultiVar.eval (MultiVar.pow (MultiVar.var i) n) env
          * MultiVar.eval p_lead env * evalC i qs env := by
  show evalC i (subC (scaleC q_lead ps) (shiftC n (scaleC p_lead qs))) env = _
  rw [evalC_subC, evalC_scaleC i env q_lead ps, evalC_shiftC i (scaleC p_lead qs) env n,
    evalC_scaleC i env p_lead qs]
  mach_ring

theorem reduceFullK_vanish {k : Nat} (i : Fin k) (env : Fin k → Real) (q_lead p_lead : MultiVar k)
    (n : Nat) (ps qs : List (MultiVar k)) (hp : evalC i ps env = 0) (hq : evalC i qs env = 0) :
    evalC i (reduceFullK q_lead p_lead n ps qs) env = 0 := by
  rw [evalC_reduceFullK, hp, hq]; mach_ring

/-! ## Length calculus -/

theorem length_scaleC {k : Nat} (c : MultiVar k) (as : List (MultiVar k)) :
    (scaleC c as).length = as.length := List.length_map _ _

theorem length_shiftC {k : Nat} (n : Nat) (as : List (MultiVar k)) :
    (shiftC n as).length = n + as.length := by
  show (List.replicate n (MultiVar.const 0) ++ as).length = n + as.length
  rw [List.length_append, List.length_replicate]

theorem length_negC {k : Nat} (bs : List (MultiVar k)) : (negC bs).length = bs.length :=
  List.length_map _ _

theorem length_addC {k : Nat} : ∀ as bs : List (MultiVar k),
    (addC as bs).length = max as.length bs.length
  | [], bs => by show bs.length = max 0 bs.length; rw [Nat.zero_max]
  | a :: as, [] => by show (a :: as).length = max (a :: as).length 0; rw [Nat.max_zero]
  | a :: as, b :: bs => by
      show (addC as bs).length + 1 = max (as.length + 1) (bs.length + 1)
      rw [length_addC as bs, Nat.succ_max_succ]

theorem length_subC {k : Nat} (as bs : List (MultiVar k)) :
    (subC as bs).length = max as.length bs.length := by
  show (addC as (negC bs)).length = _
  rw [length_addC, length_negC]

theorem length_reduceFullK {k : Nat} (q_lead p_lead : MultiVar k) (ps qs : List (MultiVar k))
    (h : qs.length ≤ ps.length) :
    (reduceFullK q_lead p_lead (ps.length - qs.length) ps qs).length = ps.length := by
  show (subC (scaleC q_lead ps)
    (shiftC (ps.length - qs.length) (scaleC p_lead qs))).length = ps.length
  rw [length_subC, length_scaleC, length_shiftC, length_scaleC,
    show ps.length - qs.length + qs.length = ps.length from by omega, Nat.max_self]

/-- `reduceOnceK` — the reduction with its cancelled top dropped (formal length `|ps| − 1`). -/
noncomputable def reduceOnceK {k : Nat} (q_lead p_lead : MultiVar k) (ps qs : List (MultiVar k)) :
    List (MultiVar k) :=
  (reduceFullK q_lead p_lead (ps.length - qs.length) ps qs).dropLast

theorem length_reduceOnceK {k : Nat} (q_lead p_lead : MultiVar k) (ps qs : List (MultiVar k))
    (h : qs.length ≤ ps.length) :
    (reduceOnceK q_lead p_lead ps qs).length = ps.length - 1 := by
  show (reduceFullK q_lead p_lead (ps.length - qs.length) ps qs).dropLast.length = ps.length - 1
  rw [List.length_dropLast, length_reduceFullK q_lead p_lead ps qs h]

end ElimK
end MultiVarMod
end MachLib
