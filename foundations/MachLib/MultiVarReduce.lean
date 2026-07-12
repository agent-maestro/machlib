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

/-! ## The reduction step (eval core) -/

/-- Scale a `y`-coefficient list by a single coefficient `c` (multiply the polynomial by `c`). -/
noncomputable def scaleCoeffs (c : MultiVar 2) (as : List (MultiVar 2)) : List (MultiVar 2) :=
  as.map (fun b => MultiVar.mul c b)

theorem evalCoeffs_scaleCoeffs (env : Fin 2 → Real) (c : MultiVar 2) (as : List (MultiVar 2)) :
    evalCoeffs (scaleCoeffs c as) env = MultiVar.eval c env * evalCoeffs as env :=
  evalCoeffs_mapMul env c as

/-- **The pseudo-division reduction combination** `q_lead·p − p_lead·yᵏ·q` (as coefficient lists). With
`q_lead = qs.getLast`, `p_lead = ps.getLast`, `k = deg_y p − deg_y q`, its top coefficient cancels
(eval-zero); `dropLast` then lowers the formal degree while preserving eval. -/
noncomputable def reduceFull (q_lead p_lead : MultiVar 2) (k : Nat) (ps qs : List (MultiVar 2)) :
    List (MultiVar 2) :=
  subCoeffs (scaleCoeffs q_lead ps) (shiftCoeffs k (scaleCoeffs p_lead qs))

/-- **Reduction eval identity.** `evalCoeffs (reduceFull …) = q_lead·evalCoeffs ps − yᵏ·p_lead·evalCoeffs
qs`. Pure evaluation bookkeeping (`subCoeffs`/`scale`/`shift` evals) — no `getLast`. -/
theorem evalCoeffs_reduceFull (env : Fin 2 → Real) (q_lead p_lead : MultiVar 2) (k : Nat)
    (ps qs : List (MultiVar 2)) :
    evalCoeffs (reduceFull q_lead p_lead k ps qs) env
      = MultiVar.eval q_lead env * evalCoeffs ps env
        - MultiVar.eval (MultiVar.pow (MultiVar.var (1 : Fin 2)) k) env
          * MultiVar.eval p_lead env * evalCoeffs qs env := by
  show evalCoeffs (subCoeffs (scaleCoeffs q_lead ps) (shiftCoeffs k (scaleCoeffs p_lead qs))) env = _
  rw [evalCoeffs_subCoeffs, evalCoeffs_scaleCoeffs env q_lead ps,
    evalCoeffs_shiftCoeffs (scaleCoeffs p_lead qs) env k, evalCoeffs_scaleCoeffs env p_lead qs]
  mach_ring

/-- **The reduction vanishes at a common zero.** If `evalCoeffs ps = evalCoeffs qs = 0` (i.e. `p` and `q`
both vanish at `env`), so does the reduction combination — the invariant every polynomial-remainder-
sequence entry preserves. -/
theorem reduceFull_vanish (env : Fin 2 → Real) (q_lead p_lead : MultiVar 2) (k : Nat)
    (ps qs : List (MultiVar 2)) (hp : evalCoeffs ps env = 0) (hq : evalCoeffs qs env = 0) :
    evalCoeffs (reduceFull q_lead p_lead k ps qs) env = 0 := by
  rw [evalCoeffs_reduceFull, hp, hq]; mach_ring

/-! ## Length calculus (the reduction's formal-degree drop → termination) -/

theorem length_scaleCoeffs (c : MultiVar 2) (as : List (MultiVar 2)) :
    (scaleCoeffs c as).length = as.length := List.length_map _ _

theorem length_shiftCoeffs (k : Nat) (as : List (MultiVar 2)) :
    (shiftCoeffs k as).length = k + as.length := by
  show (List.replicate k (MultiVar.const 0) ++ as).length = k + as.length
  rw [List.length_append, List.length_replicate]

theorem length_negCoeffs (bs : List (MultiVar 2)) : (negCoeffs bs).length = bs.length :=
  List.length_map _ _

theorem length_addCoeffs : ∀ as bs : List (MultiVar 2),
    (addCoeffs as bs).length = max as.length bs.length
  | [], bs => by show bs.length = max 0 bs.length; rw [Nat.zero_max]
  | a :: as, [] => by show (a :: as).length = max (a :: as).length 0; rw [Nat.max_zero]
  | a :: as, b :: bs => by
      show (addCoeffs as bs).length + 1 = max (as.length + 1) (bs.length + 1)
      rw [length_addCoeffs as bs, Nat.succ_max_succ]

theorem length_subCoeffs (as bs : List (MultiVar 2)) :
    (subCoeffs as bs).length = max as.length bs.length := by
  show (addCoeffs as (negCoeffs bs)).length = _
  rw [length_addCoeffs, length_negCoeffs]

/-- **The reduction has the same length as `p`** — the top coefficient is present (cancelled but formal),
so the formal degree is unchanged until the `dropLast`. Requires `|qs| ≤ |ps|` and `k = |ps| − |qs|`. -/
theorem length_reduceFull (q_lead p_lead : MultiVar 2) (ps qs : List (MultiVar 2))
    (h : qs.length ≤ ps.length) :
    (reduceFull q_lead p_lead (ps.length - qs.length) ps qs).length = ps.length := by
  show (subCoeffs (scaleCoeffs q_lead ps)
    (shiftCoeffs (ps.length - qs.length) (scaleCoeffs p_lead qs))).length = ps.length
  rw [length_subCoeffs, length_scaleCoeffs, length_shiftCoeffs, length_scaleCoeffs,
    show ps.length - qs.length + qs.length = ps.length from by omega, Nat.max_self]

/-- **`reduceOnce` — the reduction with its cancelled top dropped.** Formal length `|ps| − 1`: the
polynomial-remainder step lowers the degree by exactly one. -/
noncomputable def reduceOnce (q_lead p_lead : MultiVar 2) (ps qs : List (MultiVar 2)) :
    List (MultiVar 2) :=
  (reduceFull q_lead p_lead (ps.length - qs.length) ps qs).dropLast

theorem length_reduceOnce (q_lead p_lead : MultiVar 2) (ps qs : List (MultiVar 2))
    (h : qs.length ≤ ps.length) :
    (reduceOnce q_lead p_lead ps qs).length = ps.length - 1 := by
  show (reduceFull q_lead p_lead (ps.length - qs.length) ps qs).dropLast.length = ps.length - 1
  rw [List.length_dropLast, length_reduceFull q_lead p_lead ps qs h]

end MultiVarMod
end MachLib
