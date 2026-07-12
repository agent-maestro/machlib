import MachLib.MultiVarElimReduce

/-!
# `MultiVar k` reduceOnce vanishes at common zeros (Gate 2d, M.0-c)

The k-generic analogue of `MultiVarReduceVanish`. The reduction's top coefficient cancels
(`reduceFullK_getLast_eval_zero`, a coefficient-eval fact independent of the Horner index), so `dropLast`
preserves eval and `reduceOnceK` inherits `reduceFullK_vanish`. Direct mirror of the `MultiVar 2` proofs
with `2 ↦ k`. The `getLast`/length/`_ne_nil` machinery is index-free; only `reduceOnceK_vanish` carries the
eliminated index `i`.
-/

namespace MachLib
namespace MultiVarMod
namespace ElimK

open MachLib.MultiVarMod.MultiVar

theorem addC_ne_nil {k : Nat} {as bs : List (MultiVar k)} (h : as.length = bs.length) (ha : as ≠ []) :
    addC as bs ≠ [] := by
  cases as with
  | nil => exact absurd rfl ha
  | cons a as' =>
    cases bs with
    | nil => simp at h
    | cons b bs' => exact List.cons_ne_nil _ _

theorem eval_getLast_addC {k : Nat} (env : Fin k → Real) :
    ∀ (as bs : List (MultiVar k)) (ha : as ≠ []) (hb : bs ≠ []) (hab : addC as bs ≠ [])
      (_h : as.length = bs.length),
      MultiVar.eval ((addC as bs).getLast hab) env
        = MultiVar.eval (as.getLast ha) env + MultiVar.eval (bs.getLast hb) env := by
  intro as
  induction as with
  | nil => intro bs ha; exact absurd rfl ha
  | cons a as' ih =>
    intro bs ha hb hab hlen
    cases bs with
    | nil => exact absurd rfl hb
    | cons b bs' =>
      cases as' with
      | nil =>
        cases bs' with
        | nil =>
          show MultiVar.eval (MultiVar.add a b) env = MultiVar.eval a env + MultiVar.eval b env
          rfl
        | cons b2 bs'' => simp at hlen
      | cons a2 as'' =>
        cases bs' with
        | nil => simp at hlen
        | cons b2 bs'' =>
          have hrest : addC (a2 :: as'') (b2 :: bs'') ≠ [] := List.cons_ne_nil _ _
          have hlen' : (a2 :: as'').length = (b2 :: bs'').length := by
            simp only [List.length_cons] at hlen ⊢; omega
          rw [show (addC (a :: a2 :: as'') (b :: b2 :: bs'')).getLast hab
                = (addC (a2 :: as'') (b2 :: bs'')).getLast hrest from by
              show (MultiVar.add a b :: addC (a2 :: as'') (b2 :: bs'')).getLast hab
                  = (addC (a2 :: as'') (b2 :: bs'')).getLast hrest
              rw [List.getLast_cons hrest],
            List.getLast_cons (List.cons_ne_nil a2 as''),
            List.getLast_cons (List.cons_ne_nil b2 bs'')]
          exact ih (b2 :: bs'') (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) hrest hlen'

theorem eval_getLast_scaleC {k : Nat} (env : Fin k → Real) (c : MultiVar k) (as : List (MultiVar k))
    (ha : as ≠ []) (h : scaleC c as ≠ []) :
    MultiVar.eval ((scaleC c as).getLast h) env
      = MultiVar.eval c env * MultiVar.eval (as.getLast ha) env := by
  show MultiVar.eval ((as.map (fun b => MultiVar.mul c b)).getLast h) env = _
  rw [List.getLast_map]; rfl

theorem shiftC_ne_nil {k : Nat} (n : Nat) {X : List (MultiVar k)} (hX : X ≠ []) :
    shiftC n X ≠ [] := by
  cases n with
  | zero => show List.replicate 0 (MultiVar.const 0) ++ X ≠ []; simpa using hX
  | succ n =>
    show MultiVar.const 0 :: (List.replicate n (MultiVar.const 0) ++ X) ≠ []
    exact List.cons_ne_nil _ _

theorem getLast_shiftC {k : Nat} {X : List (MultiVar k)} (hX : X ≠ []) :
    ∀ (n : Nat) (h : shiftC n X ≠ []), (shiftC n X).getLast h = X.getLast hX
  | 0, _ => rfl
  | n + 1, h => by
      show (MultiVar.const 0 :: shiftC n X).getLast h = X.getLast hX
      rw [List.getLast_cons (shiftC_ne_nil n hX), getLast_shiftC hX n]

theorem scaleC_ne_nil {k : Nat} (c : MultiVar k) {as : List (MultiVar k)} (ha : as ≠ []) :
    scaleC c as ≠ [] := by
  cases as with
  | nil => exact absurd rfl ha
  | cons a as' => exact List.cons_ne_nil _ _

theorem negC_ne_nil {k : Nat} {X : List (MultiVar k)} (hX : X ≠ []) : negC X ≠ [] := by
  cases X with
  | nil => exact absurd rfl hX
  | cons x xs => exact List.cons_ne_nil _ _

theorem eval_getLast_negC {k : Nat} (env : Fin k → Real) (X : List (MultiVar k)) (hX : X ≠ [])
    (h : negC X ≠ []) :
    MultiVar.eval ((negC X).getLast h) env = 0 - MultiVar.eval (X.getLast hX) env := by
  show MultiVar.eval ((X.map (fun b => MultiVar.sub (MultiVar.const 0) b)).getLast h) env = _
  rw [List.getLast_map]; rfl

/-- **The reduction's top coefficient evaluates to `0`** (leading coefficients `qs.getLast`, `ps.getLast`).
-/
theorem reduceFullK_getLast_eval_zero {k : Nat} (env : Fin k → Real) (ps qs : List (MultiVar k))
    (hps : ps ≠ []) (hqs : qs ≠ []) (hlen : qs.length ≤ ps.length)
    (h : reduceFullK (qs.getLast hqs) (ps.getLast hps) (ps.length - qs.length) ps qs ≠ []) :
    MultiVar.eval
      ((reduceFullK (qs.getLast hqs) (ps.getLast hps) (ps.length - qs.length) ps qs).getLast h) env
      = 0 := by
  have hA : scaleC (qs.getLast hqs) ps ≠ [] := scaleC_ne_nil _ hps
  have hXscale : scaleC (ps.getLast hps) qs ≠ [] := scaleC_ne_nil _ hqs
  have hBshift : shiftC (ps.length - qs.length) (scaleC (ps.getLast hps) qs) ≠ [] :=
    shiftC_ne_nil _ hXscale
  have hnegB : negC (shiftC (ps.length - qs.length) (scaleC (ps.getLast hps) qs)) ≠ [] :=
    negC_ne_nil hBshift
  have hleneq : (scaleC (qs.getLast hqs) ps).length
      = (negC (shiftC (ps.length - qs.length) (scaleC (ps.getLast hps) qs))).length := by
    rw [length_scaleC, length_negC, length_shiftC, length_scaleC]; omega
  show MultiVar.eval ((addC (scaleC (qs.getLast hqs) ps)
      (negC (shiftC (ps.length - qs.length) (scaleC (ps.getLast hps) qs)))).getLast h) env = 0
  rw [eval_getLast_addC env _ _ hA hnegB h hleneq,
    eval_getLast_scaleC env (qs.getLast hqs) ps hps hA,
    eval_getLast_negC env _ hBshift hnegB,
    getLast_shiftC hXscale (ps.length - qs.length),
    eval_getLast_scaleC env (ps.getLast hps) qs hqs hXscale]
  mach_ring

theorem evalC_dropLast_of_getLast_zero {k : Nat} (i : Fin k) (env : Fin k → Real) :
    ∀ (l : List (MultiVar k)) (hl : l ≠ []), MultiVar.eval (l.getLast hl) env = 0 →
      evalC i l.dropLast env = evalC i l env
  | [], hl, _ => absurd rfl hl
  | [a], _, hz => by
      show evalC i [] env = evalC i [a] env
      simp only [evalC_cons, evalC_nil]
      rw [show MultiVar.eval a env = 0 from hz]; mach_ring
  | a :: b :: l', _, hz => by
      have hz' : MultiVar.eval ((b :: l').getLast (List.cons_ne_nil b l')) env = 0 := by
        rw [List.getLast_cons (List.cons_ne_nil b l')] at hz; exact hz
      show evalC i (a :: (b :: l').dropLast) env = evalC i (a :: b :: l') env
      rw [evalC_cons, evalC_cons,
        evalC_dropLast_of_getLast_zero i env (b :: l') (List.cons_ne_nil b l') hz']

/-- **`reduceOnceK` vanishes at a common zero.** -/
theorem reduceOnceK_vanish {k : Nat} (i : Fin k) (env : Fin k → Real) (ps qs : List (MultiVar k))
    (hps : ps ≠ []) (hqs : qs ≠ []) (hlen : qs.length ≤ ps.length)
    (hp : evalC i ps env = 0) (hq : evalC i qs env = 0) :
    evalC i (reduceOnceK (qs.getLast hqs) (ps.getLast hps) ps qs) env = 0 := by
  show evalC i
    (reduceFullK (qs.getLast hqs) (ps.getLast hps) (ps.length - qs.length) ps qs).dropLast env = 0
  have hleneq : (scaleC (qs.getLast hqs) ps).length
      = (negC (shiftC (ps.length - qs.length) (scaleC (ps.getLast hps) qs))).length := by
    rw [length_scaleC, length_negC, length_shiftC, length_scaleC]; omega
  have hne : reduceFullK (qs.getLast hqs) (ps.getLast hps) (ps.length - qs.length) ps qs ≠ [] :=
    addC_ne_nil hleneq (scaleC_ne_nil _ hps)
  rw [evalC_dropLast_of_getLast_zero i env _ hne
    (reduceFullK_getLast_eval_zero env ps qs hps hqs hlen hne)]
  exact reduceFullK_vanish i env (qs.getLast hqs) (ps.getLast hps) (ps.length - qs.length) ps qs hp hq

end ElimK
end MultiVarMod
end MachLib
