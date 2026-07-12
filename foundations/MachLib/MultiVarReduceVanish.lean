import MachLib.MultiVarReduce

/-!
# `reduceOnce` vanishes at common zeros (Gate 2d, resultant brick 3c-4b)

The `dropLast` in `reduceOnce` removes `reduceFull`'s top coefficient, which — with the leading
coefficients taken as `qs.getLast`, `ps.getLast` — **cancels** (`q_lead·p_lead − p_lead·q_lead`, eval-zero
for every `env`). So `reduceOnce` inherits `reduceFull_vanish`: it vanishes at every common zero. This
file proves the top-coefficient cancellation (`reduceFull_getLast_eval_zero`) and hence `reduceOnce_vanish`
— no identically-zero detection, just this eval fact. The one new list lemma is `getLast` of `addCoeffs`
on equal-length lists (the rest reuse core `getLast_map`/`getLast_append`).
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

theorem addCoeffs_ne_nil {as bs : List (MultiVar 2)} (h : as.length = bs.length) (ha : as ≠ []) :
    addCoeffs as bs ≠ [] := by
  cases as with
  | nil => exact absurd rfl ha
  | cons a as' =>
    cases bs with
    | nil => simp at h
    | cons b bs' => exact List.cons_ne_nil _ _

/-- **`getLast` of `addCoeffs` on equal-length lists**, at the eval level: the last coefficient of the
pointwise sum is the sum of the last coefficients. -/
theorem eval_getLast_addCoeffs (env : Fin 2 → Real) :
    ∀ (as bs : List (MultiVar 2)) (ha : as ≠ []) (hb : bs ≠ []) (hab : addCoeffs as bs ≠ [])
      (_h : as.length = bs.length),
      MultiVar.eval ((addCoeffs as bs).getLast hab) env
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
          show MultiVar.eval (MultiVar.add a b) env
              = MultiVar.eval a env + MultiVar.eval b env
          rfl
        | cons b2 bs'' => simp at hlen
      | cons a2 as'' =>
        cases bs' with
        | nil => simp at hlen
        | cons b2 bs'' =>
          have hrest : addCoeffs (a2 :: as'') (b2 :: bs'') ≠ [] := List.cons_ne_nil _ _
          have hlen' : (a2 :: as'').length = (b2 :: bs'').length := by
            simp only [List.length_cons] at hlen ⊢; omega
          rw [show (addCoeffs (a :: a2 :: as'') (b :: b2 :: bs'')).getLast hab
                = (addCoeffs (a2 :: as'') (b2 :: bs'')).getLast hrest from by
              show (MultiVar.add a b :: addCoeffs (a2 :: as'') (b2 :: bs'')).getLast hab
                  = (addCoeffs (a2 :: as'') (b2 :: bs'')).getLast hrest
              rw [List.getLast_cons hrest],
            List.getLast_cons (List.cons_ne_nil a2 as''),
            List.getLast_cons (List.cons_ne_nil b2 bs'')]
          exact ih (b2 :: bs'') (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) hrest hlen'

/-- `getLast` through `scaleCoeffs` (a `map`): the last coefficient scales. -/
theorem eval_getLast_scaleCoeffs (env : Fin 2 → Real) (c : MultiVar 2) (as : List (MultiVar 2))
    (ha : as ≠ []) (h : scaleCoeffs c as ≠ []) :
    MultiVar.eval ((scaleCoeffs c as).getLast h) env
      = MultiVar.eval c env * MultiVar.eval (as.getLast ha) env := by
  show MultiVar.eval ((as.map (fun b => MultiVar.mul c b)).getLast h) env = _
  rw [List.getLast_map]; rfl

theorem shiftCoeffs_ne_nil (k : Nat) {X : List (MultiVar 2)} (hX : X ≠ []) :
    shiftCoeffs k X ≠ [] := by
  cases k with
  | zero => show List.replicate 0 (MultiVar.const 0) ++ X ≠ []; simpa using hX
  | succ k =>
    show MultiVar.const 0 :: (List.replicate k (MultiVar.const 0) ++ X) ≠ []
    exact List.cons_ne_nil _ _

/-- `getLast` through `shiftCoeffs` (prepending zeros): unchanged. -/
theorem getLast_shiftCoeffs {X : List (MultiVar 2)} (hX : X ≠ []) :
    ∀ (k : Nat) (h : shiftCoeffs k X ≠ []), (shiftCoeffs k X).getLast h = X.getLast hX
  | 0, _ => rfl
  | k + 1, h => by
      show (MultiVar.const 0 :: shiftCoeffs k X).getLast h = X.getLast hX
      rw [List.getLast_cons (shiftCoeffs_ne_nil k hX), getLast_shiftCoeffs hX k]

theorem scaleCoeffs_ne_nil (c : MultiVar 2) {as : List (MultiVar 2)} (ha : as ≠ []) :
    scaleCoeffs c as ≠ [] := by
  cases as with
  | nil => exact absurd rfl ha
  | cons a as' => exact List.cons_ne_nil _ _

theorem negCoeffs_ne_nil {X : List (MultiVar 2)} (hX : X ≠ []) : negCoeffs X ≠ [] := by
  cases X with
  | nil => exact absurd rfl hX
  | cons x xs => exact List.cons_ne_nil _ _

/-- `getLast` through `negCoeffs` (a `map (0 - ·)`): negates the last coefficient. -/
theorem eval_getLast_negCoeffs (env : Fin 2 → Real) (X : List (MultiVar 2)) (hX : X ≠ [])
    (h : negCoeffs X ≠ []) :
    MultiVar.eval ((negCoeffs X).getLast h) env = 0 - MultiVar.eval (X.getLast hX) env := by
  show MultiVar.eval ((X.map (fun b => MultiVar.sub (MultiVar.const 0) b)).getLast h) env = _
  rw [List.getLast_map]; rfl

/-! ## The reduction's top coefficient cancels -/

/-- **The reduction's top coefficient evaluates to `0`** (with `q_lead = qs.getLast`, `p_lead =
ps.getLast`): the leading terms `q_lead·p_lead − p_lead·q_lead` cancel for every `env`. Hence `dropLast`
preserves the evaluation. -/
theorem reduceFull_getLast_eval_zero (env : Fin 2 → Real) (ps qs : List (MultiVar 2))
    (hps : ps ≠ []) (hqs : qs ≠ []) (hlen : qs.length ≤ ps.length)
    (h : reduceFull (qs.getLast hqs) (ps.getLast hps) (ps.length - qs.length) ps qs ≠ []) :
    MultiVar.eval
      ((reduceFull (qs.getLast hqs) (ps.getLast hps) (ps.length - qs.length) ps qs).getLast h) env
      = 0 := by
  have hA : scaleCoeffs (qs.getLast hqs) ps ≠ [] := scaleCoeffs_ne_nil _ hps
  have hXscale : scaleCoeffs (ps.getLast hps) qs ≠ [] := scaleCoeffs_ne_nil _ hqs
  have hBshift : shiftCoeffs (ps.length - qs.length) (scaleCoeffs (ps.getLast hps) qs) ≠ [] :=
    shiftCoeffs_ne_nil _ hXscale
  have hnegB : negCoeffs (shiftCoeffs (ps.length - qs.length) (scaleCoeffs (ps.getLast hps) qs)) ≠ [] :=
    negCoeffs_ne_nil hBshift
  have hleneq : (scaleCoeffs (qs.getLast hqs) ps).length
      = (negCoeffs (shiftCoeffs (ps.length - qs.length) (scaleCoeffs (ps.getLast hps) qs))).length := by
    rw [length_scaleCoeffs, length_negCoeffs, length_shiftCoeffs, length_scaleCoeffs]; omega
  show MultiVar.eval ((addCoeffs (scaleCoeffs (qs.getLast hqs) ps)
      (negCoeffs (shiftCoeffs (ps.length - qs.length) (scaleCoeffs (ps.getLast hps) qs)))).getLast h) env
      = 0
  rw [eval_getLast_addCoeffs env _ _ hA hnegB h hleneq,
    eval_getLast_scaleCoeffs env (qs.getLast hqs) ps hps hA,
    eval_getLast_negCoeffs env _ hBshift hnegB,
    getLast_shiftCoeffs hXscale (ps.length - qs.length),
    eval_getLast_scaleCoeffs env (ps.getLast hps) qs hqs hXscale]
  mach_ring

/-- **Dropping an eval-zero last coefficient preserves eval.** `evalCoeffs l.dropLast = evalCoeffs l`
when `l.getLast` evaluates to `0`. Induction on `l`. -/
theorem evalCoeffs_dropLast_of_getLast_zero (env : Fin 2 → Real) :
    ∀ (l : List (MultiVar 2)) (hl : l ≠ []), MultiVar.eval (l.getLast hl) env = 0 →
      evalCoeffs l.dropLast env = evalCoeffs l env
  | [], hl, _ => absurd rfl hl
  | [a], _, hz => by
      show evalCoeffs [] env = evalCoeffs [a] env
      simp only [evalCoeffs_cons, evalCoeffs_nil]
      rw [show MultiVar.eval a env = 0 from hz]; mach_ring
  | a :: b :: l', _, hz => by
      have hz' : MultiVar.eval ((b :: l').getLast (List.cons_ne_nil b l')) env = 0 := by
        rw [List.getLast_cons (List.cons_ne_nil b l')] at hz; exact hz
      show evalCoeffs (a :: (b :: l').dropLast) env = evalCoeffs (a :: b :: l') env
      rw [evalCoeffs_cons, evalCoeffs_cons,
        evalCoeffs_dropLast_of_getLast_zero env (b :: l') (List.cons_ne_nil b l') hz']

/-- **`reduceOnce` vanishes at a common zero.** With leading coefficients `qs.getLast`, `ps.getLast`, the
polynomial-remainder step preserves "vanishes at common zeros of `p, q`": `reduceFull` vanishes there
(`reduceFull_vanish`) and its dropped top is eval-zero (`reduceFull_getLast_eval_zero`), so `reduceOnce`
does too. The PRS invariant, now at the list level with the degree formally dropping. -/
theorem reduceOnce_vanish (env : Fin 2 → Real) (ps qs : List (MultiVar 2))
    (hps : ps ≠ []) (hqs : qs ≠ []) (hlen : qs.length ≤ ps.length)
    (hp : evalCoeffs ps env = 0) (hq : evalCoeffs qs env = 0) :
    evalCoeffs (reduceOnce (qs.getLast hqs) (ps.getLast hps) ps qs) env = 0 := by
  show evalCoeffs
    (reduceFull (qs.getLast hqs) (ps.getLast hps) (ps.length - qs.length) ps qs).dropLast env = 0
  have hleneq : (scaleCoeffs (qs.getLast hqs) ps).length
      = (negCoeffs (shiftCoeffs (ps.length - qs.length) (scaleCoeffs (ps.getLast hps) qs))).length := by
    rw [length_scaleCoeffs, length_negCoeffs, length_shiftCoeffs, length_scaleCoeffs]; omega
  have hne : reduceFull (qs.getLast hqs) (ps.getLast hps) (ps.length - qs.length) ps qs ≠ [] :=
    addCoeffs_ne_nil hleneq (scaleCoeffs_ne_nil _ hps)
  rw [evalCoeffs_dropLast_of_getLast_zero env _ hne
    (reduceFull_getLast_eval_zero env ps qs hps hqs hlen hne)]
  exact reduceFull_vanish env (qs.getLast hqs) (ps.getLast hps) (ps.length - qs.length) ps qs hp hq

end MultiVarMod
end MachLib
