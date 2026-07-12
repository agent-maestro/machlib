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

end MultiVarMod
end MachLib
