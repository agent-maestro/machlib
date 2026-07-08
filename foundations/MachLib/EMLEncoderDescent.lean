import MachLib.EMLEncoder
import MachLib.PfaffianChainExtendELR
import MachLib.PfaffianExpLogRecipDescent

/-!
# The encoder satisfies the descent's positivity hypothesis

Closes the loop on the positivity blocker: `combined_descent_3` was weakened to
require only `PosExceptLog` (every chain value positive EXCEPT the signed
log-type ones). Here we prove the encoder's chain actually satisfies it — so the
weakening is genuinely satisfiable by `enc`, not just vacuously weaker.

Per `eml` node: the reciprocal value `1/⟦t2⟧` is positive (`⟦t2⟧>0` from
`LogArgPos`), the exp value `exp⟦t1⟧` is positive unconditionally — both take the
positive disjunct — while the log value `log⟦t2⟧` (possibly signed) takes the
`degreeY = 0` disjunct, true because a log node's relation omits its own variable.

No new axioms.
-/

namespace MachLib

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
  MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain
  MachLib.PfaffianGeneralReduce MachLib.PfaffianExpLogRecip

/-- **`chainExtend` preserves `PosExceptLog`.** Lower variables keep their
disjunct (`degreeY` under `liftLastY` via `degreeY_liftLastY_of_lt`, values
preserved); the new top variable is supplied by `hnew` — either its relation is
log-type (`degreeY` of `nr` at the top is 0) or its value `ne` is positive. -/
theorem chainExtend_PosExceptLog {n : Nat} (c : PfaffianChain n) (ne : Real → Real)
    (nr : MultiPoly (n + 1)) (a b : Real)
    (hc : PosExceptLog c a b)
    (hnew : MultiPoly.degreeY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) nr = 0
            ∨ (∀ z, a < z → z < b → 0 < ne z)) :
    PosExceptLog (chainExtend c ne nr) a b := by
  intro z hza hzb i
  by_cases h : i.val < n
  · rcases hc z hza hzb ⟨i.val, h⟩ with hlog | hp
    · left
      rw [chainExtend_relations_of_lt c ne nr i h,
          degreeY_liftLastY_of_lt i h (c.relations ⟨i.val, h⟩)]
      exact hlog
    · right
      rw [chainExtend_evals_of_lt c ne nr i h]
      exact hp
  · have hval : i.val = n := by omega
    have hi : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hval
    rcases hnew with hd | hpos
    · left; rw [hi, chainExtend_relations_last c ne nr]; exact hd
    · right; rw [hi, chainExtend_evals_last c ne nr]; exact hpos z hza hzb

/-- **The eml step satisfies `PosExceptLog`.** recip node → positive (`1/⟦t2⟧`),
log node → `degreeY = 0` (relation omits its own variable), exp node → positive
(`exp⟦t1⟧`). Node-by-node via `chainExtend_PosExceptLog`. -/
theorem encEmlStepR_PosExceptLog {M : Nat} (cb : PfaffianChain M) (b1 w : MultiPoly M)
    (a b : Real)
    (hcb : PosExceptLog cb a b)
    (hwpos : ∀ z, a < z → z < b → 0 < MultiPoly.eval w z (cb.chainValues z)) :
    PosExceptLog (encEmlStepR cb b1 w) a b := by
  have dmul : ∀ {k : Nat} (i : Fin k) (p q : MultiPoly k),
      MultiPoly.degreeY i (MultiPoly.mul p q)
        = MultiPoly.degreeY i p + MultiPoly.degreeY i q := fun _ _ _ => rfl
  have hccP : PosExceptLog (stepCC cb w) a b := by
    simp only [stepCC]
    apply chainExtend_PosExceptLog cb _ _ a b hcb
    right; intro z hza hzb
    exact Real.one_div_pos_of_pos (hwpos z hza hzb)
  have hcdP : PosExceptLog (stepCD cb w) a b := by
    simp only [stepCD]
    apply chainExtend_PosExceptLog (stepCC cb w) _ _ a b hccP
    left
    rw [dmul, degreeY_top_liftLastY, Nat.zero_add]
    show (if (⟨M + 1, Nat.lt_succ_self (M + 1)⟩ : Fin (M + 2)) = (⟨M, by omega⟩ : Fin (M + 2))
        then (1 : Nat) else 0) = 0
    rw [if_neg (Fin.ne_of_val_ne (Nat.succ_ne_self M))]
  simp only [encEmlStepR]
  apply chainExtend_PosExceptLog (stepCD cb w) _ _ a b hcdP
  right; intro z hza hzb
  exact Real.exp_pos _

/-- **The encoder satisfies `PosExceptLog`.** If the context chain does, and every
`eml` node's log-argument stays positive (`LogArgPos`), then `enc t chain`'s chain
does too — exactly the positivity `combined_descent_3` now requires. -/
theorem enc_PosExceptLog (t : EMLTree) :
    ∀ {N : Nat} (chain : PfaffianChain N) (a b : Real),
      PosExceptLog chain a b → LogArgPos t a b → PosExceptLog (enc t chain).1 a b := by
  induction t with
  | const c => intro N chain a b hchain _; exact hchain
  | var => intro N chain a b hchain _; exact hchain
  | eml t1 t2 ih1 ih2 =>
    intro N chain a b hchain hpos
    obtain ⟨hpos1, hpos2, hposLog⟩ := hpos
    have hcbP := ih1 (enc t2 chain).1 a b (ih2 chain a b hchain hpos2) hpos1
    have hwpos : ∀ z, a < z → z < b → 0 < MultiPoly.eval (encLift t1 (enc t2 chain).2) z
        ((enc t1 (enc t2 chain).1).1.chainValues z) := by
      intro z hza hzb
      rw [enc_encLift_eval t1 t2 chain z (t2.eval z) (enc_eval t2 chain z)]
      exact hposLog z hza hzb
    show PosExceptLog (encEmlStepR (enc t1 (enc t2 chain).1).1 (enc t1 (enc t2 chain).1).2
      (encLift t1 (enc t2 chain).2)) a b
    exact encEmlStepR_PosExceptLog (enc t1 (enc t2 chain).1).1
      (enc t1 (enc t2 chain).1).2 (encLift t1 (enc t2 chain).2) a b hcbP hwpos

end MachLib
