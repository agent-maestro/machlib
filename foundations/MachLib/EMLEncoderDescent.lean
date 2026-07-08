import MachLib.EMLEncoder
import MachLib.PfaffianChainExtendELR
import MachLib.PfaffianExpLogRecipDescent
import MachLib.DivisionError

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
  MachLib.PfaffianChainMod.PfaffianFn
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

/-! ## The encoder produces an `IsExpLogRecipW` chain (the 4th descent input) -/

/-- `degreeY` of a negation equals that of the argument (`neg p = sub 0 p`, and
`degreeY` of a `sub` is the `max`, with the zero summand contributing 0). -/
theorem degreeY_neg {n : Nat} (i : Fin n) (p : MultiPoly n) :
    MultiPoly.degreeY i (MultiPoly.neg p) = MultiPoly.degreeY i p := by
  show Nat.max (MultiPoly.degreeY i (MultiPoly.const 0)) (MultiPoly.degreeY i p)
     = MultiPoly.degreeY i p
  exact Nat.max_eq_right (Nat.zero_le _)

/-- **The eml step's chain is `IsExpLogRecipW`.** recip node → reciprocal-type
(witness `liftLastY w = ⟦t2⟧`, `y·v=1` via `div_mul_cancel`, `v>0` from `hwpos`),
log node → log-type (`degreeY` of its own variable is 0), exp node → exp-type
(`G·y_top`). Node-by-node via `chainExtend_IsExpLogRecipW`. -/
theorem encEmlStepR_IsExpLogRecipW {M : Nat} (cb : PfaffianChain M) (b1 w : MultiPoly M)
    (a b : Real)
    (hcb : IsExpLogRecipW cb a b)
    (hwpos : ∀ x, a < x → x < b → 0 < MultiPoly.eval w x (cb.chainValues x)) :
    IsExpLogRecipW (encEmlStepR cb b1 w) a b := by
  have dmul : ∀ {k : Nat} (i : Fin k) (p q : MultiPoly k),
      MultiPoly.degreeY i (MultiPoly.mul p q)
        = MultiPoly.degreeY i p + MultiPoly.degreeY i q := fun _ _ _ => rfl
  -- reciprocal node
  have hcc : IsExpLogRecipW (stepCC cb w) a b := by
    simp only [stepCC]
    apply chainExtend_IsExpLogRecipW cb a b _ _ hcb
    refine ⟨Or.inr (Or.inr ⟨MultiPoly.neg (MultiPoly.liftLastY (chainTotalDeriv cb w)),
        MultiPoly.liftLastY w, ?_, ?_, ?_, ?_, ?_⟩), ?_⟩
    · rw [degreeY_neg]; exact degreeY_top_liftLastY _
    · rw [chainExtend_relations_last cb _ _]
    · intro j hj
      have hjval : j.val = M := by omega
      have hjeq : j = (⟨M, Nat.lt_succ_self M⟩ : Fin (M + 1)) := Fin.ext hjval
      rw [hjeq]; exact degreeY_top_liftLastY w
    · intro x hxa hxb
      rw [chainExtend_evals_last cb _ _, eval_liftLastY_chainExtend cb _ _ w x]
      show (1 / MultiPoly.eval w x (cb.chainValues x)) * MultiPoly.eval w x (cb.chainValues x) = 1
      exact div_mul_cancel (ne_of_gt (hwpos x hxa hxb))
    · intro x hxa hxb
      rw [eval_liftLastY_chainExtend cb _ _ w x]; exact hwpos x hxa hxb
    · intro j hj; exact absurd hj (by omega)
  -- log node
  have hcd : IsExpLogRecipW (stepCD cb w) a b := by
    simp only [stepCD]
    apply chainExtend_IsExpLogRecipW (stepCC cb w) a b _ _ hcc
    refine ⟨Or.inr (Or.inl ?_), ?_⟩
    · rw [chainExtend_relations_last (stepCC cb w) _ _, dmul, degreeY_top_liftLastY, Nat.zero_add]
      show (if (⟨M + 1, Nat.lt_succ_self (M + 1)⟩ : Fin (M + 2)) = (⟨M, by omega⟩ : Fin (M + 2))
          then (1 : Nat) else 0) = 0
      rw [if_neg (Fin.ne_of_val_ne (Nat.succ_ne_self M))]
    · intro j hj; exact absurd hj (by omega)
  -- exp node
  simp only [encEmlStepR]
  apply chainExtend_IsExpLogRecipW (stepCD cb w) a b _ _ hcd
  refine ⟨Or.inl ⟨MultiPoly.liftLastY (chainTotalDeriv (stepCD cb w) (liftLastYBy 2 b1)), ?_, ?_⟩, ?_⟩
  · exact degreeY_top_liftLastY _
  · rw [chainExtend_relations_last (stepCD cb w) _ _]
  · intro j hj; exact absurd hj (by omega)

/-- **The encoder produces an `IsExpLogRecipW` chain.** Given the context chain is
in the class and every log-argument stays positive (`LogArgPos`), so is
`enc t chain`. The fourth and last descent input the encoder owes. -/
theorem enc_IsExpLogRecipW (t : EMLTree) :
    ∀ {N : Nat} (chain : PfaffianChain N) (a b : Real),
      IsExpLogRecipW chain a b → LogArgPos t a b → IsExpLogRecipW (enc t chain).1 a b := by
  induction t with
  | const c => intro N chain a b hchain _; exact hchain
  | var => intro N chain a b hchain _; exact hchain
  | eml t1 t2 ih1 ih2 =>
    intro N chain a b hchain hpos
    obtain ⟨hpos1, hpos2, hposLog⟩ := hpos
    have hcbW := ih1 (enc t2 chain).1 a b (ih2 chain a b hchain hpos2) hpos1
    have hwpos : ∀ x, a < x → x < b → 0 < MultiPoly.eval (encLift t1 (enc t2 chain).2) x
        ((enc t1 (enc t2 chain).1).1.chainValues x) := by
      intro x hxa hxb
      rw [enc_encLift_eval t1 t2 chain x (t2.eval x) (enc_eval t2 chain x)]
      exact hposLog x hxa hxb
    show IsExpLogRecipW (encEmlStepR (enc t1 (enc t2 chain).1).1 (enc t1 (enc t2 chain).1).2
      (encLift t1 (enc t2 chain).2)) a b
    exact encEmlStepR_IsExpLogRecipW (enc t1 (enc t2 chain).1).1
      (enc t1 (enc t2 chain).1).2 (encLift t1 (enc t2 chain).2) a b hcbW hwpos

end MachLib
