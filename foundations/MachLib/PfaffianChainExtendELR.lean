import MachLib.PfaffianChainExtend
import MachLib.PfaffianExpLogRecipClass

/-!
# `liftLastY` degree companion — toward `chainExtend` preserving `IsExpLogRecipW`

The encoder builds a chain by repeated `chainExtend`. Proving the built
chain stays in the exp∨log∨reciprocal class (`chainExtend_IsExpLogRecipW`)
needs, for the old relations lifted through `liftLastY`:
- the relation TYPE preserved (`liftLastY_mul`/`_varY` are definitional),
- triangularity to the new top (`degreeY_top_liftLastY`, already present),
- and triangularity/degree at OLD indices — supplied here.

`degreeY_liftLastY_of_lt` is the missing structural companion of the
existing `degreeY_top_liftLastY`: lifting preserves the formal `y_j`-degree
at every old index `j.val < n`. The full `chainExtend_IsExpLogRecipW`
(three type cases, reciprocal eval-conditions transferred via
`eval_liftLastY_chainExtend`) is the next brick.

No new axioms.
-/

namespace MachLib

open MachLib.Real MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
  MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain
  MachLib.PfaffianGeneralReduce MachLib.PfaffianExpLogRecip

/-- Lifting preserves the formal `y`-degree at every OLD index. -/
theorem degreeY_liftLastY_of_lt {n : Nat} (i : Fin (n + 1)) (h : i.val < n)
    (p : MultiPoly n) :
    MultiPoly.degreeY i (MultiPoly.liftLastY p) = MultiPoly.degreeY ⟨i.val, h⟩ p := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY j =>
    show (if i = (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1)) then (1 : Nat) else 0)
       = (if (⟨i.val, h⟩ : Fin n) = j then 1 else 0)
    simp only [Fin.ext_iff]
  | add p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY i (MultiPoly.liftLastY p))
                 (MultiPoly.degreeY i (MultiPoly.liftLastY q))
       = Nat.max (MultiPoly.degreeY ⟨i.val, h⟩ p) (MultiPoly.degreeY ⟨i.val, h⟩ q)
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show Nat.max (MultiPoly.degreeY i (MultiPoly.liftLastY p))
                 (MultiPoly.degreeY i (MultiPoly.liftLastY q))
       = Nat.max (MultiPoly.degreeY ⟨i.val, h⟩ p) (MultiPoly.degreeY ⟨i.val, h⟩ q)
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show MultiPoly.degreeY i (MultiPoly.liftLastY p)
         + MultiPoly.degreeY i (MultiPoly.liftLastY q)
       = MultiPoly.degreeY ⟨i.val, h⟩ p + MultiPoly.degreeY ⟨i.val, h⟩ q
    rw [ihp, ihq]

/-- **`chainExtend` preserves `IsExpLogRecipW`.** If `c` is in the class and
the appended top relation is itself one of the three admissible shapes (the
`hnew` hypothesis, stated for the extended chain at index `n`), so is
`chainExtend c ne nr`. Old relations keep their shape through `liftLastY`
(structural rules are definitional; reciprocal eval-conditions transfer via
`eval_liftLastY_chainExtend`) and their triangularity via
`degreeY_liftLastY_of_lt` (old cols) + `degreeY_top_liftLastY` (new col). -/
theorem chainExtend_IsExpLogRecipW {n : Nat} (c : PfaffianChain n) (a b : Real)
    (ne : Real → Real) (nr : MultiPoly (n + 1))
    (hc : IsExpLogRecipW c a b)
    (hnew :
      ( (∃ G : MultiPoly (n + 1),
            MultiPoly.degreeY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) G = 0
            ∧ (chainExtend c ne nr).relations (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
                = MultiPoly.mul G (MultiPoly.varY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))))
        ∨ (MultiPoly.degreeY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
              ((chainExtend c ne nr).relations (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))) = 0)
        ∨ (∃ (G v : MultiPoly (n + 1)),
              MultiPoly.degreeY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) G = 0
              ∧ (chainExtend c ne nr).relations (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
                  = MultiPoly.mul G (MultiPoly.mul
                      (MultiPoly.varY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)))
                      (MultiPoly.varY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))))
              ∧ (∀ j : Fin (n + 1), n ≤ j.val → MultiPoly.degreeY j v = 0)
              ∧ (∀ x : Real, a < x → x < b →
                  (chainExtend c ne nr).evals (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) x
                    * MultiPoly.eval v x ((chainExtend c ne nr).chainValues x) = 1)
              ∧ (∀ x : Real, a < x → x < b →
                  0 < MultiPoly.eval v x ((chainExtend c ne nr).chainValues x)) ) )
      ∧ (∀ j : Fin (n + 1), n < j.val →
          MultiPoly.degreeY j
            ((chainExtend c ne nr).relations (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))) = 0)) :
    IsExpLogRecipW (chainExtend c ne nr) a b := by
  intro i
  by_cases h : i.val < n
  · obtain ⟨htype, htri⟩ := hc ⟨i.val, h⟩
    refine ⟨?_, ?_⟩
    · rcases htype with hexp | hlog | hrec
      · -- exp-type
        obtain ⟨G, hG, hrel⟩ := hexp
        refine Or.inl ⟨MultiPoly.liftLastY G, ?_, ?_⟩
        · rw [degreeY_liftLastY_of_lt i h G]; exact hG
        · rw [chainExtend_relations_of_lt c ne nr i h, hrel]
          show MultiPoly.mul (MultiPoly.liftLastY G)
                (MultiPoly.varY (⟨i.val, Nat.lt_succ_of_lt h⟩ : Fin (n + 1)))
             = MultiPoly.mul (MultiPoly.liftLastY G) (MultiPoly.varY i)
          exact congrArg (MultiPoly.mul (MultiPoly.liftLastY G))
            (congrArg MultiPoly.varY (Fin.ext rfl))
      · -- log-type
        refine Or.inr (Or.inl ?_)
        rw [chainExtend_relations_of_lt c ne nr i h,
            degreeY_liftLastY_of_lt i h (c.relations ⟨i.val, h⟩)]
        exact hlog
      · -- reciprocal-type
        obtain ⟨G, v, hG, hrel, hvtf, hvcoh, hvpos⟩ := hrec
        refine Or.inr (Or.inr ⟨MultiPoly.liftLastY G, MultiPoly.liftLastY v, ?_, ?_, ?_, ?_, ?_⟩)
        · rw [degreeY_liftLastY_of_lt i h G]; exact hG
        · rw [chainExtend_relations_of_lt c ne nr i h, hrel]
          show MultiPoly.mul (MultiPoly.liftLastY G)
                (MultiPoly.mul (MultiPoly.varY (⟨i.val, Nat.lt_succ_of_lt h⟩ : Fin (n + 1)))
                               (MultiPoly.varY (⟨i.val, Nat.lt_succ_of_lt h⟩ : Fin (n + 1))))
             = MultiPoly.mul (MultiPoly.liftLastY G)
                (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.varY i))
          have hvar : (MultiPoly.varY (⟨i.val, Nat.lt_succ_of_lt h⟩ : Fin (n + 1)))
              = MultiPoly.varY i := congrArg MultiPoly.varY (Fin.ext rfl)
          rw [hvar]
        · intro j hj
          by_cases hjn : j.val < n
          · rw [degreeY_liftLastY_of_lt j hjn v]
            exact hvtf ⟨j.val, hjn⟩ hj
          · have hjeq : j = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := by
              apply Fin.ext; show j.val = n; have := j.isLt; omega
            rw [hjeq]; exact degreeY_top_liftLastY v
        · intro x hxa hxb
          rw [chainExtend_evals_of_lt c ne nr i h, eval_liftLastY_chainExtend c ne nr v x]
          exact hvcoh x hxa hxb
        · intro x hxa hxb
          rw [eval_liftLastY_chainExtend c ne nr v x]
          exact hvpos x hxa hxb
    · -- triangularity for the old column
      intro j hj
      rw [chainExtend_relations_of_lt c ne nr i h]
      by_cases hjn : j.val < n
      · rw [degreeY_liftLastY_of_lt j hjn (c.relations ⟨i.val, h⟩)]
        exact htri ⟨j.val, hjn⟩ hj
      · have hjeq : j = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := by
          apply Fin.ext; show j.val = n; have := j.isLt; omega
        rw [hjeq]; exact degreeY_top_liftLastY _
  · -- new top column i = ⟨n, _⟩
    have hi : i = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) := by
      apply Fin.ext; show i.val = n; have := i.isLt; omega
    rw [hi]; exact hnew

end MachLib
