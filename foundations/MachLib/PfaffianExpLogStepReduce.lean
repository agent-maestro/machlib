import MachLib.PfaffianExpLogRecipDescent
import MachLib.PfaffianGeneralWF

/-!
# Degree-0 discharge of the exp/log steps — Brick A-4b''

The two remaining classical obligations `exp_step` and `log_step` each split by
the target's degree in the top variable. The `degreeY_top p = 0` case (target
does not use the top generator) is **free** — the general
`pfaffianChainFn_bound_of_degreeYtop_zero` (no `IsExpChain`, no coherence needed)
reduces it straight to the restricted-chain IH. So each step reduces to its
`degreeY_top p > 0` core (`exp_hard` / `log_hard`) — the genuine Rolle /
integrating-factor content. This tightens what the classical machinery must
still deliver.
-/

namespace MachLib
namespace PfaffianExpLogRecip
open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianGeneralReduce
open MachLib.PfaffianExpRecipW

/-- The exp-top obligation, reduced to its degree>0 core: given the reduction
for `degreeY_top p > 0`, the full `exp_step` follows (the `degreeY_top p = 0` case
is free via the general `pfaffianChainFn_bound_of_degreeYtop_zero`). -/
theorem exp_step_from_hard (a b : Real) (hab : a < b)
    (exp_hard : ∀ (k : Nat) (c : PfaffianChain (k + 1)),
        IsExpLogRecipW c a b → c.IsCoherentOn a b →
        (∀ z, a < z → z < b → ∀ i : Fin (k + 1), 0 < c.evals i z) →
        (∃ G : MultiPoly (k + 1), MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ G = 0
            ∧ c.relations ⟨k, Nat.lt_succ_self k⟩
                = MultiPoly.mul G (MultiPoly.varY ⟨k, Nat.lt_succ_self k⟩)) →
        (∀ j : Fin (k + 1), j ≠ ⟨k, Nat.lt_succ_self k⟩ →
            MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ (c.relations j) = 0) →
        (∀ q : MultiPoly k,
            (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z ≠ 0) →
            BoundedZeros (pfaffianChainFn (chainRestrict c) q) a b) →
        ∀ p : MultiPoly (k + 1),
          (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
          0 < MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ p →
          BoundedZeros (pfaffianChainFn c p) a b) :
    ∀ (k : Nat) (c : PfaffianChain (k + 1)),
        IsExpLogRecipW c a b → c.IsCoherentOn a b →
        (∀ z, a < z → z < b → ∀ i : Fin (k + 1), 0 < c.evals i z) →
        (∃ G : MultiPoly (k + 1), MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ G = 0
            ∧ c.relations ⟨k, Nat.lt_succ_self k⟩
                = MultiPoly.mul G (MultiPoly.varY ⟨k, Nat.lt_succ_self k⟩)) →
        (∀ j : Fin (k + 1), j ≠ ⟨k, Nat.lt_succ_self k⟩ →
            MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ (c.relations j) = 0) →
        (∀ q : MultiPoly k,
            (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z ≠ 0) →
            BoundedZeros (pfaffianChainFn (chainRestrict c) q) a b) →
        ∀ p : MultiPoly (k + 1),
          (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
          BoundedZeros (pfaffianChainFn c p) a b := by
  intro k c hW hcoh hpos hexp htf hIH p hne
  by_cases hd : MultiPoly.degreeY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) p = 0
  · exact pfaffianChainFn_bound_of_degreeYtop_zero c p hd a b hab hne hIH
  · exact exp_hard k c hW hcoh hpos hexp htf hIH p hne (Nat.pos_of_ne_zero hd)

/-- The log-top obligation, reduced to its degree>0 core (same split). -/
theorem log_step_from_hard (a b : Real) (hab : a < b)
    (log_hard : ∀ (k : Nat) (c : PfaffianChain (k + 1)),
        IsExpLogRecipW c a b → c.IsCoherentOn a b →
        (∀ z, a < z → z < b → ∀ i : Fin (k + 1), 0 < c.evals i z) →
        (MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ (c.relations ⟨k, Nat.lt_succ_self k⟩) = 0) →
        (∀ j : Fin (k + 1), j ≠ ⟨k, Nat.lt_succ_self k⟩ →
            MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ (c.relations j) = 0) →
        (∀ q : MultiPoly k,
            (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z ≠ 0) →
            BoundedZeros (pfaffianChainFn (chainRestrict c) q) a b) →
        ∀ p : MultiPoly (k + 1),
          (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
          0 < MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ p →
          BoundedZeros (pfaffianChainFn c p) a b) :
    ∀ (k : Nat) (c : PfaffianChain (k + 1)),
        IsExpLogRecipW c a b → c.IsCoherentOn a b →
        (∀ z, a < z → z < b → ∀ i : Fin (k + 1), 0 < c.evals i z) →
        (MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ (c.relations ⟨k, Nat.lt_succ_self k⟩) = 0) →
        (∀ j : Fin (k + 1), j ≠ ⟨k, Nat.lt_succ_self k⟩ →
            MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ (c.relations j) = 0) →
        (∀ q : MultiPoly k,
            (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z ≠ 0) →
            BoundedZeros (pfaffianChainFn (chainRestrict c) q) a b) →
        ∀ p : MultiPoly (k + 1),
          (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
          BoundedZeros (pfaffianChainFn c p) a b := by
  intro k c hW hcoh hpos hlog htf hIH p hne
  by_cases hd : MultiPoly.degreeY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) p = 0
  · exact pfaffianChainFn_bound_of_degreeYtop_zero c p hd a b hab hne hIH
  · exact log_hard k c hW hcoh hpos hlog htf hIH p hne (Nat.pos_of_ne_zero hd)

end PfaffianExpLogRecip
end MachLib
