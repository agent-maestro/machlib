import MachLib.MultiPoly
import MachLib.PfaffianChain
import MachLib.PfaffianGeneralReduce

/-!
# Witness-enriched exp-or-reciprocal chain class — Brick A-4a foundation

The combined extended descent (`sin_not_in_eml_any_depth` retirement, full route)
strips interleaved exp and reciprocal tops. The reciprocal-top step
(`MachLib.PfaffianExpRecip.recip_top_step`) needs the **witness** `v` of the top
reciprocal level — the log argument, with `y_top = 1/v`. The bare class
`IsExpOrRecipChain` records only that a level's relation is `G·y²`; it does not
carry `v`. This file enriches the class to carry that witness (per reciprocal
level), which is what the descent consumes at each strip.

Witness data per reciprocal level `i` (domain `(a,b)`):
- `v : MultiPoly N` top-free at and above `i` (`degreeY j v = 0` for `i ≤ j`), so
  `v` lives over the sub-chain strictly below `i`;
- coherence `yᵢ · v = 1` on `(a,b)` (i.e. `yᵢ = 1/v`);
- positivity `v > 0` on `(a,b)` (EML domain-safety: `log` arguments are positive).

The load-bearing fact is `IsExpOrRecipW_chainRestrict`: the enriched class is
closed under `chainRestrict`, with the witness `dropLastY`'d and its
coherence/positivity transferred via `eval_dropLastY` (`v` is top-free at the
dropped top). Together with `IsExpOrRecipW_top`, the depth descent can strip a
top and recurse within the class, carrying witnesses.
-/

namespace MachLib
namespace PfaffianExpRecipW

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianGeneralReduce

/-- **Witness-enriched exp-or-reciprocal chain (domain `(a,b)`).** Each level is
exp-type, or reciprocal-type *with a witness* `v` (the log argument): `v` is
top-free at and above `i`, `yᵢ·v = 1` on `(a,b)`, and `v > 0` there. Strictly
refines `IsExpOrRecipChain` by pinning the reciprocal denominator. -/
def IsExpOrRecipW {N : Nat} (c : PfaffianChain N) (a b : Real) : Prop :=
  ∀ i : Fin N,
    ( (∃ G : MultiPoly N, MultiPoly.degreeY i G = 0
          ∧ c.relations i = MultiPoly.mul G (MultiPoly.varY i))
      ∨ (∃ (G v : MultiPoly N),
            MultiPoly.degreeY i G = 0
            ∧ c.relations i
                = MultiPoly.mul G (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.varY i))
            ∧ (∀ j : Fin N, i.val ≤ j.val → MultiPoly.degreeY j v = 0)
            ∧ (∀ x : Real, a < x → x < b →
                c.evals i x * MultiPoly.eval v x (c.chainValues x) = 1)
            ∧ (∀ x : Real, a < x → x < b → 0 < MultiPoly.eval v x (c.chainValues x)) ) )
    ∧ (∀ j : Fin N, i.val < j.val → MultiPoly.degreeY j (c.relations i) = 0)

/-- Every exp-type chain is witness-enriched (all levels exp, witnesses vacuous). -/
theorem IsExpChain_imp_IsExpOrRecipW {N : Nat} (c : PfaffianChain N) (a b : Real)
    (h : IsExpChain c) : IsExpOrRecipW c a b := by
  intro i
  obtain ⟨hrel, htri⟩ := h i
  exact ⟨Or.inl hrel, htri⟩

/-- **`chainRestrict` preserves the witness-enriched class.** Exp disjunct and
triangularity mirror `IsExpOrRecipChain_chainRestrict`; the reciprocal witness
`v` is `dropLastY`'d and its coherence/positivity transfer via `eval_dropLastY`
(`v` is top-free at the dropped top) + `chainRestrict`'s definitional value
agreement. So the depth descent recurses within the class, carrying witnesses. -/
theorem IsExpOrRecipW_chainRestrict {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real)
    (h : IsExpOrRecipW c a b) : IsExpOrRecipW (chainRestrict c) a b := by
  intro i
  have hdrop : MultiPoly.dropLastY
        (MultiPoly.varY (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (N + 1)))
      = MultiPoly.varY i := by
    show (if hlt : i.val < N then MultiPoly.varY ⟨i.val, hlt⟩ else MultiPoly.const 0)
        = MultiPoly.varY i
    rw [dif_pos i.isLt]
  refine ⟨?_, ?_⟩
  · rcases (h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).1 with hexp | hrec
    · obtain ⟨G, hG, hrel⟩ := hexp
      refine Or.inl ⟨MultiPoly.dropLastY G, ?_, ?_⟩
      · have hle := MultiPoly.degreeY_dropLastY_le G i
        rw [hG] at hle; exact Nat.le_zero.mp hle
      · show MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
            = MultiPoly.mul (MultiPoly.dropLastY G) (MultiPoly.varY i)
        rw [hrel]
        show MultiPoly.mul (MultiPoly.dropLastY G)
              (MultiPoly.dropLastY (MultiPoly.varY ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
            = MultiPoly.mul (MultiPoly.dropLastY G) (MultiPoly.varY i)
        rw [hdrop]
    · obtain ⟨G, v, hG, hrel, hvtf, hvcoh, hvpos⟩ := hrec
      have hvN : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) v = 0 :=
        hvtf ⟨N, Nat.lt_succ_self N⟩ (Nat.le_of_lt i.isLt)
      have heval : ∀ x : Real, MultiPoly.eval (MultiPoly.dropLastY v) x
            ((chainRestrict c).chainValues x) = MultiPoly.eval v x (c.chainValues x) := by
        intro x
        exact MultiPoly.eval_dropLastY v hvN x (c.chainValues x)
      refine Or.inr ⟨MultiPoly.dropLastY G, MultiPoly.dropLastY v, ?_, ?_, ?_, ?_, ?_⟩
      · have hle := MultiPoly.degreeY_dropLastY_le G i
        rw [hG] at hle; exact Nat.le_zero.mp hle
      · show MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
            = MultiPoly.mul (MultiPoly.dropLastY G)
                (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.varY i))
        rw [hrel]
        show MultiPoly.mul (MultiPoly.dropLastY G)
              (MultiPoly.mul
                (MultiPoly.dropLastY (MultiPoly.varY ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
                (MultiPoly.dropLastY (MultiPoly.varY ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)))
            = MultiPoly.mul (MultiPoly.dropLastY G)
                (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.varY i))
        rw [hdrop]
      · intro j hj
        have hle := MultiPoly.degreeY_dropLastY_le v j
        rw [hvtf ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ hj] at hle
        exact Nat.le_zero.mp hle
      · intro x hxa hxb
        show (chainRestrict c).evals i x
            * MultiPoly.eval (MultiPoly.dropLastY v) x ((chainRestrict c).chainValues x) = 1
        rw [heval x]
        exact hvcoh x hxa hxb
      · intro x hxa hxb
        rw [heval x]
        exact hvpos x hxa hxb
  · intro j hij
    have hle := MultiPoly.degreeY_dropLastY_le
      (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) j
    rw [(h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).2
      ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ hij] at hle
    exact Nat.le_zero.mp hle

/-- **Top extraction (witness-enriched).** The top level `⟨N,_⟩` is exp-type or
reciprocal-type *with a witness*, and every other level is top-free in the top
variable. The disjunction the combined descent step cases on. -/
theorem IsExpOrRecipW_top {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real)
    (h : IsExpOrRecipW c a b) :
    ( (∃ G : MultiPoly (N + 1), MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ G = 0
          ∧ c.relations ⟨N, Nat.lt_succ_self N⟩
              = MultiPoly.mul G (MultiPoly.varY ⟨N, Nat.lt_succ_self N⟩))
      ∨ (∃ (G v : MultiPoly (N + 1)), MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ G = 0
            ∧ c.relations ⟨N, Nat.lt_succ_self N⟩
                = MultiPoly.mul G (MultiPoly.mul (MultiPoly.varY ⟨N, Nat.lt_succ_self N⟩)
                                                 (MultiPoly.varY ⟨N, Nat.lt_succ_self N⟩))
            ∧ (∀ j : Fin (N + 1), N ≤ j.val → MultiPoly.degreeY j v = 0)
            ∧ (∀ x : Real, a < x → x < b →
                c.evals ⟨N, Nat.lt_succ_self N⟩ x * MultiPoly.eval v x (c.chainValues x) = 1)
            ∧ (∀ x : Real, a < x → x < b → 0 < MultiPoly.eval v x (c.chainValues x)) ) )
    ∧ (∀ j : Fin (N + 1), j ≠ ⟨N, Nat.lt_succ_self N⟩ →
        MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ (c.relations j) = 0) := by
  refine ⟨(h ⟨N, Nat.lt_succ_self N⟩).1, ?_⟩
  intro j hj
  have hjlt : j.val < N := by
    rcases Nat.lt_or_ge j.val N with h' | h'
    · exact h'
    · exact absurd (Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp j.isLt) h')) hj
  exact (h j).2 ⟨N, Nat.lt_succ_self N⟩ hjlt

end PfaffianExpRecipW
end MachLib
