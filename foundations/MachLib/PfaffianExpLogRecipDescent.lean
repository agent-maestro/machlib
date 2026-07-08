import MachLib.PfaffianExpRecipDescent
import MachLib.PfaffianExpLogRecipClass
import MachLib.PfaffianGeneralBoundPos

/-!
# Three-way combined descent — Brick A-4b' (log arm added)

The depth descent for the 3-type `IsExpLogRecipW` class. Dispatches per top level
via `IsExpLogRecipW_top`: reciprocal → `recip_top_combined` (PROVEN, reused
verbatim from the 2-type development — it is chain-parametric); exp → `exp_step`;
log → `log_step`. Reduces the general EML barrier to `base` + `exp_step` +
`log_step`, with the entire reciprocal side + dispatch + recursion + base proven.

`base` is discharged by the depth-0 polynomial bound (`base_case`), leaving the
barrier on `exp_step` + `log_step` — the classical exp/log Khovanskii content.
-/

namespace MachLib
namespace PfaffianExpLogRecip
open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianGeneralReduce
open MachLib.PfaffianExpRecip
open MachLib.PfaffianExpRecipW

/-- **Three-way combined descent.** For a 3-type witness-enriched chain, a
non-vanishing polynomial has finitely many zeros — conditional on `base` +
`exp_step` + `log_step`. The reciprocal arm is proven (reusing
`recip_top_combined`); exp and log arms are the classical Khovanskii content. -/
theorem combined_descent_3 (a b : Real)
    (base : ∀ (c : PfaffianChain 0) (p : MultiPoly 0),
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
        BoundedZeros (pfaffianChainFn c p) a b)
    (exp_step : ∀ (k : Nat) (c : PfaffianChain (k + 1)),
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
          BoundedZeros (pfaffianChainFn c p) a b)
    (log_step : ∀ (k : Nat) (c : PfaffianChain (k + 1)),
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
          BoundedZeros (pfaffianChainFn c p) a b) :
    ∀ (N : Nat) (c : PfaffianChain N), IsExpLogRecipW c a b → c.IsCoherentOn a b →
      (∀ z, a < z → z < b → ∀ i : Fin N, 0 < c.evals i z) →
      ∀ (p : MultiPoly N),
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
        BoundedZeros (pfaffianChainFn c p) a b := by
  intro N
  induction N with
  | zero => intro c _ _ _ p hne; exact base c p hne
  | succ k ih =>
    intro c hW hcoh hpos p hne
    have hIHrestrict : ∀ q : MultiPoly k,
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z ≠ 0) →
        BoundedZeros (pfaffianChainFn (chainRestrict c) q) a b :=
      fun q hq => ih (chainRestrict c) (IsExpLogRecipW_chainRestrict c a b hW)
        (chainRestrict_isCoherentOn_ELR c a b hW hcoh) (positivity_chainRestrict c a b hpos) q hq
    rcases (IsExpLogRecipW_top c a b hW).1 with hexp | hlog | hrec
    · obtain ⟨G, hG, hrel⟩ := hexp
      exact exp_step k c hW hcoh hpos ⟨G, hG, hrel⟩ (IsExpLogRecipW_top c a b hW).2 hIHrestrict p hne
    · exact log_step k c hW hcoh hpos hlog (IsExpLogRecipW_top c a b hW).2 hIHrestrict p hne
    · obtain ⟨G, v, hG, hrel, hvtf, hvcoh, hvpos⟩ := hrec
      have hvN : MultiPoly.degreeY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) v = 0 :=
        hvtf ⟨k, Nat.lt_succ_self k⟩ (Nat.le_refl k)
      have heval : ∀ x : Real, MultiPoly.eval (MultiPoly.dropLastY v) x
            ((chainRestrict c).chainValues x) = MultiPoly.eval v x (c.chainValues x) :=
        fun x => MultiPoly.eval_dropLastY v hvN x (c.chainValues x)
      have hvpos_r : ∀ x : Real, a < x → x < b →
          0 < MultiPoly.eval (MultiPoly.dropLastY v) x ((chainRestrict c).chainValues x) :=
        fun x hxa hxb => by rw [heval x]; exact hvpos x hxa hxb
      have hwitness : ∀ x : Real, a < x → x < b →
          c.chainValues x ⟨k, Nat.lt_succ_self k⟩
            = 1 / MultiPoly.eval (MultiPoly.dropLastY v) x ((chainRestrict c).chainValues x) := by
        intro x hxa hxb
        have hw := ne_of_gt (hvpos_r x hxa hxb)
        have hcoh1 : c.evals ⟨k, Nat.lt_succ_self k⟩ x
            * MultiPoly.eval (MultiPoly.dropLastY v) x ((chainRestrict c).chainValues x) = 1 := by
          rw [heval x]; exact hvcoh x hxa hxb
        show c.evals ⟨k, Nat.lt_succ_self k⟩ x
            = 1 / MultiPoly.eval (MultiPoly.dropLastY v) x ((chainRestrict c).chainValues x)
        rw [← hcoh1, mul_comm, mul_div_cancel_left' hw]
      have hnv := clearTop_nonvanishing c (MultiPoly.dropLastY v) a b hwitness hvpos_r p hne
      obtain ⟨M, hM⟩ := hIHrestrict (clearTop (MultiPoly.dropLastY v) p) hnv
      exact ⟨M, recip_top_combined c a b v hvtf hvcoh hvpos p M hM⟩

/-- **Three-way descent, `base` pre-discharged.** With `a < b`, the depth-0 base
is `base_case`, so the general EML barrier rests on TWO classical hypotheses —
`exp_step` and `log_step` — with the entire reciprocal side proven. -/
theorem combined_descent_3_of_steps (a b : Real) (hab : a < b)
    (exp_step : ∀ (k : Nat) (c : PfaffianChain (k + 1)),
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
          BoundedZeros (pfaffianChainFn c p) a b)
    (log_step : ∀ (k : Nat) (c : PfaffianChain (k + 1)),
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
          BoundedZeros (pfaffianChainFn c p) a b) :
    ∀ (N : Nat) (c : PfaffianChain N), IsExpLogRecipW c a b → c.IsCoherentOn a b →
      (∀ z, a < z → z < b → ∀ i : Fin N, 0 < c.evals i z) →
      ∀ (p : MultiPoly N),
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
        BoundedZeros (pfaffianChainFn c p) a b :=
  combined_descent_3 a b (MachLib.PfaffianExpRecipW.base_case a b hab) exp_step log_step

end PfaffianExpLogRecip
end MachLib
