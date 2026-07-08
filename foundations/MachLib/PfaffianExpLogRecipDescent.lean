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

/-- **Positivity except at log-type variables.** Every chain value is positive on
`(a,b)` EXCEPT possibly the log-type ones, whose own value (`log w`) may be signed.
A variable is log-type exactly when its relation omits its own variable
(`degreeY i (relations i) = 0`); exp-type (`G·yᵢ`) and reciprocal-type (`G·yᵢ²`)
variables have `degreeY i (relations i) ∈ {1,2} ≠ 0`, so this predicate forces
THEIR positivity while exempting logs.

This is the weakest positivity the descent's leaf machinery actually consumes:
the exp arm needs only its own (exp, hence positive) top variable; the recip arm
draws positivity from the class witness (`hvpos`), not from here; the log arm
needs none. Unlike blanket all-positivity, it is satisfiable by an EML encoder
chain whose `log⟦t2⟧` nodes are genuinely signed — which is exactly why the
statement is phrased this way. -/
def PosExceptLog {N : Nat} (c : PfaffianChain N) (a b : Real) : Prop :=
  ∀ z, a < z → z < b → ∀ i : Fin N,
    MultiPoly.degreeY i (c.relations i) = 0 ∨ 0 < c.evals i z

/-- `PosExceptLog` descends to the restricted chain: values are a prefix, and
`degreeY i` of a top-free relation is preserved by `dropLastY`
(`degreeY_dropLastY_le` + `Nat.le_zero`). The typed analogue of
`positivity_chainRestrict`. -/
theorem positivity_chainRestrict_typed {N : Nat} (c : PfaffianChain (N + 1))
    (a b : Real) (hpos : PosExceptLog c a b) : PosExceptLog (chainRestrict c) a b := by
  intro z hza hzb i
  rcases hpos z hza hzb ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ with hlog | hp
  · left
    show MultiPoly.degreeY i
        (MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) = 0
    have hle := MultiPoly.degreeY_dropLastY_le
      (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) i
    omega
  · right
    show 0 < c.evals ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ z
    exact hp

/-- **Three-way combined descent.** For a 3-type witness-enriched chain, a
non-vanishing polynomial has finitely many zeros — conditional on `base` +
`exp_step` + `log_step`. The reciprocal arm is proven (reusing
`recip_top_combined`); exp and log arms are the classical Khovanskii content.

Positivity is required only as `PosExceptLog` (all chain values positive except
possibly the signed log-type ones) — the weakest form the leaf machinery uses,
and the one an EML encoder chain can actually satisfy. -/
theorem combined_descent_3 (a b : Real)
    (base : ∀ (c : PfaffianChain 0) (p : MultiPoly 0),
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
        BoundedZeros (pfaffianChainFn c p) a b)
    (exp_step : ∀ (k : Nat) (c : PfaffianChain (k + 1)),
        IsExpLogRecipW c a b → c.IsCoherentOn a b →
        PosExceptLog c a b →
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
        PosExceptLog c a b →
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
      PosExceptLog c a b →
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
        (chainRestrict_isCoherentOn_ELR c a b hW hcoh) (positivity_chainRestrict_typed c a b hpos) q hq
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
        PosExceptLog c a b →
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
        PosExceptLog c a b →
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
      PosExceptLog c a b →
      ∀ (p : MultiPoly N),
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
        BoundedZeros (pfaffianChainFn c p) a b :=
  combined_descent_3 a b (MachLib.PfaffianExpRecipW.base_case a b hab) exp_step log_step

end PfaffianExpLogRecip
end MachLib
