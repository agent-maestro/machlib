import MachLib.MultiPoly
import MachLib.PfaffianChain
import MachLib.PfaffianGeneralReduce

/-!
# Three-type witness-enriched chain class — Brick A-4a' (log-type added)

The two-type `IsExpOrRecipW` (exp + reciprocal) cannot encode an EML chain, which
needs a **log-type** level (`log(v)' = v'·(1/v)` is top-free in log's own
variable — see the LOG-TYPE GAP note in the exploration FINDINGS). This file adds
that third type: `IsExpLogRecipW` has exp-type (`G·y`), log-type (top-free
relation, `degreeY_i = 0`), and reciprocal-type (`G·y²` with witness) levels.

Mechanical extension of the two-type class: same closure / top-extraction /
coherence, with a log arm added to the dispatch. The reciprocal machinery
(`recip_top_step`, `clearTop`, `base_case`, the preservation lemmas) is
chain-parametric and reused unchanged by the eventual three-way descent. What
remains for the descent is `exp_step` (as before) and `log_step` (Rolle on the
top coefficient's complexity — no integrating factor, since a log level's own
variable is absent from its relation).
-/

namespace MachLib
namespace PfaffianExpLogRecip
open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianGeneralReduce

/-- **Three-type witness-enriched chain.** Each level is exp-type (`G·y`), or
**log-type** (top-free relation, `degreeY_i = 0` — `y = log v`), or
reciprocal-type (`G·y²` with a witness). This is the class EML actually needs
(`eml t1 t2 = exp t1 − log t2`). Superset of the two-type `IsExpOrRecipW`. -/
def IsExpLogRecipW {N : Nat} (c : PfaffianChain N) (a b : Real) : Prop :=
  ∀ i : Fin N,
    ( (∃ G : MultiPoly N, MultiPoly.degreeY i G = 0
          ∧ c.relations i = MultiPoly.mul G (MultiPoly.varY i))
      ∨ (MultiPoly.degreeY i (c.relations i) = 0)
      ∨ (∃ (G v : MultiPoly N),
            MultiPoly.degreeY i G = 0
            ∧ c.relations i
                = MultiPoly.mul G (MultiPoly.mul (MultiPoly.varY i) (MultiPoly.varY i))
            ∧ (∀ j : Fin N, i.val ≤ j.val → MultiPoly.degreeY j v = 0)
            ∧ (∀ x : Real, a < x → x < b →
                c.evals i x * MultiPoly.eval v x (c.chainValues x) = 1)
            ∧ (∀ x : Real, a < x → x < b → 0 < MultiPoly.eval v x (c.chainValues x)) ) )
    ∧ (∀ j : Fin N, i.val < j.val → MultiPoly.degreeY j (c.relations i) = 0)

theorem IsExpChain_imp_ELR {N : Nat} (c : PfaffianChain N) (a b : Real)
    (h : IsExpChain c) : IsExpLogRecipW c a b := by
  intro i; obtain ⟨hrel, htri⟩ := h i; exact ⟨Or.inl hrel, htri⟩

theorem IsExpLogRecipW_chainRestrict {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real)
    (h : IsExpLogRecipW c a b) : IsExpLogRecipW (chainRestrict c) a b := by
  intro i
  have hdrop : MultiPoly.dropLastY
        (MultiPoly.varY (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (N + 1)))
      = MultiPoly.varY i := by
    show (if hlt : i.val < N then MultiPoly.varY ⟨i.val, hlt⟩ else MultiPoly.const 0)
        = MultiPoly.varY i
    rw [dif_pos i.isLt]
  refine ⟨?_, ?_⟩
  · rcases (h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).1 with hexp | hlog | hrec
    · obtain ⟨G, hG, hrel⟩ := hexp
      refine Or.inl ⟨MultiPoly.dropLastY G, ?_, ?_⟩
      · have hle := MultiPoly.degreeY_dropLastY_le G i; rw [hG] at hle; exact Nat.le_zero.mp hle
      · show MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
            = MultiPoly.mul (MultiPoly.dropLastY G) (MultiPoly.varY i)
        rw [hrel]
        show MultiPoly.mul (MultiPoly.dropLastY G)
              (MultiPoly.dropLastY (MultiPoly.varY ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))
            = MultiPoly.mul (MultiPoly.dropLastY G) (MultiPoly.varY i)
        rw [hdrop]
    · -- log-type: restricted relation stays top-free
      refine Or.inr (Or.inl ?_)
      show MultiPoly.degreeY i
          (MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) = 0
      have hle := MultiPoly.degreeY_dropLastY_le
        (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) i
      rw [hlog] at hle; exact Nat.le_zero.mp hle
    · obtain ⟨G, v, hG, hrel, hvtf, hvcoh, hvpos⟩ := hrec
      have hvN : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) v = 0 :=
        hvtf ⟨N, Nat.lt_succ_self N⟩ (Nat.le_of_lt i.isLt)
      have heval : ∀ x : Real, MultiPoly.eval (MultiPoly.dropLastY v) x
            ((chainRestrict c).chainValues x) = MultiPoly.eval v x (c.chainValues x) :=
        fun x => MultiPoly.eval_dropLastY v hvN x (c.chainValues x)
      refine Or.inr (Or.inr ⟨MultiPoly.dropLastY G, MultiPoly.dropLastY v, ?_, ?_, ?_, ?_, ?_⟩)
      · have hle := MultiPoly.degreeY_dropLastY_le G i; rw [hG] at hle; exact Nat.le_zero.mp hle
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
        rw [hvtf ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ hj] at hle; exact Nat.le_zero.mp hle
      · intro x hxa hxb
        show (chainRestrict c).evals i x
            * MultiPoly.eval (MultiPoly.dropLastY v) x ((chainRestrict c).chainValues x) = 1
        rw [heval x]; exact hvcoh x hxa hxb
      · intro x hxa hxb; rw [heval x]; exact hvpos x hxa hxb
  · intro j hij
    have hle := MultiPoly.degreeY_dropLastY_le
      (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) j
    rw [(h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).2 ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ hij] at hle
    exact Nat.le_zero.mp hle


theorem IsExpLogRecipW_top {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real)
    (h : IsExpLogRecipW c a b) :
    ( (∃ G : MultiPoly (N + 1), MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ G = 0
          ∧ c.relations ⟨N, Nat.lt_succ_self N⟩
              = MultiPoly.mul G (MultiPoly.varY ⟨N, Nat.lt_succ_self N⟩))
      ∨ (MultiPoly.degreeY ⟨N, Nat.lt_succ_self N⟩ (c.relations ⟨N, Nat.lt_succ_self N⟩) = 0)
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

theorem chainRestrict_isCoherentOn_ELR {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real)
    (h : IsExpLogRecipW c a b) (hcoh : c.IsCoherentOn a b) :
    (chainRestrict c).IsCoherentOn a b := by
  intro x hax hxb i
  show HasDerivAt (c.evals ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    (MultiPoly.eval (MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) x
      ((chainRestrict c).chainValues x)) x
  have hc := hcoh x hax hxb ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
  have htop : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
      (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) = 0 :=
    (h ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).2 (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) i.isLt
  have heval : MultiPoly.eval (MultiPoly.dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) x
        ((chainRestrict c).chainValues x)
      = MultiPoly.eval (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) x (c.chainValues x) := by
    have hrestrict : (chainRestrict c).chainValues x
        = (fun j => (c.chainValues x) ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) := by
      funext j; exact chainRestrict_chainValues c x j
    rw [hrestrict, MultiPoly.eval_dropLastY (c.relations ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) htop x
      (c.chainValues x)]
  rw [heval]; exact hc

end PfaffianExpLogRecip
end MachLib
