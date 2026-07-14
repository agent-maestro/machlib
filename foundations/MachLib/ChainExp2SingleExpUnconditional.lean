import MachLib.ChainExp2PathC

/-!
# MachLib.ChainExp2SingleExpUnconditional — the unconditional SingleExp bound

`ChainExp2PathC.singleExp_khovanskii_bound` proves the SingleExp `PfaffianFn`
zero-count bound *through the generic reduction pipeline*, but it threads a
`sdr_other : PfaffianFn.StepwiseDecreaseReducer` (a total step-wise reducer for
*arbitrary* chains — itself the open general problem) as a hypothesis. Per that
theorem's own comment the fallback is **never invoked** when the start is a
`⟨1, SingleExpChain, p⟩`: `scaledReduction` and `dropLast` preserve the chain,
and the recursion drops chain length 1 → 0 in one step. So the hypothesis is
vacuous, yet nobody can supply it (constructing a total SDR is the open problem).

This module removes it. `se_reduces` builds the Khovanskii witness by a bespoke
well-founded recursion on the shipped `lexMeasure`, staying entirely in the
`⟨1, SingleExpChain, ·⟩` shape (so every intermediate polynomial is a concrete
`MultiPoly 1` and no `sdr_other` is needed). Feeding that witness to
`PfaffianFn.khovanskii_bound_full` yields an **unconditional** SingleExp bound.

`#print axioms singleExp_khovanskii_bound_unconditional` must show only the
`MachLib.Real` foundation — no `zero_count_bound_classical`.

Reuses (all `sorry`-free, in `ChainExp2PathC`): `singleExp_reduceStep_closed`
(the reduce arm, `polyTrueDegreeStrict > 0`), `singleExp_canonicalTrim_step` (the
canonical-trim arm, `= 0`), and the `¬h_strict → getLast-canonically-zero` bridge
inlined here (mirrors `singleExp_dispatch_step`).
-/

namespace MachLib
namespace ChainExp2PathC

open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.PolynomialCanonical
open MachLib.MultiPolyReconstruct

/-- **Bespoke SingleExp witness construction.** For any `p : MultiPoly 1`, the
`⟨1, SingleExpChain, p⟩` PfaffianFn reduces (via reduce/trim steps, then a single
`dropLast`) to a chain-length-0 PfaffianFn. Well-founded recursion on the shipped
`lexMeasure`: at `lex.1 = 0` drop; otherwise dispatch on `polyTrueDegreeStrict`
(reduce vs. canonical-trim) and recurse on the strictly smaller measure. -/
theorem se_reduces (p0 : MultiPoly 1) :
    ∃ (g : PfaffianFn) (k : Nat),
      g.n = 0 ∧
      PfaffianFn.IsKhovanskiiReducible (⟨1, SingleExpChain, p0⟩ : PfaffianFn) g k := by
  -- Package the recursion target as a statement parameterised by the measure pair.
  suffices H : ∀ (m1 m2 : Nat) (p : MultiPoly 1),
      lexMeasure (⟨1, SingleExpChain, p⟩ : PfaffianFn) rfl = (m1, m2) →
      ∃ (g : PfaffianFn) (k : Nat),
        g.n = 0 ∧
        PfaffianFn.IsKhovanskiiReducible (⟨1, SingleExpChain, p⟩ : PfaffianFn) g k from
    H _ _ p0 rfl
  intro m1
  induction m1 using Nat.strongRecOn with
  | _ m1 ih1 =>
    intro m2
    induction m2 using Nat.strongRecOn with
    | _ m2 ih2 =>
      intro p h_lex_eq
      -- The first lex component is `m1` (degreeY 0 of p).
      have h_fst : (lexMeasure (⟨1, SingleExpChain, p⟩ : PfaffianFn) rfl).1 = m1 := by
        rw [h_lex_eq]
      by_cases h_m1_zero : m1 = 0
      · -- Drop: lex first component is 0, so `dropLast` takes chain length 1 → 0.
        have h_lex_zero : (lexMeasure (⟨1, SingleExpChain, p⟩ : PfaffianFn) rfl).1 = 0 := by
          rw [h_fst]; exact h_m1_zero
        refine ⟨(⟨1, SingleExpChain, p⟩ : PfaffianFn).dropLast rfl, 0, ?_, ?_⟩
        · exact PfaffianFn.dropLast_n (⟨1, SingleExpChain, p⟩ : PfaffianFn) rfl
        · exact PfaffianFn.IsKhovanskiiReducible.drop_one
            (⟨1, SingleExpChain, p⟩ : PfaffianFn) rfl h_lex_zero
      · -- Reduce or trim: lex first component positive.
        have h_pos : (lexMeasure (⟨1, SingleExpChain, p⟩ : PfaffianFn) rfl).1 > 0 := by
          rw [h_fst]; exact Nat.pos_of_ne_zero h_m1_zero
        by_cases h_strict :
            polyTrueDegreeStrict
              (polyCoeffs (multiPolyToPolyForLex
                (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))) > 0
        · -- Reduce arm.
          let step := PfaffianFn.singleExp_reduceStep_closed p h_pos h_strict
          let nextP : MultiPoly 1 :=
            MultiPoly.sub
              (chainTotalDeriv SingleExpChain p)
              (MultiPoly.mul
                (MultiPoly.const
                  (Real.natCast (lexMeasure (⟨1, SingleExpChain, p⟩ : PfaffianFn) rfl).1))
                p)
          have hlt : lexLT (lexMeasure (⟨1, SingleExpChain, nextP⟩ : PfaffianFn) rfl)
                          (m1, m2) := by
            have hd := step.lex_decrease
            rw [h_lex_eq] at hd
            exact hd
          have hrec : ∃ (g : PfaffianFn) (k : Nat), g.n = 0 ∧
              PfaffianFn.IsKhovanskiiReducible
                (⟨1, SingleExpChain, nextP⟩ : PfaffianFn) g k := by
            rcases hpair : lexMeasure (⟨1, SingleExpChain, nextP⟩ : PfaffianFn) rfl
              with ⟨a, c⟩
            rw [hpair] at hlt
            simp only [lexLT] at hlt
            rcases hlt with h1 | ⟨h1eq, h2lt⟩
            · exact ih1 a h1 c nextP hpair
            · rw [h1eq] at hpair
              exact ih2 c h2lt nextP hpair
          obtain ⟨g, k, hg0, wit⟩ := hrec
          exact ⟨g, step.counter + k, hg0,
            PfaffianFn.IsKhovanskiiReducible.trans step.witness wit⟩
        · -- Canonical-trim arm: polyTrueDegreeStrict = 0.
          have h_zero : polyTrueDegreeStrict
              (polyCoeffs (multiPolyToPolyForLex
                (MultiPoly.leadingCoeffY ⟨0, by omega⟩ p))) = 0 := by
            omega
          have h_canon_zero : CanonicallyZero (polyCoeffs (multiPolyToPolyForLex
              (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 1) p))) := by
            apply Classical.byContradiction
            intro h_not
            rw [polyTrueDegreeStrict_of_not_canonicallyZero _ h_not] at h_zero
            omega
          have h_lcY_zero : ∀ (x : Real) (env : Fin 1 → Real),
              MultiPoly.eval (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 1) p) x env = 0 := by
            intro x env
            have h_canon_x := h_canon_zero x
            rw [polyCoeffs_eval] at h_canon_x
            have h_y_free : ∀ j : Fin 1,
                MultiPoly.degreeY j (MultiPoly.leadingCoeffY (⟨0, by omega⟩ : Fin 1) p) = 0 := by
              intro j
              have hj_eq : j = (⟨0, by omega⟩ : Fin 1) := Subsingleton.elim _ _
              rw [hj_eq]
              exact MultiPoly.degreeY_leadingCoeffY _ p
            rw [multiPolyToPolyForLex_eval_of_y_free _ h_y_free x env] at h_canon_x
            exact h_canon_x
          have h_getLast_zero :
              ∀ (h_ne : MachLib.MultiPolyMod.MultiPoly.yCoeffsAt
                          (⟨0, by omega⟩ : Fin 1) p ≠ [])
                (x : Real) (env : Fin 1 → Real),
                MultiPoly.eval
                  ((MachLib.MultiPolyMod.MultiPoly.yCoeffsAt
                      (⟨0, by omega⟩ : Fin 1) p).getLast h_ne) x env = 0 := by
            intro h_ne x env
            rw [← eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast p h_ne x env]
            exact h_lcY_zero x env
          have h_deg_pos : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 1) p > 0 := h_pos
          let step := PfaffianFn.singleExp_canonicalTrim_step p h_deg_pos h_getLast_zero
          let nextP : MultiPoly 1 := dropLeadingY p
          have hlt : lexLT (lexMeasure (⟨1, SingleExpChain, nextP⟩ : PfaffianFn) rfl)
                          (m1, m2) := by
            have hd := step.lex_decrease
            rw [h_lex_eq] at hd
            exact hd
          have hrec : ∃ (g : PfaffianFn) (k : Nat), g.n = 0 ∧
              PfaffianFn.IsKhovanskiiReducible
                (⟨1, SingleExpChain, nextP⟩ : PfaffianFn) g k := by
            rcases hpair : lexMeasure (⟨1, SingleExpChain, nextP⟩ : PfaffianFn) rfl
              with ⟨a, c⟩
            rw [hpair] at hlt
            simp only [lexLT] at hlt
            rcases hlt with h1 | ⟨h1eq, h2lt⟩
            · exact ih1 a h1 c nextP hpair
            · rw [h1eq] at hpair
              exact ih2 c h2lt nextP hpair
          obtain ⟨g, k, hg0, wit⟩ := hrec
          exact ⟨g, step.counter + k, hg0,
            PfaffianFn.IsKhovanskiiReducible.trans step.witness wit⟩

/-- **End-to-end unconditional bound for any SingleExp PfaffianFn.** No
`sdr_other` hypothesis: the witness is built directly by `se_reduces`. The only
remaining hypothesis is the genuine "terminal non-triviality" side condition of
`khovanskii_bound_full` (the chain-length-0 endpoint is not identically zero). -/
theorem singleExp_khovanskii_bound_unconditional
    (p : MultiPoly 1)
    (a b : Real) (hab : a < b)
    (terminal_nonzero :
       ∀ g k, g.n = 0 →
         PfaffianFn.IsKhovanskiiReducible (⟨1, SingleExpChain, p⟩ : PfaffianFn) g k →
         ∃ x : Real, g.eval x ≠ 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (⟨1, SingleExpChain, p⟩ : PfaffianFn).eval z = 0) →
      zeros.length ≤ N := by
  obtain ⟨g, k, hg0, hwit⟩ := se_reduces p
  refine ⟨MultiPoly.degreeX g.poly + k, ?_⟩
  intro zeros hnodup hzeros
  exact PfaffianFn.khovanskii_bound_full
    (⟨1, SingleExpChain, p⟩ : PfaffianFn) g k hwit
    SingleExpChain_isTriangular hg0 a b hab
    (SingleExpChain_isCoherentOn a b)
    (terminal_nonzero g k hg0 hwit) zeros hnodup hzeros

end ChainExp2PathC
end MachLib
