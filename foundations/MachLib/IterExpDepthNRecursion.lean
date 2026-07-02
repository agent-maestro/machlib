import MachLib.IterExpDepthNBridge

/-!
# The recursion closes, for every depth `N = M+3 → M+2` (abstract-index)

Payoff of bricks 1–4: the depth-`(M+3)` graded reduce's dropped top coefficient, evaluated one chain
down, **is a depth-`(M+2)` reduce** of `dropLastY (lcY_top p)`, with multiplier simply
`dropLastY (m_rest)`. No separate closed-form nested multiplier is needed — the recursion is carried by
`dropLastY`.

The proof is assembled purely term-mode from bricks 3 (`chainNReduce_graded_cancels`) + 4 (the
`dropLastY` bridge) + `degreeYtop_cTD_eq'`. **Critically, the top index is an abstract variable `i` with
`hi : i.val = M+2`, not the literal `⟨M+2, by omega⟩`** — the literal is what makes `whnf` diverge on the
stuck `leadingCoeffY`/`eval`/`chainNReduce` recursors at a symbolic index (the lemma-(1) wall). Two tiny
wrappers re-state the bridge lemmas' `degreeY` hypotheses at the abstract `i`, confining the one literal
`rw` to a one-equation goal. Generic-`N` analog of depth-3's `chain3Reduce_dropLastY_lcY2_eval_eq`. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpDepthNReduce

-- Keep the stuck recursors atomic (belt-and-braces with the abstract index).
attribute [local irreducible] MultiPoly.leadingCoeffY MultiPoly.degreeY MultiPoly.dropLastY
  chainTotalDeriv MachLib.IterExpTopIdentity.Ffac gradedTop

/-! ## Abstract-index wrappers for the bridge lemmas (confine the literal to a one-equation `rw`). -/

private theorem dropLastY_eval_IterExp' (M : Nat) (i : Fin (M + 2)) (hi : i.val = M + 1)
    (q : MultiPoly (M + 2)) (hq : MultiPoly.degreeY i q = 0) (z : Real) :
    MultiPoly.eval q z ((IterExpChain (M + 2)).chainValues z)
      = MultiPoly.eval (MultiPoly.dropLastY q) z ((IterExpChain (M + 1)).chainValues z) := by
  have h : i = (⟨M + 1, by omega⟩ : Fin (M + 2)) := Fin.ext hi
  rw [h] at hq
  exact dropLastY_eval_IterExp M q hq z

private theorem dropLastY_cTD_commute' (M : Nat) (i : Fin (M + 2)) (hi : i.val = M + 1)
    (q : MultiPoly (M + 2)) (hq : MultiPoly.degreeY i q = 0) :
    MultiPoly.dropLastY (chainTotalDeriv (IterExpChain (M + 2)) q)
      = chainTotalDeriv (IterExpChain (M + 1)) (MultiPoly.dropLastY q) := by
  have h : i = (⟨M + 1, by omega⟩ : Fin (M + 2)) := Fin.ext hi
  rw [h] at hq
  exact dropLastY_cTD_commute M q hq

/-- **The depth-`(M+3)` → depth-`(M+2)` recursion, at eval level, `∀M`** (abstract top index `i`). -/
theorem chainNReduce_dropLastY_recursion (M : Nat) (i : Fin (M + 3)) (hi : i.val = M + 2)
    (m_rest p : MultiPoly (M + 3)) (hmr : MultiPoly.degreeY i m_rest = 0) (x : Real) :
    MultiPoly.eval (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i
        (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p)))
      x ((IterExpChain (M + 2)).chainValues x)
    = MultiPoly.eval (chainNReduce M (MultiPoly.dropLastY m_rest)
        (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p)))
      x ((IterExpChain (M + 2)).chainValues x) := by
  have hq0 : MultiPoly.degreeY i (MultiPoly.leadingCoeffY i p) = 0 :=
    MultiPoly.degreeY_leadingCoeffY i p
  have hcTDq0 : MultiPoly.degreeY i
                 (chainTotalDeriv (IterExpChain (M + 3)) (MultiPoly.leadingCoeffY i p)) = 0 := by
    rw [degreeYtop_cTD_eq' (M + 1) i hi (MultiPoly.leadingCoeffY i p)]; exact hq0
  have hX0 : MultiPoly.degreeY i (MultiPoly.leadingCoeffY i
                 (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p)) = 0 :=
    MultiPoly.degreeY_leadingCoeffY i _
  have e1 := dropLastY_eval_IterExp' (M + 1) i hi
      (MultiPoly.leadingCoeffY i (chainNReduce (M + 1)
        (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p)) hX0 x
  have e2 := chainNReduce_graded_cancels (M + 1) i hi m_rest p hmr x
      ((IterExpChain (M + 3)).chainValues x)
  have e3 : MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 3)) (MultiPoly.leadingCoeffY i p)) x
        ((IterExpChain (M + 3)).chainValues x)
      = MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2))
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p))) x ((IterExpChain (M + 2)).chainValues x) :=
    (dropLastY_eval_IterExp' (M + 1) i hi
        (chainTotalDeriv (IterExpChain (M + 3)) (MultiPoly.leadingCoeffY i p)) hcTDq0 x).trans
      (congrArg (fun t => MultiPoly.eval t x ((IterExpChain (M + 2)).chainValues x))
        (dropLastY_cTD_commute' (M + 1) i hi (MultiPoly.leadingCoeffY i p) hq0))
  have e4 := dropLastY_eval_IterExp' (M + 1) i hi m_rest hmr x
  have e5 := dropLastY_eval_IterExp' (M + 1) i hi (MultiPoly.leadingCoeffY i p) hq0 x
  have ecancel :
      MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 3)) (MultiPoly.leadingCoeffY i p)) x
          ((IterExpChain (M + 3)).chainValues x)
        - MultiPoly.eval m_rest x ((IterExpChain (M + 3)).chainValues x)
          * MultiPoly.eval (MultiPoly.leadingCoeffY i p) x ((IterExpChain (M + 3)).chainValues x)
      = MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2))
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p))) x ((IterExpChain (M + 2)).chainValues x)
        - MultiPoly.eval (MultiPoly.dropLastY m_rest) x ((IterExpChain (M + 2)).chainValues x)
          * MultiPoly.eval (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p)) x
              ((IterExpChain (M + 2)).chainValues x) := by
    rw [e3, e4, e5]
  have e6 :
      MultiPoly.eval (chainNReduce M (MultiPoly.dropLastY m_rest)
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p))) x ((IterExpChain (M + 2)).chainValues x)
      = MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2))
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p))) x ((IterExpChain (M + 2)).chainValues x)
        - MultiPoly.eval (MultiPoly.dropLastY m_rest) x ((IterExpChain (M + 2)).chainValues x)
          * MultiPoly.eval (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p)) x
              ((IterExpChain (M + 2)).chainValues x) := by
    unfold chainNReduce
    rw [MultiPoly.eval_sub, MultiPoly.eval_mul]
  exact e1.symm.trans (e2.trans (ecancel.trans e6.symm))

end MachLib.IterExpDepthN
