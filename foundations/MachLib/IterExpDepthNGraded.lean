import MachLib.IterExpDepthNReduce

/-!
# The graded-multiplier cancellation, for every depth `N = M+2`

The reduce operator and its top-`leadingCoeffY` seam are already generic in `N`
(`IterExpDepthNReduce`): for any top-free multiplier `m`,

  `eval(lcY_top(cTD p − m·p)) = eval(cTD(lcY_top p)) + (degreeY_top p)·eval(Ffac M)·eval(lcY_top p)
                                − eval(m)·eval(lcY_top p)`.

The middle term is lemma (1)'s product injection. This file lands the **recursion's heart**: if the
multiplier's *top graded term* is exactly `gradedTop = (degreeY_top p)·Ffac M`, that injection
**cancels exactly**, and the reduce's top coefficient collapses to

  `eval(lcY_top(cTD p − (gradedTop + m_rest)·p)) = eval(cTD(lcY_top p)) − eval(m_rest)·eval(lcY_top p)`

— an honest reduce of `lcY_top p` by the *remainder* `m_rest`. When `m_rest` is instantiated (in a
later brick) as the depth-`(N-1)` graded multiplier for `lcY_top p` (viewed one level down via
`dropLastY`), this is precisely the depth-`N` → depth-`(N-1)` step. Here it is proved for **any**
top-free `m_rest`, so the specific nested-degree recursion plugs in without redoing the cancellation.

This is the generic-`N` analog of chain-2's `chain2Reduce_lcY1_eval` and depth-3's
`chain3Reduce_lcY2_eval`, one identity above them. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpTopIdentity
open MachLib.IterExpDepthNReduce

/-- The multiplier's top graded term: `(degreeY_top p) · Ffac M` (= `d·y₀·…·y_M`, `d = degreeY_top p`).
This is the coefficient that cancels lemma (1)'s injection. -/
noncomputable def gradedTop (M : Nat) (i : Fin (M + 2)) (p : MultiPoly (M + 2)) : MultiPoly (M + 2) :=
  MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY i p))) (Ffac M)

/-- `gradedTop` is free of the top variable (both factors are). -/
theorem gradedTop_degreeYtop_zero (M : Nat) (i : Fin (M + 2)) (hi : i.val = M + 1)
    (p : MultiPoly (M + 2)) : MultiPoly.degreeY i (gradedTop M i p) = 0 := by
  unfold gradedTop
  show MultiPoly.degreeY i (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY i p)))
       + MultiPoly.degreeY i (Ffac M) = 0
  rw [Ffac_degreeYtop_zero' M i hi]
  rfl

/-- The ring identity behind the cancellation, on fresh universally-quantified atoms (so it goes
through `mach_mpoly`'s parser — `generalize`-introduced locals do not). `d·(F·L)` cancels `L·(F·d)`. -/
private theorem graded_cancel_ring (A F L R d : Real) :
    A + d * (F * L) - (d * F + R) * L = A - R * L := by
  mach_mpoly [A, F, L, R, d]

/-- **The graded-multiplier cancellation, `∀N`.** With the top graded term
`gradedTop = (degreeY_top p)·Ffac M`, lemma (1)'s injection cancels exactly and the reduce's top
coefficient becomes an honest reduce of `lcY_top p` by the remainder `m_rest`:
`eval(lcY_top(cTD p − (gradedTop + m_rest)·p)) = eval(cTD(lcY_top p)) − eval(m_rest)·eval(lcY_top p)`,
for any top-free `m_rest`. -/
theorem chainNReduce_graded_cancels (M : Nat) (i : Fin (M + 2)) (hi : i.val = M + 1)
    (m_rest p : MultiPoly (M + 2)) (hmr : MultiPoly.degreeY i m_rest = 0)
    (x : Real) (env : Fin (M + 2) → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY i
        (chainNReduce M (MultiPoly.add (gradedTop M i p) m_rest) p)) x env
    = MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2)) (MultiPoly.leadingCoeffY i p)) x env
      - MultiPoly.eval m_rest x env * MultiPoly.eval (MultiPoly.leadingCoeffY i p) x env := by
  have hm : MultiPoly.degreeY i (MultiPoly.add (gradedTop M i p) m_rest) = 0 := by
    show Nat.max (MultiPoly.degreeY i (gradedTop M i p)) (MultiPoly.degreeY i m_rest) = 0
    rw [gradedTop_degreeYtop_zero M i hi p, hmr]
    decide
  rw [chainNReduce_lcY_top_eval M i hi (MultiPoly.add (gradedTop M i p) m_rest) p hm x env]
  -- expand eval of the graded multiplier: eval(gradedTop + m_rest) = degreeY_top p·eval(Ffac M) + eval m_rest
  unfold gradedTop
  simp only [MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_const]
  generalize MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2)) (MultiPoly.leadingCoeffY i p)) x env = A
  generalize MultiPoly.eval (Ffac M) x env = F
  generalize MultiPoly.eval (MultiPoly.leadingCoeffY i p) x env = L
  generalize MultiPoly.eval m_rest x env = R
  generalize MachLib.Real.natCast (MultiPoly.degreeY i p) = d
  exact graded_cancel_ring A F L R d

/-- **The graded reduce preserves the top y-degree, `∀N`.** The measure's first-component tie for the
reduce arm: `gradedTop + m_rest` is top-free, so `chainNReduce_fst_preserved` applies. -/
theorem chainNReduce_graded_fst_preserved (M : Nat) (i : Fin (M + 2)) (hi : i.val = M + 1)
    (m_rest p : MultiPoly (M + 2)) (hmr : MultiPoly.degreeY i m_rest = 0) :
    MultiPoly.degreeY i (chainNReduce M (MultiPoly.add (gradedTop M i p) m_rest) p)
      = MultiPoly.degreeY i p := by
  have hm : MultiPoly.degreeY i (MultiPoly.add (gradedTop M i p) m_rest) = 0 := by
    show Nat.max (MultiPoly.degreeY i (gradedTop M i p)) (MultiPoly.degreeY i m_rest) = 0
    rw [gradedTop_degreeYtop_zero M i hi p, hmr]
    decide
  exact MachLib.IterExpDepthNReduce.chainNReduce_fst_preserved M i hi
    (MultiPoly.add (gradedTop M i p) m_rest) p hm

end MachLib.IterExpDepthN
