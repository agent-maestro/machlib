import MachLib.IterExpDepthNTopIdentity

/-!
# The reduce operator, for every depth `N = M+2`

Building on `IterExpDepthN.leadingCoeffYtop_cTD_eval_IterExpN` (Frontier-1 lemma (1), proven `∀N`),
this file establishes the depth-N **reduce** operator and its two structural facts — the generic-`N`
analogs of chain-2's `chain2Reduce_*` and depth-3's `chain3Reduce_*`.

`chainNReduce M m p = cTD p − m · p`. The correct Khovanskii reduce uses a *graded* multiplier
`m = Σ_{k} dₖ·(y₀···y_{k-1}) + c`; here we prove the two facts that hold for **any** multiplier `m`
that is free of the top variable (`degreeY_top m = 0`, which every graded multiplier is), so the
specific graded `m` plugs in later without redoing this algebra:

  1. `chainNReduce_fst_preserved` : the reduce preserves the top y-degree.
  2. `chainNReduce_lcY_top_eval`  : the reduce's top leading coefficient, evaluated, equals
       `eval(cTD(lcY_top p)) + (degreeY_top p)·eval(Ffac M)·eval(lcY_top p) − eval(m)·eval(lcY_top p)`.

Fact (2) is the seam where the recursion closes: when `m`'s top graded term is exactly
`(degreeY_top p)·Ffac M`, the middle `+ … · Ffac …` cancels that part of `eval(m)·…`, leaving a
depth-`(N-1)` reduce of `lcY_top p` — the depth-N → depth-(N-1) step, at the eval level.

Uses the abstract-index discipline of `IterExpDepthNTopIdentity`: the top index stays an opaque
variable `i` with `hi : i.val = M+1`, so no `kabstract` blowup. No `sorry`.
-/

namespace MachLib.IterExpDepthNReduce

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpTopIdentity
open MachLib.ChainExp2NoZeros
open MachLib.IterExpDepthN

/-- The depth-`N` reduce with an explicit multiplier: `cTD p − m · p`. -/
noncomputable def chainNReduce (M : Nat) (m p : MultiPoly (M + 2)) : MultiPoly (M + 2) :=
  MultiPoly.sub (chainTotalDeriv (IterExpChain (M + 2)) p) (MultiPoly.mul m p)

/-- **The reduce preserves the top y-degree**, for any top-free multiplier `m`. Generic-`N` analog
of `chain2Reduce_fst_preserved` / `chain3Reduce_fst_preserved`. -/
theorem chainNReduce_fst_preserved (M : Nat) (i : Fin (M + 2)) (hi : i.val = M + 1)
    (m p : MultiPoly (M + 2)) (hm : MultiPoly.degreeY i m = 0) :
    MultiPoly.degreeY i (chainNReduce M m p) = MultiPoly.degreeY i p := by
  unfold chainNReduce
  show Nat.max (MultiPoly.degreeY i (chainTotalDeriv (IterExpChain (M + 2)) p))
              (MultiPoly.degreeY i (MultiPoly.mul m p))
     = MultiPoly.degreeY i p
  rw [degreeYtop_cTD_eq' M i hi p, degreeY_mul' i m p, hm, Nat.zero_add]
  exact Nat.max_self _

/-- **The reduce's top leading coefficient, evaluated** — the depth-N → depth-(N-1) seam. For any
top-free multiplier `m`,
`eval(lcY_top(cTD p − m·p)) = eval(cTD(lcY_top p)) + (degreeY_top p)·eval(Ffac M)·eval(lcY_top p)
                             − eval(m)·eval(lcY_top p)`.
The `+ (degreeY_top p)·eval(Ffac M)·…` term is lemma (1)'s product injection; a graded `m` whose top
term is `(degreeY_top p)·Ffac M` cancels it, leaving an honest depth-(N-1) reduce of `lcY_top p`. -/
theorem chainNReduce_lcY_top_eval (M : Nat) (i : Fin (M + 2)) (hi : i.val = M + 1)
    (m p : MultiPoly (M + 2)) (hm : MultiPoly.degreeY i m = 0) (x : Real) (env : Fin (M + 2) → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY i (chainNReduce M m p)) x env
    = MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2)) (MultiPoly.leadingCoeffY i p)) x env
      + MachLib.Real.natCast (MultiPoly.degreeY i p)
        * (MultiPoly.eval (Ffac M) x env * MultiPoly.eval (MultiPoly.leadingCoeffY i p) x env)
      - MultiPoly.eval m x env * MultiPoly.eval (MultiPoly.leadingCoeffY i p) x env := by
  have h1 := idN_general M i hi p x env
  unfold IdN at h1
  simp only [MultiPoly.eval_mul] at h1
  unfold chainNReduce
  rw [MultiPoly.leadingCoeffY_sub_of_eq i (chainTotalDeriv (IterExpChain (M + 2)) p)
        (MultiPoly.mul m p)
        (by rw [degreeYtop_cTD_eq' M i hi p, degreeY_mul' i m p, hm, Nat.zero_add]),
      lcY_mul i m p, leadingCoeffY_eq_self_of_degreeY_zero i m hm]
  simp only [MultiPoly.eval_sub, MultiPoly.eval_mul]
  rw [h1]; mach_ring

end MachLib.IterExpDepthNReduce
