import MachLib.IterExpDepthNRecursion

/-!
# Phase C, brick 3a — the recursion brick, FULL-ENV (∀N)

`chainNReduce_dropLastY_recursion` closes the depth-`(M+3)`→`(M+2)` recursion **on the chain values**.
The measure descent needs it on **every** environment (the eval-invariant measure's eval-invariance
quantifies over all envs). This file re-derives it full-env — the ∀N analog of the depth-3
`chain3Reduce_dropLastY_lcY2_eval_eq_full` — by replacing the chain-values `dropLastY_eval_IterExp'`
with the framework `MultiPoly.eval_dropLastY` (env-restriction) and `dropLastY_cTD_commute`, keeping the
abstract-index discipline (the top index is a variable `i` with `hi : i.val = M+2`). No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpDepthNReduce

attribute [local irreducible] MultiPoly.leadingCoeffY MultiPoly.degreeY MultiPoly.dropLastY
  chainTotalDeriv MachLib.IterExpTopIdentity.Ffac gradedTop

/-- The environment `env : Fin (M+2) → Real` lifted to `Fin (M+3)` by `0` at the top slot. -/
private noncomputable def extEnv (M : Nat) (env : Fin (M + 2) → Real) : Fin (M + 3) → Real :=
  fun k => if h : k.val < M + 2 then env ⟨k.val, h⟩ else 0

/-- Full-env `dropLastY` bridge at the abstract top index: `eval (dropLastY Y) x env = eval Y x (extEnv env)`
for `Y` free of the top variable. Confines the one literal-index step to `MultiPoly.eval_dropLastY`. -/
private theorem dropLastY_eval_full' (M : Nat) (i : Fin (M + 3)) (hi : i.val = M + 2)
    (Y : MultiPoly (M + 3)) (hY : MultiPoly.degreeY i Y = 0)
    (x : Real) (env : Fin (M + 2) → Real) :
    MultiPoly.eval (MultiPoly.dropLastY Y) x env = MultiPoly.eval Y x (extEnv M env) := by
  have hi' : i = (⟨M + 2, by omega⟩ : Fin (M + 3)) := Fin.ext hi
  rw [hi'] at hY
  have hrestrict : (fun j : Fin (M + 2) => extEnv M env ⟨j.val, by omega⟩) = env := by
    funext j
    show (if h : j.val < M + 2 then env ⟨j.val, h⟩ else 0) = env j
    rw [dif_pos j.isLt]
  have hev := MultiPoly.eval_dropLastY Y hY x (extEnv M env)
  rwa [hrestrict] at hev

/-- Full-env `dropLastY`/`cTD` commutation at the abstract top index. -/
private theorem dropLastY_cTD_commute'' (M : Nat) (i : Fin (M + 3)) (hi : i.val = M + 2)
    (q : MultiPoly (M + 3)) (hq : MultiPoly.degreeY i q = 0) :
    MultiPoly.dropLastY (chainTotalDeriv (IterExpChain (M + 3)) q)
      = chainTotalDeriv (IterExpChain (M + 2)) (MultiPoly.dropLastY q) := by
  have h : i = (⟨M + 2, by omega⟩ : Fin (M + 3)) := Fin.ext hi
  rw [h] at hq
  exact dropLastY_cTD_commute (M + 1) q hq

/-- **The recursion brick, full-env, `∀M`.** The depth-`(M+3)` graded reduce's dropped top coefficient,
evaluated at *any* environment, equals a depth-`(M+2)` reduce of `dropLastY (lcY_top p)` with multiplier
`dropLastY m_rest`. -/
theorem chainNReduce_dropLastY_recursion_full (M : Nat) (i : Fin (M + 3)) (hi : i.val = M + 2)
    (m_rest p : MultiPoly (M + 3)) (hmr : MultiPoly.degreeY i m_rest = 0)
    (x : Real) (env : Fin (M + 2) → Real) :
    MultiPoly.eval (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i
        (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p))) x env
    = MultiPoly.eval (chainNReduce M (MultiPoly.dropLastY m_rest)
        (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p))) x env := by
  have hq0 : MultiPoly.degreeY i (MultiPoly.leadingCoeffY i p) = 0 :=
    MultiPoly.degreeY_leadingCoeffY i p
  have hcTDq0 : MultiPoly.degreeY i
                 (chainTotalDeriv (IterExpChain (M + 3)) (MultiPoly.leadingCoeffY i p)) = 0 := by
    rw [degreeYtop_cTD_eq' (M + 1) i hi (MultiPoly.leadingCoeffY i p)]; exact hq0
  have hX0 : MultiPoly.degreeY i (MultiPoly.leadingCoeffY i
                 (chainNReduce (M + 1) (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p)) = 0 :=
    MultiPoly.degreeY_leadingCoeffY i _
  -- LHS: drop → eval at the lifted env, then the graded cancellation.
  have e1 := dropLastY_eval_full' M i hi
      (MultiPoly.leadingCoeffY i (chainNReduce (M + 1)
        (MultiPoly.add (gradedTop (M + 1) i p) m_rest) p)) hX0 x env
  have e2 := chainNReduce_graded_cancels (M + 1) i hi m_rest p hmr x (extEnv M env)
  -- Each surviving term, lifted env → dropped env.
  have e3 : MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 3)) (MultiPoly.leadingCoeffY i p)) x
        (extEnv M env)
      = MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2))
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p))) x env :=
    (dropLastY_eval_full' M i hi
        (chainTotalDeriv (IterExpChain (M + 3)) (MultiPoly.leadingCoeffY i p)) hcTDq0 x env).symm.trans
      (congrArg (fun t => MultiPoly.eval t x env)
        (dropLastY_cTD_commute'' M i hi (MultiPoly.leadingCoeffY i p) hq0))
  have e4 := dropLastY_eval_full' M i hi m_rest hmr x env
  have e5 := dropLastY_eval_full' M i hi (MultiPoly.leadingCoeffY i p) hq0 x env
  have ecancel :
      MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 3)) (MultiPoly.leadingCoeffY i p)) x
          (extEnv M env)
        - MultiPoly.eval m_rest x (extEnv M env)
          * MultiPoly.eval (MultiPoly.leadingCoeffY i p) x (extEnv M env)
      = MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2))
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p))) x env
        - MultiPoly.eval (MultiPoly.dropLastY m_rest) x env
          * MultiPoly.eval (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p)) x env := by
    rw [e3, ← e4, ← e5]
  have e6 :
      MultiPoly.eval (chainNReduce M (MultiPoly.dropLastY m_rest)
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p))) x env
      = MultiPoly.eval (chainTotalDeriv (IterExpChain (M + 2))
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p))) x env
        - MultiPoly.eval (MultiPoly.dropLastY m_rest) x env
          * MultiPoly.eval (MultiPoly.dropLastY (MultiPoly.leadingCoeffY i p)) x env := by
    unfold chainNReduce
    rw [MultiPoly.eval_sub, MultiPoly.eval_mul]
  exact e1.trans (e2.trans (ecancel.trans e6.symm))

end MachLib.IterExpDepthN
