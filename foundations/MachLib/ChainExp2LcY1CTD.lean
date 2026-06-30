import MachLib.ChainExp2SDR

/-!
# The general `leadingCoeffY₁`-under-`chainTotalDeriv` identity for chain-2 (Piece 3 core)

The descent that closes chain-2 termination rests on computing `lcY₁(chain2Reduce c p)`, which needs the
*general* (any-environment) identity — the chain-2 analog of single-exp's
`leadingCoeffY_chainTotalDeriv_eval_SingleExp_*` (`ChainExp2PathC`):

  `eval(lcY₁(cTD₂ p)) x env = eval(cTD₂(lcY₁ p)) x env  +  d · eval(y₀ · lcY₁ p) x env`,  `d = degreeY₁ p`.

The extra term carries a `y₀` factor (vs single-exp's bare `d·lcY₀ p`) because `y₁' = y₀·y₁`. Setting
`y₀ = 0` recovers the existing `ChainExp2SDR.lcY1_cTD_eval_zero_IterExp2`.

We build it the way the single-exp version was built: **case by case**. This file ships the **base cases**
(`const`, `varX`, `varY 0`, `varY 1`); the inductive `add`/`sub`/`mul` cases and the final assembly follow
(separate lemmas, same skeleton as `ChainExp2SDR.lcY1_cTD_eval_zero_IterExp2`). `ChainExp2SDR` is untouched
(Path B); no `sorry`.

The heart of *why* chain-2 differs is the `varY 1` base case: `cTD₂(y₁) = y₀·y₁`, so `lcY₁(cTD₂ y₁) = y₀`,
whereas `cTD₂(lcY₁ y₁) = cTD₂(1) = 0` — the whole `eval` is carried by the `d·y₀·lcY₁` term (`d = 1`).
-/

namespace MachLib.ChainExp2LcY1CTD

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2SDR

/-- **Base cases** of the general chain-2 `leadingCoeffY₁`-under-`cTD` identity, for `const`, `varX`,
`varY 0`, `varY 1`. The `varY 1` conjunct is the structural reason chain-2 needs the `y₀` factor. -/
theorem leadingCoeffY1_cTD_eval_IterExp2_base (x : Real) (env : Fin 2 → Real) :
    (∀ c : Real,
      MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (chainTotalDeriv (IterExpChain 2) (MultiPoly.const c : MultiPoly 2))) x env
      = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.const c))) x env
        + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.const c))
          * MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.const c))) x env)
  ∧ (MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (chainTotalDeriv (IterExpChain 2) (MultiPoly.varX : MultiPoly 2))) x env
      = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.varX : MultiPoly 2))) x env
        + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.varX : MultiPoly 2))
          * MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.varX : MultiPoly 2))) x env)
  ∧ (MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (chainTotalDeriv (IterExpChain 2) (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))) x env
      = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))) x env
        + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
            (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
          * MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
                (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))) x env)
  ∧ (MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
          (chainTotalDeriv (IterExpChain 2) (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))) x env
      = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
          (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))) x env
        + MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
            (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))
          * MultiPoly.eval (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
              (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
                (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))) x env) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- const c: cTD₂(const c)=0, lcY₁(0)=0 ⇒ LHS 0; lcY₁(const c)=const c, cTD₂=0 ⇒ RHS 0; degreeY₁=0.
    intro c
    show (0 : Real) = 0 + MachLib.Real.natCast 0
        * (env (⟨0, by omega⟩ : Fin 2) * c)
    rw [MachLib.Real.natCast_zero]; mach_ring
  · -- varX: cTD₂(varX)=const 1, lcY₁(1)=1 ⇒ LHS 1; lcY₁(varX)=varX, cTD₂=1 ⇒ RHS 1; degreeY₁=0.
    show (1 : Real) = 1 + MachLib.Real.natCast 0
        * (env (⟨0, by omega⟩ : Fin 2) * x)
    rw [MachLib.Real.natCast_zero]; mach_ring
  · -- varY 0: cTD₂(y₀)=y₀, lcY₁(y₀)=y₀ ⇒ LHS env 0; RHS env 0; degreeY₁(y₀)=0.
    show env (⟨0, by omega⟩ : Fin 2)
        = env (⟨0, by omega⟩ : Fin 2) + MachLib.Real.natCast 0
          * (env (⟨0, by omega⟩ : Fin 2) * env (⟨0, by omega⟩ : Fin 2))
    rw [MachLib.Real.natCast_zero]; mach_ring
  · -- varY 1: cTD₂(y₁)=y₀·y₁ ⇒ lcY₁=y₀ ⇒ LHS env 0 · 1; lcY₁(y₁)=1, cTD₂(1)=0 ⇒ RHS 0; degreeY₁=1.
    show env (⟨0, by omega⟩ : Fin 2) * (1 : Real)
        = 0 + MachLib.Real.natCast 1
          * (env (⟨0, by omega⟩ : Fin 2) * (1 : Real))
    rw [MachLib.Real.natCast_succ, MachLib.Real.natCast_zero]; mach_ring

end MachLib.ChainExp2LcY1CTD
