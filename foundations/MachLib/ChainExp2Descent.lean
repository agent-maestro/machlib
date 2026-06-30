import MachLib.ChainExp2CanonMeasure
import MachLib.ChainExp2LcY1CTD

/-!
# Piece 3 — the cancellation: `lcY₁(chain2Reduce c p)` is the single-exp reduce of `lcY₁ p`

The correct chain-2 reduce is `chain2Reduce c p = P' − ((degreeY₁ p)·y₀ + c)·P` (`ChainExp2Reducer`). The
*defining property* — the reason it is the right operator — is that its `y₁`-leading coefficient is the
**single-exp reduce** of `lcY₁ p`, i.e. `a_d' − c·a_d`. This file proves it (eval-level), now that the
general `leadingCoeffY₁`-under-`cTD` identity is available.

The algebra: the two `sub`-summands of `chain2Reduce` have equal `degreeY₁`, so its leading coefficient is
`sub(lcY₁(cTD₂ p))(m·lcY₁ p)` with `m = (degreeY₁ p)·y₀ + c` (which is `y₁`-free, so `lcY₁ m = m`). The
general identity expands `lcY₁(cTD₂ p) = cTD₂(lcY₁ p) + (degreeY₁ p)·y₀·lcY₁ p`; the `(degreeY₁ p)·y₀·lcY₁ p`
term **exactly cancels** the `(degreeY₁ p)·y₀` part of `m·lcY₁ p`, leaving `cTD₂(lcY₁ p) − c·lcY₁ p` — the
single-exp reduce. (That cancellation is the whole point of choosing the multiplier `(degreeY₁ p)·y₀ + c`.)

`ChainExp2SDR` and the single-exp framework are untouched (Path B).
-/

namespace MachLib.ChainExp2Descent

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.ChainExp2SDR
open MachLib.ChainExp2Reducer
open MachLib.ChainExp2LcY1CTD

/-- The ring identity at the end of the cancellation — isolated with universally-quantified variables so
`mach_mpoly` (the complete normaliser; `mach_ring` stalls on the triple-product reassociation) can close
it. `A + N·(Y·LP) − (N·Y + c)·LP = A − c·LP`: the injected `N·y₀·lcY₁` term cancels. -/
private theorem cancel_ring (A LP N Y c : Real) :
    A + N * (Y * LP) - (N * Y + c) * LP = A - c * LP := by
  mach_mpoly [A, LP, N, Y, c]

/-- **The cancellation.** The `y₁`-leading coefficient of the correct reduce `chain2Reduce c p` evaluates
to the single-exp reduce of `lcY₁ p`: `cTD₂(lcY₁ p) − c·lcY₁ p`. The injected `(degreeY₁ p)·y₀·lcY₁ p` from
the chain total derivative is cancelled by the multiplier's `(degreeY₁ p)·y₀` term. -/
theorem chain2Reduce_lcY1_eval (c : Real) (p : MultiPoly 2) (x : Real) (env : Fin 2 → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) (chain2Reduce c p)) x env
    = MultiPoly.eval (chainTotalDeriv (IterExpChain 2)
        (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)) x env
      - c * MultiPoly.eval (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) x env := by
  unfold chain2Reduce
  -- the two `sub`-summands have equal `degreeY₁` (= degreeY₁ p), so leadingCoeffY of the sub distributes.
  have hcond : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p)
             = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
                 (MultiPoly.mul
                   (MultiPoly.add
                     (MultiPoly.mul (MultiPoly.const
                         (MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)))
                       (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
                     (MultiPoly.const c))
                   p) := by
    rw [degreeY1_chainTotalDeriv_eq_IterExp2 p]
    show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
       = 0 + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
    rw [Nat.zero_add]
  rw [MultiPoly.leadingCoeffY_sub_of_eq (⟨1, by omega⟩ : Fin 2)
        (chainTotalDeriv (IterExpChain 2) p)
        (MultiPoly.mul
          (MultiPoly.add
            (MultiPoly.mul (MultiPoly.const
                (MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)))
              (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
            (MultiPoly.const c))
          p) hcond,
      -- leadingCoeffY of `mul m p` = `mul m (lcY₁ p)` (m is `y₁`-free ⇒ `lcY₁ m = m`); definitional.
      show MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2)
             (MultiPoly.mul
               (MultiPoly.add
                 (MultiPoly.mul (MultiPoly.const
                     (MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)))
                   (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
                 (MultiPoly.const c))
               p)
         = MultiPoly.mul
             (MultiPoly.add
               (MultiPoly.mul (MultiPoly.const
                   (MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)))
                 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
               (MultiPoly.const c))
             (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) from rfl,
      MultiPoly.eval_sub, MultiPoly.eval_mul,
      leadingCoeffY1_cTD_eval_IterExp2 p x env]
  simp only [MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_const, MultiPoly.eval_varY]
  exact cancel_ring _ _ _ _ _

end MachLib.ChainExp2Descent
