import MachLib.IterExpTopIdentity

/-!
# Depth-3 recursion-cancellation: the reduce's leading coefficient IS a depth-2 reduce

The payoff of lemma (1) (`IterExpTopIdentity.leadingCoeffY2_cTD_eval_IterExp3`). The correct depth-3
reduce uses the GRADED multiplier the scope identified,

  `m = (degreeY₂ p)·y₀·y₁ + (degreeY₁(lcY₂ p))·y₀ + c`,

whose `(degreeY₂ p)·y₀·y₁` term exactly cancels the `y₀·y₁` injection that `cTD` puts into the top
leading coefficient (lemma 1). What survives is

  `eval(lcY₂(chain3Reduce c p)) = eval(cTD(lcY₂ p)) − (degreeY₁(lcY₂ p)·y₀ + c)·eval(lcY₂ p)`,

which is *exactly* a DEPTH-2 reduce of `lcY₂ p` (a `y₂`-free poly in `x, y₀, y₁`, multiplier `d₁·y₀+c`).
So the depth-3 descent recurses to a depth-2 problem — the scope's central claim, now proven concretely.
This mirrors chain-2's `ChainExp2Descent.chain2Reduce_lcY1_eval` one level up. Path B; no `sorry`.
-/

namespace MachLib.IterExpDepth3Descent

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod
open MachLib.IterExpTopIdentity

/-- The graded depth-3 reduce multiplier `m = d₂·y₀·y₁ + d₁·y₀ + c`
(`d₂ = degreeY₂ p`, `d₁ = degreeY₁(lcY₂ p)`). `y₂`-free by construction. -/
noncomputable def mult3 (c : Real) (p : MultiPoly 3) : MultiPoly 3 :=
  MultiPoly.add
    (MultiPoly.add
      (MultiPoly.mul
        (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)))
        (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 3))
                       (MultiPoly.varY (⟨1, by omega⟩ : Fin 3))))
      (MultiPoly.mul
        (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3)
            (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))))
        (MultiPoly.varY (⟨0, by omega⟩ : Fin 3))))
    (MultiPoly.const c)

/-- **The correct depth-3 reduce** `R(p) = p' − m·p`. -/
noncomputable def chain3Reduce (c : Real) (p : MultiPoly 3) : MultiPoly 3 :=
  MultiPoly.sub (chainTotalDeriv (IterExpChain 3) p) (MultiPoly.mul (mult3 c p) p)

/-- The multiplier is `y₂`-free. -/
theorem degreeY2_mult3 (c : Real) (p : MultiPoly 3) :
    MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (mult3 c p) = 0 := rfl

/-- The ring cancellation: the `d₂·y₀·y₁` injection cancels the `d₂·y₀·y₁` multiplier term. -/
private theorem cancel3_ring (CT D2 D1 Y0 Y1 LP c : Real) :
    (CT + D2 * ((Y0 * Y1) * LP)) - (D2 * (Y0 * Y1) + D1 * Y0 + c) * LP
    = CT - (D1 * Y0 + c) * LP := by
  mach_mpoly [CT, D2, D1, Y0, Y1, LP, c]

/-- **The depth-3 recursion-cancellation identity.** `eval(lcY₂(chain3Reduce c p))` collapses to a
DEPTH-2 reduce of `lcY₂ p`: `eval(cTD(lcY₂ p)) − (degreeY₁(lcY₂ p)·y₀ + c)·eval(lcY₂ p)`. The scope's
"recursion closes" claim, machine-checked at depth 3 via lemma (1). -/
theorem chain3Reduce_lcY2_eval (c : Real) (p : MultiPoly 3) (x : Real) (env : Fin 3 → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) (chain3Reduce c p)) x env
    = MultiPoly.eval (chainTotalDeriv (IterExpChain 3)
        (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) x env
      - (MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3)
            (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p))
          * MultiPoly.eval (MultiPoly.varY (⟨0, by omega⟩ : Fin 3)) x env + c)
        * MultiPoly.eval (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p) x env := by
  -- degreeY₂ preserved on the derivative summand, 0 on the multiplier·p summand ⇒ they tie.
  have hdeg : MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (chainTotalDeriv (IterExpChain 3) p)
            = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (MultiPoly.mul (mult3 c p) p) := by
    rw [degreeY2_cTD_eq_IterExp3 p]
    show MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p
       = MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) (mult3 c p)
         + MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p
    rw [degreeY2_mult3 c p]; omega
  have hlcM : MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) (mult3 c p) = mult3 c p := rfl
  show MultiPoly.eval (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3)
        (MultiPoly.sub (chainTotalDeriv (IterExpChain 3) p) (MultiPoly.mul (mult3 c p) p))) x env = _
  rw [MultiPoly.leadingCoeffY_sub_of_eq (⟨2, by omega⟩ : Fin 3)
        (chainTotalDeriv (IterExpChain 3) p) (MultiPoly.mul (mult3 c p) p) hdeg,
      lcY_mul (⟨2, by omega⟩ : Fin 3) (mult3 c p) p, hlcM,
      MultiPoly.eval_sub, MultiPoly.eval_mul,
      leadingCoeffY2_cTD_eval_IterExp3 p x env]
  -- expand eval of the multiplier and the injection factor, then cancel.
  show MultiPoly.eval (chainTotalDeriv (IterExpChain 3)
          (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) x env
        + MachLib.Real.natCast (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p)
          * MultiPoly.eval (MultiPoly.mul (MultiPoly.mul (MultiPoly.varY (⟨0, by omega⟩ : Fin 3))
              (MultiPoly.varY (⟨1, by omega⟩ : Fin 3)))
              (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) x env
      - MultiPoly.eval (mult3 c p) x env
        * MultiPoly.eval (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p) x env
      = _
  unfold mult3
  simp only [MultiPoly.eval_add, MultiPoly.eval_mul, MultiPoly.eval_const]
  generalize MultiPoly.eval (chainTotalDeriv (IterExpChain 3)
      (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) x env = CT
  generalize MachLib.Real.natCast (MultiPoly.degreeY (⟨2, by omega⟩ : Fin 3) p) = D2
  generalize MachLib.Real.natCast (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 3)
      (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p)) = D1
  generalize MultiPoly.eval (MultiPoly.varY (⟨0, by omega⟩ : Fin 3)) x env = Y0
  generalize MultiPoly.eval (MultiPoly.varY (⟨1, by omega⟩ : Fin 3)) x env = Y1
  generalize MultiPoly.eval (MultiPoly.leadingCoeffY (⟨2, by omega⟩ : Fin 3) p) x env = LP
  exact cancel3_ring CT D2 D1 Y0 Y1 LP c

end MachLib.IterExpDepth3Descent
