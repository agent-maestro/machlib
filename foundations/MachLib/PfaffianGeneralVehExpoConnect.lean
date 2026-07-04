import MachLib.PfaffianGeneralVehExpo
import MachLib.PfaffianGeneralBaseHnz
namespace MachLib.PfaffianGeneralVehExpo
open MachLib.Real MachLib.PfaffianChainMod MachLib.MultiPolyMod
open MachLib.PfaffianGeneralReduce MachLib.ChainExp2CanonMeasure MachLib.IterExpTopIdentity

set_option maxHeartbeats 1000000 in
/-- **The depth-2 reduce→ODE identity.** The general log-vehExpo derivative over both levels IS
`−eval(reduce multiplier)`: for a depth-2 exp-chain (`relations ⟨i⟩ = Gᵢ·yᵢ`) with `yᵢ(z) ≠ 0`, and the
degree function `deg` matching the graded multiplier (`deg ⟨1⟩ = degreeY₁ q`, `deg ⟨0⟩ = cdegY0(lcY₁ q)`),
`logVehExpoDerivAux c deg z 2 = −(pfaffianChainFn c (gradedMultStep …)).eval z`. So the brick-37 vehExpo is
exactly the integrating factor the reduce arm needs. Uses `gradedMultStep_eval` + the per-level cancellation
`(1/yᵢ)·(Gᵢ·yᵢ) = Gᵢ`. -/
theorem logVehExpoDeriv2_eq_neg_reduceMult {c : PfaffianChain 2} (G0 G1 q : MultiPoly 2) (z : Real)
    (deg : Fin 2 → Nat)
    (hdeg0 : deg (⟨0, by omega⟩ : Fin 2) = cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))
    (hdeg1 : deg (⟨1, by omega⟩ : Fin 2) = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q)
    (hrel0 : c.relations (⟨0, by omega⟩ : Fin 2) = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hrel1 : c.relations (⟨1, by omega⟩ : Fin 2) = MultiPoly.mul G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))
    (hy0 : c.evals (⟨0, by omega⟩ : Fin 2) z ≠ 0) (hy1 : c.evals (⟨1, by omega⟩ : Fin 2) z ≠ 0) :
    logVehExpoDerivAux c deg z 2 (Nat.le_refl 2)
    = -(pfaffianChainFn c
        (gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) q
          (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)))) G0))).eval z := by
  have hlev : ∀ (i : Fin 2) (Gi : MultiPoly 2),
      c.relations i = MultiPoly.mul Gi (MultiPoly.varY i) → c.evals i z ≠ 0 →
      (1 / c.evals i z) * MultiPoly.eval (c.relations i) z (c.chainValues z)
        = MultiPoly.eval Gi z (c.chainValues z) := by
    intro i Gi hrel hne
    rw [hrel, MultiPoly.eval_mul, MultiPoly.eval_varY,
        show (1 / c.evals i z) * (MultiPoly.eval Gi z (c.chainValues z) * c.chainValues z i)
            = MultiPoly.eval Gi z (c.chainValues z) * ((1 / c.evals i z) * c.chainValues z i) from by mach_ring]
    show MultiPoly.eval Gi z (c.chainValues z) * ((1 / c.evals i z) * c.evals i z) = _
    rw [show (1 / c.evals i z) * c.evals i z = 1 from by rw [mul_comm]; exact mul_inv _ hne, mul_one_ax]
  show (-MachLib.Real.natCast (deg (⟨1, by omega⟩ : Fin 2)))
          * ((1 / c.evals (⟨1, by omega⟩ : Fin 2) z)
              * MultiPoly.eval (c.relations (⟨1, by omega⟩ : Fin 2)) z (c.chainValues z))
        + ((-MachLib.Real.natCast (deg (⟨0, by omega⟩ : Fin 2)))
            * ((1 / c.evals (⟨0, by omega⟩ : Fin 2) z)
                * MultiPoly.eval (c.relations (⟨0, by omega⟩ : Fin 2)) z (c.chainValues z))
          + 0) = _
  rw [hdeg0, hdeg1,
      hlev (⟨1, by omega⟩ : Fin 2) G1 hrel1 hy1,
      hlev (⟨0, by omega⟩ : Fin 2) G0 hrel0 hy0]
  show _ = -(MultiPoly.eval (gradedMultStep G1 (⟨1, by omega⟩ : Fin 2) q
          (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)))) G0)) z (c.chainValues z))
  rw [gradedMultStep_eval, MultiPoly.eval_mul, MultiPoly.eval_const]
  mach_ring

end MachLib.PfaffianGeneralVehExpo
