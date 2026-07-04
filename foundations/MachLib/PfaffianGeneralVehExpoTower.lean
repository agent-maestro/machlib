import MachLib.PfaffianGeneralBound2
namespace MachLib.PfaffianGeneralVehExpo
open MachLib.Real MachLib.PfaffianChainMod MachLib.MultiPolyMod
open MachLib.PfaffianGeneralReduce MachLib.IterExpTopIdentity
open MachLib.MultiPolyMod.MultiPoly

/-- **The step eval-bridge for the tower reduce multiplier.** The one-level reduce multiplier
`gradedMultStep G ⟨top⟩ q (liftLastY m')` evaluated along `c` splits into the top-level term
`degreeY_top(q)·G` plus the sub-multiplier `m'` evaluated along `chainRestrict c` — the recursion the
integrating-factor tower descends on. `gradedMultStep_eval` + `eval_liftLastY` + `chainRestrict_chainValues`. -/
theorem gradedMultStep_liftLastY_eval_chain {k : Nat} (c : PfaffianChain (k + 3)) (G : MultiPoly (k + 3))
    (m' : MultiPoly (k + 2)) (q : MultiPoly (k + 3)) (z : Real) :
    MultiPoly.eval (gradedMultStep G (⟨k + 2, by omega⟩ : Fin (k + 3)) q (MultiPoly.liftLastY m')) z
        (c.chainValues z)
      = MachLib.Real.natCast (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)
          * MultiPoly.eval G z (c.chainValues z)
        + MultiPoly.eval m' z ((chainRestrict c).chainValues z) := by
  rw [gradedMultStep_eval, eval_liftLastY]
  congr 1

set_option maxHeartbeats 1000000 in
/-- **The integrating-factor tower step.** Given an integrating factor `E'` for the sub-multiplier `m'` on
`chainRestrict c`, `E z = −degreeY_top(q)·log(y_top z) + E' z` is an integrating factor for the full
multiplier `gradedMultStep G ⟨top⟩ q (liftLastY m')` on `c`. The top log term contributes `−deg·(y_top'/y_top)
= −deg·G` (coherence + positivity + `hrel`), and the eval-bridge splits the multiplier so the two pieces sum
to `−eval(full mult)`. This is the inductive step that lifts the depth-2 vehExpo (`hE_vehExpo_bound2`) to all
depths — the hIF tower. -/
theorem vehExpo_tower_step {k : Nat} (c : PfaffianChain (k + 3)) (G : MultiPoly (k + 3))
    (q : MultiPoly (k + 3)) (m' : MultiPoly (k + 2)) (a b : Real)
    (hrel : c.relations (⟨k + 2, by omega⟩ : Fin (k + 3)) = MultiPoly.mul G (MultiPoly.varY (⟨k + 2, by omega⟩ : Fin (k + 3))))
    (hcoh : c.IsCoherentOn a b)
    (hpos_top : ∀ z, a < z → z < b → 0 < c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z)
    (E' : Real → Real)
    (hE' : ∀ z, a < z → z < b → HasDerivAt E' (-(pfaffianChainFn (chainRestrict c) m').eval z) z) :
    ∃ E : Real → Real, ∀ z, a < z → z < b →
      HasDerivAt E (-(pfaffianChainFn c (gradedMultStep G (⟨k + 2, by omega⟩ : Fin (k + 3)) q
        (MultiPoly.liftLastY m'))).eval z) z := by
  refine ⟨fun z => (-MachLib.Real.natCast (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))
      * Real.log (c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z) + E' z, ?_⟩
  intro z hza hzb
  have hlog : HasDerivAt (fun z => Real.log (c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z))
      ((1 / c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z)
        * MultiPoly.eval (c.relations (⟨k + 2, by omega⟩ : Fin (k + 3))) z (c.chainValues z)) z :=
    HasDerivAt_comp Real.log (c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)))
      (MultiPoly.eval (c.relations (⟨k + 2, by omega⟩ : Fin (k + 3))) z (c.chainValues z))
      (1 / c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z) z
      (hcoh z hza hzb (⟨k + 2, by omega⟩ : Fin (k + 3))) (HasDerivAt_log_pos _ (hpos_top z hza hzb))
  have hlvl : HasDerivAt (fun z => (-MachLib.Real.natCast (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))
        * Real.log (c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z))
      ((-MachLib.Real.natCast (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))
        * ((1 / c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z)
          * MultiPoly.eval (c.relations (⟨k + 2, by omega⟩ : Fin (k + 3))) z (c.chainValues z))) z := by
    have h := HasDerivAt_mul (fun _ => -MachLib.Real.natCast (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))
      (fun z => Real.log (c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z)) 0
      ((1 / c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z)
        * MultiPoly.eval (c.relations (⟨k + 2, by omega⟩ : Fin (k + 3))) z (c.chainValues z)) z
      (HasDerivAt_const _ z) hlog
    rw [zero_mul, zero_add] at h; exact h
  have hadd := HasDerivAt_add _ E' _ _ z hlvl (hE' z hza hzb)
  have hlev_top : (1 / c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z)
      * MultiPoly.eval (c.relations (⟨k + 2, by omega⟩ : Fin (k + 3))) z (c.chainValues z)
      = MultiPoly.eval G z (c.chainValues z) := by
    rw [hrel, MultiPoly.eval_mul, MultiPoly.eval_varY,
        show (1 / c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z)
            * (MultiPoly.eval G z (c.chainValues z) * c.chainValues z (⟨k + 2, by omega⟩ : Fin (k + 3)))
          = MultiPoly.eval G z (c.chainValues z)
            * ((1 / c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z) * c.chainValues z (⟨k + 2, by omega⟩ : Fin (k + 3)))
          from by mach_ring]
    show MultiPoly.eval G z (c.chainValues z)
        * ((1 / c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z) * c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z) = _
    rw [show (1 / c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z) * c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z = 1
          from by rw [mul_comm]; exact mul_inv _ (ne_of_gt (hpos_top z hza hzb)), mul_one_ax]
  have hval : (-MachLib.Real.natCast (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))
        * ((1 / c.evals (⟨k + 2, by omega⟩ : Fin (k + 3)) z)
          * MultiPoly.eval (c.relations (⟨k + 2, by omega⟩ : Fin (k + 3))) z (c.chainValues z))
        + (-(pfaffianChainFn (chainRestrict c) m').eval z)
      = -(pfaffianChainFn c (gradedMultStep G (⟨k + 2, by omega⟩ : Fin (k + 3)) q (MultiPoly.liftLastY m'))).eval z := by
    rw [hlev_top]
    show (-MachLib.Real.natCast (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) * MultiPoly.eval G z (c.chainValues z)
        + (-(MultiPoly.eval m' z ((chainRestrict c).chainValues z)))
      = -(MultiPoly.eval (gradedMultStep G (⟨k + 2, by omega⟩ : Fin (k + 3)) q (MultiPoly.liftLastY m')) z (c.chainValues z))
    rw [gradedMultStep_liftLastY_eval_chain]
    mach_ring
  rw [hval] at hadd
  exact hadd

end MachLib.PfaffianGeneralVehExpo
