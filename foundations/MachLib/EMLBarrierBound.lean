import MachLib.EMLEncoderDescent
import MachLib.EMLEncoderAnalytic

/-!
# Capstone: the EML barrier has boundedly many zeros (modulo the two classical steps)

Assembles the whole encoder into the descent. The encoder produces, from any
`EMLTree t`, a coherent `IsExpLogRecipW` Pfaffian chain that is analytic and
`PosExceptLog`, with barrier evaluating to `t.eval` (`enc_eval`). Feeding those
four inputs to `combined_descent_3(_of_steps)` yields: **`t.eval` has boundedly
many zeros on `(a,b)`**, conditional only on `LogArgPosOn t (Icc a b)` and the
descent bound `hdescent` — which `combined_descent_3_of_steps a b hab exp_step
log_step` provides. So the ONLY remaining inputs are the two classical Khovanskii
steps `exp_step`/`log_step`; every interface between encoder and descent is
proven to compose here.

`hdescent` is exactly the conclusion of `combined_descent_3_of_steps`; taking it
as a hypothesis (rather than re-stating the two long step types) keeps this
capstone about the *assembly*.

No new axioms.
-/

namespace MachLib

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
  MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain
  MachLib.PfaffianChainMod.PfaffianFn
  MachLib.PfaffianGeneralReduce MachLib.PfaffianExpRecipW MachLib.PfaffianExpLogRecip

/-- The length-0 Pfaffian chain (no variables); the encoder's initial context.
Every per-variable property (`IsExpLogRecipW`, coherence, `PosExceptLog`,
chain-value analyticity) holds vacuously over `Fin 0`. -/
def emlEmptyChain : PfaffianChain 0 := ⟨fun i => i.elim0, fun i => i.elim0⟩

/-- **The EML value function has boundedly many zeros.** Given the descent bound
`hdescent` (= `combined_descent_3_of_steps a b hab exp_step log_step`) and
`LogArgPosOn t (Icc a b)`, if `t.eval` is somewhere nonzero on `(a,b)` then it has
at most `K` zeros there for some `K`. The encoder supplies all four descent inputs
on `enc t emlEmptyChain`; `enc_eval` bridges the barrier to `t.eval`. -/
theorem eml_eval_boundedZeros (t : EMLTree) (a b : Real)
    (hdescent : ∀ (N : Nat) (c : PfaffianChain N),
        IsExpLogRecipW c a b → c.IsCoherentOn a b → PosExceptLog c a b →
        (∀ r : MultiPoly N, IsAnalyticOnReals (pfaffianChainFn c r).eval (Icc a b)) →
        ∀ (p : MultiPoly N),
          (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
          BoundedZeros (pfaffianChainFn c p) a b)
    (hlog : LogArgPosOn t (Icc a b))
    (hne : ∃ z, a < z ∧ z < b ∧ t.eval z ≠ 0) :
    ∃ K : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ t.eval z = 0) → zeros.length ≤ K := by
  have hlogOpen : LogArgPos t a b := LogArgPos_of_LogArgPosOn_Icc a b t hlog
  have hbridge : ∀ z, (pfaffianChainFn (enc t emlEmptyChain).1 (enc t emlEmptyChain).2).eval z
      = t.eval z := fun z => enc_eval t emlEmptyChain z
  have hne' : ∃ z, a < z ∧ z < b ∧
      (pfaffianChainFn (enc t emlEmptyChain).1 (enc t emlEmptyChain).2).eval z ≠ 0 := by
    obtain ⟨z, hza, hzb, hz0⟩ := hne
    exact ⟨z, hza, hzb, by rw [hbridge z]; exact hz0⟩
  obtain ⟨K, hK⟩ := hdescent (len t 0) (enc t emlEmptyChain).1
    (enc_IsExpLogRecipW t emlEmptyChain a b (fun i => i.elim0) hlogOpen)
    (enc_isCoherentOn t emlEmptyChain a b (fun _ _ _ i => i.elim0) hlogOpen)
    (enc_PosExceptLog t emlEmptyChain a b (fun _ _ _ i => i.elim0) hlogOpen)
    (fun r => enc_hAnalytic t emlEmptyChain (Icc a b) (fun i => i.elim0) hlog r)
    (enc t emlEmptyChain).2 hne'
  refine ⟨K, fun zeros hnodup hzeros => hK zeros hnodup (fun z hz => ?_)⟩
  obtain ⟨hza, hzb, hz0⟩ := hzeros z hz
  exact ⟨hza, hzb, by rw [hbridge z]; exact hz0⟩

end MachLib
