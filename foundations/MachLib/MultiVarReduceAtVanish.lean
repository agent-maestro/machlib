import MachLib.MultiVarEvalAt
import MachLib.MultiVarReduceVanish

/-!
# `reduceOnce` vanishes at common zeros — EXTERNAL Horner (Gate 2d, Rung 1 brick 1.0-b)

The `reduceOnce`-vanishing invariant of the polynomial layer (`reduceOnce_vanish`), restated for
`evalCoeffsAt` (external Horner value `yv`). The top-coefficient cancellation
(`reduceFull_getLast_eval_zero`) is a **coefficient**-eval fact (env-based, no Horner), so it is reused
verbatim; only the Horner-sum steps (`reduceFull` eval identity, the dropLast preservation) get their
external-Horner twins. This makes the entire PRS-remainder step preserve "vanishes at common zeros" when
the Horner variable is supplied from outside the coefficient environment.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

/-- **Reduction eval identity (external Horner).** -/
theorem evalCoeffsAt_reduceFull (env : Fin 2 → Real) (yv : Real) (q_lead p_lead : MultiVar 2) (k : Nat)
    (ps qs : List (MultiVar 2)) :
    evalCoeffsAt (reduceFull q_lead p_lead k ps qs) env yv
      = MultiVar.eval q_lead env * evalCoeffsAt ps env yv
        - ypow yv k * MultiVar.eval p_lead env * evalCoeffsAt qs env yv := by
  show evalCoeffsAt (subCoeffs (scaleCoeffs q_lead ps) (shiftCoeffs k (scaleCoeffs p_lead qs))) env yv = _
  rw [evalCoeffsAt_subCoeffs, evalCoeffsAt_scaleCoeffs env yv q_lead ps,
    evalCoeffsAt_shiftCoeffs (scaleCoeffs p_lead qs) env yv k, evalCoeffsAt_scaleCoeffs env yv p_lead qs]
  mach_ring

/-- **The reduction vanishes at a common zero (external Horner).** -/
theorem reduceFull_vanish_at (env : Fin 2 → Real) (yv : Real) (q_lead p_lead : MultiVar 2) (k : Nat)
    (ps qs : List (MultiVar 2)) (hp : evalCoeffsAt ps env yv = 0) (hq : evalCoeffsAt qs env yv = 0) :
    evalCoeffsAt (reduceFull q_lead p_lead k ps qs) env yv = 0 := by
  rw [evalCoeffsAt_reduceFull, hp, hq]; mach_ring

/-- **Dropping an eval-zero last coefficient preserves eval (external Horner).** -/
theorem evalCoeffsAt_dropLast_of_getLast_zero (env : Fin 2 → Real) (yv : Real) :
    ∀ (l : List (MultiVar 2)) (hl : l ≠ []), MultiVar.eval (l.getLast hl) env = 0 →
      evalCoeffsAt l.dropLast env yv = evalCoeffsAt l env yv
  | [], hl, _ => absurd rfl hl
  | [a], _, hz => by
      show evalCoeffsAt [] env yv = evalCoeffsAt [a] env yv
      simp only [evalCoeffsAt_cons, evalCoeffsAt_nil]
      rw [show MultiVar.eval a env = 0 from hz]; mach_ring
  | a :: b :: l', _, hz => by
      have hz' : MultiVar.eval ((b :: l').getLast (List.cons_ne_nil b l')) env = 0 := by
        rw [List.getLast_cons (List.cons_ne_nil b l')] at hz; exact hz
      show evalCoeffsAt (a :: (b :: l').dropLast) env yv = evalCoeffsAt (a :: b :: l') env yv
      rw [evalCoeffsAt_cons, evalCoeffsAt_cons,
        evalCoeffsAt_dropLast_of_getLast_zero env yv (b :: l') (List.cons_ne_nil b l') hz']

/-- **`reduceOnce` vanishes at a common zero (external Horner).** Reuses the env-based top-coefficient
cancellation `reduceFull_getLast_eval_zero` verbatim; only the Horner steps are external-Horner twins. -/
theorem reduceOnce_vanish_at (env : Fin 2 → Real) (yv : Real) (ps qs : List (MultiVar 2))
    (hps : ps ≠ []) (hqs : qs ≠ []) (hlen : qs.length ≤ ps.length)
    (hp : evalCoeffsAt ps env yv = 0) (hq : evalCoeffsAt qs env yv = 0) :
    evalCoeffsAt (reduceOnce (qs.getLast hqs) (ps.getLast hps) ps qs) env yv = 0 := by
  show evalCoeffsAt
    (reduceFull (qs.getLast hqs) (ps.getLast hps) (ps.length - qs.length) ps qs).dropLast env yv = 0
  have hleneq : (scaleCoeffs (qs.getLast hqs) ps).length
      = (negCoeffs (shiftCoeffs (ps.length - qs.length) (scaleCoeffs (ps.getLast hps) qs))).length := by
    rw [length_scaleCoeffs, length_negCoeffs, length_shiftCoeffs, length_scaleCoeffs]; omega
  have hne : reduceFull (qs.getLast hqs) (ps.getLast hps) (ps.length - qs.length) ps qs ≠ [] :=
    addCoeffs_ne_nil hleneq (scaleCoeffs_ne_nil _ hps)
  rw [evalCoeffsAt_dropLast_of_getLast_zero env yv _ hne
    (reduceFull_getLast_eval_zero env ps qs hps hqs hlen hne)]
  exact reduceFull_vanish_at env yv (qs.getLast hqs) (ps.getLast hps) (ps.length - qs.length) ps qs hp hq

end MultiVarMod
end MachLib
