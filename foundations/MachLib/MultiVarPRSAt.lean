import MachLib.MultiVarReduceAtVanish
import MachLib.MultiVarPRS

/-!
# The PRS loop preserves vanishing — EXTERNAL Horner (Gate 2d, Rung 1 brick 1.0-c)

`prsLoop_vanish`, restated for `evalCoeffsAt` (external Horner value). The loop *definition* (`prsLoop`,
`reduceStep`) and its termination (`prsLoop_terminates`) are structural — independent of how coefficients
are evaluated — so they are reused verbatim; only the vanishing invariant needs its external-Horner twin.
This is the last elimination brick: with the Horner variable supplied from outside, the PRS still drives a
common zero of `{ps, qs}` into a common zero of its `y`-free remainder.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar

theorem reduceStep_vanish_at (env : Fin 2 → Real) (yv : Real) (ps qs : List (MultiVar 2))
    (hps : ps ≠ []) (hqs : qs ≠ []) (hlen : qs.length ≤ ps.length)
    (hp : evalCoeffsAt ps env yv = 0) (hq : evalCoeffsAt qs env yv = 0) :
    evalCoeffsAt (reduceStep ps qs) env yv = 0 := by
  show evalCoeffsAt
    (reduceOnce (qs.getLastD (MultiVar.const 0)) (ps.getLastD (MultiVar.const 0)) ps qs) env yv = 0
  rw [getLastD_eq_getLast hqs, getLastD_eq_getLast hps]
  exact reduceOnce_vanish_at env yv ps qs hps hqs hlen hp hq

/-- **The PRS loop preserves vanishing at a common zero (external Horner).** -/
theorem prsLoop_vanish_at (env : Fin 2 → Real) (yv : Real) :
    ∀ (fuel : Nat) (ps qs : List (MultiVar 2)),
      evalCoeffsAt ps env yv = 0 → evalCoeffsAt qs env yv = 0 →
      evalCoeffsAt (prsLoop fuel ps qs) env yv = 0
  | 0, _, _, hp, _ => hp
  | fuel + 1, ps, qs, hp, hq => by
      show evalCoeffsAt (if qs.length ≤ 1 then qs
          else if ps.length ≤ 1 then ps
          else if ps.length ≤ qs.length then prsLoop fuel (reduceStep qs ps) ps
          else prsLoop fuel (reduceStep ps qs) qs) env yv = 0
      split
      · exact hq
      · split
        · exact hp
        · split
          · rename_i hq1 hp1 hpq
            have hqs : qs ≠ [] := fun he => hq1 (by rw [he]; simp)
            have hps : ps ≠ [] := fun he => hp1 (by rw [he]; simp)
            exact prsLoop_vanish_at env yv fuel (reduceStep qs ps) ps
              (reduceStep_vanish_at env yv qs ps hqs hps hpq hq hp) hp
          · rename_i hq1 hp1 hpq
            have hqs : qs ≠ [] := fun he => hq1 (by rw [he]; simp)
            have hps : ps ≠ [] := fun he => hp1 (by rw [he]; simp)
            exact prsLoop_vanish_at env yv fuel (reduceStep ps qs) qs
              (reduceStep_vanish_at env yv ps qs hps hqs (Nat.le_of_lt (Nat.lt_of_not_le hpq)) hp hq) hq

end MultiVarMod
end MachLib
