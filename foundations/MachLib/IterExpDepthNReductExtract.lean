import MachLib.IterExpDepthNVehicle
import MachLib.IterExpDepthNCoupling

/-!
# Phase D (D3, step i cont.) — `reductMultP = reductMult` via degree extraction

The vehicle machinery states the reduce value with `reductMult d c z m` (a `Σ dₖ·prodExp + c` for a fixed
degree function `d`), while the coupling produces `reductMultP k p z` (the same sum, degrees extracted
inline from `p`). This file reconciles them: `dExtract`/`cExtract` peel the level degrees/constant out of
`p`, and `reductMultP_eq_reductMult` shows the two multiplier values agree. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.IterExpChainMod
open MachLib.ChainExp2CanonMeasure

/-- `reductMult` depends on the degree function only below the number of levels. -/
theorem reductMult_congr (d d' : Nat → Nat) (c : Real) (z : Real) :
    ∀ (m : Nat), (∀ j, j < m → d j = d' j) → reductMult d c z m = reductMult d' c z m
  | 0, _ => rfl
  | m + 1, h => by
      show MachLib.Real.natCast (d m) * prodExp z m + reductMult d c z m
        = MachLib.Real.natCast (d' m) * prodExp z m + reductMult d' c z m
      rw [h m (by omega), reductMult_congr d d' c z m (fun j hj => h j (by omega))]

/-- The recursively-extracted level-degree function of `p` at depth `k+2`. -/
noncomputable def dExtract : (k : Nat) → MultiPoly (k + 2) → Nat → Nat
  | 0 => fun p => fun _ => MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
  | k + 1 => fun p => fun j =>
      if j = k + 1 then MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) p
      else dExtract k (MultiPoly.dropLastY
            (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) p)) j

/-- The recursively-extracted base constant of `p`. -/
noncomputable def cExtract : (k : Nat) → MultiPoly (k + 2) → Real
  | 0 => fun p => MachLib.Real.natCast (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p))
  | k + 1 => fun p => cExtract k (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) p))

/-- **`reductMultP` is `reductMult` with the extracted degrees/constant.** -/
theorem reductMultP_eq_reductMult :
    ∀ (k : Nat) (p : MultiPoly (k + 2)) (z : Real),
      reductMultP k p z = reductMult (dExtract k p) (cExtract k p) z (k + 1)
  | 0, p, z => by simp only [reductMultP, dExtract, cExtract, reductMult]
  | k + 1, p, z => by
      show MachLib.Real.natCast (MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) p) * prodExp z (k + 1)
            + reductMultP k (MultiPoly.dropLastY
                (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) p)) z
        = MachLib.Real.natCast (dExtract (k + 1) p (k + 1)) * prodExp z (k + 1)
            + reductMult (dExtract (k + 1) p) (cExtract (k + 1) p) z (k + 1)
      rw [show dExtract (k + 1) p (k + 1)
            = MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) p from if_pos rfl]
      congr 1
      rw [reductMultP_eq_reductMult k
            (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) p)) z]
      apply reductMult_congr
      intro j hj
      show dExtract k _ j = dExtract (k + 1) p j
      simp only [dExtract]
      rw [if_neg (Nat.ne_of_lt hj)]

end MachLib.IterExpDepthN
