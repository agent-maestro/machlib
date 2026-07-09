import MachLib.IterExpDepthNCanonLcYBound
import MachLib.IterExpDepth3CdegY1

/-!
# EIrank base-case bounds (step-3 support): the chain-2 canonical measure's components ≤ degrees

`chainNMeasureEI 0 = chain2MeasureCanonEvalInv q = (cdegY1 q, singleExpMeasureCanon (canonLcY1 q))`, so
bounding `EIrank` at the base needs each component under a global `B`:
`cdegY1 q ≤ degreeY₁ q`, `cdegY0(canonLcY1 q) ≤ degreeY₀ q`, `b(canonLcY1 q) ≤ degreeX q + 2`. This file
supplies the missing pieces (`canonLcY1` uses `coeffCanonZeroB1`, so it is NOT `canonLcYAt ⟨1⟩` and needs
its own bounds; and the `singleExpMeasure` `.2` bound needs a version for an arbitrary poly, not just a
`leadingCoeffY`).

  * `singleExpMeasureCanon_snd_le_gen` — `(singleExpMeasureCanon r).2 ≤ degreeX r + 2`, ANY `r`.
  * `cdegY1_le_degreeY1` — canonical `y₁`-degree refines the syntactic one (mirror of `cdegY0_le_degreeY0`).
  * `canonLcY1_mem_or_zero` + `degreeX_canonLcY1_le` / `degreeY_canonLcY1_le`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.PolynomialCanonical
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2Explicit
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpDepth3CdegY1

/-- `(l.dropWhile pr).length ≤ l.length`. -/
theorem length_dropWhile_le {α : Type} (pr : α → Bool) :
    ∀ l : List α, (l.dropWhile pr).length ≤ l.length
  | [] => Nat.le_refl _
  | b :: bs => by
      rw [List.dropWhile_cons]
      by_cases hpb : pr b = true
      · rw [if_pos hpb]; exact Nat.le_trans (length_dropWhile_le pr bs) (Nat.le_succ _)
      · rw [if_neg hpb]; exact Nat.le_refl _

/-- **General single-exp `.2` bound.** For ANY `MultiPoly 2` `r`, the canonical single-exp measure's
x-component `≤ degreeX r + 2`. Same proof as `singleExpMeasureCanon_snd_le` but without the
`leadingCoeffY` wrapper — uses the general `degreeX_canonLcY0_le`. -/
theorem singleExpMeasureCanon_snd_le_gen (r : MultiPoly 2) :
    (singleExpMeasureCanon r).2 ≤ degreeX r + 2 := by
  show polyTrueDegreeStrict (polyCoeffs (multiPolyToPolyForLex (canonLcY0 r))) ≤ degreeX r + 2
  have h1 := polyTrueDegreeStrict_le_length (polyCoeffs (multiPolyToPolyForLex (canonLcY0 r)))
  have h3 := length_polyCoeffs_mP2PFL_le (canonLcY0 r)
  have h2 := degreeX_canonLcY0_le r
  omega

/-- **`cdegY1` refines the syntactic `degreeY₁`** (mirror of `cdegY0_le_degreeY0`). -/
theorem cdegY1_le_degreeY1 (q : MultiPoly 2) :
    cdegY1 q ≤ MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q := by
  unfold cdegY1
  have h1 : ((yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB1).length
      ≤ (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).length :=
    calc ((yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB1).length
          ≤ (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).reverse.length := length_dropWhile_le _ _
      _ = (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).length := List.length_reverse _
  have h2 := yCoeffsAt_length_le (⟨1, by omega⟩ : Fin 2) q
  omega

/-- `canonLcY1 q` is `const 0` or one of `q`'s `y₁`-coefficients. -/
theorem canonLcY1_mem_or_zero (q : MultiPoly 2) :
    canonLcY1 q = MultiPoly.const 0 ∨ canonLcY1 q ∈ yCoeffsAt (⟨1, by omega⟩ : Fin 2) q := by
  unfold canonLcY1
  cases h : (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB1 with
  | nil => left; rfl
  | cons a t =>
      right
      have ha_dw : a ∈ (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).reverse.dropWhile coeffCanonZeroB1 := by
        rw [h]; exact List.mem_cons_self a t
      have ha_rev : a ∈ (yCoeffsAt (⟨1, by omega⟩ : Fin 2) q).reverse :=
        mem_of_mem_dropWhile coeffCanonZeroB1 _ a ha_dw
      exact List.mem_reverse.mp ha_rev

/-- `canonLcY1` does not raise `degreeX`. -/
theorem degreeX_canonLcY1_le (q : MultiPoly 2) :
    MultiPoly.degreeX (canonLcY1 q) ≤ MultiPoly.degreeX q := by
  rcases canonLcY1_mem_or_zero q with h | h
  · rw [h]; exact Nat.zero_le _
  · exact yCoeffsAt_entries_degreeX_le (⟨1, by omega⟩ : Fin 2) q _ h

/-- `canonLcY1` does not raise any `degreeY`. -/
theorem degreeY_canonLcY1_le (jt : Fin 2) (q : MultiPoly 2) :
    MultiPoly.degreeY jt (canonLcY1 q) ≤ MultiPoly.degreeY jt q := by
  rcases canonLcY1_mem_or_zero q with h | h
  · rw [h]; exact Nat.zero_le _
  · exact yCoeffsAt_entries_degreeY_le jt (⟨1, by omega⟩ : Fin 2) q _ h

end MachLib.IterExpDepthN
