import MachLib.IterExpDepthNEIBase
import MachLib.IterExpDepthNRankNested
import MachLib.IterExpDepthNMeasureEI
import MachLib.IterExpDepthNDegreeX
import MachLib.IterExpDepthNDegreeY
import MachLib.IterExpDepthNAssembly
import MachLib.IterExpDepthNDescentInduction
import MachLib.PfaffianLogCdegSpike

/-!
# `EIrank` — the deep inner rank is bounded (step 3 of the chain-N explicit bound)

`EIrank m B q := rankNested (chainNMeasureEI m q)` against the all-`B` bound vector — the linearization of
the M5⁺ inner measure (design doc §4′). This file proves it is **bounded** (`≤ maxRank (allBNested B)`)
whenever `B` bounds `q`'s degrees, via the recursive `nestedLe (chainNMeasureEI m q ≤ allBNested B)`:

  * base (`m=0`, `chain2MeasureCanonEvalInv`): `cdegY1 ≤ degreeY₁ ≤ B`, `cdegY0(canonLcY1) ≤ degreeY₀ ≤ B`,
    `b(canonLcY1) ≤ degreeX+2 ≤ B` (the base bounds from `IterExpDepthNEIBase`);
  * step: `cdegYAt ⟨top⟩ q ≤ degreeY ⟨top⟩ q ≤ B` (`cdegYAt_le_degreeYAt`), then recurse into
    `dropLastY(canonLcYAt ⟨top⟩ q)` whose degrees stay `≤ B` (the `canonLcYAt` bounds + `dropLastY`
    degree-preservation).

`EIrank`-DROPS-on-reduce (the other half, from `chainNReduce_order5p_hnz`'s `nestedOrder` drop +
`rankNested_lt`) is the next brick.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.ExplicitBound
open MachLib.ChainExp2CanonMeasure
open MachLib.IterExpDepth3CdegY1
open MachLib.PfaffianLogLead
open MachLib.IterExpDepthNReduce

/-- The all-`B` bound vector: every level's bound is `B`. -/
def allBNested : (n : Nat) → Nat → NestedNat n
  | 0, B => B
  | k + 1, B => (B, allBNested k B)

/-- **The chain-N inner measure is bounded componentwise by `B`** whenever `B ≥ degreeX q + 2` and
`B ≥ every degreeY`. Recursion on depth: the head is a canonical `y`-degree `≤` a syntactic one `≤ B`; the
tail recurses into `dropLastY(canonLcYAt)`, whose degrees are `≤ q`'s (hence `≤ B`). -/
theorem chainNMeasureEI_le_allB : ∀ (m : Nat) (q : MultiPoly (m + 2)) (B : Nat),
    MultiPoly.degreeX q + 2 ≤ B → (∀ i : Fin (m + 2), MultiPoly.degreeY i q ≤ B) →
    nestedLe (m + 2) (chainNMeasureEI m q) (allBNested (m + 2) B)
  | 0, q, B, hx, hy => by
      refine ⟨?_, ?_, ?_⟩
      · exact Nat.le_trans (cdegY1_le_degreeY1 q) (hy (⟨1, by omega⟩ : Fin 2))
      · exact Nat.le_trans (cdegY0_le_degreeY0 (canonLcY1 q))
          (Nat.le_trans (degreeY_canonLcY1_le (⟨0, by omega⟩ : Fin 2) q) (hy (⟨0, by omega⟩ : Fin 2)))
      · exact Nat.le_trans (singleExpMeasureCanon_snd_le_gen (canonLcY1 q))
          (Nat.le_trans (Nat.add_le_add_right (degreeX_canonLcY1_le q) 2) hx)
  | m + 1, q, B, hx, hy => by
      refine ⟨Nat.le_trans (cdegYAt_le_degreeYAt (⟨m + 2, by omega⟩ : Fin (m + 3)) q)
                (hy (⟨m + 2, by omega⟩ : Fin (m + 3))), ?_⟩
      refine chainNMeasureEI_le_allB m
        (MultiPoly.dropLastY (canonLcYAt (⟨m + 2, by omega⟩ : Fin (m + 3)) q)) B ?_ ?_
      · have hdx : MultiPoly.degreeX (MultiPoly.dropLastY
            (canonLcYAt (⟨m + 2, by omega⟩ : Fin (m + 3)) q)) ≤ MultiPoly.degreeX q :=
          Nat.le_trans (Nat.le_of_eq (degreeX_dropLastY _)) (degreeX_canonLcYAt_le _ q)
        omega
      · intro i
        rw [degreeY_dropLastY_eq_prev (m + 2)
            (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 3)) i rfl]
        exact Nat.le_trans (degreeY_canonLcYAt_le (⟨m + 2, by omega⟩ : Fin (m + 3))
            (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 3)) q)
          (hy (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (m + 3)))

/-- The deep inner rank: `chainNMeasureEI` linearized against the all-`B` bound vector. -/
noncomputable def EIrank (m B : Nat) (q : MultiPoly (m + 2)) : Nat :=
  rankNested (m + 2) (allBNested (m + 2) B) (chainNMeasureEI m q)

/-- **`EIrank` is bounded** by `maxRank (allBNested B)` whenever `B` bounds `q`'s degrees. -/
theorem EIrank_le_maxRank (m B : Nat) (q : MultiPoly (m + 2))
    (hx : MultiPoly.degreeX q + 2 ≤ B) (hy : ∀ i : Fin (m + 2), MultiPoly.degreeY i q ≤ B) :
    EIrank m B q ≤ maxRank (m + 2) (allBNested (m + 2) B) :=
  rankNested_le_maxRank (m + 2) (allBNested (m + 2) B) (chainNMeasureEI m q)
    (chainNMeasureEI_le_allB m q B hx hy)

/-- **`EIrank` strictly drops on a reduce** — the other half of step 3, the count-carrying descent. For a
`Reducing k q`, the reduce with the full graded multiplier lowers `chainNMeasureEI` in `nestedOrder`
(`chainNReduce_descends`), and the reduced poly's degrees stay `≤ B` (degreeX non-increasing, degreeY
`≤ +1`/reduce — the `B ≥ degreeY + 1` slack absorbs it), so `rankNested_lt` gives the strict `EIrank` drop. -/
theorem EIrank_reduce_lt (k B : Nat) (q : MultiPoly (k + 2)) (hred : Reducing k q)
    (hx : MultiPoly.degreeX q + 2 ≤ B) (hy : ∀ i : Fin (k + 2), MultiPoly.degreeY i q + 1 ≤ B) :
    EIrank k B (chainNReduce k (fullMult k q) q) < EIrank k B q := by
  unfold EIrank
  refine rankNested_lt (k + 2) (allBNested (k + 2) B) (chainNMeasureEI k q)
    (chainNMeasureEI k (chainNReduce k (fullMult k q) q)) ?_ (chainNReduce_descends k q hred)
  refine chainNMeasureEI_le_allB k (chainNReduce k (fullMult k q) q) B ?_ ?_
  · exact Nat.le_trans (Nat.add_le_add_right (degreeX_chainNReduce_fullMult_le k q) 2) hx
  · intro i
    exact Nat.le_trans (degreeY_chainNReduce_fullMult_growth_le k q i) (hy i)

end MachLib.IterExpDepthN
