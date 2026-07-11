import MachLib.PfaffianGeneralBound2
import MachLib.PfaffianGeneralRankRecAlpha
import MachLib.PfaffianGeneralFormat2
import MachLib.ChainExp2ExplicitFinal

/-!
# The general order-2 Pfaffian EXPLICIT bound (WIP assembly)

Making `pfaffian_bound2_gen` (`∃N`) explicit. The α-budget stack being complete, the assembly collapses:
since `chain2MeasureCanon : Nat × (Nat × Nat) = NestedNat 2` and `nestedLT = nestedOrder 2` (both
`LexProd (·<·) (LexProd (·<·) (·<·))`), and `rankRecA_drop` gives the `≥α` drop on ANY `nestedOrder`
step under `≤α` growth (reduce AND trim), the invariant is a single term:

    zeros.length ≤ rankRecA α 2 (Bcap q) (chain2MeasureCanon q)

with `α := max-format + 1` (≥1, ≥ every per-reduce degree growth) and `Bcap q := max(degreeY₁, degreeY₀,
degreeX) q + 2` (bounds every measure digit; grows ≤α per reduce, non-increasing on trim). Each arm:
reduce/trim → `rankRecA_drop` (`rankRecA child + α ≤ rankRecA p`, so `+1` for the Rolle count since
`α≥1`); vehicle → 0; contradiction → `p≡0` vs `hne`.

STATUS: WIP. The architecture + the `rankRecA_drop` wiring are the point; the per-reduce degree-growth
of the specific multiplier `bound2Mult` and the digit bounds are the remaining obligations (marked).
-/

namespace MachLib.PfaffianGeneralVehExpo

open MachLib.Real MachLib.PfaffianChainMod MachLib.MultiPolyMod
open MachLib.PfaffianGeneralReduce MachLib.ChainExp2CanonMeasure MachLib.IterExpTopIdentity
open MachLib.ChainExp2NoZeros MachLib.ChainExp2Capstone MachLib.ChainExp2Trim
open MachLib.MultiPolyMod.MultiPoly
open MachLib.IterExpDepthN MachLib.ExplicitBound
open MachLib.ChainExp2Explicit
open MachLib.PfaffianChainMod.PfaffianFn (formatX2 formatY2)

/-- The order-2 format cap: `≥ 1` and `≥` every per-reduce degree growth (x and both y-levels). -/
noncomputable def α2 (c2 : PfaffianChain 2) : Nat :=
  Nat.max (Nat.max (formatX2 c2) (formatY2 c2 (⟨0, by omega⟩ : Fin 2)))
          (formatY2 c2 (⟨1, by omega⟩ : Fin 2)) + 1

theorem one_le_α2 (c2 : PfaffianChain 2) : 1 ≤ α2 c2 := Nat.le_add_left 1 _

/-- The order-2 digit cap: bounds every digit of `chain2MeasureCanon` (`degreeY₁`, `cdegY0 ≤ degreeY₀`,
`b ≤ degreeX+2`). -/
noncomputable def Bcap2 (q : MultiPoly 2) : Nat :=
  Nat.max (Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q)
                   (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q))
          (MultiPoly.degreeX q) + 2

/-- **The explicit order-2 bound**, as a `rankRecA` of the canonical measure. -/
noncomputable def Ngen2 (c2 : PfaffianChain 2) (q : MultiPoly 2) : Nat :=
  rankRecA (α2 c2) 2 (Bcap2 q) (chain2MeasureCanon q)

/-- **`Ngen2` drops by `≥ α` on a `nestedOrder` measure step** (reduce or trim) under `≤α` degree
growth — the one fact every arm consumes. Wraps `rankRecA_drop` with the digit-bound / growth
obligations. -/
theorem Ngen2_drop (c2 : PfaffianChain 2) (p q : MultiPoly 2)
    (hgrow : Bcap2 q ≤ Bcap2 p + α2 c2)
    (hle : nestedLe 2 (chain2MeasureCanon q) (allBNested 2 (Bcap2 q)))
    (hstep : nestedOrder 2 (chain2MeasureCanon q) (chain2MeasureCanon p)) :
    Ngen2 c2 q + α2 c2 ≤ Ngen2 c2 p :=
  rankRecA_drop (α2 c2) 2 (Bcap2 p) (Bcap2 q) (chain2MeasureCanon p) (chain2MeasureCanon q)
    hgrow hle hstep

/-- Digit bounds: every digit of `chain2MeasureCanon q` is `≤ Bcap2 q` (so `hle` of `Ngen2_drop`).
`degreeY₁ ≤ Bcap`, `cdegY0(lcY₁) ≤ degreeY₀ ≤ Bcap`, `b ≤ degreeX+2 ≤ Bcap`. -/
theorem measure_le_Bcap2 (q : MultiPoly 2) :
    nestedLe 2 (chain2MeasureCanon q) (allBNested 2 (Bcap2 q)) := by
  -- chain2MeasureCanon q = (degreeY₁ q, (cdegY0(lcY₁ q), b q)); allBNested 2 B = (B,(B,B))
  refine ⟨?_, ?_, ?_⟩
  · show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q ≤ Bcap2 q
    show MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q
        ≤ Nat.max (Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q)
            (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)) (MultiPoly.degreeX q) + 2
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ 2))
  · -- (singleExpMeasureCanon (lcY₁ q)).1 = cdegY0(lcY₁ q) ≤ degreeY₀ q ≤ Bcap2 q
    have hcd : cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)
        ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q := cdegY0_lcY1_le_degreeY0 q
    have hd0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q ≤ Bcap2 q :=
      Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ 2))
    show cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q) ≤ Bcap2 q
    exact Nat.le_trans hcd hd0
  · -- b q ≤ degreeX q + 2 ≤ Bcap2 q
    have hb : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2
        ≤ MultiPoly.degreeX q + 2 := singleExpMeasureCanon_snd_le q
    show (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 ≤ Bcap2 q
    show (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2
        ≤ Nat.max (Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q)
            (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)) (MultiPoly.degreeX q) + 2
    have : MultiPoly.degreeX q + 2
        ≤ Nat.max (Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q)
            (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) q)) (MultiPoly.degreeX q) + 2 :=
      Nat.add_le_add_right (Nat.le_max_right _ _) 2
    exact Nat.le_trans hb this

/-- **The reduce multiplier `bound2Mult` is `degreeX`-format-bounded.**
`bound2Mult G0 G1 p = (natCast degreeY₁ p)·G1 + (natCast cdegY0)·G0`, so `degreeX = max(degreeX G0,
degreeX G1)`; and `degreeX G = degreeX (G·varY) = degreeX (relations …) ≤ formatX2` (the `varY` factor is
x-free). This discharges the `h_m` of `degreeX_chainReduce_le_format` for the descent reduce. -/
theorem degreeX_bound2Mult_le (c2 : PfaffianChain 2) (G0 G1 p : MultiPoly 2)
    (hrel0 : c2.relations (⟨0, by omega⟩ : Fin 2)
      = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hrel1 : c2.relations (⟨1, by omega⟩ : Fin 2)
      = MultiPoly.mul G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2))) :
    MultiPoly.degreeX (bound2Mult G0 G1 p)
      ≤ MachLib.PfaffianChainMod.PfaffianFn.formatX2 c2 := by
  have hG0 : MultiPoly.degreeX G0
      ≤ MachLib.PfaffianChainMod.PfaffianFn.formatX2 c2 := by
    have h := MachLib.PfaffianChainMod.PfaffianFn.relations_degreeX_le_formatX2 c2
      (⟨0, by omega⟩ : Fin 2)
    rw [hrel0] at h
    -- degreeX (mul G0 (varY 0)) = degreeX G0 + 0
    show MultiPoly.degreeX G0 ≤ _
    have he : MultiPoly.degreeX (MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
        = MultiPoly.degreeX G0 := by
      show MultiPoly.degreeX G0 + MultiPoly.degreeX (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
          = MultiPoly.degreeX G0
      rw [MultiPoly.degreeX_varY, Nat.add_zero]
    rw [he] at h; exact h
  have hG1 : MultiPoly.degreeX G1
      ≤ MachLib.PfaffianChainMod.PfaffianFn.formatX2 c2 := by
    have h := MachLib.PfaffianChainMod.PfaffianFn.relations_degreeX_le_formatX2 c2
      (⟨1, by omega⟩ : Fin 2)
    rw [hrel1] at h
    show MultiPoly.degreeX G1 ≤ _
    have he : MultiPoly.degreeX (MultiPoly.mul G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)))
        = MultiPoly.degreeX G1 := by
      show MultiPoly.degreeX G1 + MultiPoly.degreeX (MultiPoly.varY (⟨1, by omega⟩ : Fin 2))
          = MultiPoly.degreeX G1
      rw [MultiPoly.degreeX_varY, Nat.add_zero]
    rw [he] at h; exact h
  -- degreeX (bound2Mult) = max (degreeX G1) (degreeX G0)
  show MultiPoly.degreeX
      (MultiPoly.add
        (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast
          (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p))) G1)
        (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast
          (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)))) G0))
      ≤ MachLib.PfaffianChainMod.PfaffianFn.formatX2 c2
  show Nat.max
      (MultiPoly.degreeX (MultiPoly.const _) + MultiPoly.degreeX G1)
      (MultiPoly.degreeX (MultiPoly.const _) + MultiPoly.degreeX G0)
      ≤ MachLib.PfaffianChainMod.PfaffianFn.formatX2 c2
  rw [MultiPoly.degreeX_const, MultiPoly.degreeX_const]
  exact Nat.max_le.mpr ⟨by omega, by omega⟩

end MachLib.PfaffianGeneralVehExpo
