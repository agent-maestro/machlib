import MachLib.PfaffianGeneralBound2
import MachLib.PfaffianGeneralRankRecAlpha
import MachLib.PfaffianGeneralFormat2
import MachLib.PfaffianGeneralFormatDegree
import MachLib.ChainExp2ExplicitFinal
import MachLib.IterExpDepthNTrimQDegHelpers

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
open MachLib.MultiPolyReconstruct
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

/-- **The reduce multiplier `bound2Mult` is `degreeY i`-format-bounded.** Parallel to the `degreeX`
version; here `degreeY i G ≤ degreeY i (G·varY) = degreeY i (relations …) ≤ formatY2` (the `varY` factor
only *raises* `degreeY`, so `G`'s `degreeY` is `≤` the relation's). Discharges the `h_m` of
`degreeY_chainReduce_le_format`. -/
theorem degreeY_bound2Mult_le (c2 : PfaffianChain 2) (G0 G1 p : MultiPoly 2) (i : Fin 2)
    (hrel0 : c2.relations (⟨0, by omega⟩ : Fin 2)
      = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hrel1 : c2.relations (⟨1, by omega⟩ : Fin 2)
      = MultiPoly.mul G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2))) :
    MultiPoly.degreeY i (bound2Mult G0 G1 p)
      ≤ MachLib.PfaffianChainMod.PfaffianFn.formatY2 c2 i := by
  have hG0 : MultiPoly.degreeY i G0
      ≤ MachLib.PfaffianChainMod.PfaffianFn.formatY2 c2 i := by
    have h := MachLib.PfaffianChainMod.PfaffianFn.relations_degreeY_le_formatY2 c2 i
      (⟨0, by omega⟩ : Fin 2)
    rw [hrel0] at h
    refine Nat.le_trans ?_ h
    show MultiPoly.degreeY i G0
        ≤ MultiPoly.degreeY i G0 + MultiPoly.degreeY i (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))
    exact Nat.le_add_right _ _
  have hG1 : MultiPoly.degreeY i G1
      ≤ MachLib.PfaffianChainMod.PfaffianFn.formatY2 c2 i := by
    have h := MachLib.PfaffianChainMod.PfaffianFn.relations_degreeY_le_formatY2 c2 i
      (⟨1, by omega⟩ : Fin 2)
    rw [hrel1] at h
    refine Nat.le_trans ?_ h
    show MultiPoly.degreeY i G1
        ≤ MultiPoly.degreeY i G1 + MultiPoly.degreeY i (MultiPoly.varY (⟨1, by omega⟩ : Fin 2))
    exact Nat.le_add_right _ _
  show MultiPoly.degreeY i
      (MultiPoly.add
        (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast
          (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p))) G1)
        (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast
          (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)))) G0))
      ≤ MachLib.PfaffianChainMod.PfaffianFn.formatY2 c2 i
  show Nat.max
      (MultiPoly.degreeY i (MultiPoly.const _) + MultiPoly.degreeY i G1)
      (MultiPoly.degreeY i (MultiPoly.const _) + MultiPoly.degreeY i G0)
      ≤ MachLib.PfaffianChainMod.PfaffianFn.formatY2 c2 i
  rw [MultiPoly.degreeY_const, MultiPoly.degreeY_const]
  exact Nat.max_le.mpr ⟨by omega, by omega⟩

theorem formatX2_le_α2 (c2 : PfaffianChain 2) :
    MachLib.PfaffianChainMod.PfaffianFn.formatX2 c2 ≤ α2 c2 :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _))

theorem formatY2_0_le_α2 (c2 : PfaffianChain 2) :
    MachLib.PfaffianChainMod.PfaffianFn.formatY2 c2 (⟨0, by omega⟩ : Fin 2) ≤ α2 c2 :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _))

theorem formatY2_1_le_α2 (c2 : PfaffianChain 2) :
    MachLib.PfaffianChainMod.PfaffianFn.formatY2 c2 (⟨1, by omega⟩ : Fin 2) ≤ α2 c2 :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)

/-- **`Bcap2` grows by `≤ α2` under the descent reduce** (the `hgrow` of `Ngen2_drop`, reduce arm). Every
degree grows by `≤ format ≤ α2` (`degreeX/Y_chainReduce_le_format` + the `bound2Mult` bounds), so the
max grows by `≤ α2`. -/
theorem Bcap2_growth_reduce (c2 : PfaffianChain 2) (G0 G1 p : MultiPoly 2)
    (hrel0 : c2.relations (⟨0, by omega⟩ : Fin 2)
      = MultiPoly.mul G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2)))
    (hrel1 : c2.relations (⟨1, by omega⟩ : Fin 2)
      = MultiPoly.mul G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2))) :
    Bcap2 (chainReduce c2 (bound2Mult G0 G1 p) p) ≤ Bcap2 p + α2 c2 := by
  have hx := MachLib.PfaffianChainMod.PfaffianFn.degreeX_chainReduce_le_format c2
    (MachLib.PfaffianChainMod.PfaffianFn.formatX2 c2) (bound2Mult G0 G1 p) p
    (MachLib.PfaffianChainMod.PfaffianFn.relations_degreeX_le_formatX2 c2)
    (degreeX_bound2Mult_le c2 G0 G1 p hrel0 hrel1)
  have hy0 := MachLib.PfaffianChainMod.PfaffianFn.degreeY_chainReduce_le_format c2
    (⟨0, by omega⟩ : Fin 2) (MachLib.PfaffianChainMod.PfaffianFn.formatY2 c2 (⟨0, by omega⟩ : Fin 2))
    (bound2Mult G0 G1 p) p
    (MachLib.PfaffianChainMod.PfaffianFn.relations_degreeY_le_formatY2 c2 (⟨0, by omega⟩ : Fin 2))
    (degreeY_bound2Mult_le c2 G0 G1 p (⟨0, by omega⟩ : Fin 2) hrel0 hrel1)
  have hy1 := MachLib.PfaffianChainMod.PfaffianFn.degreeY_chainReduce_le_format c2
    (⟨1, by omega⟩ : Fin 2) (MachLib.PfaffianChainMod.PfaffianFn.formatY2 c2 (⟨1, by omega⟩ : Fin 2))
    (bound2Mult G0 G1 p) p
    (MachLib.PfaffianChainMod.PfaffianFn.relations_degreeY_le_formatY2 c2 (⟨1, by omega⟩ : Fin 2))
    (degreeY_bound2Mult_le c2 G0 G1 p (⟨1, by omega⟩ : Fin 2) hrel0 hrel1)
  have hfx := formatX2_le_α2 c2
  have hfy0 := formatY2_0_le_α2 c2
  have hfy1 := formatY2_1_le_α2 c2
  have b1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (chainReduce c2 (bound2Mult G0 G1 p) p)
      ≤ MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p + α2 c2 := by omega
  have b0 : MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainReduce c2 (bound2Mult G0 G1 p) p)
      ≤ MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p + α2 c2 := by omega
  have bX : MultiPoly.degreeX (chainReduce c2 (bound2Mult G0 G1 p) p)
      ≤ MultiPoly.degreeX p + α2 c2 := by omega
  have hkey : Nat.max (Nat.max
        (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (chainReduce c2 (bound2Mult G0 G1 p) p))
        (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainReduce c2 (bound2Mult G0 G1 p) p)))
        (MultiPoly.degreeX (chainReduce c2 (bound2Mult G0 G1 p) p))
      ≤ Nat.max (Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
        (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p)) (MultiPoly.degreeX p) + α2 c2 := by
    apply Nat.max_le.mpr
    refine ⟨Nat.max_le.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Nat.le_trans b1 (Nat.add_le_add_right
        (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) _)
    · exact Nat.le_trans b0 (Nat.add_le_add_right
        (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) _)
    · exact Nat.le_trans bX (Nat.add_le_add_right (Nat.le_max_right _ _) _)
  show Nat.max (Nat.max
        (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (chainReduce c2 (bound2Mult G0 G1 p) p))
        (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (chainReduce c2 (bound2Mult G0 G1 p) p)))
        (MultiPoly.degreeX (chainReduce c2 (bound2Mult G0 G1 p) p)) + 2
      ≤ Nat.max (Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
        (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p)) (MultiPoly.degreeX p) + 2 + α2 c2
  omega

/-- **`Bcap2` is non-increasing under the descent trim.** `dropLeadingYAt ⟨1⟩` lowers `degreeY₁` and
doesn't raise `degreeY₀`/`degreeX`, so every digit — hence `Bcap2` — is `≤`. (`≤ Bcap2 p ≤ Bcap2 p + α2`
gives the `hgrow` of `Ngen2_drop` in the trim arm.) -/
theorem Bcap2_growth_trim (p : MultiPoly 2)
    (hpos : 0 < MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p) :
    Bcap2 (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p) ≤ Bcap2 p := by
  have hx : MultiPoly.degreeX (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p) ≤ MultiPoly.degreeX p :=
    degreeX_dropLeadingYAt_le (⟨1, by omega⟩ : Fin 2) p
  have hy := degreeY_dropLeadingYAt_le_all (⟨1, by omega⟩ : Fin 2) p hpos
  have hy0 := hy (⟨0, by omega⟩ : Fin 2)
  have hy1 := hy (⟨1, by omega⟩ : Fin 2)
  have hkey : Nat.max (Nat.max
        (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p))
        (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)))
        (MultiPoly.degreeX (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p))
      ≤ Nat.max (Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
        (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p)) (MultiPoly.degreeX p) := by
    apply Nat.max_le.mpr
    refine ⟨Nat.max_le.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Nat.le_trans hy1 (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    · exact Nat.le_trans hy0 (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
    · exact Nat.le_trans hx (Nat.le_max_right _ _)
  show Nat.max (Nat.max
        (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p))
        (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)))
        (MultiPoly.degreeX (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)) + 2
      ≤ Nat.max (Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
        (MultiPoly.degreeY (⟨0, by omega⟩ : Fin 2) p)) (MultiPoly.degreeX p) + 2
  omega

set_option maxHeartbeats 2000000 in
/-- **The general order-2 Pfaffian EXPLICIT Khovanskii bound.** For a positive-coherent exp-chain `c2`
of depth 2, any `p0` not identically vanishing on `(a,b)` has `≤ Ngen2 c2 p0` zeros there — the explicit
`N` (a `rankRecA` of the canonical measure, format-parameterised) making `pfaffian_bound2_gen` effective.
Same WF recursion + 4-arm dispatch, carrying the `Ngen2` invariant instead of `∃N`; every arm's measure
step feeds `Ngen2_drop` (the cracked nut), the reduce arm's Rolle `+1` absorbed since `α2 ≥ 1`. -/
theorem pfaffian_bound2_gen_explicit (c2 : PfaffianChain 2) (hexp : IsExpChain c2) (a b : Real)
    (hab : a < b) (hcoh : c2.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin 2, 0 < c2.evals i z)
    (p0 : MultiPoly 2) (hne0 : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c2 p0).eval z ≠ 0) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c2 p0).eval z = 0) →
      zeros.length ≤ Ngen2 c2 p0 := by
  obtain ⟨⟨G0, hG0, hrel0⟩, htri0⟩ := hexp (⟨0, by omega⟩ : Fin 2)
  obtain ⟨⟨G1, hG1, hrel1⟩, _⟩ := hexp (⟨1, by omega⟩ : Fin 2)
  have hG0y1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) G0 = 0 := by
    have h := htri0 (⟨1, by omega⟩ : Fin 2) Nat.zero_lt_one
    rw [hrel0, degreeY_mul' (⟨1, by omega⟩ : Fin 2) G0 (MultiPoly.varY (⟨0, by omega⟩ : Fin 2))] at h
    omega
  have htri1 : ∀ (j : Fin 2), j ≠ (⟨1, by omega⟩ : Fin 2) →
      MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (c2.relations j) = 0 := by
    intro j hj
    have hj0 : j = (⟨0, by omega⟩ : Fin 2) := by
      apply Fin.ext; show j.val = 0; have := j.isLt
      have hne1 : j.val ≠ 1 := fun h => hj (Fin.ext h)
      omega
    rw [hj0]; exact htri0 (⟨1, by omega⟩ : Fin 2) Nat.zero_lt_one
  have hreltop1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2)
      (c2.relations (⟨1, by omega⟩ : Fin 2)) = 1 := by
    rw [hrel1, degreeY_mul' (⟨1, by omega⟩ : Fin 2) G1 (MultiPoly.varY (⟨1, by omega⟩ : Fin 2)), hG1]
    show 0 + (if (⟨1, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) then 1 else 0) = 1
    rw [if_pos rfl]
  refine WellFounded.induction
    (C := fun q => (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c2 q).eval z ≠ 0) →
      ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c2 q).eval z = 0) → zeros.length ≤ Ngen2 c2 q)
    chain2OrderCanon_wf p0 ?_ hne0
  clear hne0 p0
  intro p ih hne zeros hnd hz
  by_cases hcz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)).2 = 0
  · by_cases hd1 : MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p = 0
    · -- contradiction: degreeY₁ = 0 ∧ lcY₁ canon-zero ⟹ p ≡ 0
      exfalso
      have hlcp : MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p = p :=
        leadingCoeffY_eq_self_of_degreeY_zero (⟨1, by omega⟩ : Fin 2) p hd1
      have hpz : ∀ (x : Real) (env : Fin 2 → Real), MultiPoly.eval p x env = 0 := by
        have h := smc2_zero_eval_zero (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)
          (MultiPoly.degreeY_leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) hcz
        rw [hlcp] at h; exact h
      obtain ⟨z, _, _, hzne⟩ := hne
      exact hzne (hpz z (c2.chainValues z))
    · -- trim
      have hlast : ∀ (x : Real) (env : Fin 2 → Real),
          MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨1, by omega⟩ : Fin 2) p).getLast
            (yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) p)) x env = 0 := by
        intro x env
        rw [← eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general (⟨1, by omega⟩ : Fin 2) p
              (yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) p) x env]
        exact smc2_zero_eval_zero (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)
          (MultiPoly.degreeY_leadingCoeffY (⟨1, by omega⟩ : Fin 2) p) hcz x env
      have htrim_eval : ∀ z, (pfaffianChainFn c2 p).eval z
          = (pfaffianChainFn c2 (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)).eval z := fun z =>
        (eval_dropLeadingYAt_of_last_canonically_zero (⟨1, by omega⟩ : Fin 2) p
          (yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) p) hlast z (c2.chainValues z)).symm
      have hne_trim : ∃ z, a < z ∧ z < b ∧
          (pfaffianChainFn c2 (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)).eval z ≠ 0 := by
        obtain ⟨z, hza, hzb, hzne⟩ := hne
        exact ⟨z, hza, hzb, by rw [← htrim_eval z]; exact hzne⟩
      have hzeros' : ∀ z ∈ zeros, a < z ∧ z < b ∧
          (pfaffianChainFn c2 (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)).eval z = 0 := fun z hzmem => by
        obtain ⟨ha, hb', hzero⟩ := hz z hzmem
        exact ⟨ha, hb', by rw [← htrim_eval z]; exact hzero⟩
      have hN := ih (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p) (chain2_trim_order p hd1)
        hne_trim zeros hnd hzeros'
      have hdrop := Ngen2_drop c2 p (dropLeadingYAt (⟨1, by omega⟩ : Fin 2) p)
        (Nat.le_trans (Bcap2_growth_trim p (Nat.pos_of_ne_zero hd1)) (Nat.le_add_right _ _))
        (measure_le_Bcap2 _) (chain2_trim_order p hd1)
      omega
  · rcases Classical.em (∀ z, a < z → z < b →
        (pfaffianChainFn c2 (chainReduce c2 (bound2Mult G0 G1 p) p)).eval z = 0) with hrz | hrz
    · -- vehicle: reduce ≡ 0 ⟹ p has no zeros
      obtain ⟨z₀, hz₀a, hz₀b, hz₀ne⟩ := hne
      have hnoz := pfaffianChainFn_no_zeros_of_reduct_zero_gen c2 (bound2Mult G0 G1 p) p a b hab
        (logVehExpoAux c2 (bound2Deg p) 2 (Nat.le_refl 2)) hcoh
        (hE_vehExpo_bound2 G0 G1 p a b hrel0 hrel1 hcoh hpos) hrz z₀ hz₀a hz₀b hz₀ne
      cases zeros with
      | nil => exact Nat.zero_le _
      | cons z zs =>
        obtain ⟨ha, hb', hzero⟩ := hz z (List.mem_cons_self _ _)
        exact absurd hzero (hnoz z ha hb')
    · -- reduce: recurse + Rolle +1
      have hnz : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) p)).2 ≠ 0 := hcz
      have hne' : ∃ z, a < z ∧ z < b ∧
          (pfaffianChainFn c2 (chainReduce c2 (bound2Mult G0 G1 p) p)).eval z ≠ 0 :=
        Classical.byContradiction fun hcon =>
          hrz fun z hza hzb => Classical.byContradiction fun hz0 => hcon ⟨z, hza, hzb, hz0⟩
      have hN := ih (chainReduce c2 (bound2Mult G0 G1 p) p)
        (chain2ReduceGen_nestedLT_canon_hnz G0 G1 hrel0 hG0 hG0y1 hrel1 hG1 htri1 hreltop1 p hnz) hne'
      have hstep := pfaffianChainFn_reduce_step_gen c2 (bound2Mult G0 G1 p) p a b hab
        (logVehExpoAux c2 (bound2Deg p) 2 (Nat.le_refl 2)) hcoh
        (hE_vehExpo_bound2 G0 G1 p a b hrel0 hrel1 hcoh hpos)
        (Ngen2 c2 (chainReduce c2 (bound2Mult G0 G1 p) p)) hN zeros hnd hz
      -- hstep : zeros.length ≤ Ngen2 c2 (reduce) + 1
      have hdrop := Ngen2_drop c2 p (chainReduce c2 (bound2Mult G0 G1 p) p)
        (Bcap2_growth_reduce c2 G0 G1 p hrel0 hrel1)
        (measure_le_Bcap2 _)
        (chain2ReduceGen_nestedLT_canon_hnz G0 G1 hrel0 hG0 hG0y1 hrel1 hG1 htri1 hreltop1 p hnz)
      have hα := one_le_α2 c2
      omega

end MachLib.PfaffianGeneralVehExpo
