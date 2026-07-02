import MachLib.IterExpDepthNDescentD
import MachLib.IterExpDepthNBaseReduce
import MachLib.MultiPolyLiftLastY

/-!
# Phase C, CLOSED — the reduce-descent `D(k)` for every depth (∀N)

Everything is now in hand to run the descent induction:

* `fullMult k q` — the **recursive graded multiplier**: the depth-2 base multiplier at `k=0`, and at
  `k+1` the top graded term `gradedTop` plus the *lifted* (`liftLastY`) lower multiplier for the projected
  leading coefficient. Its `dropLastY` recovers the lower multiplier (`dropLastY_liftLastY`), which is
  exactly what the D-step's inner reduce needs.
* `Reducing k q` — the **recursive reducing predicate**: the depth-2 conditions at `k=0`; at `k+1`,
  non-phantom top + positive top degree + `Reducing` of the projected leading coefficient (so the
  inductive hypothesis applies to the inner polynomial).
* `chainNReduce_descends` — **the payoff**: for a reducing `q`, the reduce with the full graded multiplier
  strictly lowers `chainNMeasureEI k`, for **every depth `k`**. Base = `chainNReduce_evalinv_descent_base`
  (the transported depth-2 descent); step = `chainNReduce_evalinv_descent` (the D-step) fed the inductive
  hypothesis via `dropLastY_liftLastY`.

This is the ∀N reduce-descent — the last mechanical piece of the tower's well-founded step. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.IterExpDepthNReduce
open MachLib.ChainExp2CanonMeasure
open MachLib.IterExpDepth3CdegY1

/-- The recursive full graded multiplier for the depth-`(k+2)` reduce. -/
noncomputable def fullMult : (k : Nat) → MultiPoly (k + 2) → MultiPoly (k + 2)
  | 0 => fun q =>
      MultiPoly.add (gradedTop 0 (⟨1, by omega⟩ : Fin 2) q)
        (MultiPoly.const (MachLib.Real.natCast
          (cdegY0 (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q))))
  | k + 1 => fun q =>
      MultiPoly.add (gradedTop (k + 1) (⟨k + 2, by omega⟩ : Fin (k + 3)) q)
        (liftLastY (fullMult k (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))))

/-- The recursive reducing predicate for `MultiPoly (k+2)`. -/
def Reducing : (k : Nat) → MultiPoly (k + 2) → Prop
  | 0 => fun q =>
      coeffCanonZeroB1 (y1top q) = false
      ∧ 0 < MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) q
      ∧ (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 ≠ 0
  | k + 1 => fun q =>
      canonZeroB (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) q) = false
      ∧ 0 < MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q
      ∧ Reducing k (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))

/-- **The ∀N reduce-descent.** For a reducing `q`, the reduce with the full graded multiplier strictly
lowers the eval-invariant measure, at every depth. -/
theorem chainNReduce_descends : ∀ (k : Nat) (q : MultiPoly (k + 2)), Reducing k q →
    nestedOrder (k + 2) (chainNMeasureEI k (chainNReduce k (fullMult k q) q)) (chainNMeasureEI k q)
  | 0, q, hred => by
      simp only [fullMult]
      exact chainNReduce_evalinv_descent_base q hred.1 hred.2.1 hred.2.2
  | k + 1, q, hred => by
      simp only [fullMult]
      have hInner :
          nestedOrder (k + 2)
            (chainNMeasureEI k (chainNReduce k
              (MultiPoly.dropLastY (liftLastY (fullMult k
                (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)))))
              (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))))
            (chainNMeasureEI k
              (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))) := by
        rw [dropLastY_liftLastY]
        exact chainNReduce_descends k
          (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))
          hred.2.2
      exact chainNReduce_evalinv_descent k (⟨k + 2, by omega⟩ : Fin (k + 3)) rfl
        (liftLastY (fullMult k (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)))) q
        (degreeY_top_liftLastY _) hred.1 hred.2.1 hInner

end MachLib.IterExpDepthN
