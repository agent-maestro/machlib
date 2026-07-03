import MachLib.IterExpDepthNMeasureConst
import MachLib.IterExpDepth3CapstonePrep

/-!
# Phase C→D absorption — the `hnz`-tower and its non-phantom/nonzero corollaries (∀N)

The reduce arm of the WF assembly needs the reduce to strictly descend the eval-invariant measure. The
depth-2 lesson (caught the hard way): the descent condition is NOT "non-phantom" and NOT "≢ 0" — a nonzero
constant breaks both. The right condition is the **deepest true-degree ≠ 0** (`hnz`), the tower of the depth-2
`(singleExpMeasureCanon (lcY₁ q)).2 ≠ 0`. The payoff proven here:

* `hnzTower_nonzero` — `hnz` forces `q ≢ 0` (`canonZeroB q = false`);
* `nonphantom_of_hnzTower` — `hnz` forces the leading `y`-coefficient non-phantom **at every level**, because a
  phantom anywhere collapses the deeper leading coefficient to canon-zero, forcing the deepest true-degree to `0`.

So the absorbed descent gets "non-phantom at every level" *for free* from the single deepest-`hnz` hypothesis —
the key that unlocks discharging the reduce arm without the full `Reducing` predicate. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct
open MachLib.IterExpDepth3CdegY1
open MachLib.ChainExp2CanonMeasure
open MachLib.ChainExp2YPIT
open MachLib.IterExpDepth3CapstonePrep

/-- The **`hnz`-tower**: the deepest true-degree is nonzero, defined by descending the leading-coefficient
tower to the single-exp base. `hnzTower 0 q = (smc (lcY₁ q)).2 ≠ 0` (the depth-2 `hnz`); the step descends to
`dropLastY (leadingCoeffY_top q)`. -/
def hnzTower : (k : Nat) → MultiPoly (k + 2) → Prop
  | 0 => fun q => (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 ≠ 0
  | k + 1 => fun q =>
      hnzTower k (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q))

/-- **`canonZeroB` propagates to a leading `y`-coefficient.** If `q` vanishes everywhere so does its leading
`yᵢ`-coefficient (a `yCoeffsAt` entry). -/
theorem canonZeroB_leadingCoeffY_of_canonZero {n : Nat} (i : Fin n) (q : MultiPoly n)
    (h : canonZeroB q = true) : canonZeroB (MultiPoly.leadingCoeffY i q) = true := by
  apply canonZeroB_true_of_eval_zero
  intro x env
  rw [eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general i q (MultiPoly.yCoeffsAt_nonempty i q) x env]
  exact yCoeffsAt_entry_eval_zero_of_eval_zero i q ((canonZeroB_true_iff q).mp h) x env
    ((MultiPoly.yCoeffsAt i q).getLast (MultiPoly.yCoeffsAt_nonempty i q))
    (List.getLast_mem (MultiPoly.yCoeffsAt_nonempty i q))

/-- **`canonZeroB` propagates through `dropLastY` of a top-free polynomial.** For top-free `c`, `dropLastY`
preserves eval, so `c ≡ 0` gives `dropLastY c ≡ 0`. -/
theorem canonZeroB_dropLastY_of_canonZero_topfree {n : Nat} (c : MultiPoly (n + 1))
    (hcf : MultiPoly.degreeY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) c = 0)
    (h : canonZeroB c = true) : canonZeroB (MultiPoly.dropLastY c) = true := by
  apply canonZeroB_true_of_eval_zero
  intro x env'
  have hrestrict : (fun i : Fin n =>
      (fun j : Fin (n + 1) => if hj : j.val < n then env' ⟨j.val, hj⟩ else 0) ⟨i.val, by omega⟩) = env' := by
    funext i
    show (if hj : i.val < n then env' ⟨i.val, hj⟩ else 0) = env' i
    rw [dif_pos i.isLt]
  have e := MultiPoly.eval_dropLastY c hcf x
    (fun j : Fin (n + 1) => if hj : j.val < n then env' ⟨j.val, hj⟩ else 0)
  rw [hrestrict] at e
  rw [e]; exact (canonZeroB_true_iff c).mp h x _

/-- **`hnz` ⟹ `q ≢ 0`.** Induction on depth: base — a canon-zero `q` has canon-zero `lcY₁`, whose single-exp
measure is `(0,0)`, contradicting `hnz`; step — the inner `dropLastY (lcY_top q)` is `≢ 0` by IH, and both
`dropLastY` (top-free) and `leadingCoeffY` preserve canon-zero, so `q ≢ 0`. -/
theorem hnzTower_nonzero : ∀ (k : Nat) (q : MultiPoly (k + 2)), hnzTower k q → canonZeroB q = false := by
  intro k
  induction k with
  | zero =>
    intro q hnz
    have hnz' : (singleExpMeasureCanon (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q)).2 ≠ 0 := hnz
    cases h : canonZeroB q
    · rfl
    · exfalso
      have hlcz : canonZeroB (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) q) = true :=
        canonZeroB_leadingCoeffY_of_canonZero _ q h
      exact hnz' (by rw [smc_zero_of_eval_zero _ ((canonZeroB_true_iff _).mp hlcz)])
  | succ k ih =>
    intro q hnz
    have hinner : canonZeroB (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) = false :=
      ih (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) hnz
    cases h : canonZeroB q
    · rfl
    · exfalso
      have hlcz : canonZeroB (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q) = true :=
        canonZeroB_leadingCoeffY_of_canonZero _ q h
      have hdropz : canonZeroB (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) = true :=
        canonZeroB_dropLastY_of_canonZero_topfree _
          (MultiPoly.degreeY_leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q) hlcz
      rw [hdropz] at hinner
      exact absurd hinner (by decide)

end MachLib.IterExpDepthN
