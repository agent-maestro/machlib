import MachLib.IterExpDepthNMeasureConst
import MachLib.IterExpDepthNCanonBridge
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
open MachLib.ChainExp2CdegInv

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

/-- **`hnz` forces the top `y`-coefficient non-phantom** (the step-level non-phantom the descent feeds to
`chainNReduce_evalinv_descent`). Since `hnzTower (k+1) q = hnzTower k (dropLastY(lcY_top q))`, the inner is
`≢ 0` (`hnzTower_nonzero`), so `lcY_top q ≢ 0` (dropLastY preserves canon-zero for top-free), and `ytopAt`
(the `getLast` of `yCoeffsAt`) is eval-equal to `leadingCoeffY`, so `canonZeroB (ytopAt_top q) = false`. -/
theorem nonphantom_of_hnzTower_step (k : Nat) (q : MultiPoly (k + 3))
    (hnz : hnzTower (k + 1) q) :
    canonZeroB (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) q) = false := by
  have hdrop : canonZeroB (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) = false :=
    hnzTower_nonzero k _ hnz
  have hlcnz : canonZeroB (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q) = false := by
    cases h : canonZeroB (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)
    · rfl
    · exfalso
      have hd := canonZeroB_dropLastY_of_canonZero_topfree _
        (MultiPoly.degreeY_leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q) h
      rw [hd] at hdrop; exact absurd hdrop (by decide)
  rw [canonZeroB_eq_of_eval_eq (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) q)
      (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)
      (fun x env => (eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general
        (⟨k + 2, by omega⟩ : Fin (k + 3)) q
        (MultiPoly.yCoeffsAt_nonempty (⟨k + 2, by omega⟩ : Fin (k + 3)) q) x env).symm)]
  exact hlcnz

/-- **`nestedZero` is the strict minimum:** any nested tuple different from the all-zeros floor is strictly
above it. Induction on depth: base — `X ≠ 0 ⟹ 0 < X`; step — if the head is positive drop the first
component, else the head ties at `0` and the tail differs, recurse. -/
theorem nestedZero_lt_of_ne : ∀ (n : Nat) (X : NestedNat n),
    X ≠ nestedZero n → nestedOrder n (nestedZero n) X := by
  intro n
  induction n with
  | zero => intro X h; exact Nat.pos_of_ne_zero h
  | succ k ih =>
    intro X h
    obtain ⟨a, b⟩ := X
    by_cases ha : 0 < a
    · exact nestedOrder_of_fst ha
    · have ha0 : a = 0 := Nat.le_zero.mp (Nat.not_lt.mp ha)
      subst ha0
      have hb : b ≠ nestedZero k := fun hbz => h (by subst hbz; rfl)
      exact nestedOrder_of_snd rfl (ih b hb)

/-- **`hnz` ⟹ the eval-invariant measure is strictly above the floor.** The measure-positivity the reduce
arm needs for the degree-zero / reduce-`≡0` collapse (`measure(reduce ≡ 0) = floor < measure(q)`). Induction
on depth via `nestedZero_lt_of_ne`: the measure differs from the floor because its deepest component is the
true-degree, `≠ 0` by `hnz` (base: `canonLcY1 = y1top` eval-equal `leadingCoeffY` under non-phantom, so
`smc`'s `.2` = `hnz`; step: the head is `≥ 0` and the tail `≠ floor` by IH after the eval-invariant
`canonLcYAt ↔ leadingCoeffY` rewrite). -/
theorem hnzTower_measure_pos : ∀ (k : Nat) (r : MultiPoly (k + 2)),
    hnzTower k r → nestedOrder (k + 2) (nestedZero (k + 2)) (chainNMeasureEI k r) := by
  intro k
  induction k with
  | zero =>
    intro r hnz
    have hnp : coeffCanonZeroB1 (y1top r) = false := nonphantom_of_hnz r hnz
    have hsmc2 : (singleExpMeasureCanon (canonLcY1 r)).2 ≠ 0 := by
      rw [canonLcY1_eq_top r hnp,
          singleExpMeasureCanon_eq_of_eval_eq (y1top r)
            (MultiPoly.leadingCoeffY (⟨1, by omega⟩ : Fin 2) r)
            (fun x env => (eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general
              (⟨1, by omega⟩ : Fin 2) r (MultiPoly.yCoeffsAt_nonempty (⟨1, by omega⟩ : Fin 2) r) x env).symm)]
      exact hnz
    apply nestedZero_lt_of_ne
    intro heq
    exact hsmc2 (congrArg (fun p : Nat × Nat × Nat => p.2.2) heq)
  | succ k ih =>
    intro r hnz
    have hnp : canonZeroB (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) r) = false :=
      nonphantom_of_hnzTower_step k r hnz
    have hinner_eq : chainNMeasureEI k (MultiPoly.dropLastY
          (canonLcYAt (⟨k + 2, by omega⟩ : Fin (k + 3)) r))
        = chainNMeasureEI k (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) r)) := by
      apply chainNMeasureEI_eq_of_eval_eq k
      exact dropLastY_eval_eq_of_topfree _ _
        (canonLcYAt_degreeY_zero (⟨k + 2, by omega⟩ : Fin (k + 3)) r)
        (MultiPoly.degreeY_leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) r)
        (fun x env => canonLcYAt_eval_eq_leadingCoeffY_of_nonphantom
          (⟨k + 2, by omega⟩ : Fin (k + 3)) r hnp x env)
    simp only [chainNMeasureEI]
    by_cases hc : 0 < cdegYAt (⟨k + 2, by omega⟩ : Fin (k + 3)) r
    · exact nestedOrder_of_fst hc
    · refine nestedOrder_of_snd (by simp only [nestedZero]; omega) ?_
      rw [hinner_eq]
      exact ih (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) r)) hnz

end MachLib.IterExpDepthN
