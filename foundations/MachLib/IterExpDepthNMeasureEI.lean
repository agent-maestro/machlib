import MachLib.IterExpDepthNCanonDegree
import MachLib.IterExpDepthNMeasure
import MachLib.IterExpDepth3CdegY1

/-!
# Phase B — the uniform eval-invariant measure by recursion on depth (∀N)

The depth-3 descent used `chain2MeasureCanonEvalInv` (the fully eval-invariant depth-2 measure) as the
*inner* nested component. To climb the tower we need that inner measure at **every** depth, built
uniformly. This file defines it and proves it eval-invariant for all depths.

`chainNMeasureEI k : MultiPoly (k+2) → NestedNat (k+2)` — the depth-`(k+2)` eval-invariant canonical
measure:

* base `k = 0` — literally `chain2MeasureCanonEvalInv` (so the base of every induction is the existing,
  already-proven depth-2 machinery — nothing to reconcile);
* step `k+1` — `(cdegYAt_top p, chainNMeasureEI k (dropLastY (canonLcYAt_top p)))`: the canonical
  top-degree (Phase A) as the outer component, recursing on the canonical leading coefficient projected
  one variable down. Both ingredients are eval-invariant (Phase A), so the whole measure is.

`chainNMeasureEI_eq_of_eval_eq` — **eval-invariant for every depth**, by induction: the base is
`chain2MeasureCanonEvalInv_eq_of_eval_eq`; the step combines `cdegYAt_eq_of_eval_eq` (outer),
`canonLcYAt_eval_eq_of_eval_eq` + `dropLastY_eval_eq_of_topfree` (the projected coefficient stays
eval-equal), and the inductive hypothesis (inner). No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.IterExpDepth3CdegY1

/-- **`dropLastY` preserves eval-equality for top-free polynomials.** If `c1, c2 : MultiPoly (n+1)` are
both free of the top variable and eval-equal, then their `dropLastY` projections (in `MultiPoly n`) are
eval-equal. (Each side equals the original at the environment extended by `0` at the top, via
`eval_dropLastY`; the originals agree there.) -/
theorem dropLastY_eval_eq_of_topfree {n : Nat} (c1 c2 : MultiPoly (n + 1))
    (h1 : MultiPoly.degreeY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) c1 = 0)
    (h2 : MultiPoly.degreeY (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) c2 = 0)
    (h : ∀ (x : Real) (env : Fin (n + 1) → Real), MultiPoly.eval c1 x env = MultiPoly.eval c2 x env) :
    ∀ (x : Real) (env' : Fin n → Real),
      MultiPoly.eval (MultiPoly.dropLastY c1) x env' = MultiPoly.eval (MultiPoly.dropLastY c2) x env' := by
  intro x env'
  have hrestrict : (fun i : Fin n =>
      (fun j : Fin (n + 1) => if h : j.val < n then env' ⟨j.val, h⟩ else 0) ⟨i.val, by omega⟩) = env' := by
    funext i
    show (if h : i.val < n then env' ⟨i.val, h⟩ else 0) = env' i
    rw [dif_pos i.isLt]
  have e1 := MultiPoly.eval_dropLastY c1 h1 x
    (fun j : Fin (n + 1) => if h : j.val < n then env' ⟨j.val, h⟩ else 0)
  have e2 := MultiPoly.eval_dropLastY c2 h2 x
    (fun j : Fin (n + 1) => if h : j.val < n then env' ⟨j.val, h⟩ else 0)
  rw [hrestrict] at e1 e2
  rw [e1, e2]
  exact h x _

/-- **The uniform eval-invariant measure**, depth `k+2`. Base = `chain2MeasureCanonEvalInv`; step pairs
the canonical top-degree with the measure of the projected canonical leading coefficient. -/
noncomputable def chainNMeasureEI : (k : Nat) → MultiPoly (k + 2) → NestedNat (k + 2)
  | 0 => chain2MeasureCanonEvalInv
  | k + 1 => fun p =>
      (cdegYAt (⟨k + 2, by omega⟩ : Fin (k + 3)) p,
       chainNMeasureEI k (MultiPoly.dropLastY (canonLcYAt (⟨k + 2, by omega⟩ : Fin (k + 3)) p)))

/-- **The uniform measure is eval-invariant at every depth.** Induction on depth: base is the existing
`chain2MeasureCanonEvalInv_eq_of_eval_eq`; the step combines Phase A's degree/leading-coefficient
eval-invariance, `dropLastY_eval_eq_of_topfree`, and the inductive hypothesis. -/
theorem chainNMeasureEI_eq_of_eval_eq :
    ∀ (k : Nat) (q1 q2 : MultiPoly (k + 2)),
      (∀ (x : Real) (env : Fin (k + 2) → Real), MultiPoly.eval q1 x env = MultiPoly.eval q2 x env) →
      chainNMeasureEI k q1 = chainNMeasureEI k q2 := by
  intro k
  induction k with
  | zero =>
      intro q1 q2 h
      simp only [chainNMeasureEI]
      exact chain2MeasureCanonEvalInv_eq_of_eval_eq q1 q2 h
  | succ k ih =>
      intro q1 q2 h
      simp only [chainNMeasureEI]
      have hcdeg := cdegYAt_eq_of_eval_eq (⟨k + 2, by omega⟩ : Fin (k + 3)) q1 q2 h
      have hcanon : ∀ (x : Real) (env : Fin (k + 3) → Real),
          MultiPoly.eval (canonLcYAt (⟨k + 2, by omega⟩ : Fin (k + 3)) q1) x env
            = MultiPoly.eval (canonLcYAt (⟨k + 2, by omega⟩ : Fin (k + 3)) q2) x env :=
        fun x env => canonLcYAt_eval_eq_of_eval_eq _ q1 q2 h x env
      have hdrop := dropLastY_eval_eq_of_topfree _ _
        (canonLcYAt_degreeY_zero (⟨k + 2, by omega⟩ : Fin (k + 3)) q1)
        (canonLcYAt_degreeY_zero (⟨k + 2, by omega⟩ : Fin (k + 3)) q2) hcanon
      rw [hcdeg, ih _ _ hdrop]

end MachLib.IterExpDepthN
