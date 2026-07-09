import MachLib.PfaffianLogGeneralDegree
import MachLib.IterExpDepthNCanonBridge
import MachLib.IterExpDepthNMeasureEI

/-!
# Feasibility spike (port plan step 1.2): the log Wronskian drops the CANONICAL top-degree

The mixed-chain measure descent (`roadmap/exp-hard-mixed-measure-port.md`) hinges on: at a LOG
level, the Wronskian reduct `g = c_D·cTD(q) − cTD(c_D)·q` strictly lowers `chainNMeasureEI`. Its
first component is `cdegYAt` — the *canonical* (eval-invariant) top y-degree. This file tests the
central bridge: does `cdegYAt` drop, given the log lemmas speak of the *syntactic* `degreeY`?

**Result: YES, cleanly** (`log_wronskian_cdegYAt_lt`). The abstract core
`cdegYAt_lt_of_leadY_evalzero` — "any reduct of degree `≤ D` whose degree-`D` coefficient is
eval-zero has `cdegYAt < cdegYAt` of a non-phantom degree-`D` polynomial" — is fed by the log
lemmas `degreeYtop_wronskian_le` + `wronskian_leadY_eval_zero` with no loss, via the
canonical/syntactic bridges `cdegYAt_lt_degreeYAt_of_top` / `cdegYAt_eq_degreeYAt_of_top`.

So the `cdegYAt/canonLcYAt ↔ degreeY/leadingCoeffY` bridge — flagged in the port plan as the real
risk of step 1.2 — is NOT lossy for the log arm. The reframe ("different levels drop different
measure components") is sound; the interface widening (step 1.1) is worth building. No new axioms.
-/

namespace MachLib
namespace PfaffianLogLead

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpDepthN
open MachLib.MultiPolyReconstruct

/-- **`cdegYAt` is bounded by the syntactic `degreeY`** (dropWhile only shortens). -/
theorem cdegYAt_le_degreeYAt {n : Nat} (i : Fin n) (q : MultiPoly n) :
    cdegYAt i q ≤ MultiPoly.degreeY i q := by
  unfold cdegYAt
  have hlen : ∀ (l : List (MultiPoly n)), (l.dropWhile canonZeroB).length ≤ l.length := by
    intro l
    induction l with
    | nil => exact Nat.le_refl 0
    | cons a as ih =>
      unfold List.dropWhile
      split
      · exact Nat.le_succ_of_le ih
      · exact Nat.le_refl _
  have h := hlen (yCoeffsAt i q).reverse
  rw [List.length_reverse, yCoeffsAt_length_eq] at h
  omega

/-- **Abstract canonical-degree drop.** If `q` is non-phantom of positive syntactic degree `D`
(so `cdegYAt q = D`) and `g` has syntactic degree `≤ D` with its degree-`D` coefficient eval-zero,
then `cdegYAt g < cdegYAt q`. The `chainNMeasureEI` first-component drop, expressed purely on the
canonical/syntactic degree bridge — reusable for ANY reduct with an eval-zero leading term. -/
theorem cdegYAt_lt_of_leadY_evalzero {N : Nat} (top : Fin N) (q g : MultiPoly N)
    (hq_np : canonZeroB (ytopAt top q) = false)
    (hq_pos : 0 < MultiPoly.degreeY top q)
    (hgle : MultiPoly.degreeY top g ≤ MultiPoly.degreeY top q)
    (hglead : ∀ (x : Real) (env : Fin N → Real),
        MultiPoly.eval ((yCoeffsAt top g).getD (MultiPoly.degreeY top q) (MultiPoly.const 0)) x env = 0) :
    cdegYAt top g < cdegYAt top q := by
  have hqcdeg : cdegYAt top q = MultiPoly.degreeY top q := cdegYAt_eq_degreeYAt_of_top top q hq_np
  have hcle := cdegYAt_le_degreeYAt top g
  by_cases hgp : canonZeroB (ytopAt top g) = true
  · by_cases hgd0 : 0 < MultiPoly.degreeY top g
    · have hlt := cdegYAt_lt_degreeYAt_of_top top g hgp hgd0; omega
    · omega
  · have hgnp : canonZeroB (ytopAt top g) = false := by simpa using hgp
    have hgcdeg := cdegYAt_eq_degreeYAt_of_top top g hgnp
    have hne : MultiPoly.degreeY top g ≠ MultiPoly.degreeY top q := by
      intro heq
      have hphantom : canonZeroB (ytopAt top g) = true := by
        apply canonZeroB_true_of_eval_zero
        intro x env
        have hlast_eq : ytopAt top g = (yCoeffsAt top g).getD (MultiPoly.degreeY top q) (MultiPoly.const 0) := by
          unfold ytopAt
          have hlen : (yCoeffsAt top g).length - 1 = MultiPoly.degreeY top q := by
            rw [yCoeffsAt_length_eq]; omega
          rw [← hlen]
          exact (list_getD_pred_eq_getLast (yCoeffsAt top g) (MultiPoly.const 0) (yCoeffsAt_nonempty top g)).symm
        rw [hlast_eq]; exact hglead x env
      rw [hphantom] at hgnp; exact absurd hgnp (by decide)
    omega

/-- **SPIKE (port step 1.2): the log Wronskian strictly drops the canonical top-degree.** For a
LOG-type top and a barrier `q` non-phantom (canonical leading coefficient eval-nonzero) of positive
degree, the Wronskian `g = c_D·cTD(q) − cTD(c_D)·q` has `cdegYAt g < cdegYAt q` — the
`chainNMeasureEI` first-component drop a log level contributes to the mixed measure descent. -/
theorem log_wronskian_cdegYAt_lt {N : Nat} (c : PfaffianChain N) (top : Fin N)
    (h_top : MultiPoly.degreeY top (c.relations top) = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (q : MultiPoly N)
    (hq_np : canonZeroB (ytopAt top q) = false)
    (hq_pos : 0 < MultiPoly.degreeY top q) :
    cdegYAt top (MultiPoly.sub
        (MultiPoly.mul (MultiPoly.leadingCoeffY top q) (chainTotalDeriv c q))
        (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY top q)) q))
      < cdegYAt top q :=
  cdegYAt_lt_of_leadY_evalzero top q _ hq_np hq_pos
    (degreeYtop_wronskian_le c top h_top h_tri q)
    (fun x env => wronskian_leadY_eval_zero c top h_top h_tri q x env)

/-- **The log level descends `chainNMeasureEI` (port step 1.1 input).** Lifts the `cdegYAt` drop
to the full nested measure: since `cdegYAt` is the FIRST component of `chainNMeasureEI`, a strict
drop there gives `nestedOrder` by `lexProd_of_fst`. This is the exact `chainNMeasureEI`-descent
witness the mixed-chain measure recursion needs at a log level — the log analog of the exp
`chainReduce_orderCanon_gen`, but the reduct is the Wronskian, not `chainReduce c m q`. Confirms the
spike composes with the real measure machinery. -/
theorem log_wronskian_chainNMeasureEI_lt {k : Nat} (c : PfaffianChain (k + 3))
    (h_top : MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3))
        (c.relations (⟨k + 2, by omega⟩ : Fin (k + 3))) = 0)
    (h_tri : ∀ j : Fin (k + 3), j ≠ (⟨k + 2, by omega⟩ : Fin (k + 3)) →
        MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) (c.relations j) = 0)
    (q : MultiPoly (k + 3))
    (hq_np : canonZeroB (ytopAt (⟨k + 2, by omega⟩ : Fin (k + 3)) q) = false)
    (hq_pos : 0 < MultiPoly.degreeY (⟨k + 2, by omega⟩ : Fin (k + 3)) q) :
    nestedOrder (k + 3)
      (chainNMeasureEI (k + 1) (MultiPoly.sub
        (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q) (chainTotalDeriv c q))
        (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY (⟨k + 2, by omega⟩ : Fin (k + 3)) q)) q)))
      (chainNMeasureEI (k + 1) q) := by
  have hlt := log_wronskian_cdegYAt_lt c (⟨k + 2, by omega⟩ : Fin (k + 3)) h_top h_tri q hq_np hq_pos
  simp only [chainNMeasureEI, nestedOrder]
  exact MachLib.IterExpDepth3CdegY1.lexProd_of_fst hlt

end PfaffianLogLead
end MachLib
