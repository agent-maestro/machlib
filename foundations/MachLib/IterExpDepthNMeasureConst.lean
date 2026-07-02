import MachLib.IterExpDepthNMeasureEI
import MachLib.IterExpDepth3CapstonePrep

/-!
# Phase C→D absorption brick — the eval-invariant measure of the zero polynomial (∀N)

`chainNMeasureEI_const0` — `chainNMeasureEI k (const 0)` is the all-zeros nested `Nat` (`nestedZero`).
The ∀N lift of the depth-2 `chain2MeasureCanonEvalInv_const0`, by induction on depth: the canonical
top-degree of `const 0` is `0` and its canonical leading coefficient is `const 0` again (its only
`y`-coefficient, `const 0`, is canon-zero so it is dropped), so the measure recurses on `const 0` one
level down. This is the floor of the eval-invariant measure — the value the phantom-reduce case of the
absorption collapses to. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.IterExpDepth3CdegY1

/-- The all-zeros element of `NestedNat n`. -/
def nestedZero : (n : Nat) → NestedNat n
  | 0 => 0
  | k + 1 => (0, nestedZero k)

/-- **Canonical top-degree of `const 0` is `0`.** Its only `y`-coefficient is `const 0`, which is
canon-zero, so the canonical (phantom-trimmed) `y`-coefficient list is empty. -/
theorem cdegYAt_const0 {n : Nat} (i : Fin n) : cdegYAt i (MultiPoly.const (0 : Real)) = 0 := by
  show ((MultiPoly.yCoeffsAt i (MultiPoly.const (0 : Real))).reverse.dropWhile canonZeroB).length - 1 = 0
  rw [show MultiPoly.yCoeffsAt i (MultiPoly.const (0 : Real)) = [MultiPoly.const 0] from rfl]
  show (([MultiPoly.const (0 : Real)]).dropWhile canonZeroB).length - 1 = 0
  rw [List.dropWhile_cons_of_pos (by rw [canonZeroB_const0])]
  rfl

/-- **Canonical leading coefficient of `const 0` is `const 0`.** Same reason — the canonical list is
empty, so the `headD` default `const 0` is returned. -/
theorem canonLcYAt_const0 {n : Nat} (i : Fin n) :
    canonLcYAt i (MultiPoly.const (0 : Real)) = MultiPoly.const 0 := by
  show ((MultiPoly.yCoeffsAt i (MultiPoly.const (0 : Real))).reverse.dropWhile canonZeroB).headD
      (MultiPoly.const 0) = MultiPoly.const 0
  rw [show MultiPoly.yCoeffsAt i (MultiPoly.const (0 : Real)) = [MultiPoly.const 0] from rfl]
  show (([MultiPoly.const (0 : Real)]).dropWhile canonZeroB).headD (MultiPoly.const 0) = MultiPoly.const 0
  rw [List.dropWhile_cons_of_pos (by rw [canonZeroB_const0])]
  rfl

/-- **The eval-invariant measure of the zero polynomial is `nestedZero`.** Induction on depth: base is
`chain2MeasureCanonEvalInv_const0 = (0,(0,0)) = nestedZero 2`; the step uses `cdegYAt_const0` (outer `= 0`),
`canonLcYAt_const0` + `dropLastY (const 0) = const 0` (the projected coefficient is `const 0` again), and
the inductive hypothesis. -/
theorem chainNMeasureEI_const0 :
    ∀ (k : Nat), chainNMeasureEI k (MultiPoly.const (0 : Real)) = nestedZero (k + 2) := by
  intro k
  induction k with
  | zero =>
    show chain2MeasureCanonEvalInv (MultiPoly.const (0 : Real)) = nestedZero 2
    rw [MachLib.IterExpDepth3CapstonePrep.chain2MeasureCanonEvalInv_const0]
    rfl
  | succ k ih =>
    show (cdegYAt (⟨k + 2, by omega⟩ : Fin (k + 3)) (MultiPoly.const (0 : Real)),
          chainNMeasureEI k (MultiPoly.dropLastY
            (canonLcYAt (⟨k + 2, by omega⟩ : Fin (k + 3)) (MultiPoly.const (0 : Real)))))
        = nestedZero (k + 3)
    rw [cdegYAt_const0, canonLcYAt_const0,
        show MultiPoly.dropLastY (MultiPoly.const (0 : Real)) = MultiPoly.const 0 from rfl, ih]
    rfl

end MachLib.IterExpDepthN
