import MachLib.IterExpDepthNBudget5
import MachLib.IterExpDepthNBudgetMax
import MachLib.PfaffianGeneralRankRecAlpha

/-!
# α-generalized depth-N budget `budgetN5A` (general Pfaffian explicit bound, step 4 foundation)

The concrete depth-N step's invariant is `budgetN5 m B q + Ndep(…)`, where
`budgetN5 = invPhiG (descentBound (m+2)) 0 degreeY_top (rankRec (m+2) B (chainNMeasureEI …)) B` — the
top-level trim budget (`invPhiG` over `degreeY_top`) layered over the inner `rankRec`. For a general
chain the reduce grows `degreeX` by the format `α`, so this needs the α-versions: `descentBoundA α` as
the `invPhiG` cap and `rankRecA α` as the inner rank. `budgetN5A` is that budget; `rankRecA_mono_B` (the
inner rank is monotone in the degree bound) and `budgetN5A_mono_B` are the monotonicity the depth
induction (`Ndep` recurrence) needs.
-/

namespace MachLib.IterExpDepthN

open MachLib.ExplicitBound MachLib.MultiPolyMod

/-- The inner rank is monotone in the degree bound `B` (larger bound ⇒ larger rank). Base is
`B`-independent (`α·a`); the recursion grows via `levelBudgetGA_mono_B`. -/
theorem rankRecA_mono_B (α : Nat) :
    ∀ (n B B' : Nat), B ≤ B' → ∀ (v : NestedNat n), rankRecA α n B v ≤ rankRecA α n B' v
  | 0, _, _, _, a => Nat.le_refl _
  | n + 1, B, B', h, v => by
      show rankRecA α n B v.2
            + levelBudgetGA (descentBoundA α n) α 0 v.1 (B + rankRecA α n B v.2 + α)
          ≤ rankRecA α n B' v.2
            + levelBudgetGA (descentBoundA α n) α 0 v.1 (B' + rankRecA α n B' v.2 + α)
      have hrec := rankRecA_mono_B α n B B' h v.2
      have hlb := levelBudgetGA_mono_B (descentBoundA α n)
        (fun {_ _} hh => descentBoundA_mono α n hh) α 0 v.1
        (show B + rankRecA α n B v.2 + α ≤ B' + rankRecA α n B' v.2 + α from by omega)
      omega

/-- **The α-generalized depth-N budget.** `invPhiG (descentBoundA α (m+2))` over `degreeY_top` with the
inner `rankRecA α (m+2)` of `chainNMeasureEI`. The α-version of `budgetN5`. -/
noncomputable def budgetN5A (α m B : Nat) (q : MultiPoly (m + 3)) : Nat :=
  invPhiG (descentBoundA α (m + 2)) 0 (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) q)
    (rankRecA α (m + 2) B (chainNMeasureEI m (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) q)))) B

/-- `budgetN5A` is monotone in the degree bound `B` — the `hNdep`-style monotonicity the depth induction
consumes. Both the `invPhiG` cap-arg and the inner rank grow with `B`. -/
theorem budgetN5A_mono_B (α m : Nat) (q : MultiPoly (m + 3)) {B B' : Nat} (h : B ≤ B') :
    budgetN5A α m B q ≤ budgetN5A α m B' q := by
  unfold budgetN5A
  refine Nat.le_trans (invPhiG_mono_ir (descentBoundA α (m + 2))
    (fun {_ _} hh => descentBoundA_mono α (m + 2) hh) 0
    (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) q) B
    (rankRecA_mono_B α (m + 2) B B' h _)) ?_
  exact invPhiG_mono_B (descentBoundA α (m + 2))
    (fun {_ _} hh => descentBoundA_mono α (m + 2) hh) 0
    (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) q)
    (rankRecA α (m + 2) B' (chainNMeasureEI m (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) q)))) h

end MachLib.IterExpDepthN
