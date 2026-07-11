import MachLib.IterExpDepthNBudget5
import MachLib.IterExpDepthNBudgetMax
import MachLib.PfaffianGeneralRankRecAlpha
import MachLib.PfaffianGeneralBudgetGrow

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

/-- **Leaf arm:** `budgetN5A = 0` when `degreeY_top q = 0` (`invPhiG` at level `d = 0` is `Nleaf = 0`).
The depth-N step's leaf hands off to the depth-below `Ndep`. -/
theorem budgetN5A_leaf (α m B : Nat) (q : MultiPoly (m + 3))
    (h : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) q = 0) :
    budgetN5A α m B q = 0 := by
  unfold budgetN5A; rw [h]; rfl

/-- **Lift arm:** `budgetN5A` is unchanged when the canonical measure ties (`degreeY_top` and the inner
`chainNMeasureEI` both preserved) — the depth-N step's inner-lift adds no zeros and no budget. -/
theorem budgetN5A_lift (α m B : Nat) (lift q : MultiPoly (m + 3))
    (h1 : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) lift
        = MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) q)
    (h2 : chainNMeasureEI m (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) lift))
        = chainNMeasureEI m (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) q))) :
    budgetN5A α m B lift = budgetN5A α m B q := by
  unfold budgetN5A; rw [h1, h2]

/-- The inner `rankRecA` is `< descentBoundA α` when the polynomial's degrees fit under `B` (α-analogue
of `rankRec_inner_lt`). -/
theorem rankRecA_inner_lt (α m : Nat) (hα : 1 ≤ α) (r : MultiPoly (m + 3)) (B : Nat)
    (hrx : MultiPoly.degreeX r + 2 ≤ B) (hry : ∀ i : Fin (m + 3), MultiPoly.degreeY i r ≤ B) :
    rankRecA α (m + 2) B (chainNMeasureEI m (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) r))) < descentBoundA α (m + 2) B :=
  rankRecA_lt_descentBoundA α (m + 2) B _ hα (chainNMeasureEI_inner_le_allB m r B hrx hry)

/-- **Trim arm:** `budgetN5A(trim) ≤ budgetN5A(p)` when the trim drops `degreeY_top` (`degreeY_top p =
d'+1`, `degreeY_top trim ≤ d'`) and `trim`'s degrees fit under `B`. Via `invPhiG_trim_any` (α-analogue of
the concrete step's `hle`). -/
theorem budgetN5A_trim (α m B d' : Nat) (hα : 1 ≤ α) (trim p : MultiPoly (m + 3))
    (hd' : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p = d' + 1)
    (htrim : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) trim ≤ d')
    (htx : MultiPoly.degreeX trim + 2 ≤ B)
    (hty : ∀ i : Fin (m + 3), MultiPoly.degreeY i trim ≤ B) :
    budgetN5A α m B trim ≤ budgetN5A α m B p := by
  unfold budgetN5A
  rw [hd']
  exact invPhiG_trim_any (descentBoundA α (m + 2))
    (fun {_ _} hh => descentBoundA_mono α (m + 2) hh) 0
    (rankRecA α (m + 2) B (chainNMeasureEI m (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))))
    (rankRecA α (m + 2) B (chainNMeasureEI m (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) trim)))) B B
    htrim (Nat.le_refl _) (Nat.le_of_lt (rankRecA_inner_lt α m hα trim B htx hty))

/-- **Reduce arm:** `budgetN5A(red at B+D) + 1 ≤ budgetN5A(p at B)`, absorbing the Rolle `+1`. The format
`α = D` (the multiplier/relation degree bound): the reduce preserves `degreeY_top` (`htie`) and grows the
cap by `≤ D`; the inner `rankRecA` drops by `≥ D` (`rankRecA_drop`, `B' ≤ B+D`), which both covers the `+1`
and compensates the cap growth (`invPhiG_reduce_grow`). -/
theorem budgetN5A_reduce (m B D d' : Nat) (hD : 1 ≤ D) (red p : MultiPoly (m + 3))
    (htie : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) red
        = MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)
    (hdp : MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p = d' + 1)
    (hEI : nestedOrder (m + 2)
        (chainNMeasureEI m (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) red)))
        (chainNMeasureEI m (MultiPoly.dropLastY
          (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))))
    (hrx : MultiPoly.degreeX red + 2 ≤ B + D)
    (hry : ∀ i : Fin (m + 3), MultiPoly.degreeY i red ≤ B + D) :
    budgetN5A D m (B + D) red + 1 ≤ budgetN5A D m B p := by
  have hdrop : rankRecA D (m + 2) (B + D) (chainNMeasureEI m (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) red))) + D
      ≤ rankRecA D (m + 2) B (chainNMeasureEI m (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))) :=
    rankRecA_drop D (m + 2) B (B + D) _ _ (Nat.le_refl _)
      (chainNMeasureEI_inner_le_allB m red (B + D) hrx hry) hEI
  unfold budgetN5A
  rw [htie, hdp]
  exact invPhiG_reduce_grow (descentBoundA D (m + 2))
    (fun {_ _} hh => descentBoundA_mono D (m + 2) hh) 0 d'
    (rankRecA D (m + 2) B (chainNMeasureEI m (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))))
    (rankRecA D (m + 2) (B + D) (chainNMeasureEI m (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) red))))
    B (B + D) (by omega) (by omega)

end MachLib.IterExpDepthN
