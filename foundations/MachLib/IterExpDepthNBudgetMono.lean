import MachLib.IterExpDepthNRankRec

/-!
# Chain-N explicit bound — monotonicity prerequisites for the outer WF wrap

The outer `invPhiG(degreeY_top)` recursion threads a per-poly degree bound `B` and a FIXED leaf bound
`Nleaf` (the depth-below `Ndepth m`, pre-computed large enough for all reachable leaf degrees, so it stays
constant while `B` grows — the reduce closure `invPhiG_reduce` needs the same `Nleaf` on both sides). These
are the monotonicity facts that threading needs:

  * `levelBudgetG_mono_Nleaf` / `invPhiG_mono_Nleaf` — a larger fixed leaf bound only raises the budget
    (so a valid over-estimate of `Ndepth m` is safe throughout).
  * `rankRec_mono_B` — the inner rank is monotone in the degree bound (relate per-poly `B`s).
-/

namespace MachLib.IterExpDepthN

open MachLib.ExplicitBound

/-- `levelBudgetG` is monotone in the leaf bound `Nleaf`. -/
theorem levelBudgetG_mono_Nleaf (cap : Nat → Nat) {Nleaf Nleaf' : Nat} (hN : Nleaf ≤ Nleaf') :
    ∀ (d B : Nat), levelBudgetG cap Nleaf d B ≤ levelBudgetG cap Nleaf' d B
  | 0, _ => hN
  | d + 1, B => by
      show cap B + levelBudgetG cap Nleaf d (B + cap B + 1)
          ≤ cap B + levelBudgetG cap Nleaf' d (B + cap B + 1)
      exact Nat.add_le_add_left (levelBudgetG_mono_Nleaf cap hN d (B + cap B + 1)) (cap B)

/-- `invPhiG` is monotone in the leaf bound `Nleaf`. -/
theorem invPhiG_mono_Nleaf (cap : Nat → Nat) {Nleaf Nleaf' : Nat} (hN : Nleaf ≤ Nleaf')
    (d ir B : Nat) : invPhiG cap Nleaf d ir B ≤ invPhiG cap Nleaf' d ir B := by
  cases d with
  | zero => exact hN
  | succ d => exact Nat.add_le_add_left (levelBudgetG_mono_Nleaf cap hN d (B + ir + 1)) ir

/-- **The inner rank is monotone in the degree bound `B`** (larger radices ⇒ larger mixed value). -/
theorem rankRec_mono_B : ∀ (n : Nat) {B B' : Nat} (v : NestedNat n), B ≤ B' →
    rankRec n B v ≤ rankRec n B' v
  | 0, _, _, _, _ => Nat.le_refl _
  | n + 1, B, B', v, h => by
      show rankRec n B v.2 + levelBudgetG (descentBound n) 0 v.1 (B + rankRec n B v.2 + 1)
          ≤ rankRec n B' v.2 + levelBudgetG (descentBound n) 0 v.1 (B' + rankRec n B' v.2 + 1)
      have ih := rankRec_mono_B n v.2 h
      have hlb := levelBudgetG_mono_B (descentBound n) (fun {_ _} hh => descentBound_mono n hh) 0 v.1
        (show B + rankRec n B v.2 + 1 ≤ B' + rankRec n B' v.2 + 1 from by omega)
      omega

end MachLib.IterExpDepthN
