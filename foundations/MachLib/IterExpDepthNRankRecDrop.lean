import MachLib.IterExpDepthNRankRec

/-!
# Chain-N explicit bound — `rankRec_drop`: the inner rank drops ≥1 per reduce

The recursive inner rank `rankRec` strictly drops on a `nestedOrder` step of the measure, even under the
`≤ +1` degree growth — the property the outer `invPhiG(degreeY_top)` recursion needs (`ir` drops ⇒
`invPhiG_reduce` fires with the Rolle `+1`). Both descent cases (design §4‴) close:

  * **tail-drop** (top ties, tail drops in `nestedOrder`): the tail rank drops by ≥1 (IH), and the
    `levelBudgetG` argument `B + ir + 1` makes that drop and the `≤ +1` degree growth CANCEL.
  * **top-drop** (`v'.1 < v.1`): the source carries an extra level `cap (B+ir+1)` (`levelBudgetG_succ`)
    that strictly exceeds the reset inner rank `ir' < descentBound n B' ≤ cap (B+ir+1)` — the strict
    boundedness `rankRec_lt_descentBound`. This is where that lemma pays off.
-/

namespace MachLib.IterExpDepthN

open MachLib.ExplicitBound

/-- **The inner rank drops by ≥1 on a `nestedOrder` step**, given `≤ +1` degree growth (`B' ≤ B+1`) and
`v'` bounded by `B'`. -/
theorem rankRec_drop : ∀ (n B B' : Nat) (v v' : NestedNat n),
    B' ≤ B + 1 → nestedLe n v' (allBNested n B') → nestedOrder n v' v →
    rankRec n B' v' + 1 ≤ rankRec n B v
  | 0, _, _, a, a', _, _, h => h
  | n + 1, B, B', v, v', hB, hle, h => by
      obtain ⟨_htop', htail'⟩ := hle
      rcases h with hlt | ⟨heq, hinner⟩
      · -- top-drop: v'.1 < v.1
        obtain ⟨s, hs⟩ : ∃ s, v.1 = s + 1 :=
          ⟨v.1 - 1, by have := Nat.lt_of_le_of_lt (Nat.zero_le v'.1) hlt; omega⟩
        show rankRec n B' v'.2 + levelBudgetG (descentBound n) 0 v'.1 (B' + rankRec n B' v'.2 + 1) + 1
            ≤ rankRec n B v.2 + levelBudgetG (descentBound n) 0 v.1 (B + rankRec n B v.2 + 1)
        rw [hs, levelBudgetG_succ]
        have hcapmono : descentBound n B' ≤ descentBound n (B + rankRec n B v.2 + 1) :=
          descentBound_mono n (by omega)
        have hir'lt : rankRec n B' v'.2 < descentBound n B' :=
          rankRec_lt_descentBound n B' v'.2 htail'
        have hle_v' : levelBudgetG (descentBound n) 0 v'.1 (B' + rankRec n B' v'.2 + 1)
            ≤ levelBudgetG (descentBound n) 0 s
                (B + rankRec n B v.2 + 1 + descentBound n (B + rankRec n B v.2 + 1) + 1) :=
          Nat.le_trans
            (levelBudgetG_mono_d (descentBound n) (fun {_ _} hh => descentBound_mono n hh) 0
              (B' + rankRec n B' v'.2 + 1) (show v'.1 ≤ s by omega))
            (levelBudgetG_mono_B (descentBound n) (fun {_ _} hh => descentBound_mono n hh) 0 s
              (by omega))
        omega
      · -- tail-drop: v'.1 = v.1, tail drops
        have ihd : rankRec n B' v'.2 + 1 ≤ rankRec n B v.2 :=
          rankRec_drop n B B' v.2 v'.2 hB htail' hinner
        show rankRec n B' v'.2 + levelBudgetG (descentBound n) 0 v'.1 (B' + rankRec n B' v'.2 + 1) + 1
            ≤ rankRec n B v.2 + levelBudgetG (descentBound n) 0 v.1 (B + rankRec n B v.2 + 1)
        rw [heq]
        have hmono : levelBudgetG (descentBound n) 0 v.1 (B' + rankRec n B' v'.2 + 1)
            ≤ levelBudgetG (descentBound n) 0 v.1 (B + rankRec n B v.2 + 1) :=
          levelBudgetG_mono_B (descentBound n) (fun {_ _} hh => descentBound_mono n hh) 0 v.1
            (by omega)
        omega

end MachLib.IterExpDepthN
