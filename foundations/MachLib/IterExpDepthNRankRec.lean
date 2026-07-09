import MachLib.IterExpDepthNDescentBound
import MachLib.IterExpDepthNEIrank

/-!
# Chain-N explicit bound — the recursive inner rank `rankRec` + STRICT boundedness (closing the nut)

The nested inner rank (design §4‴): `rankRec n B v` is the "remaining descent" of a `NestedNat n` measure
`v` under the reduce's `nestedOrder` drops. It is `invPhiG (descentBound (n−1))`-shaped with base `= ir`
(level `= top+1`, so `top = 0` returns the tail rank, not a leaf), mirroring `chainNMeasureEI`'s recursion.

The crux this file closes is the **strict** boundedness `rankRec n B v < descentBound n B` (given `v`'s
digits `≤ B`). That strictness is exactly what the phantom top-drop `+1` needs: the reset inner rank
`ir' = rankRec n B' (tail) < descentBound n B' ≤ descentBound n (B+1)`, so `ir' + 1 ≤ descentBound n (B+1)`
— the top-drop closure's missing headroom. The proof is an induction on depth using the `dLevel`
monotonicity; the `top ≥ 1` case gets its strict `−1` from the extra level `cap B` that `dLevel cap (t+1)`
carries over the `ir`-shifted `dLevel cap t`.
-/

namespace MachLib.IterExpDepthN

open MachLib.ExplicitBound

/-- The base-`0` level-budget is `dLevel` shifted by one (`dLevel`'s base is `cap B`, `levelBudgetG …0…`'s is
`0`). -/
theorem lbg0_eq_dLevel (cap : Nat → Nat) : ∀ (d B : Nat),
    levelBudgetG cap 0 (d + 1) B = dLevel cap d B
  | 0, _ => rfl
  | d + 1, B => by
      show cap B + levelBudgetG cap 0 (d + 1) (B + cap B + 1) = cap B + dLevel cap d (B + cap B + 1)
      rw [lbg0_eq_dLevel cap d (B + cap B + 1)]

/-- `dLevel` dominates its base cap. -/
theorem dLevel_ge_base (cap : Nat → Nat) (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (d B : Nat) : cap B ≤ dLevel cap d B :=
  dLevel_mono_d cap hcap B (Nat.zero_le d)

/-- One extra depth only adds count. -/
theorem descentBound_le_succ_n (n B : Nat) : descentBound n B ≤ descentBound (n + 1) B :=
  dLevel_ge_base (descentBound n) (fun {_ _} h => descentBound_mono n h) B B

/-- **The recursive inner rank.** `rankRec n B v` = the remaining `nestedOrder`-descent of `v` (digits `≤ B`,
lower digits growing `≤ 1`/step). Base = the digit itself; step = the tail rank plus the current top digit's
worth of full tail-descents, at the degree bound grown by the tail rank (the chain-2 cancellation). -/
def rankRec : (n : Nat) → Nat → NestedNat n → Nat
  | 0,     _, a => a
  | n + 1, B, v => rankRec n B v.2 + levelBudgetG (descentBound n) 0 v.1 (B + rankRec n B v.2 + 1)

/-- **STRICT boundedness** — `rankRec n B v < descentBound n B` whenever `v`'s digits are `≤ B`. The `+1`
headroom the phantom top-drop needs. Induction on depth; `top ≥ 1` gets its strict drop from the extra
`cap B` level in `dLevel cap (t+1) B`. -/
theorem rankRec_lt_descentBound : ∀ (n B : Nat) (v : NestedNat n),
    nestedLe n v (allBNested n B) → rankRec n B v < descentBound n B
  | 0, B, a, h => by
      show a < B + 1
      exact Nat.lt_succ_of_le h
  | n + 1, B, v, h => by
      obtain ⟨htop, htail⟩ := h
      have hir : rankRec n B v.2 + 1 ≤ descentBound n B := rankRec_lt_descentBound n B v.2 htail
      -- abbreviations
      have hcap : ∀ {B₁ B₂ : Nat}, B₁ ≤ B₂ → descentBound n B₁ ≤ descentBound n B₂ :=
        fun {_ _} hh => descentBound_mono n hh
      cases hv : v.1 with
      | zero =>
          -- rankRec = ir + levelBudgetG … 0 0 … = ir < descentBound n B ≤ descentBound (n+1) B
          show rankRec n B v.2 + levelBudgetG (descentBound n) 0 v.1 (B + rankRec n B v.2 + 1)
              < descentBound (n + 1) B
          rw [hv]
          have h0 : levelBudgetG (descentBound n) 0 0 (B + rankRec n B v.2 + 1) = 0 := rfl
          rw [h0]
          have := descentBound_le_succ_n n B
          omega
      | succ t =>
          show rankRec n B v.2 + levelBudgetG (descentBound n) 0 v.1 (B + rankRec n B v.2 + 1)
              < descentBound (n + 1) B
          rw [hv, lbg0_eq_dLevel (descentBound n) t (B + rankRec n B v.2 + 1)]
          -- goal: ir + dLevel cap t (B+ir+1) < dLevel cap B B   (= descentBound (n+1) B)
          have htB : t + 1 ≤ B := by rw [← hv]; exact htop
          have h1 : dLevel (descentBound n) t (B + rankRec n B v.2 + 1)
              ≤ dLevel (descentBound n) t (B + descentBound n B + 1) :=
            dLevel_mono_B (descentBound n) hcap t (by omega)
          have hdef : dLevel (descentBound n) (t + 1) B
              = descentBound n B + dLevel (descentBound n) t (B + descentBound n B + 1) := rfl
          have hmonod : dLevel (descentBound n) (t + 1) B ≤ dLevel (descentBound n) B B :=
            dLevel_mono_d (descentBound n) hcap B htB
          show rankRec n B v.2 + dLevel (descentBound n) t (B + rankRec n B v.2 + 1)
              < dLevel (descentBound n) B B
          omega

end MachLib.IterExpDepthN
