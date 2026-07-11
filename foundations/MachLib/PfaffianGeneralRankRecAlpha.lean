import MachLib.IterExpDepthNRankRec
import MachLib.IterExpDepthNRankNested
import MachLib.PfaffianGeneralLevelBudgetAlpha
import MachLib.PfaffianGeneralDescentBoundAlpha

/-!
# α-generalized recursive inner rank (general Pfaffian explicit bound)

`rankRec` (`IterExpDepthNRankRec.lean`) is the recursive inner rank whose `nestedOrder`-drop is the
`ir`-drop the reduce arm consumes — but it is built on `descentBound` / `levelBudgetG` (the tower's
`≤ 1` lower-digit growth) and its boundedness/drop lemmas hardcode `B' ≤ B + 1`. `rankRecA α` is the
general-chain version on `descentBoundA α` / `levelBudgetGA cap α`, so it tolerates the format-`α` growth
of the inner digit `b` per reduce. This file gives the def, the `levelBudgetGA↔dLevelA` bridge, and the
**strict boundedness** `rankRecA α n B v < descentBoundA α n B` — the `+1` headroom the phantom top-drop
needs. (`rankRecA_drop`, with `B' ≤ B + α`, is the next file.) Mirrors `rankRec_lt_descentBound` with α
threaded. `rankRecA 1 = rankRec` shape at α = 1.
-/

namespace MachLib.IterExpDepthN

open MachLib.ExplicitBound

/-- `levelBudgetGA … 0 …` is `dLevelA` shifted by one (α-analogue of `lbg0_eq_dLevel`). -/
theorem lbg0_eq_dLevelA (cap : Nat → Nat) (α : Nat) : ∀ (d B : Nat),
    levelBudgetGA cap α 0 (d + 1) B = dLevelA cap α d B
  | 0, _ => rfl
  | d + 1, B => by
      show cap B + levelBudgetGA cap α 0 (d + 1) (B + cap B + α)
          = cap B + dLevelA cap α d (B + cap B + α)
      rw [lbg0_eq_dLevelA cap α d (B + cap B + α)]

/-- `dLevelA` dominates its base cap (α-analogue of `dLevel_ge_base`). -/
theorem dLevelA_ge_base (cap : Nat → Nat) (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (α d B : Nat) : cap B ≤ dLevelA cap α d B :=
  dLevelA_mono_d cap hcap α B (Nat.zero_le d)

/-- One extra depth only adds count (α-analogue of `descentBound_le_succ_n`). -/
theorem descentBoundA_le_succ_n (α n B : Nat) : descentBoundA α n B ≤ descentBoundA α (n + 1) B :=
  dLevelA_ge_base (descentBoundA α n) (fun {_ _} h => descentBoundA_mono α n h) α B B

/-- **The α-recursive inner rank.** Same shape as `rankRec` on `descentBoundA α` / `levelBudgetGA … α`:
the tail rank plus the current top digit's worth of tail-descents, degree bound grown by the tail rank
and the α-reset. -/
def rankRecA (α : Nat) : (n : Nat) → Nat → NestedNat n → Nat
  | 0,     _, a => a
  | n + 1, B, v => rankRecA α n B v.2
      + levelBudgetGA (descentBoundA α n) α 0 v.1 (B + rankRecA α n B v.2 + α)

/-- **STRICT boundedness** — `rankRecA α n B v < descentBoundA α n B` when `v`'s digits are `≤ B`. The
`+1` headroom the phantom top-drop needs. Mirrors `rankRec_lt_descentBound`, α threaded. -/
theorem rankRecA_lt_descentBoundA (α : Nat) : ∀ (n B : Nat) (v : NestedNat n),
    nestedLe n v (allBNested n B) → rankRecA α n B v < descentBoundA α n B
  | 0, B, a, h => by
      show a < B + 1
      exact Nat.lt_succ_of_le h
  | n + 1, B, v, h => by
      obtain ⟨htop, htail⟩ := h
      have hcap : ∀ {B₁ B₂ : Nat}, B₁ ≤ B₂ → descentBoundA α n B₁ ≤ descentBoundA α n B₂ :=
        fun {_ _} hh => descentBoundA_mono α n hh
      cases hv : v.1 with
      | zero =>
          show rankRecA α n B v.2
              + levelBudgetGA (descentBoundA α n) α 0 v.1 (B + rankRecA α n B v.2 + α)
              < descentBoundA α (n + 1) B
          rw [hv]
          have h0 : levelBudgetGA (descentBoundA α n) α 0 0 (B + rankRecA α n B v.2 + α) = 0 := rfl
          rw [h0]
          have hir : rankRecA α n B v.2 < descentBoundA α n B :=
            rankRecA_lt_descentBoundA α n B v.2 htail
          have := descentBoundA_le_succ_n α n B
          omega
      | succ t =>
          show rankRecA α n B v.2
              + levelBudgetGA (descentBoundA α n) α 0 v.1 (B + rankRecA α n B v.2 + α)
              < descentBoundA α (n + 1) B
          rw [hv, lbg0_eq_dLevelA (descentBoundA α n) α t (B + rankRecA α n B v.2 + α)]
          have htB : t + 1 ≤ B := by rw [← hv]; exact htop
          have h1 : dLevelA (descentBoundA α n) α t (B + rankRecA α n B v.2 + α)
              ≤ dLevelA (descentBoundA α n) α t (B + descentBoundA α n B + α) :=
            dLevelA_mono_B (descentBoundA α n) hcap α t (by
              have hir : rankRecA α n B v.2 < descentBoundA α n B :=
                rankRecA_lt_descentBoundA α n B v.2 htail
              omega)
          have hmonod : dLevelA (descentBoundA α n) α (t + 1) B
              ≤ dLevelA (descentBoundA α n) α B B :=
            dLevelA_mono_d (descentBoundA α n) hcap α B htB
          have hdef : dLevelA (descentBoundA α n) α (t + 1) B
              = descentBoundA α n B + dLevelA (descentBoundA α n) α t (B + descentBoundA α n B + α) :=
            rfl
          show rankRecA α n B v.2 + dLevelA (descentBoundA α n) α t (B + rankRecA α n B v.2 + α)
              < dLevelA (descentBoundA α n) α B B
          have hir : rankRecA α n B v.2 < descentBoundA α n B :=
            rankRecA_lt_descentBoundA α n B v.2 htail
          omega

end MachLib.IterExpDepthN
