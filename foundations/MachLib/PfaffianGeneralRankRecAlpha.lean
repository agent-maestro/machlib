import MachLib.IterExpDepthNRankRec
import MachLib.IterExpDepthNRankNested
import MachLib.PfaffianGeneralLevelBudgetAlpha
import MachLib.PfaffianGeneralDescentBoundAlpha

/-!
# α-generalized recursive inner rank + its ≥α drop (general Pfaffian explicit bound — the nut)

`rankRec` (`IterExpDepthNRankRec.lean`) is the recursive inner rank whose `nestedOrder`-drop is the
`ir`-drop the reduce arm consumes; its boundedness/drop hardcode `B' ≤ B + 1` (the tower, format `α=1`).
For a general chain the inner digit `b` grows by the format `α` per reduce (`b ≤ degreeX+2`, `degreeX`
growing by `α`), so `B' ≤ B + α`, and the tower's tail-drop cancellation (`+1↔−1`) breaks: it must be
`+α↔−α`. So the **α-recursive inner rank must drop by `≥ α`** (not `≥1`), which forces:

* the **base rank α-scaled**: `rankRecA α 0 B a := α · a` (so `a' < a ⟹ α·a' + α ≤ α·a`); and
* the boundedness in **strong (gap-`≥α`) form** `rankRecA α n B v + α ≤ descentBoundA α n B`, which forces
  `descentBoundA α 0 B := α·(B+1)` (`PfaffianGeneralDescentBoundAlpha`) so the base gap is `≥ α`.

With those, both descent cases close (design §4‴-α): **tail-drop** — the IH's `≥α` drop and `B' ≤ B+α`
give `B' + rank' ≤ B + rank`, so `LB' ≤ LB` and the total drops `≥α` (the `α` cancels the growth
exactly); **top-drop** — the strong boundedness supplies `rank' + α ≤ descentBoundA α n B' ≤` the extra
level, covering the phantom `+α`. `α = 1` recovers `rankRec`. Pure `Nat`.
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

/-- **The α-recursive inner rank**, base digit α-scaled so the drop is `≥ α`. -/
def rankRecA (α : Nat) : (n : Nat) → Nat → NestedNat n → Nat
  | 0,     _, a => α * a
  | n + 1, B, v => rankRecA α n B v.2
      + levelBudgetGA (descentBoundA α n) α 0 v.1 (B + rankRecA α n B v.2 + α)

/-- **STRONG boundedness (gap `≥ α`)** — `rankRecA α n B v + α ≤ descentBoundA α n B` when `v`'s digits
are `≤ B`. The `α`-headroom the top-drop needs. Mirrors `rankRec_lt_descentBound`, strengthened to `+α`. -/
theorem rankRecA_add_le_descentBoundA (α : Nat) : ∀ (n B : Nat) (v : NestedNat n),
    nestedLe n v (allBNested n B) → rankRecA α n B v + α ≤ descentBoundA α n B
  | 0, B, a, h => by
      have hab : a ≤ B := h
      show α * a + α ≤ α * (B + 1)
      have hm : α * (a + 1) ≤ α * (B + 1) :=
        Nat.mul_le_mul (Nat.le_refl α) (Nat.add_le_add_right hab 1)
      rw [Nat.mul_succ] at hm
      exact hm
  | n + 1, B, v, h => by
      obtain ⟨htop, htail⟩ := h
      have hcap : ∀ {B₁ B₂ : Nat}, B₁ ≤ B₂ → descentBoundA α n B₁ ≤ descentBoundA α n B₂ :=
        fun {_ _} hh => descentBoundA_mono α n hh
      have hIH : rankRecA α n B v.2 + α ≤ descentBoundA α n B :=
        rankRecA_add_le_descentBoundA α n B v.2 htail
      cases hv : v.1 with
      | zero =>
          show rankRecA α n B v.2
              + levelBudgetGA (descentBoundA α n) α 0 v.1 (B + rankRecA α n B v.2 + α) + α
              ≤ descentBoundA α (n + 1) B
          rw [hv]
          have h0 : levelBudgetGA (descentBoundA α n) α 0 0 (B + rankRecA α n B v.2 + α) = 0 := rfl
          rw [h0]
          have := descentBoundA_le_succ_n α n B
          omega
      | succ t =>
          show rankRecA α n B v.2
              + levelBudgetGA (descentBoundA α n) α 0 v.1 (B + rankRecA α n B v.2 + α) + α
              ≤ descentBoundA α (n + 1) B
          rw [hv, lbg0_eq_dLevelA (descentBoundA α n) α t (B + rankRecA α n B v.2 + α)]
          have htB : t + 1 ≤ B := by rw [← hv]; exact htop
          have h1 : dLevelA (descentBoundA α n) α t (B + rankRecA α n B v.2 + α)
              ≤ dLevelA (descentBoundA α n) α t (B + descentBoundA α n B + α) :=
            dLevelA_mono_B (descentBoundA α n) hcap α t (by omega)
          have hmonod : dLevelA (descentBoundA α n) α (t + 1) B
              ≤ dLevelA (descentBoundA α n) α B B :=
            dLevelA_mono_d (descentBoundA α n) hcap α B htB
          have hdef : dLevelA (descentBoundA α n) α (t + 1) B
              = descentBoundA α n B + dLevelA (descentBoundA α n) α t (B + descentBoundA α n B + α) :=
            rfl
          show rankRecA α n B v.2 + dLevelA (descentBoundA α n) α t (B + rankRecA α n B v.2 + α) + α
              ≤ dLevelA (descentBoundA α n) α B B
          omega

/-- Weak boundedness (the `< descentBoundA` form), a corollary of the strong one. -/
theorem rankRecA_lt_descentBoundA (α : Nat) (n B : Nat) (v : NestedNat n) (hα : 1 ≤ α)
    (h : nestedLe n v (allBNested n B)) : rankRecA α n B v < descentBoundA α n B := by
  have := rankRecA_add_le_descentBoundA α n B v h
  omega

/-- **The α inner rank drops by `≥ α` on a `nestedOrder` step**, given format-`α` growth (`B' ≤ B + α`)
and `v'` bounded by `B'`. The α-analogue of `rankRec_drop` (`≥1` for `B' ≤ B+1`). Tail-drop: the `≥α`
IH cancels the `B'≤B+α` growth exactly. Top-drop: the strong boundedness covers the phantom `+α`. -/
theorem rankRecA_drop (α : Nat) : ∀ (n B B' : Nat) (v v' : NestedNat n),
    B' ≤ B + α → nestedLe n v' (allBNested n B') → nestedOrder n v' v →
    rankRecA α n B' v' + α ≤ rankRecA α n B v
  | 0, _, _, a, a', _, _, h => by
      have haa : a' + 1 ≤ a := h
      show α * a' + α ≤ α * a
      have hm : α * (a' + 1) ≤ α * a := Nat.mul_le_mul (Nat.le_refl α) haa
      rw [Nat.mul_succ] at hm
      exact hm
  | n + 1, B, B', v, v', hB, hle, h => by
      obtain ⟨_htop', htail'⟩ := hle
      rcases h with hlt | ⟨heq, hinner⟩
      · -- top-drop: v'.1 < v.1
        obtain ⟨s, hs⟩ : ∃ s, v.1 = s + 1 :=
          ⟨v.1 - 1, by have := Nat.lt_of_le_of_lt (Nat.zero_le v'.1) hlt; omega⟩
        show rankRecA α n B' v'.2
              + levelBudgetGA (descentBoundA α n) α 0 v'.1 (B' + rankRecA α n B' v'.2 + α) + α
            ≤ rankRecA α n B v.2
              + levelBudgetGA (descentBoundA α n) α 0 v.1 (B + rankRecA α n B v.2 + α)
        rw [hs, levelBudgetGA_succ]
        -- strong boundedness supplies the phantom +α
        have hir'strong : rankRecA α n B' v'.2 + α ≤ descentBoundA α n B' :=
          rankRecA_add_le_descentBoundA α n B' v'.2 htail'
        have hcapmono : descentBoundA α n B' ≤ descentBoundA α n (B + rankRecA α n B v.2 + α) :=
          descentBoundA_mono α n (by omega)
        have hle_v' : levelBudgetGA (descentBoundA α n) α 0 v'.1 (B' + rankRecA α n B' v'.2 + α)
            ≤ levelBudgetGA (descentBoundA α n) α 0 s
                (B + rankRecA α n B v.2 + α
                  + descentBoundA α n (B + rankRecA α n B v.2 + α) + α) :=
          Nat.le_trans
            (levelBudgetGA_mono_d (descentBoundA α n) (fun {_ _} hh => descentBoundA_mono α n hh) α 0
              (B' + rankRecA α n B' v'.2 + α) (show v'.1 ≤ s by omega))
            (levelBudgetGA_mono_B (descentBoundA α n) (fun {_ _} hh => descentBoundA_mono α n hh) α 0 s
              (by omega))
        omega
      · -- tail-drop: v'.1 = v.1, tail drops
        have ihd : rankRecA α n B' v'.2 + α ≤ rankRecA α n B v.2 :=
          rankRecA_drop α n B B' v.2 v'.2 hB htail' hinner
        show rankRecA α n B' v'.2
              + levelBudgetGA (descentBoundA α n) α 0 v'.1 (B' + rankRecA α n B' v'.2 + α) + α
            ≤ rankRecA α n B v.2
              + levelBudgetGA (descentBoundA α n) α 0 v.1 (B + rankRecA α n B v.2 + α)
        rw [heq]
        have hmono : levelBudgetGA (descentBoundA α n) α 0 v.1 (B' + rankRecA α n B' v'.2 + α)
            ≤ levelBudgetGA (descentBoundA α n) α 0 v.1 (B + rankRecA α n B v.2 + α) :=
          levelBudgetGA_mono_B (descentBoundA α n) (fun {_ _} hh => descentBoundA_mono α n hh) α 0 v.1
            (by omega)
        omega

end MachLib.IterExpDepthN
