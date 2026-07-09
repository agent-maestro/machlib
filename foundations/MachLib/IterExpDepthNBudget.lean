import MachLib.IterExpDepthNEIrank

/-!
# Chain-N explicit bound — the level-indexed budget (step 4, arithmetic core)

The depth step's zero count is `#reduces + Ndepth m(leaf)`, and `#reduces` is a level-indexed budget over
`(degreeY_top, EIrank)` — the SAME shape as chain-2's `invPhi`/`levelBudget` (design §4′), with:

  * the per-level reduce cap `(G+1)(B+1)` → `capN m B = maxRank (allBNested B)` (EIrank's bound,
    `EIrank_le_maxRank`); a reduce strictly drops `EIrank` (`EIrank_reduce_lt`), so ≤ `capN` per level;
  * the growing budget argument `G` → `B` (the global degree bound: `degreeX` fixed, `degreeY ≤ +1`/reduce);
  * the base (chain-2's `0`/contradiction at `degreeY₁ = 0`) → `Nleaf` (the depth-below leaf `Ndepth m`).

This file is the reusable pure-`Nat` core: `capN` + its monotonicity, `levelBudgetN`, `invPhiN`, and the
closure lemmas the M5⁺ WF assembly (step 5) discharges — `invPhiN_reduce` (drops ≥1 on a reduce, absorbing
the Rolle `+1`), `invPhiN_trim_any` (non-increasing on a degree-trim), `invPhiN_mono_B` (the inner-lift
arm, degrees non-increasing). No new axioms.
-/

namespace MachLib.IterExpDepthN

open MachLib.ExplicitBound

/-- `capN m B` = `maxRank` of the all-`B` bound vector — the cap on `EIrank` at depth `m`, degree bound `B`
(`EIrank_le_maxRank`). The chain-N analog of chain-2's per-level reduce cap `(G+1)(B+1)`. -/
def capN (m B : Nat) : Nat := maxRank (m + 2) (allBNested (m + 2) B)

/-- `maxRank (allBNested B)` is monotone in `B` (both the head factor and the recursive tail grow). -/
theorem maxRank_allBNested_mono : ∀ (n : Nat) {B B' : Nat}, B ≤ B' →
    maxRank n (allBNested n B) ≤ maxRank n (allBNested n B')
  | 0, B, B', h => h
  | k + 1, B, B', h => by
      show B * (maxRank k (allBNested k B) + 1) + maxRank k (allBNested k B)
          ≤ B' * (maxRank k (allBNested k B') + 1) + maxRank k (allBNested k B')
      have ih := maxRank_allBNested_mono k h
      have hmul : B * (maxRank k (allBNested k B) + 1) ≤ B' * (maxRank k (allBNested k B') + 1) :=
        Nat.mul_le_mul h (Nat.add_le_add_right ih 1)
      omega

/-- `capN m` is monotone in `B`. -/
theorem capN_mono (m : Nat) {B B' : Nat} (h : B ≤ B') : capN m B ≤ capN m B' :=
  maxRank_allBNested_mono (m + 2) h

/-- **The level-indexed budget.** `d` = the `degreeY_top` level, `B` = the global degree budget, `Nleaf` =
the depth-below leaf. At each level: ≤ `capN m B` reduces, then a trim to the next level with `B` grown by
≤ `capN m B` (the `degreeY` growth); the base level is the leaf. -/
def levelBudgetN (m Nleaf : Nat) : Nat → Nat → Nat
  | 0,     _ => Nleaf
  | d + 1, B => capN m B + levelBudgetN m Nleaf d (B + capN m B + 1)

@[simp] theorem levelBudgetN_zero (m Nleaf B : Nat) : levelBudgetN m Nleaf 0 B = Nleaf := rfl

@[simp] theorem levelBudgetN_succ (m Nleaf d B : Nat) :
    levelBudgetN m Nleaf (d + 1) B = capN m B + levelBudgetN m Nleaf d (B + capN m B + 1) := rfl

/-- The leaf is a lower bound of the budget (it sits at the base and only summands are added). -/
theorem Nleaf_le_levelBudgetN (m Nleaf : Nat) : ∀ (d B : Nat), Nleaf ≤ levelBudgetN m Nleaf d B
  | 0, _ => Nat.le_refl _
  | d + 1, B => by
      show Nleaf ≤ capN m B + levelBudgetN m Nleaf d (B + capN m B + 1)
      exact Nat.le_trans (Nleaf_le_levelBudgetN m Nleaf d (B + capN m B + 1)) (Nat.le_add_left _ _)

/-- **Monotone in the degree budget `B`.** A larger `B` only increases the budget — so bounding the degrees
above suffices, and the inner block's grown degrees are absorbed at the next level (via `capN_mono`). -/
theorem levelBudgetN_mono_B (m Nleaf : Nat) :
    ∀ (d : Nat) {B B' : Nat}, B ≤ B' → levelBudgetN m Nleaf d B ≤ levelBudgetN m Nleaf d B'
  | 0, _, _, _ => Nat.le_refl _
  | d + 1, B, B', h => by
      have hcap := capN_mono m h
      show capN m B + levelBudgetN m Nleaf d (B + capN m B + 1)
          ≤ capN m B' + levelBudgetN m Nleaf d (B' + capN m B' + 1)
      have hrec := levelBudgetN_mono_B m Nleaf d
        (show B + capN m B + 1 ≤ B' + capN m B' + 1 from by omega)
      omega

/-- One extra level only adds budget (absorb the current level's growth via `mono_B`, then prepend). -/
theorem levelBudgetN_le_succ (m Nleaf d B : Nat) :
    levelBudgetN m Nleaf d B ≤ levelBudgetN m Nleaf (d + 1) B := by
  rw [levelBudgetN_succ]
  calc levelBudgetN m Nleaf d B
        ≤ levelBudgetN m Nleaf d (B + capN m B + 1) := levelBudgetN_mono_B m Nleaf d (by omega)
    _ ≤ capN m B + levelBudgetN m Nleaf d (B + capN m B + 1) := Nat.le_add_left _ _

/-- **Monotone in the level `d`.** -/
theorem levelBudgetN_mono_d (m Nleaf B : Nat) {d d' : Nat} (h : d ≤ d') :
    levelBudgetN m Nleaf d B ≤ levelBudgetN m Nleaf d' B := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (levelBudgetN_le_succ m Nleaf _ B)

/-- **The WF-induction invariant bound.** At `degreeY_top = 0` the leaf fires (`Nleaf`); at level `d+1`, the
current level's actual `EIrank` (`ir`) plus the lower levels' budget (with `B` grown by `ir`). -/
def invPhiN (m Nleaf : Nat) : Nat → Nat → Nat → Nat
  | 0,     _,  _ => Nleaf
  | d + 1, ir, B => ir + levelBudgetN m Nleaf d (B + ir + 1)

/-- **Reduce closure.** A reduce ties `degreeY_top` (level `d+1`), drops `EIrank` (`ir' + 1 ≤ ir`) and grows
the degree budget by ≤ 1 (`B' ≤ B + 1`); then `invPhiN` drops by ≥ 1 — absorbing the Rolle `+1`. -/
theorem invPhiN_reduce (m Nleaf d ir ir' B B' : Nat) (hir : ir' + 1 ≤ ir) (hB : B' ≤ B + 1) :
    invPhiN m Nleaf (d + 1) ir' B' + 1 ≤ invPhiN m Nleaf (d + 1) ir B := by
  show ir' + levelBudgetN m Nleaf d (B' + ir' + 1) + 1 ≤ ir + levelBudgetN m Nleaf d (B + ir + 1)
  have hmono := levelBudgetN_mono_B m Nleaf d
    (show B' + ir' + 1 ≤ B + ir + 1 from by omega)
  omega

/-- Trim, lower half: the child's `invPhiN` (level `d'`, inner rank within a level's cap) is `≤` the
`levelBudgetN` at any level `≥ d'`. -/
theorem invPhiN_trim (m Nleaf : Nat) {d d' : Nat} (ir' B' : Nat) (hd : d' ≤ d) (hir : ir' ≤ capN m B') :
    invPhiN m Nleaf d' ir' B' ≤ levelBudgetN m Nleaf d B' := by
  cases d' with
  | zero => exact Nleaf_le_levelBudgetN m Nleaf d B'
  | succ d'' =>
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      show ir' + levelBudgetN m Nleaf d'' (B' + ir' + 1)
          ≤ capN m B' + levelBudgetN m Nleaf e (B' + capN m B' + 1)
      have hrec : levelBudgetN m Nleaf d'' (B' + ir' + 1)
          ≤ levelBudgetN m Nleaf e (B' + capN m B' + 1) :=
        Nat.le_trans (levelBudgetN_mono_d m Nleaf (B' + ir' + 1) (show d'' ≤ e from by omega))
          (levelBudgetN_mono_B m Nleaf e (by omega))
      omega

/-- **Trim closure.** A degree-trim drops `degreeY_top` (`d' ≤ d`), does not raise the degree budget
(`B' ≤ B`), and exposes a child whose `EIrank` is within a level's cap (`ir' ≤ capN m B'`); then the
child's `invPhiN` is `≤` the source's. -/
theorem invPhiN_trim_any (m Nleaf : Nat) {d d' : Nat} (ir ir' B B' : Nat)
    (hd : d' ≤ d) (hB : B' ≤ B) (hir : ir' ≤ capN m B') :
    invPhiN m Nleaf d' ir' B' ≤ invPhiN m Nleaf (d + 1) ir B := by
  have h1 := invPhiN_trim m Nleaf ir' B' hd hir
  have h2 : levelBudgetN m Nleaf d B' ≤ levelBudgetN m Nleaf d (B + ir + 1) :=
    levelBudgetN_mono_B m Nleaf d (by omega)
  show invPhiN m Nleaf d' ir' B' ≤ ir + levelBudgetN m Nleaf d (B + ir + 1)
  omega

/-- **Inner-lift closure.** A lift ties `degreeY_top` and `EIrank`, and does not raise the degree budget
(`B ≤ B'` source→child means the child's `B` is `≤`; here stated as monotonicity). -/
theorem invPhiN_mono_B (m Nleaf d ir : Nat) {B B' : Nat} (h : B ≤ B') :
    invPhiN m Nleaf d ir B ≤ invPhiN m Nleaf d ir B' := by
  cases d with
  | zero => exact Nat.le_refl _
  | succ d =>
      show ir + levelBudgetN m Nleaf d (B + ir + 1) ≤ ir + levelBudgetN m Nleaf d (B' + ir + 1)
      exact Nat.add_le_add_left (levelBudgetN_mono_B m Nleaf d (by omega)) ir

end MachLib.IterExpDepthN
