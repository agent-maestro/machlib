import MachLib.ExplicitBoundRank

/-!
# Explicit chain-2 bound — the level-indexed recurrence (arithmetic core)

The A-bound cannot use `rankLex` with a fixed `A`: the inner component `cdegY0(lcY₁ q)` is bounded by
`degreeY₀ q` (`cdegY0_lcY1_le_degreeY0`), which GROWS `+1` per reduce, so no fixed `A` bounds it
globally — `A` is entangled with the reduce count itself. The resolution is a **level-indexed**
accounting, organized by the `degreeY₁` level (the outer measure component):

  * `reduce` PRESERVES `degreeY₁` and drops the inner `(cdegY0(lcY₁), b)` lex measure (adds one zero).
  * `trim` DROPS `degreeY₁` by ≥ 1 (adds no zero).

So the recursion runs a block of reduces at each `degreeY₁`-level `d`, then trims to `d−1`. At level `d`
with a `degreeY₀`-budget `G` (so `cdegY0(lcY₁ ·) ≤ G`) and x-degree budget `B` (so `b(·) ≤ B`, GLOBAL —
`degreeX` is non-increasing under both arms, `ChainExp2ExplicitTrim`):

  * the reduces at level `d` are ≤ the inner-lex rank `(G+1)(B+1)` (each strictly drops it);
  * `degreeY₀` then has grown to `≤ G + (G+1)(B+1)`, and a trim moves to level `d−1`.

This is the recurrence `Φ B d G = (G+1)(B+1) + Φ B (d−1) (G + (G+1)(B+1))`, `Φ B 0 G = (G+1)(B+1)` —
an explicit (exponential-in-`d`) zero-count bound. `levelBudget` below IS `Φ`; this file is its
reusable **arithmetic core** (the analogue of `rankLex` for the level accounting), pinned down
independent of the Pfaffian machinery. The eventual A-bound theorem is
`zeros.length ≤ levelBudget (degreeX p₀ + 2) (degreeY₁ p₀) (degreeY₀ p₀)`, proved by a double induction
(outer on `degreeY₁`, inner on the reduce block) whose per-step accounting is exactly this recurrence;
`levelBudget_mono_G` is what lets the inner block's grown `degreeY₀` be absorbed into the next level's
budget. Pure `Nat` arithmetic — no new axioms.
-/

namespace MachLib.ExplicitBound

/-- **The level-indexed budget `Φ B d G`.** `d` = the `degreeY₁` level, `G` = the `degreeY₀` budget,
`B` = the (global) x-degree budget. The explicit exponential-in-`d` zero-count bound; see the recurrence
in the module docstring. -/
def levelBudget (B : Nat) : Nat → Nat → Nat
  | 0,     G => (G + 1) * (B + 1)
  | d + 1, G => (G + 1) * (B + 1) + levelBudget B d (G + (G + 1) * (B + 1))

@[simp] theorem levelBudget_zero (B G : Nat) :
    levelBudget B 0 G = (G + 1) * (B + 1) := rfl

@[simp] theorem levelBudget_succ (B d G : Nat) :
    levelBudget B (d + 1) G = (G + 1) * (B + 1) + levelBudget B d (G + (G + 1) * (B + 1)) := rfl

/-- The per-level reduce bound `(G+1)(B+1)` is a summand of the budget, so the budget dominates it. -/
theorem level_le_levelBudget (B d G : Nat) : (G + 1) * (B + 1) ≤ levelBudget B d G := by
  cases d with
  | zero => exact Nat.le_refl _
  | succ d => exact Nat.le_add_right _ _

/-- **Monotone in the `degreeY₀`-budget `G`.** The property the accounting relies on: a larger `G`
only increases the budget, so bounding `degreeY₀` above suffices — the inner block's grown `degreeY₀`
is absorbed by evaluating the next level's budget at a larger `G`. -/
theorem levelBudget_mono_G (B : Nat) :
    ∀ (d : Nat) {G G' : Nat}, G ≤ G' → levelBudget B d G ≤ levelBudget B d G'
  | 0, G, G', h => by
      show (G + 1) * (B + 1) ≤ (G' + 1) * (B + 1)
      exact Nat.mul_le_mul (Nat.add_le_add_right h 1) (Nat.le_refl _)
  | d + 1, G, G', h => by
      show (G + 1) * (B + 1) + levelBudget B d (G + (G + 1) * (B + 1))
          ≤ (G' + 1) * (B + 1) + levelBudget B d (G' + (G' + 1) * (B + 1))
      have hmul : (G + 1) * (B + 1) ≤ (G' + 1) * (B + 1) :=
        Nat.mul_le_mul (Nat.add_le_add_right h 1) (Nat.le_refl _)
      exact Nat.add_le_add hmul (levelBudget_mono_G B d (Nat.add_le_add h hmul))

/-- **One extra `degreeY₁`-level only adds budget.** Adding a level absorbs the current level's
`degreeY₀` growth (via `mono_G`) then prepends a non-negative summand. -/
theorem levelBudget_le_succ (B d G : Nat) : levelBudget B d G ≤ levelBudget B (d + 1) G := by
  rw [levelBudget_succ]
  calc levelBudget B d G
        ≤ levelBudget B d (G + (G + 1) * (B + 1)) :=
            levelBudget_mono_G B d (Nat.le_add_right _ _)
    _ ≤ (G + 1) * (B + 1) + levelBudget B d (G + (G + 1) * (B + 1)) := Nat.le_add_left _ _

/-- **Monotone in the level `d`** (derived from `levelBudget_le_succ` by `Nat.le` induction). -/
theorem levelBudget_mono_d (B G : Nat) {d d' : Nat} (h : d ≤ d') :
    levelBudget B d G ≤ levelBudget B d' G := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (levelBudget_le_succ B _ G)

end MachLib.ExplicitBound
