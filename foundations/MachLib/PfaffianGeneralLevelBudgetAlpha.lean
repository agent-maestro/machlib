import MachLib.IterExpDepthNBudgetGen

/-!
# α-generalized level budget (general Pfaffian explicit bound — inner-rank foundation)

`levelBudgetG` (`IterExpDepthNBudgetGen.lean`) bakes in a per-drop reset headroom of **`+1`** (the
`B + cap B + 1` recursion) — right for the iterated-exp *tower* whose lower digits grow `≤ 1` per step.
The **inner** rank of a general chain (the `(cdegY0, b, …)` lex measure) has its lower digit `b` grow by
the format `α` per reduce (`b ≤ degreeX+2`, `degreeX` growing by `α`), so its budget needs a `+α` reset
headroom. `levelBudgetGA cap α` is that generalization; `levelBudgetGA cap 1 = levelBudgetG cap`. Pure
`Nat`, mirroring the existing file's monotonicity lemmas with `α` threaded through. This is the
foundation the α-recursive inner rank (`rankRecA`, next) is built on.
-/

namespace MachLib.IterExpDepthN

/-- α-generalized level budget: per-drop reset headroom `+α` in place of `+1`. -/
def levelBudgetGA (cap : Nat → Nat) (α Nleaf : Nat) : Nat → Nat → Nat
  | 0,     _ => Nleaf
  | d + 1, B => cap B + levelBudgetGA cap α Nleaf d (B + cap B + α)

@[simp] theorem levelBudgetGA_zero (cap : Nat → Nat) (α Nleaf B : Nat) :
    levelBudgetGA cap α Nleaf 0 B = Nleaf := rfl

@[simp] theorem levelBudgetGA_succ (cap : Nat → Nat) (α Nleaf d B : Nat) :
    levelBudgetGA cap α Nleaf (d + 1) B
      = cap B + levelBudgetGA cap α Nleaf d (B + cap B + α) := rfl

theorem Nleaf_le_levelBudgetGA (cap : Nat → Nat) (α Nleaf : Nat) :
    ∀ (d B : Nat), Nleaf ≤ levelBudgetGA cap α Nleaf d B
  | 0, _ => Nat.le_refl _
  | d + 1, B => by
      show Nleaf ≤ cap B + levelBudgetGA cap α Nleaf d (B + cap B + α)
      exact Nat.le_trans (Nleaf_le_levelBudgetGA cap α Nleaf d (B + cap B + α)) (Nat.le_add_left _ _)

/-- Monotone in `B`, given `cap` monotone. -/
theorem levelBudgetGA_mono_B (cap : Nat → Nat) (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (α Nleaf : Nat) :
    ∀ (d : Nat) {B B' : Nat}, B ≤ B' → levelBudgetGA cap α Nleaf d B ≤ levelBudgetGA cap α Nleaf d B'
  | 0, _, _, _ => Nat.le_refl _
  | d + 1, B, B', h => by
      have hc := hcap h
      show cap B + levelBudgetGA cap α Nleaf d (B + cap B + α)
          ≤ cap B' + levelBudgetGA cap α Nleaf d (B' + cap B' + α)
      have hrec := levelBudgetGA_mono_B cap hcap α Nleaf d
        (show B + cap B + α ≤ B' + cap B' + α from by omega)
      omega

theorem levelBudgetGA_le_succ (cap : Nat → Nat) (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (α Nleaf d B : Nat) : levelBudgetGA cap α Nleaf d B ≤ levelBudgetGA cap α Nleaf (d + 1) B := by
  rw [levelBudgetGA_succ]
  calc levelBudgetGA cap α Nleaf d B
        ≤ levelBudgetGA cap α Nleaf d (B + cap B + α) :=
        levelBudgetGA_mono_B cap hcap α Nleaf d (by omega)
    _ ≤ cap B + levelBudgetGA cap α Nleaf d (B + cap B + α) := Nat.le_add_left _ _

theorem levelBudgetGA_mono_d (cap : Nat → Nat) (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (α Nleaf B : Nat) {d d' : Nat} (h : d ≤ d') :
    levelBudgetGA cap α Nleaf d B ≤ levelBudgetGA cap α Nleaf d' B := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (levelBudgetGA_le_succ cap hcap α Nleaf _ B)

/-- `levelBudgetGA cap 1 = levelBudgetG cap` — the tower's `≤ 1` growth is the `α = 1` instance
(correctness anchor). -/
theorem levelBudgetGA_one_eq (cap : Nat → Nat) (Nleaf : Nat) :
    ∀ (d B : Nat), levelBudgetGA cap 1 Nleaf d B = levelBudgetG cap Nleaf d B
  | 0, _ => rfl
  | d + 1, B => by
      show cap B + levelBudgetGA cap 1 Nleaf d (B + cap B + 1)
          = cap B + levelBudgetG cap Nleaf d (B + cap B + 1)
      rw [levelBudgetGA_one_eq cap Nleaf d (B + cap B + 1)]

end MachLib.IterExpDepthN
