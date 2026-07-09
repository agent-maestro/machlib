import MachLib.IterExpDepthNBudget

/-!
# Chain-N explicit bound — the CAP-GENERIC level-indexed budget (rework foundation)

The step-5 obstruction (design §4″): a FLAT `EIrank` with a uniform cap `capN m B = maxRank(allBNested B)`
does not thread — `EIrank` is monotone in `B`, and the reduce's `+1` degreeY growth forces `B → B+1`, which
fights the drop. The corrected structure is a **depth-recursive** budget: each `degreeY` level gets its own
chain-2-style `(level-index, inner-rank)` accounting, and the inner cap at level `k` is the budget at level
`k−1` — a recursion mirroring `chainNMeasureEI`'s own depth recursion.

The enabling refactor is here: the level-indexed budget, with the per-level cap abstracted from the concrete
`capN m` to an arbitrary **monotone function** `cap : Nat → Nat`. All the closure lemmas (`IterExpDepthNBudget`)
used only `capN_mono`, so they generalize verbatim. Then `invPhiN m = invPhiG (capN m)` (the flat instance),
and the nested `budgetRec` is built by *iterating* `invPhiG` with `cap` := the previous level's budget — which
is the whole point: the inner rank becomes a recursive budget, not a flat rank.
-/

namespace MachLib.IterExpDepthN

open MachLib.ExplicitBound

/-- The level-indexed budget with an abstract per-level cap function `cap`. `capN m`-instance recovers
`levelBudgetN`. -/
def levelBudgetG (cap : Nat → Nat) (Nleaf : Nat) : Nat → Nat → Nat
  | 0,     _ => Nleaf
  | d + 1, B => cap B + levelBudgetG cap Nleaf d (B + cap B + 1)

@[simp] theorem levelBudgetG_zero (cap : Nat → Nat) (Nleaf B : Nat) :
    levelBudgetG cap Nleaf 0 B = Nleaf := rfl

@[simp] theorem levelBudgetG_succ (cap : Nat → Nat) (Nleaf d B : Nat) :
    levelBudgetG cap Nleaf (d + 1) B = cap B + levelBudgetG cap Nleaf d (B + cap B + 1) := rfl

theorem Nleaf_le_levelBudgetG (cap : Nat → Nat) (Nleaf : Nat) :
    ∀ (d B : Nat), Nleaf ≤ levelBudgetG cap Nleaf d B
  | 0, _ => Nat.le_refl _
  | d + 1, B => by
      show Nleaf ≤ cap B + levelBudgetG cap Nleaf d (B + cap B + 1)
      exact Nat.le_trans (Nleaf_le_levelBudgetG cap Nleaf d (B + cap B + 1)) (Nat.le_add_left _ _)

/-- Monotone in `B`, given `cap` monotone. -/
theorem levelBudgetG_mono_B (cap : Nat → Nat) (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (Nleaf : Nat) :
    ∀ (d : Nat) {B B' : Nat}, B ≤ B' → levelBudgetG cap Nleaf d B ≤ levelBudgetG cap Nleaf d B'
  | 0, _, _, _ => Nat.le_refl _
  | d + 1, B, B', h => by
      have hc := hcap h
      show cap B + levelBudgetG cap Nleaf d (B + cap B + 1)
          ≤ cap B' + levelBudgetG cap Nleaf d (B' + cap B' + 1)
      have hrec := levelBudgetG_mono_B cap hcap Nleaf d
        (show B + cap B + 1 ≤ B' + cap B' + 1 from by omega)
      omega

theorem levelBudgetG_le_succ (cap : Nat → Nat) (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (Nleaf d B : Nat) : levelBudgetG cap Nleaf d B ≤ levelBudgetG cap Nleaf (d + 1) B := by
  rw [levelBudgetG_succ]
  calc levelBudgetG cap Nleaf d B
        ≤ levelBudgetG cap Nleaf d (B + cap B + 1) := levelBudgetG_mono_B cap hcap Nleaf d (by omega)
    _ ≤ cap B + levelBudgetG cap Nleaf d (B + cap B + 1) := Nat.le_add_left _ _

theorem levelBudgetG_mono_d (cap : Nat → Nat) (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (Nleaf B : Nat) {d d' : Nat} (h : d ≤ d') :
    levelBudgetG cap Nleaf d B ≤ levelBudgetG cap Nleaf d' B := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (levelBudgetG_le_succ cap hcap Nleaf _ B)

/-- The WF-induction invariant bound with an abstract cap. -/
def invPhiG (cap : Nat → Nat) (Nleaf : Nat) : Nat → Nat → Nat → Nat
  | 0,     _,  _ => Nleaf
  | d + 1, ir, B => ir + levelBudgetG cap Nleaf d (B + ir + 1)

/-- **Reduce closure** (cap-generic). -/
theorem invPhiG_reduce (cap : Nat → Nat) (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (Nleaf d ir ir' B B' : Nat) (hir : ir' + 1 ≤ ir) (hB : B' ≤ B + 1) :
    invPhiG cap Nleaf (d + 1) ir' B' + 1 ≤ invPhiG cap Nleaf (d + 1) ir B := by
  show ir' + levelBudgetG cap Nleaf d (B' + ir' + 1) + 1 ≤ ir + levelBudgetG cap Nleaf d (B + ir + 1)
  have hmono := levelBudgetG_mono_B cap hcap Nleaf d
    (show B' + ir' + 1 ≤ B + ir + 1 from by omega)
  omega

theorem invPhiG_trim (cap : Nat → Nat) (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (Nleaf : Nat) {d d' : Nat} (ir' B' : Nat) (hd : d' ≤ d) (hir : ir' ≤ cap B') :
    invPhiG cap Nleaf d' ir' B' ≤ levelBudgetG cap Nleaf d B' := by
  cases d' with
  | zero => exact Nleaf_le_levelBudgetG cap Nleaf d B'
  | succ d'' =>
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      show ir' + levelBudgetG cap Nleaf d'' (B' + ir' + 1)
          ≤ cap B' + levelBudgetG cap Nleaf e (B' + cap B' + 1)
      have hrec : levelBudgetG cap Nleaf d'' (B' + ir' + 1)
          ≤ levelBudgetG cap Nleaf e (B' + cap B' + 1) :=
        Nat.le_trans (levelBudgetG_mono_d cap hcap Nleaf (B' + ir' + 1) (show d'' ≤ e from by omega))
          (levelBudgetG_mono_B cap hcap Nleaf e (by omega))
      omega

/-- **Trim closure** (cap-generic). -/
theorem invPhiG_trim_any (cap : Nat → Nat) (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (Nleaf : Nat) {d d' : Nat} (ir ir' B B' : Nat)
    (hd : d' ≤ d) (hB : B' ≤ B) (hir : ir' ≤ cap B') :
    invPhiG cap Nleaf d' ir' B' ≤ invPhiG cap Nleaf (d + 1) ir B := by
  have h1 := invPhiG_trim cap hcap Nleaf ir' B' hd hir
  have h2 : levelBudgetG cap Nleaf d B' ≤ levelBudgetG cap Nleaf d (B + ir + 1) :=
    levelBudgetG_mono_B cap hcap Nleaf d (by omega)
  show invPhiG cap Nleaf d' ir' B' ≤ ir + levelBudgetG cap Nleaf d (B + ir + 1)
  omega

/-- **Inner-lift closure** (cap-generic). -/
theorem invPhiG_mono_B (cap : Nat → Nat) (hcap : ∀ {B B' : Nat}, B ≤ B' → cap B ≤ cap B')
    (Nleaf d ir : Nat) {B B' : Nat} (h : B ≤ B') :
    invPhiG cap Nleaf d ir B ≤ invPhiG cap Nleaf d ir B' := by
  cases d with
  | zero => exact Nat.le_refl _
  | succ d =>
      show ir + levelBudgetG cap Nleaf d (B + ir + 1) ≤ ir + levelBudgetG cap Nleaf d (B' + ir + 1)
      exact Nat.add_le_add_left (levelBudgetG_mono_B cap hcap Nleaf d (by omega)) ir

/-! ## The flat budget is the `capN m`-instance -/

/-- `levelBudgetN m` is `levelBudgetG (capN m)`. -/
theorem levelBudgetN_eq_G (m Nleaf d B : Nat) :
    levelBudgetN m Nleaf d B = levelBudgetG (capN m) Nleaf d B := by
  induction d generalizing B with
  | zero => rfl
  | succ d ih => show capN m B + _ = capN m B + _; rw [ih]

/-- `invPhiN m` is `invPhiG (capN m)`. -/
theorem invPhiN_eq_G (m Nleaf d ir B : Nat) :
    invPhiN m Nleaf d ir B = invPhiG (capN m) Nleaf d ir B := by
  cases d with
  | zero => rfl
  | succ d => show ir + levelBudgetN m Nleaf d _ = ir + levelBudgetG (capN m) Nleaf d _
              rw [levelBudgetN_eq_G]

end MachLib.IterExpDepthN
