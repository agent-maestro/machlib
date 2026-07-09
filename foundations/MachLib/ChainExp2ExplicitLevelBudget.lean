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

/-! ## The WF-induction invariant and its closure (design + arithmetic core)

The naive invariant `zeros(q) ≤ levelBudget B (degreeY₁ q) (degreeY₀ q)` does NOT close: a reduce
preserves `degreeY₁` but GROWS `degreeY₀`, and `levelBudget` is increasing in `G`, so the child's bound
is LARGER — adding the Rolle `+1` breaks it. The fix separates within-level counting (the inner rank,
which strictly DROPS per reduce) from cross-level (`levelBudget` over strictly-lower levels):

  `invPhi B d ir g = ir  +  (d = 0 ? 0 : levelBudget B (d−1) (g + ir + 1))`

where `ir = innerRank(q)` (the inner-lex rank `cdegY0·(B+1)+b`, drops ≥1 per reduce) and `g =
degreeY₀ q`. The two closure lemmas below — `invPhi_reduce` (Φ drops ≥1 on a reduce) and `invPhi_trim`
(Φ non-increasing on a trim, where `ir=0` since `lcY₁` is canonically zero) — are PURE `Nat`, and are
exactly what the WF induction discharges after instantiating `ir`,`g` with the Pfaffian quantities and
citing: reduce drops `ir` (`chain2Reduce_nestedLT_canon`), grows `degreeY₀` by ≤1
(`degreeY0_chain2Reduce_le`); trim drops `degreeY₁`, keeps `degreeY₀` (the trim `degreeY₀` tower, TODO),
zeros unchanged; `cdegY0(lcY₁) ≤ degreeY₀` (`cdegY0_lcY1_le_degreeY0`) and `b ≤ B` (the bridge). -/

/-- The WF-induction invariant bound (see the section docstring). -/
def invPhi (B : Nat) : Nat → Nat → Nat → Nat
  | 0,     ir, _ => ir
  | d + 1, ir, g => ir + levelBudget B d (g + ir + 1)

/-- **Reduce closure.** A reduce drops the inner rank (`ir' + 1 ≤ ir`) and grows the `degreeY₀`-budget
by ≤ 1 (`g' ≤ g + 1`); then `Φ` drops by ≥ 1 — absorbing the Rolle `+1`. The core inequality that makes
the reduce arm of the WF induction close, at any level `d`. -/
theorem invPhi_reduce (B d ir ir' g g' : Nat) (hir : ir' + 1 ≤ ir) (hg : g' ≤ g + 1) :
    invPhi B d ir' g' + 1 ≤ invPhi B d ir g := by
  cases d with
  | zero => exact hir
  | succ d =>
      show ir' + levelBudget B d (g' + ir' + 1) + 1 ≤ ir + levelBudget B d (g + ir + 1)
      have hmono := levelBudget_mono_G B d (show g' + ir' + 1 ≤ g + ir + 1 by omega)
      omega

/-- **Trim closure.** A trim leaves `lcY₁` canonically zero (`ir = 0` at the source), drops `degreeY₁`
(`d' ≤ d`), keeps `degreeY₀` (`g' ≤ g`), and the child's inner rank is within a level's worth
(`ir' + 1 ≤ (g+1)(B+1)`). Then the child's `Φ` is `≤` the source's `Φ = invPhi B (d+1) 0 g =
levelBudget B d (g+1)`. The core inequality that makes the trim arm close. -/
theorem invPhi_trim (B d d' ir' g g' : Nat) (hd : d' ≤ d) (hg : g' ≤ g)
    (hir : ir' + 1 ≤ (g + 1) * (B + 1)) :
    invPhi B d' ir' g' ≤ levelBudget B d (g + 1) := by
  have hstep : (g + 1) * (B + 1) ≤ (g + 1 + 1) * (B + 1) := Nat.mul_le_mul (Nat.le_succ _) (Nat.le_refl _)
  cases d' with
  | zero =>
      show ir' ≤ levelBudget B d (g + 1)
      have h3 : (g + 1 + 1) * (B + 1) ≤ levelBudget B d (g + 1) := level_le_levelBudget B d (g + 1)
      omega
  | succ d'' =>
      show ir' + levelBudget B d'' (g' + ir' + 1) ≤ levelBudget B d (g + 1)
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      rw [levelBudget_succ]
      have hlb : levelBudget B d'' (g' + ir' + 1)
          ≤ levelBudget B e (g + 1 + (g + 1 + 1) * (B + 1)) :=
        Nat.le_trans (levelBudget_mono_d B _ (show d'' ≤ e by omega))
          (levelBudget_mono_G B e (by omega))
      omega

/-- **Trim closure, source at level `d+1` with ANY inner rank `ir`.** The `ir=0`-in-trim assumption is
NOT needed (the trim fires on the x-degree component `= 0`, but `cdegY0` may be nonzero): a larger
source `ir` only makes `invPhi B (d+1) ir g` bigger. This is the form the WF induction's trim arm uses. -/
theorem invPhi_trim_any (B d d' ir ir' g g' : Nat) (hd : d' ≤ d) (hg : g' ≤ g)
    (hir : ir' + 1 ≤ (g + 1) * (B + 1)) :
    invPhi B d' ir' g' ≤ invPhi B (d + 1) ir g := by
  have h1 : invPhi B d' ir' g' ≤ levelBudget B d (g + 1) := invPhi_trim B d d' ir' g g' hd hg hir
  have h2 : levelBudget B d (g + 1) ≤ levelBudget B d (g + ir + 1) := levelBudget_mono_G B d (by omega)
  show invPhi B d' ir' g' ≤ ir + levelBudget B d (g + ir + 1)
  omega

/-- `invPhi` is monotone in the inner-rank argument. Lets a bound stated over the *exact* (noncomputable)
`innerRank` be weakened to one in terms of a computable upper bound — the syntactic-degree tool. -/
theorem invPhi_mono_ir (B d g : Nat) {ir ir' : Nat} (h : ir ≤ ir') :
    invPhi B d ir g ≤ invPhi B d ir' g := by
  cases d with
  | zero => exact h
  | succ d =>
    show ir + levelBudget B d (g + ir + 1) ≤ ir' + levelBudget B d (g + ir' + 1)
    exact Nat.add_le_add h (levelBudget_mono_G B d (by omega))

end MachLib.ExplicitBound
