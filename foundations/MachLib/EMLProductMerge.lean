import MachLib.EMLPeelRecursion
import MachLib.EMLGermInvariance
import MachLib.EMLBasisOverhead

/-!
# The merge's price, paid — and the class it was supposed to buy is the class we started in

`EMLPeelRecursion` records two prices the peel route never paid, and this file pays the second one
and prices the consequence:

> **The merged right-hand germ is a product**, `A₂ · C`. EML has no product node, so representing it
> as a tree costs more than one `eml`. That price is likewise **not computed here**.

The route that follows from it — *work in a class closed under products, redo the peel there, and see
what the terminal cells become* — is the obvious seventh attempt. **It is closed here, and the reason
is that the class is not new.**

## §1 — what the merge needs, and what it costs

The merge is `peel_shape_pos`: `log A₂ + log C = log (A₂ · C)`. So the recursion needs its germ class
closed under **products** and under **totalised `log`** — nothing else; the left germ stays a subtree
of `A` and is never merged.

Both are EML-internal, and were before this file existed:

```
mulGen_eval     (u v : EMLTree) (x : Real) : (mulGen u v).eval x = u.eval x * v.eval x
mulGen_depth_le (u v : EMLTree)            : (mulGen u v).depth ≤ 112 + max u.depth v.depth
logTree_eval    (t : EMLTree) (x : Real)   : (logTree t).eval x = log (t.eval x)
logTree_depth   (t : EMLTree)              : (logTree t).depth = 3 + t.depth
```

`mulGen_eval` carries **no hypothesis at all** — not positivity, not `x`. `EMLRingClosure` lifted the
side conditions in 2026-09 and no file in the decay programme had cited it before this one. So a merge costs
**≤ 115 depth levels** (`mergeTree_depth_le`), and the accumulator is an ordinary EML tree
(`mergeTree`).

Reciprocals are free for the same reason and the research file's own observation is the special case:
`recipTree` gives `e / t` at `+2`, and `EMLCharacterisation` gives the general statement —
`InEML f ↔ ExpLogClosure f`, the closure of the constants and `id` under `+`, `−`, `×`, `exp`, `log`.

## §2 — the class the route asks for

**It does not exist as an extension.** `prodClosure_iff_inEML` proves it both ways: the smallest
class containing the EML germs and closed under products and totalised `log` **is** the EML germs.

## §3 — and the complexity bound survives, which is what kills it

The crux question was whether bounded EML depth generates products of unboundedly many factors.
It does not, and the count is exact: the merge multiplies the accumulator by **one** germ per peel and
then takes a `log`, so a run on a left germ `A` performs `A.lspTree` merges — the same number
`EMLPeelRecursion` bounds by the depth (`peel_terminates`). Hence

```
peelAccum_depth_le :  (peelAccum A R).depth ≤ Nat.max R.depth A.depth + 115 * A.lspTree
peel_accumulator_bounded :  A.depth ≤ j → C.depth ≤ j → (peelAccum A C).depth ≤ 116 * j
```

Uniformity is **not** lost. That is the falsification arm's answer, and it is the wrong answer for the
route: a bounded class is a class `EMLPeelRecursion` §3 already applies to.

## §4 — the terminal cell, and it is an equivalence

```
PeelTerminalAccum ↔ EmlGermApproach          (peelTerminalAccum_iff_emlGermApproach)
```

* **⟹** costs nothing: `peelAccum (const 0) C = C` by `rfl`. A leaf left germ performs **no merges**,
  so the product-closed cell **contains** `PeelTerminalConstZero` verbatim, which §4(6) proved is the
  conjecture. Closing the class cannot shrink a cell that quantifies over the class.
* **⟸** is where §3 is spent: the accumulator never leaves EML and its depth is `≤ 116 · j`, so the
  conjecture at `116 · j` supplies the cell at `j`.

Both directions, per `EmlGermApproachResearch.md` §9 — and an equivalence with a converse is not
progress. Read positively: **the peel with the merge paid is a self-reduction of the conjecture at
depth `j` to the conjecture at depth `116 · j`.** Fourth sighting of the same direction of travel
(`recipTree` `+2`, `posEmbed` `+4`, `A − log C` `+1`, the merge `+115` per step).

And the statement does not depend on *this* class: `terminalCell_of_class_is_the_conjecture` fixes any
carrier `G` with any complexity measure into which EML trees embed with bounded complexity, and
concludes `EmlGermApproach` from its terminal cell. **No enlargement of the right-hand germ class can
shrink the terminal cell, because the cell quantifies over the class.**

## §5 — the other arm: refusing to land in EML costs the measure

The escape is to stop presenting the left germ syntactically — in a germ class, `exp (log g) = g`
restores the peel's shape at every positive germ, so the recursion need never stop. That arm is closed
too, and by the measure rather than the cell: `no_germInvariant_peel_bound` shows **no function of the
germ bounds the peel count**, because `selfLeftNode` (`EMLGermInvariance` §5b) re-presents any tree two
spine levels up *with the same germ*, unconditionally, and iterates. A parameter that survives the
closure is germ-invariant, and §4(5) proved that class empty.

So the route is squeezed: **pay the merge's price and you are in §4(6); refuse to stop and you are in
§4(5).**

## §6 — the fixture table: every verdict unchanged, one column added

| §3 fixture | merges (`lspTree`) | accumulator depth | verdict |
|---|---|---|---|
| `recipTree t` | 2 | `+230` | constant, as before |
| `posEmbed t` | 1 | `+115` | constant, as before |
| `capNode n` | 1 | `+115` | constant, as before |
| `deepDecay m` | **2** for every `m` | `≤ max C.depth (m+4) + 230` | **BLIND** — `peelCount_cannot_carry_floor` is untouched |
| `gapTarget n c` | `n + 1` | `≤ max C.depth (n+1) + 115(n+1)` | over-works where nothing is needed |
| `meetTree` / `posTree` | 1 / 2 | — | separated, as before |

The closure adds `115` per merge to a column that was not carrying `k` and still is not. Nothing in
the table moves, which is the point: **paying the price changes the arithmetic and no verdict.**

## Two things this does NOT close

* The **first** unpaid price of `EMLPeelRecursion` — a single right-hand germ for the whole tail needs
  eventual sign determination for every right child on the left spine (`evSign_all`, and with it the
  analytic axiom block). `peel_merge_tree` is still **pointwise**, with `0 < A₂.eval x` and
  `0 < R.eval x` at the point. The route dies before that price is due, exactly as in §4(6).
* `lspTree` as a measure. It descends, it terminates, and the merge now composes into trees. What is
  closed is the **cell**, again.

## Scope

**Bounds nothing, discharges nothing, assumes nothing.** No axiom; the `DecayFloor` ⇄
`EmlGermApproach` ⇄ `GrowthEnvelope` row stays open, one obligation. This is a route-closure and a
fixture set in the sense `EmlGermApproachResearch.md` §3 uses the word.
-/

namespace MachLib

open Real

/-! ## §1 — the merge, with the price paid

`mergeTree M R` is the right-hand germ after one merge, **as a tree**: `log (M · R)`. Its two
ingredients are `EMLRingClosure`'s unconditional product and `EMLAdditionClosureFailure`'s
unconditional `log`; neither is re-derived here. -/

/-- **The merged accumulator, as an EML tree.** `log (M · R)` — one `mulGen`, one `logTree`. -/
noncomputable def mergeTree (M R : EMLTree) : EMLTree := logTree (mulGen M R)

theorem mergeTree_eval (M R : EMLTree) (x : Real) :
    (mergeTree M R).eval x = log (M.eval x * R.eval x) := by
  rw [mergeTree, logTree_eval, mulGen_eval]

/-- **The price, computed.** `EMLPeelRecursion` says representing the merged germ "costs more than one
`eml`" and does not say how much. It is `115` levels, and it is the same `115` at every step. -/
theorem mergeTree_depth_le (M R : EMLTree) :
    (mergeTree M R).depth ≤ 115 + Nat.max M.depth R.depth := by
  have h : (mulGen M R).depth ≤ 112 + Nat.max M.depth R.depth := mulGen_depth_le M R
  have e : (mergeTree M R).depth = 3 + (mulGen M R).depth := logTree_depth (mulGen M R)
  omega

/-- **One peel step, with a TREE accumulator.** `peel_shape_pos` with the product named — the shape
comes back with the right-hand germ an ordinary EML tree, which is what the recursion was missing. -/
theorem peel_merge_tree (A₁ A₂ R : EMLTree) (x : Real)
    (h2 : 0 < A₂.eval x) (hR : 0 < R.eval x) :
    (EMLTree.eml A₁ A₂).eval x - log (R.eval x)
      = exp (A₁.eval x) - (mergeTree A₂ R).eval x := by
  rw [mergeTree_eval]
  exact peel_shape_pos A₁ A₂ R x h2 hR

/-- **The clamped branch keeps its shape too**, with the accumulator just `log R` — no product, since
totalised `log` kills the non-positive factor. -/
theorem peel_merge_tree_nonpos (A₁ A₂ R : EMLTree) (x : Real) (h2 : A₂.eval x ≤ 0) :
    (EMLTree.eml A₁ A₂).eval x - log (R.eval x)
      = exp (A₁.eval x) - (logTree R).eval x := by
  rw [logTree_eval]
  exact peel_shape_nonpos A₁ A₂ R x h2

/-- **The composed step, inequality form.** `peel_step_composed` with the merged germ a tree rather
than a bare product: the gap at `eml A₁ A₂` dominates the target times the gap at `A₁`. -/
theorem peel_step_tree (A₁ A₂ R : EMLTree) (x : Real)
    (h2 : 0 < A₂.eval x) (hR : 0 < R.eval x)
    (hgap : R.eval x < exp ((EMLTree.eml A₁ A₂).eval x)) :
    R.eval x * (exp (A₁.eval x) - (mergeTree A₂ R).eval x)
      ≤ exp ((EMLTree.eml A₁ A₂).eval x) - R.eval x := by
  have h := peel_step_gives_tree_form (EMLTree.eml A₁ A₂) R x hR hgap
  rw [peel_merge_tree A₁ A₂ R x h2 hR] at h
  exact h

/-- **A specimen for the step**, because a conditional theorem is not evidence until its hypotheses
are instantiated. `A₁ = var`, `A₂ = R = const 1`: the right child is positive, the target is positive,
and the gap hypothesis is `1 < exp (exp x)`. -/
theorem peel_step_tree_specimen (x : Real) :
    (EMLTree.const (1 : Real)).eval x
        * (exp (EMLTree.var.eval x) - (mergeTree (EMLTree.const 1) (EMLTree.const 1)).eval x)
      ≤ exp ((EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x)
        - (EMLTree.const (1 : Real)).eval x := by
  refine peel_step_tree EMLTree.var (EMLTree.const 1) (EMLTree.const 1) x zero_lt_one_ax
    zero_lt_one_ax ?_
  show (1 : Real) < exp ((EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x)
  have h : exp (0 : Real) < exp ((EMLTree.eml EMLTree.var (EMLTree.const 1)).eval x) := by
    refine exp_lt ?_
    show (0 : Real) < exp (EMLTree.var.eval x) - log ((1 : Real))
    rw [log_one]
    have e : exp (EMLTree.var.eval x) - (0 : Real) = exp (EMLTree.var.eval x) := by mach_ring
    rw [e]
    exact exp_pos _
  rwa [exp_zero] at h

/-! ## §2 — the closure the route asks for, and it is the class we started in

*"Define the smallest class containing EML germs and closed under multiplication (and whatever else
the merge actually needs)."* Done, as an inductive class, and identified. -/

/-- **The closure the merge needs**: EML germs, products, totalised `log`. -/
inductive ProdClosure : (Real → Real) → Prop where
  | emb (t : EMLTree) : ProdClosure t.eval
  | mul {f g : Real → Real} : ProdClosure f → ProdClosure g → ProdClosure (fun x => f x * g x)
  | log {f : Real → Real} : ProdClosure f → ProdClosure (fun x => Real.log (f x))

/-- **The class is the EML germs, both ways.** `⟸` is the embedding; `⟹` is `mulGen` and `logTree`,
neither of which carries a hypothesis. So there is no product-closed extension of EML to redo the peel
in — the route's premise is false at the class level, before any measure or cell is considered. -/
theorem prodClosure_iff_inEML (f : Real → Real) : ProdClosure f ↔ InEML f := by
  constructor
  · intro h
    induction h with
    | emb t => exact ⟨t, fun _ => rfl⟩
    | mul _ _ ih1 ih2 =>
        obtain ⟨a, ha⟩ := ih1; obtain ⟨b, hb⟩ := ih2
        exact ⟨mulGen a b, fun x => by rw [mulGen_eval, ha, hb]⟩
    | log _ ih =>
        obtain ⟨a, ha⟩ := ih
        exact ⟨logTree a, fun x => by rw [logTree_eval, ha]⟩
  · rintro ⟨t, ht⟩
    have he : t.eval = f := funext ht
    rw [← he]
    exact ProdClosure.emb t

/-- **Reciprocals were already inside**, as `EmlGermApproachResearch.md` §3 half-records: `recipTree`
gives `e / t` at `+2` depth with no hypothesis on `t` at all, so the class is closed under it for
free. Stated here because the question *"products only, or products and reciprocals?"* is the one the
route opens with. -/
theorem prodClosure_recip (t : EMLTree) : ProdClosure (fun x => exp (1 - log (t.eval x))) := by
  have he : (recipTree t).eval = fun x => exp (1 - log (t.eval x)) :=
    funext (fun x => recipTree_eval t x)
  rw [← he]
  exact ProdClosure.emb (recipTree t)

/-! ## §3 — the run, and its complexity

The recursion merges **one** germ per peel and reads no right child of the left germ except to merge
it. So the accumulated germ's complexity is governed by `lspTree`, which `peel_terminates` already
bounds by the depth. -/

/-- **The accumulator after peeling the whole leftmost spine.** One `mergeTree` per `eml` node on the
spine; a leaf leaves the accumulator alone. -/
noncomputable def peelAccum : EMLTree → EMLTree → EMLTree
  | EMLTree.const _, R => R
  | EMLTree.var, R => R
  | EMLTree.eml A₁ A₂, R => peelAccum A₁ (mergeTree A₂ R)

theorem peelAccum_const (c : Real) (R : EMLTree) : peelAccum (EMLTree.const c) R = R := rfl

theorem peelAccum_var (R : EMLTree) : peelAccum EMLTree.var R = R := rfl

theorem peelAccum_eml (A₁ A₂ R : EMLTree) :
    peelAccum (EMLTree.eml A₁ A₂) R = peelAccum A₁ (mergeTree A₂ R) := rfl

/-- Both children sit at or below the node's depth — the two facts the accumulation bound needs,
stated without `omega` so the `max` spelling never has to be negotiated. -/
private theorem depth_left_le (A B : EMLTree) : A.depth ≤ (EMLTree.eml A B).depth :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_left _ 1)

private theorem depth_right_le (A B : EMLTree) : B.depth ≤ (EMLTree.eml A B).depth :=
  Nat.le_trans (Nat.le_max_right _ _) (Nat.le_add_left _ 1)

/-- **The complexity bound survives the closure**, and the constant is `115` per merge. The crux
question of the route — whether a bounded-depth pair generates products of unboundedly many factors —
is answered NO by the shape of the merge: one factor per peel, and `peel_terminates` bounds the
peels. -/
theorem peelAccum_depth_le : ∀ (A R : EMLTree),
    (peelAccum A R).depth ≤ Nat.max R.depth A.depth + 115 * A.lspTree := by
  intro A
  induction A with
  | const c =>
      intro R
      have h : R.depth ≤ Nat.max R.depth (EMLTree.const c).depth := Nat.le_max_left _ _
      have e : (peelAccum (EMLTree.const c) R).depth = R.depth := by rw [peelAccum_const]
      have hl : (EMLTree.const c).lspTree = 0 := rfl
      rw [hl]
      omega
  | var =>
      intro R
      have h : R.depth ≤ Nat.max R.depth EMLTree.var.depth := Nat.le_max_left _ _
      have e : (peelAccum EMLTree.var R).depth = R.depth := by rw [peelAccum_var]
      have hl : EMLTree.var.lspTree = 0 := rfl
      rw [hl]
      omega
  | eml A₁ A₂ ih1 _ =>
      intro R
      have h1 := ih1 (mergeTree A₂ R)
      have h2 := mergeTree_depth_le A₂ R
      have hRle : R.depth ≤ Nat.max R.depth (EMLTree.eml A₁ A₂).depth := Nat.le_max_left _ _
      have hDle : (EMLTree.eml A₁ A₂).depth ≤ Nat.max R.depth (EMLTree.eml A₁ A₂).depth :=
        Nat.le_max_right _ _
      have hA2 : Nat.max A₂.depth R.depth ≤ Nat.max R.depth (EMLTree.eml A₁ A₂).depth :=
        Nat.max_le.mpr ⟨Nat.le_trans (depth_right_le A₁ A₂) hDle, hRle⟩
      have hstep : Nat.max (mergeTree A₂ R).depth A₁.depth
          ≤ Nat.max R.depth (EMLTree.eml A₁ A₂).depth + 115 := by
        refine Nat.max_le.mpr ⟨by omega, ?_⟩
        have h := Nat.le_trans (depth_left_le A₁ A₂) hDle
        omega
      have hl : (EMLTree.eml A₁ A₂).lspTree = A₁.lspTree + 1 := rfl
      rw [peelAccum_eml, hl]
      omega

/-- **The accumulated germ of a depth-`j` pair is an EML tree of depth `≤ 116 · j`.** Bounded — so
`EMLPeelRecursion` §3 applies to it, which is exactly why the route dies. -/
theorem peel_accumulator_bounded (A C : EMLTree) (j : Nat) (hA : A.depth ≤ j) (hC : C.depth ≤ j) :
    (peelAccum A C).depth ≤ 116 * j := by
  have h1 := peelAccum_depth_le A C
  have h2 : A.lspTree ≤ j := EMLTree.peel_terminates A j hA
  have h3 : Nat.max C.depth A.depth ≤ j := Nat.max_le.mpr ⟨hC, hA⟩
  have h4 : 115 * A.lspTree ≤ 115 * j := Nat.mul_le_mul_left 115 h2
  omega

/-! ## §4 — the terminal cell, in the product-closed vocabulary

The recursion now runs to a leaf with everything a tree. Here is the cell it stops at. -/

/-- **The terminal cell of the product-closed recursion**: the left germ peeled to a leaf, the right
germ whatever the run accumulated. -/
def PeelTerminalAccum : Prop :=
  ∀ j : Nat, ∃ k : Nat, ∀ (A C : EMLTree) (X₀ : Real),
    A.depth ≤ j → C.depth ≤ j → 1 ≤ X₀ →
    (∀ x : Real, X₀ ≤ x → (peelAccum A C).eval x < exp ((EMLTree.const 0).eval x)) →
    ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
      exp (-(EMLTree.towerFn k x)) ≤ exp ((EMLTree.const 0).eval x) - (peelAccum A C).eval x

/-- **A leaf left germ performs no merges**, so the product-closed cell contains `EMLPeelRecursion`'s
height-zero cell verbatim — and that one is the conjecture. Closing the class cannot shrink a cell
that quantifies over the class. -/
theorem peelTerminalConstZero_of_peelTerminalAccum (h : PeelTerminalAccum) :
    PeelTerminalConstZero := by
  intro j
  obtain ⟨k, hk⟩ := h j
  refine ⟨k, ?_⟩
  intro C X₀ hC hX₀ hlt
  have h0 : (EMLTree.const (0 : Real)).depth ≤ j := by simp only [EMLTree.depth]; omega
  have hpre : ∀ x : Real, X₀ ≤ x →
      (peelAccum (EMLTree.const 0) C).eval x < exp ((EMLTree.const 0).eval x) := by
    intro x hx
    rw [peelAccum_const]
    exact hlt x hx
  obtain ⟨X₁, hX₁, hf⟩ := hk (EMLTree.const 0) C X₀ h0 hC hX₀ hpre
  refine ⟨X₁, hX₁, fun x hx => ?_⟩
  have h := hf x hx
  rwa [peelAccum_const] at h

/-- **…and the conjecture gives the cell back**, at depth `116 · j`. This is where §3's bound is
spent: the accumulator never leaves EML and its depth is bounded, so the cell is no *harder* than the
conjecture either. -/
theorem peelTerminalAccum_of_emlGermApproach (hG : EmlGermApproach) : PeelTerminalAccum := by
  intro j
  obtain ⟨k, hk⟩ := hG (116 * j)
  refine ⟨k, ?_⟩
  intro A C X₀ hA hC hX₀ hlt
  have hd : (peelAccum A C).depth ≤ 116 * j := peel_accumulator_bounded A C j hA hC
  have h0 : (EMLTree.const (0 : Real)).depth ≤ 116 * j := by simp only [EMLTree.depth]; omega
  exact hk (EMLTree.const 0) (peelAccum A C) X₀ h0 hd hX₀ hlt

/-- **The product-closed terminal cell IS the conjecture — both ways.** The forward direction costs
nothing (a leaf performs no merges); the converse costs the depth inflation `j ↦ 116 · j`, which the
closure bound pays for. Per `EmlGermApproachResearch.md` §9, an equivalence with a converse is not
progress: the route has reduced the obligation to itself, one class wider and `116 ×` deeper. -/
theorem peelTerminalAccum_iff_emlGermApproach : PeelTerminalAccum ↔ EmlGermApproach :=
  ⟨fun h => peelTerminalConstZero_iff_emlGermApproach.mp
      (peelTerminalConstZero_of_peelTerminalAccum h),
   peelTerminalAccum_of_emlGermApproach⟩

/-! ### The same statement, at the width of any class whatever

Nothing above used products except to name the class. What does the work is that the cell quantifies
over the right-hand germs, so a **larger** class gives a **larger** cell. -/

/-- **No enlargement of the right-hand germ class can shrink the terminal cell.** For any carrier `G`
with any complexity measure `cx` into which EML trees embed with bounded complexity, the height-zero
terminal cell over `G` implies the conjecture.

This is the seventh mechanism at its real width: it is not about products, and not about peeling. A
recursion may work in transseries, in a Hardy field, in any closure of the EML germs whatever — if it
stops at "the left germ has exponential height 0", it has reduced the obligation to itself. -/
theorem terminalCell_of_class_is_the_conjecture
    {G : Type} (val : G → Real → Real) (cx : G → Nat) (emb : EMLTree → G)
    (hval : ∀ (t : EMLTree) (x : Real), val (emb t) x = t.eval x)
    (hcx : ∀ t : EMLTree, cx (emb t) ≤ t.depth)
    (hcell : ∀ j : Nat, ∃ k : Nat, ∀ (g : G) (X₀ : Real), cx g ≤ j → 1 ≤ X₀ →
      (∀ x : Real, X₀ ≤ x → val g x < exp ((EMLTree.const 0).eval x)) →
      ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
        exp (-(EMLTree.towerFn k x)) ≤ exp ((EMLTree.const 0).eval x) - val g x) :
    EmlGermApproach := by
  refine peelTerminalConstZero_iff_emlGermApproach.mp ?_
  intro j
  obtain ⟨k, hk⟩ := hcell j
  refine ⟨k, ?_⟩
  intro C X₀ hC hX₀ hlt
  have hcxC : cx (emb C) ≤ j := Nat.le_trans (hcx C) hC
  have hpre : ∀ x : Real, X₀ ≤ x → val (emb C) x < exp ((EMLTree.const 0).eval x) := by
    intro x hx
    rw [hval]
    exact hlt x hx
  obtain ⟨X₁, hX₁, hf⟩ := hk (emb C) X₀ hcxC hX₀ hpre
  refine ⟨X₁, hX₁, fun x hx => ?_⟩
  have h := hf x hx
  rwa [hval] at h

/-! ## §5 — the other arm: a germ class has no peel count

The escape from §4 is to stop reading the syntax — in a class of **germs**, `exp (log g) = g` restores
the peel's shape at every positive germ, so the recursion need never reach a leaf. That arm is closed
by the measure instead of the cell, and `EMLGermInvariance`'s `selfLeftNode` is the whole argument:
it re-presents any tree **two spine levels up with the same germ**, unconditionally. -/

/-- Iterated germ-preserving re-presentation: `n` applications of `selfLeftNode`. -/
noncomputable def iterSelf : Nat → EMLTree → EMLTree
  | 0, t => t
  | n + 1, t => selfLeftNode (iterSelf n t)

theorem iterSelf_germ : ∀ (n : Nat) (t : EMLTree), (iterSelf n t).eval = t.eval := by
  intro n
  induction n with
  | zero => intro t; rfl
  | succ m ih =>
      intro t
      show (selfLeftNode (iterSelf m t)).eval = t.eval
      rw [selfLeftNode_germ]
      exact ih t

/-- **Two spine levels per step**, so the peel count of a fixed germ is unbounded. -/
theorem iterSelf_lsp : ∀ (n : Nat) (t : EMLTree),
    (iterSelf n t).lspTree = t.lspTree + 2 * n := by
  intro n
  induction n with
  | zero => intro t; show t.lspTree = t.lspTree + 0; omega
  | succ m ih =>
      intro t
      have h : (selfLeftNode (iterSelf m t)).lspTree = (iterSelf m t).lspTree + 2 := rfl
      show (selfLeftNode (iterSelf m t)).lspTree = t.lspTree + 2 * (m + 1)
      rw [h, ih t]
      omega

/-- **No function of the germ bounds the peel count.** So a recursion working in a germ class — which
is what "a class closed under products" is, once the syntax is dropped — has no terminal cell to
reach and no measure to reach it by. Together with `no_germInvariant_wfDescent` (§4(5), which empties
the germ-invariant descent class outright) this closes the second arm.

Read with `peelTerminalAccum_iff_emlGermApproach`: **pay the merge's price and the cell is the
conjecture; refuse to stop and the measure is gone.** -/
theorem no_germInvariant_peel_bound (f : (Real → Real) → Nat)
    (hf : ∀ t : EMLTree, t.lspTree ≤ f t.eval) : False := by
  have hlsp := iterSelf_lsp (f EMLTree.var.eval + 1) EMLTree.var
  have hgerm := iterSelf_germ (f EMLTree.var.eval + 1) EMLTree.var
  have hb := hf (iterSelf (f EMLTree.var.eval + 1) EMLTree.var)
  rw [hgerm] at hb
  rw [hlsp] at hb
  have hv : EMLTree.var.lspTree = 0 := rfl
  omega

/-- **Both verdicts on the instrument.** `lspTree` is a live measure on trees — it descends, it
terminates, and it separates the meeting boundary (`lsp_separates_meeting`) — and it is refuted only
as a function of the **germ**. The witness is one tree and its re-presentation. -/
theorem lspTree_not_germInvariant :
    (selfLeftNode EMLTree.var).eval = EMLTree.var.eval ∧
    (selfLeftNode EMLTree.var).lspTree ≠ EMLTree.var.lspTree := by
  refine ⟨selfLeftNode_germ EMLTree.var, ?_⟩
  have h : (selfLeftNode EMLTree.var).lspTree = 2 := rfl
  have hv : EMLTree.var.lspTree = 0 := rfl
  omega

/-! ## §6 — the fixtures, priced under the extended recursion

Every family in `EmlGermApproachResearch.md` §3, with the merge column added. The peel counts are
`EMLPeelRecursion` §2's and do not move; what is new is the accumulator's depth. -/

/-- **The extremal family is still blind, and now with a computed accumulator.** `deepDecay m` merges
twice for every `m` — the accumulator's depth tracks `m` only through the *operands*, never through
the merge count — while the floor it forces is `m + 1`. `peelCount_cannot_carry_floor` is untouched
by the closure. -/
theorem prod_peel_blind_on_deepDecay (m : Nat) (C : EMLTree) :
    (deepDecay m).lspTree = 2 ∧
    (peelAccum (deepDecay m) C).depth ≤ Nat.max C.depth (m + 4) + 230 := by
  refine ⟨lsp_deepDecay m, ?_⟩
  have h1 := peelAccum_depth_le (deepDecay m) C
  have h2 : (deepDecay m).lspTree = 2 := lsp_deepDecay m
  have h3 : (deepDecay m).depth = m + 4 := deepDecay_depth m
  rw [h2, h3] at h1
  omega

/-- **…and the family the measure does follow still over-works.** `gapTarget n c` merges `n + 1`
times, paying `115` a piece, for a gap that is the constant `c` and a floor of height `0`. The
anti-correlation `peel_measure_anticorrelated` records survives the closure with a bigger constant. -/
theorem prod_peel_overworks_on_gapTarget (n : Nat) (c : Real) (C : EMLTree) :
    (gapTarget n c).lspTree = n + 1 ∧
    (peelAccum (gapTarget n c) C).depth ≤ Nat.max C.depth (n + 1) + 115 * (n + 1) := by
  refine ⟨lsp_gapTarget n c, ?_⟩
  have h1 := peelAccum_depth_le (gapTarget n c) C
  have h2 : (gapTarget n c).lspTree = n + 1 := lsp_gapTarget n c
  have h3 : (gapTarget n c).depth = n + 1 := gapTarget_depth n c
  rw [h2, h3] at h1
  omega

/-! ## §7 — the mechanism, in one statement -/

/-- **Mechanism (7).** Three facts, and the route is between them:

1. the class the route asks for is the class it started in (`prodClosure_iff_inEML`);
2. its complexity bound survives — `116 · j` — which is what makes `EMLPeelRecursion` §3 apply
   (`peel_accumulator_bounded`);
3. so the terminal cell is the conjecture, **with a converse** (`peelTerminalAccum_iff_emlGermApproach`),
   and no class enlargement whatever can change that (`terminalCell_of_class_is_the_conjecture`).

The escape — dropping the syntax so the recursion never stops — is `no_germInvariant_peel_bound`. -/
theorem product_closure_changes_nothing :
    (∀ f : Real → Real, ProdClosure f ↔ InEML f) ∧
    (∀ (A C : EMLTree) (j : Nat), A.depth ≤ j → C.depth ≤ j →
      (peelAccum A C).depth ≤ 116 * j) ∧
    (PeelTerminalAccum ↔ EmlGermApproach) :=
  ⟨prodClosure_iff_inEML, peel_accumulator_bounded, peelTerminalAccum_iff_emlGermApproach⟩

end MachLib
