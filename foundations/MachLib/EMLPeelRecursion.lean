import MachLib.EMLPolarityMeasure

/-!
# Peeling as a recursion — the sixth failed mechanism, and it fails somewhere new

`EmlGermApproachResearch.md` §4(3) records *"peeling an exponential"* as failed, on the grounds that
`gap_ge_target_mul_log_gap` reduces the gap to the pair `(A, log C)`, which sits one depth **above**
`A` and `C`. That is a statement about **depth**. It is not the whole story, and this file says what
the rest of it is.

Peeling also strips one `exp` from the **left** germ, so a recursion whose measure is the number of
`exp`s remaining on the left — the leftmost-spine length `lspTree`, a *one-sided, syntactic*
measure — descends while the depth budget is allowed to grow. That class is the one the research
file leaves open after `EMLPolarityMeasure` (§4(4), *"a measure descending on **one** side only"*)
and after `EMLGermInvariance` (§4(5), which empties the **germ-invariant** version of it — so
`lspTree` being syntactic is load-bearing, not incidental). So the route is not ruled out by
anything already proved, and it is built here.

## What was built, in the order the discipline requires

1. **The recursion and its measure, stated before anything is proved** (§1). The step is the
   peeling inequality at **germ** level (`peel_step`), stated on values rather than on trees
   because the right-hand germ after one peel is the evaluation of no tree the recursion was
   handed; `gap_ge_target_mul_log_gap` is its instance (`peel_step_gives_tree_form`). The measure
   is `lspTree` — **syntactic**, which §4(5) makes load-bearing, and one-sided: it descends into
   **left children only**. Two shape lemmas (`peel_shape_pos`, `peel_shape_nonpos`) show the
   peeled gap is again of the form `exp (left germ) − (right germ)`, so the step composes;
   `peel_terminates` bounds the leftmost-spine length by the depth bound, so the recursion
   performs at most `lspTree A + 1` peels — one per `eml` node on that spine, plus the first —
   hence at most `j + 1`.
2. **The §3 fixtures, measured before any theorem was attempted** (§2).
3. **The terminal cells, identified** (§3). This is where it dies.

## The fixture table — and the two entries that decide it

| §3 fixture | `lspTree` | height the floor needs | verdict |
|---|---|---|---|
| `recipTree t` | **2**, for every `t` | — | priced at a CONSTANT |
| `posEmbed t` | **1**, for every `t` | — | priced at a constant |
| `capNode n` | **1**, for every `n` | — | priced at a constant |
| `deepDecay m` | **2**, for every `m` | `m + 1` | **BLIND** — the extremal family |
| `gapTarget n c` | `n + 1` | `0` | over-works where nothing is needed |
| `meetTree` / `posTree` | `1` / `2` | — | **separated** (the polarity pair is blind here) |

Two of those rows are the argument.

* **`deepDecay m` is priced at `2` for every `m`** (`lsp_deepDecay`) while the floor it forces is
  `m + 1` (`floorHeight_of_deepDecay`). `gapTarget n c` is priced at `n + 1` while the floor it
  needs is `0` (`gapTarget_meets_floor`). The peel count is not merely a loose bound on the height:
  it is **anti-correlated** with it (`peel_measure_anticorrelated`), and no function of it can
  produce `k` (`peelCount_cannot_carry_floor`, which concludes `False`).
* So the recursion's `k` **must** come from the terminal cell, exactly as the route intends. §3 is
  about what that cell is.

Only one row is a genuine positive, and it is recorded because `EMLPolarityMeasure` could not get
it: `lspTree` **separates the hypothesis boundary** — `meetTree` (gap identically `0`) and
`posTree` (`exp (1 − x)`, positive everywhere) have the same four-vector under both earlier
candidates (`measure_blind_at_meeting`) and different peel counts here (`lsp_separates_meeting`).

## Where it dies: THE TERMINAL CELL IS THE CONJECTURE

The route's premise is that the floor comes from *"a germ pair with no cancellation left"*. There
are exactly two ways the recursion can stop, and **each one is the whole obligation**:

```
PeelTerminalNoCancel   ↔  GrowthEnvelope     (peelTerminalNoCancel_iff_growthEnvelope)
PeelTerminalConstZero  ↔  EmlGermApproach    (peelTerminalConstZero_iff_emlGermApproach)
```

* **T1, no cancellation** (`C ≤ 0` on the ray). `approach_gap_ge_exp_of_nonpos` leaves the gap at
  least `exp (A x)`, and a floor `exp (−towerFn k x) ≤ exp (A x)` is exactly an **upper** envelope
  on `−A` uniform in depth. That is `GrowthEnvelope` — the third name of the same obligation. Both
  directions are proved and each costs `+2` depth; the cell→envelope direction costs `+1` height
  and the envelope→cell direction costs none. **The cancellation-free cell is not free.**
* **T2, nothing left to peel.** The recursion stops when the left germ has no `exp` to strip, i.e.
  at `lspTree A = 0`. Take the very simplest such cell, `A = const 0`. It implies `DecayFloor` at
  `−2` depth by an argument the corpus **already contains**: `decayFloor_of_emlGermApproach` never
  instantiates `A` at anything but `const 0`. So peeling `A` down to a leaf achieves nothing —
  `EmlGermApproach` restricted to a single leaf left germ implies `EmlGermApproach` in full.

> **The recursion terminates, in at most `j + 1` steps, and lands on the statement it started
> from.**

That is a different failure from the five before it. Mechanisms (1)–(5) die on the **measure**:
`recipTree` travels up and no both-children descent survives it, and no germ-invariant parameter
descends at all. This one has a measure that works — one-sided, syntactic, terminating, outside
`WfDescent` because it never claims descent to the right child, and outside `GermDescent` because
it reads the tree. It dies on the **base case**. The number of peels is bounded by `j + 1`
exactly as hoped; what is not bounded is the difficulty of the cell the peels reach.

## Two costs this route would pay even if the terminal cell were free

Recorded so that a seventh attempt does not pay them again.

* **The merge is pointwise; the recursion needs it on a tail.** Composing two peels needs
  `A x − log (C x)` rewritten as `exp (A₁ x) − log (·)`, and which of `peel_shape_pos` /
  `peel_shape_nonpos` applies is decided **by the sign of `A₂` at `x`**. Totalised `log` makes both
  branches true pointwise and neither uniform: a single right-hand germ for the whole tail needs
  eventual sign determination for every right child along the left spine, i.e. `evSign_all`, and
  with it the analytic axiom block (`rolle_ct`, `analytic_finite_zeros_compact`) that
  `EMLDecayFloorIsGrowth` was deliberately routed around. **This is a real price and it is unpaid
  here**, because the route dies before it is due.
* **The merged right-hand germ is a product**, `A₂ · C`. EML has no product node, so representing
  it as a tree costs more than one `eml`. That price is likewise **not computed here**: the T2 death
  is independent of it, since the terminal right-hand germ is at least as deep as the original `C`
  however the merge is spelt.

## What this rules IN and OUT, at the right width

**Out.** Any argument whose base case is *"a germ pair with no cancellation"* or *"a pair whose left
germ has exponential height 0"*. Both cells are equivalent to the conjecture, so a recursion
reaching them has reduced nothing, whatever its measure and however fast it terminates. That is
stated about the **cells**, not about peeling: it holds for *every* recursion that stops there.

**In, still.** A recursion whose terminal cell is genuinely smaller than either of these — the
open question is whether one exists, and §3 says what it must avoid. `lspTree` itself is untouched
as a *measure*: it descends, it terminates, and it separates the meeting boundary. Nothing here
says the peel step is wrong; `peel_step` and the shape lemmas are proved and usable.

## Scope

**Bounds nothing, discharges nothing, assumes nothing.** No axiom; the `DecayFloor` ⇄
`EmlGermApproach` ⇄ `GrowthEnvelope` row stays open, one obligation. This is a route-closure and a
fixture set in the sense `EmlGermApproachResearch.md` §3 uses the word.
-/

namespace MachLib

namespace EMLTree

/-! ## §1a — the measure, stated before anything is proved

`lspTree` is the length of the **leftmost** spine: the number of `exp`s the peel can strip from the
left germ before it reaches a leaf. It is deliberately **one-sided** — it says nothing whatever
about right children, which is what puts it outside `WfDescent` (`EMLPolarityMeasure` §4) rather
than inside it. -/

/-- **The peel measure.** One `eml` node on the leftmost spine costs one; right children are not
read at all. -/
def lspTree : EMLTree → Nat
  | const _ => 0
  | var     => 0
  | eml A _ => A.lspTree + 1

theorem lspTree_eml (A B : EMLTree) : (eml A B).lspTree = A.lspTree + 1 := rfl

/-- **The measure descends on the left**, which is the side the peel recurses into. -/
theorem lspTree_left_lt (A B : EMLTree) : A.lspTree < (eml A B).lspTree := by
  rw [lspTree_eml]; omega

/-- **And it is silent on the right, by design.** A right child may be priced anywhere — above,
below or equal — so `lspTree` is not a `WfDescent` measure and `recip_not_below` does not reach it.
The witness is `capNode`: the node is priced `1` and its right child `n`. -/
theorem lspTree_right_unbounded (n : Nat) :
    (towerTree (n + 1)).lspTree = n + 1 ∧
    (eml (const 0) (towerTree (n + 1))).lspTree = 1 := by
  constructor
  · show (towerTree n).lspTree + 1 = n + 1
    have h : ∀ k : Nat, (towerTree k).lspTree = k := by
      intro k
      induction k with
      | zero => rfl
      | succ j ih => show (towerTree j).lspTree + 1 = j + 1; omega
    rw [h n]
  · rfl

/-- **The peel count is bounded by the exponential height**, hence by the depth. -/
theorem lspTree_le_ehTree : ∀ t : EMLTree, t.lspTree ≤ t.ehTree := by
  intro t
  induction t with
  | const c => exact Nat.le_refl 0
  | var     => exact Nat.le_refl 0
  | eml A B ihA ihB =>
      have h := ehTree_left_le A B
      show A.lspTree + 1 ≤ (eml A B).ehTree
      omega

theorem lspTree_le_depth (t : EMLTree) : t.lspTree ≤ t.depth :=
  Nat.le_trans (lspTree_le_ehTree t) (ehTree_le_depth t)

/-- **Termination, and the bound the route needs.** The recursion peels once per `eml` node on the
leftmost spine of the left germ, so a depth-`j` left germ admits at most `j` peels. This half of the
route works exactly as intended. -/
theorem peel_terminates (A : EMLTree) (j : Nat) (h : A.depth ≤ j) : A.lspTree ≤ j :=
  Nat.le_trans (lspTree_le_depth A) h

end EMLTree

open Real

/-! ## §1b — the step, at germ level

The route asks for a **semantic** measure, so the step is stated on germ *values* rather than on
trees. `gap_ge_target_mul_log_gap` is this lemma's instance at `a := A.eval x`, `c := C.eval x`
(`peel_step_gives_tree_form`), so nothing is re-derived: what is added is the generality the
recursion needs, since the right-hand germ after one peel is not the evaluation of any tree the
recursion was handed. -/

/-- **One peel.** Where `0 < c < exp a`, the gap `exp a − c` dominates the gap one `log` down,
scaled by `c`. Same proof as `gap_ge_target_mul_log_gap`, with the trees removed. -/
theorem peel_step (a c : Real) (hc : 0 < c) (hgap : c < exp a) :
    c * (a - log c) ≤ exp a - c := by
  have hlt : log c < a := by
    have h := log_lt_log hc hgap
    rw [log_exp] at h; exact h
  have hu : 0 < a - log c := by
    have u := add_lt_add_left hlt (-(log c))
    have e1 : -log c + log c = 0 := by mach_ring
    have e2 : -log c + a = a - log c := by mach_ring
    rw [e1, e2] at u; exact u
  have hkey : c * exp (a - log c) = exp a := by
    have e : log c + (a - log c) = a := by mach_ring
    calc c * exp (a - log c)
        = exp (log c) * exp (a - log c) := by rw [exp_log hc]
      _ = exp (log c + (a - log c)) := by rw [exp_add]
      _ = exp a := by rw [e]
  have h1 : 1 + (a - log c) < exp (a - log c) := exp_gt_one_plus_self _ hu
  have h2 : a - log c ≤ exp (a - log c) - 1 := by
    have u := add_lt_add_left h1 (-(1 : Real))
    have e1 : -(1 : Real) + (1 + (a - log c)) = a - log c := by mach_ring
    have e2 : -(1 : Real) + exp (a - log c) = exp (a - log c) - 1 := by mach_ring
    rw [e1, e2] at u; exact le_of_lt u
  have h3 := mul_le_mul_of_nonneg_left h2 (le_of_lt hc)
  have e3 : c * (exp (a - log c) - 1) = c * exp (a - log c) - c := by mach_ring
  rw [e3, hkey] at h3
  exact h3

/-- **The tree form is an instance**, so `§4(3)`'s inequality and this one are one lemma and the
generalisation is machine-checked rather than asserted. -/
theorem peel_step_gives_tree_form (A C : EMLTree) (x : Real)
    (hC : 0 < C.eval x) (hgap : C.eval x < exp (A.eval x)) :
    C.eval x * (A.eval x - log (C.eval x)) ≤ exp (A.eval x) - C.eval x :=
  peel_step (A.eval x) (C.eval x) hC hgap

/-- **The peeled pair's positivity IS inherited.** `EmlGermApproachResearch.md` §6 warns that it is
not automatic; the warning is about the *hypothesis*, not about the step. Given the strict
hypothesis the obligation already carries, the peeled gap is strictly positive with no further
input — which is why `eTree (eTree A)`, whose gap is identically `0`, fails at the *entry* to the
recursion rather than inside it. -/
theorem peel_gap_pos (a c : Real) (hc : 0 < c) (hgap : c < exp a) : 0 < a - log c := by
  have hlt : log c < a := by
    have h := log_lt_log hc hgap
    rw [log_exp] at h; exact h
  have u := add_lt_add_left hlt (-(log c))
  have e1 : -log c + log c = 0 := by mach_ring
  have e2 : -log c + a = a - log c := by mach_ring
  rw [e1, e2] at u; exact u

/-! ## §1c — the step composes: the peeled gap has the same shape

One peel takes `exp (A x) − C x` to `A x − log (C x)`. For a second peel that has to be read again
as `exp (·) − (·)`, which needs the top of `A` unfolded. Both branches of the sign of `A`'s right
child give the shape back, and **that is the whole reason the recursion exists**. -/

/-- **The merge, positive branch.** `log A₂ + log C = log (A₂ · C)`, so the peeled gap is again an
`exp` minus a `log`, with left germ the **left child** of `A`. -/
theorem peel_shape_pos (A₁ A₂ C : EMLTree) (x : Real)
    (h2 : 0 < A₂.eval x) (hC : 0 < C.eval x) :
    (EMLTree.eml A₁ A₂).eval x - log (C.eval x)
      = exp (A₁.eval x) - log (A₂.eval x * C.eval x) := by
  show exp (A₁.eval x) - log (A₂.eval x) - log (C.eval x)
      = exp (A₁.eval x) - log (A₂.eval x * C.eval x)
  rw [log_mul h2 hC]
  mach_ring

/-- **The merge, clamped branch.** A non-positive right child totalises its `log` to `0`, so the
shape comes back with the right-hand germ **unchanged**. -/
theorem peel_shape_nonpos (A₁ A₂ C : EMLTree) (x : Real) (h2 : A₂.eval x ≤ 0) :
    (EMLTree.eml A₁ A₂).eval x - log (C.eval x)
      = exp (A₁.eval x) - log (C.eval x) := by
  show exp (A₁.eval x) - log (A₂.eval x) - log (C.eval x)
      = exp (A₁.eval x) - log (C.eval x)
  rw [log_nonpos h2]
  mach_ring

/-- **One full step of the recursion.** From a gap at left germ `eml A₁ A₂` to a gap at left germ
`A₁` — one strictly smaller in `lspTree` (`lspTree_left_lt`) — with the right-hand germ merged. -/
theorem peel_step_composed (A₁ A₂ C : EMLTree) (x : Real)
    (h2 : 0 < A₂.eval x) (hC : 0 < C.eval x)
    (hgap : C.eval x < exp ((EMLTree.eml A₁ A₂).eval x)) :
    C.eval x * (exp (A₁.eval x) - log (A₂.eval x * C.eval x))
      ≤ exp ((EMLTree.eml A₁ A₂).eval x) - C.eval x := by
  have h := peel_step_gives_tree_form (EMLTree.eml A₁ A₂) C x hC hgap
  rw [peel_shape_pos A₁ A₂ C x h2 hC] at h
  exact h

/-! ## §2 — the §3 fixtures, measured before any theorem was attempted

Every adversarial family in `EmlGermApproachResearch.md` §3, priced by the peel measure. These are
computed here once so that the next candidate is tested rather than argued about — the same
discipline `EMLPolarityMeasure` §6 follows. -/

/-- **`recipTree` is priced at a CONSTANT.** The family that kills mechanisms (1)–(4) costs two
peels however deep `t` is. Under a both-children measure that would be fatal
(`no_wf_descent_of_cheap_recip`); here it is not a contradiction, because `lspTree` never claims to
descend to a right child — it is instead the first sign that the measure is not doing the work. -/
theorem lsp_recipTree (t : EMLTree) : (recipTree t).lspTree = 2 := rfl

/-- **`posEmbed` likewise**, at one. -/
theorem lsp_posEmbed (t : EMLTree) : (posEmbed t).lspTree = 1 := rfl

/-- **`capNode n` likewise**, at one, for every `n` — while its right child is the `(n+1)`-tower. -/
theorem lsp_capNode (n : Nat) : (capNode n).lspTree = 1 := rfl

theorem lsp_towerTree : ∀ n : Nat, (EMLTree.towerTree n).lspTree = n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih => show (EMLTree.towerTree k).lspTree + 1 = k + 1; omega

/-- **`gapTarget n c` is the one family the measure follows** — and it is the family that needs
tower height `0` (`gapTarget_meets_floor`). The recursion does `n + 1` peels for a gap that is the
constant `c`. -/
theorem lsp_gapTarget (n : Nat) (c : Real) : (gapTarget n c).lspTree = n + 1 := by
  show (EMLTree.towerTree n).lspTree + 1 = n + 1
  rw [lsp_towerTree n]

/-- **The extremal family is priced at a CONSTANT.** `deepDecay m` forces tower height `m + 1`
(`floorHeight_of_deepDecay`) and costs two peels for every `m`. The recursion is blind exactly
where `EmlGermApproachResearch.md` §3 says an instrument must not be. -/
theorem lsp_deepDecay (m : Nat) : (deepDecay m).lspTree = 2 := rfl

/-- **The one genuine positive: the meeting boundary is SEPARATED.** `meetTree` (gap identically
`0`) and `posTree` (`exp (1 − x)`, positive everywhere) carry the same four-vector under both
earlier candidates (`measure_blind_at_meeting`) and the same `depth`; the peel measure tells them
apart. It changes no verdict below, and it is recorded because it is the first measure in this
corpus that does. -/
theorem lsp_separates_meeting :
    meetTree.lspTree = 1 ∧ posTree.lspTree = 2 ∧ meetTree.lspTree ≠ posTree.lspTree ∧
      meetTree.depth = posTree.depth := by
  have h1 : meetTree.lspTree = 1 := rfl
  have h2 : posTree.lspTree = 2 := rfl
  refine ⟨h1, h2, fun h => ?_, rfl⟩
  rw [h1, h2] at h
  omega

/-! ### The verdict: `k` cannot come from the peel count

Two fixtures, pulling opposite ways. This is the measurement the route has to survive and does
not. -/

/-- **The peel count is ANTI-correlated with the height the floor needs.** `deepDecay m` is priced
at `2` for every `m` and falls below the height-`m` floor; `gapTarget n 1` is priced at `n + 1` for
every `n` and meets the height-`0` floor. -/
theorem peel_measure_anticorrelated (m n : Nat) :
    (deepDecay m).lspTree = 2 ∧
    (gapTarget n 1).lspTree = n + 1 ∧
    (∀ x : Real, 1 ≤ x → (deepDecay m).eval x < exp (-(EMLTree.towerFn m x))) ∧
    (∀ x : Real, 0 ≤ x → exp (-(EMLTree.towerFn 0 x))
      ≤ exp ((EMLTree.towerTree n).eval x) - (gapTarget n 1).eval x) :=
  ⟨lsp_deepDecay m, lsp_gapTarget n 1,
   fun _ hx => deepDecay_below_floor m hx,
   fun _ hx => gapTarget_meets_floor n hx⟩

/-- **No floor height is a function of the peel count.** The mirror of
`deepDecay_forces_first_component` for this measure, and sharper: there the second component was
merely pinned, here the *whole* measure is, so the conclusion is `False` rather than a bound.

Read positively, this is what sends the route to its terminal cell: **`k` must come from the base
case**, because the recursion's own parameter cannot supply it. -/
theorem peelCount_cannot_carry_floor (f : Nat → Nat)
    (hf : ∀ t : EMLTree, (∀ x : Real, 1 ≤ x → 0 < t.eval x) →
      ∃ X₁ : Real, 1 ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
        exp (-(EMLTree.towerFn (f t.lspTree) x)) ≤ t.eval x) : False := by
  have key : ∀ m : Nat, m + 1 ≤ f 2 := by
    intro m
    obtain ⟨X₁, hX₁, h⟩ := hf (deepDecay m) (fun x _ => deepDecay_pos m x)
    rw [lsp_deepDecay m] at h
    exact floorHeight_of_deepDecay m (f 2) X₁ hX₁ h
  have h := key (f 2)
  omega

/-- **Discrimination — the refutation is about the MEASURE, not about the shape of the statement.**
The instrument must be shown capable of both verdicts before either is read. Run the same argument
against `depth` and it cannot fire: `deepDecay m` has depth `m + 4`, so what it forces is
`m + 1 ≤ f (m + 4)` — the bound `EmlGermApproachResearch.md` §6 records as *attained*, not a
contradiction. `lspTree` is refuted because it is **constant** on that family; a tree parameter is
not refuted for being a tree parameter. -/
theorem lspTree_refuted_where_depth_is_not (m : Nat) :
    (deepDecay m).depth = m + 4 ∧ (deepDecay m).lspTree = 2 :=
  ⟨deepDecay_depth m, lsp_deepDecay m⟩

/-! ## §3 — the terminal cells, and why the route dies at them

The recursion terminates (`peel_terminates`) and its parameter cannot carry `k`
(`peelCount_cannot_carry_floor`), so everything rests on the cell it stops at. There are two ways to
stop, and **each is the conjecture**. -/

/-! ### T1 — no cancellation left

The route's own description of its base case. `approach_gap_ge_exp_of_nonpos` says a non-positive
target leaves the gap at least `exp (A x)`, so the cell asks for `exp (−towerFn k x) ≤ exp (A x)`
uniformly in depth — an **upper envelope on `−A`**, which is `GrowthEnvelope`. -/

/-- **The cancellation-free cell**, stated in the obligation's own vocabulary. -/
def PeelTerminalNoCancel : Prop :=
  ∀ j : Nat, ∃ k : Nat, ∀ (A C : EMLTree) (X₀ : Real),
    A.depth ≤ j → C.depth ≤ j → 1 ≤ X₀ →
    (∀ x : Real, X₀ ≤ x → C.eval x ≤ 0) →
    ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
      exp (-(EMLTree.towerFn k x)) ≤ exp (A.eval x) - C.eval x

/-- **The envelope two levels up gives the cancellation-free cell**, at the same height. Routed
through `approachTarget A`, whose value is `1 − A x`, so the envelope's ceiling becomes a floor on
`A` with a constant to spare. -/
theorem peelTerminalNoCancel_of_growthEnvelope (hGE : GrowthEnvelope) : PeelTerminalNoCancel := by
  intro j
  obtain ⟨k, hk⟩ := hGE (j + 2)
  refine ⟨k, ?_⟩
  intro A C X₀ hA _hC hX₀ hnonpos
  have hd : (approachTarget A).depth ≤ j + 2 := by rw [approachTarget_depth]; omega
  obtain ⟨X₁, hX₁, hup⟩ := hk (approachTarget A) X₀ hd hX₀
  refine ⟨X₁, hX₁, fun x hx => ?_⟩
  have hceil : (1 : Real) - A.eval x ≤ EMLTree.towerFn k x := by
    have h := hup x hx
    rw [approachTarget_eval] at h; exact h
  -- `1 - A x ≤ T` gives `-T ≤ A x - 1 ≤ A x`
  have hlow : -(EMLTree.towerFn k x) ≤ A.eval x := by
    have u := add_le_add_wit hceil (le_refl (A.eval x - 1))
    have e1 : (1 : Real) - A.eval x + (A.eval x - 1) = 0 := by mach_ring
    have e2 : EMLTree.towerFn k x + (A.eval x - 1) = A.eval x - 1 + EMLTree.towerFn k x := by
      mach_ring
    rw [e1, e2] at u
    -- `0 ≤ A x - 1 + T`, hence `-T ≤ A x - 1`
    have v := add_le_add_wit u (le_refl (-(EMLTree.towerFn k x)))
    have e3 : (0 : Real) + -(EMLTree.towerFn k x) = -(EMLTree.towerFn k x) := by mach_ring
    have e4 : A.eval x - 1 + EMLTree.towerFn k x + -(EMLTree.towerFn k x) = A.eval x - 1 := by
      mach_ring
    rw [e3, e4] at v
    have w := add_le_add_wit v (le_of_lt zero_lt_one_ax)
    have e5 : -(EMLTree.towerFn k x) + (0 : Real) = -(EMLTree.towerFn k x) := by mach_ring
    have e6 : A.eval x - 1 + (1 : Real) = A.eval x := by mach_ring
    rw [e5, e6] at w
    exact w
  exact le_trans (exp_monotone hlow)
    (approach_gap_ge_exp_of_nonpos A C x (hnonpos x (le_trans hX₁ hx)))

/-- **…and the cell two levels up gives the envelope back**, at height `k + 1`. The input is
`A := approachTarget t` with `C := const 0`, whose value is `0` — non-positive, so the cell applies
with no sign analysis at all. -/
theorem growthEnvelope_of_peelTerminalNoCancel (hT : PeelTerminalNoCancel) : GrowthEnvelope := by
  intro j
  obtain ⟨k, hk⟩ := hT (j + 2)
  refine ⟨k + 1, ?_⟩
  intro t X₀ hdepth hX₀
  have hA : (approachTarget t).depth ≤ j + 2 := by rw [approachTarget_depth]; omega
  have hC : (EMLTree.const 0).depth ≤ j + 2 := by simp only [EMLTree.depth]; omega
  obtain ⟨X₁, hX₁, hf⟩ :=
    hk (approachTarget t) (EMLTree.const 0) X₀ hA hC hX₀ (fun _ _ => le_refl 0)
  refine ⟨X₁, hX₁, fun x hx => ?_⟩
  have hx1 : (1 : Real) ≤ x := le_trans hX₀ (le_trans hX₁ hx)
  have h := hf x hx
  have hgap : exp ((approachTarget t).eval x) - (EMLTree.const 0).eval x
      = exp (1 - t.eval x) := by
    rw [approachTarget_eval]
    show exp (1 - t.eval x) - (0 : Real) = exp (1 - t.eval x)
    mach_ring
  rw [hgap] at h
  -- strip the `exp`
  have hlog : -(EMLTree.towerFn k x) ≤ 1 - t.eval x := by
    have m := log_le_log (exp_pos (-(EMLTree.towerFn k x))) h
    rwa [log_exp, log_exp] at m
  have hup : t.eval x ≤ 1 + EMLTree.towerFn k x := by
    have u := add_le_add_wit hlog (le_refl (t.eval x + EMLTree.towerFn k x))
    have e1 : -(EMLTree.towerFn k x) + (t.eval x + EMLTree.towerFn k x) = t.eval x := by mach_ring
    have e2 : (1 : Real) - t.eval x + (t.eval x + EMLTree.towerFn k x)
        = 1 + EMLTree.towerFn k x := by mach_ring
    rw [e1, e2] at u; exact u
  show t.eval x ≤ exp (EMLTree.towerFn k x)
  exact le_trans hup (one_add_le_exp_of_one_le (towerFn_ge_one k hx1))

/-- **The cancellation-free terminal cell IS the growth envelope**, hence `DecayFloor`, hence
`EmlGermApproach`. A recursion that stops there has reduced the obligation to itself. -/
theorem peelTerminalNoCancel_iff_growthEnvelope : PeelTerminalNoCancel ↔ GrowthEnvelope :=
  ⟨growthEnvelope_of_peelTerminalNoCancel, peelTerminalNoCancel_of_growthEnvelope⟩

/-! ### T2 — nothing left to peel

The other way to stop: the left germ has no `exp` to strip, `lspTree A = 0`. The simplest such cell
fixes `A` at the single tree `const 0` — and it is already enough. -/

/-- **The height-zero cell**, with the left germ fixed at one leaf. `lspTree (const 0) = 0`, so the
recursion admits **no peels at all** here — and `deepDecay`, through `approachTarget`, is an
instance of exactly this cell (`decayFloor_of_emlGermApproach` routes through it). -/
def PeelTerminalConstZero : Prop :=
  ∀ j : Nat, ∃ k : Nat, ∀ (C : EMLTree) (X₀ : Real),
    C.depth ≤ j → 1 ≤ X₀ →
    (∀ x : Real, X₀ ≤ x → C.eval x < exp ((EMLTree.const 0).eval x)) →
    ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
      exp (-(EMLTree.towerFn k x)) ≤ exp ((EMLTree.const 0).eval x) - C.eval x

theorem lsp_constZero : (EMLTree.const (0 : Real)).lspTree = 0 := rfl

/-- **Peeling to a leaf achieves nothing.** The cell with the left germ fixed at `const 0` implies
`DecayFloor` at `−2` depth — by the argument the corpus already contains, since
`decayFloor_of_emlGermApproach` never instantiates `A` at anything else. -/
theorem decayFloor_of_peelTerminalConstZero (hT : PeelTerminalConstZero) : DecayFloor := by
  intro j
  obtain ⟨k, hk⟩ := hT (j + 2)
  refine ⟨k, ?_⟩
  intro t X₀ hdepth hX₀ hpos
  have hC : (approachTarget t).depth ≤ j + 2 := by rw [approachTarget_depth]; omega
  have hgap : ∀ x : Real, exp ((EMLTree.const 0).eval x) - (approachTarget t).eval x
      = t.eval x := by
    intro x
    rw [approachTarget_eval]
    show exp ((0 : Real)) - (1 - t.eval x) = t.eval x
    rw [exp_zero]; mach_ring
  have hlt : ∀ x : Real, X₀ ≤ x →
      (approachTarget t).eval x < exp ((EMLTree.const 0).eval x) := by
    intro x hx
    have u := add_lt_add_left (hpos x hx) (1 - t.eval x)
    have e1 : (1 : Real) - t.eval x + 0 = 1 - t.eval x := by mach_ring
    have e2 : (1 : Real) - t.eval x + t.eval x = 1 := by mach_ring
    rw [e1, e2] at u
    rw [approachTarget_eval]
    show (1 : Real) - t.eval x < exp ((0 : Real))
    rw [exp_zero]; exact u
  obtain ⟨X₁, hX₁, hf⟩ := hk (approachTarget t) X₀ hC hX₀ hlt
  refine ⟨X₁, hX₁, fun x hx => ?_⟩
  have h := hf x hx
  rw [hgap x] at h
  exact h

/-- The converse is the trivial instantiation: `const 0` has depth `0`. -/
theorem peelTerminalConstZero_of_emlGermApproach (hG : EmlGermApproach) :
    PeelTerminalConstZero := by
  intro j
  obtain ⟨k, hk⟩ := hG j
  refine ⟨k, ?_⟩
  intro C X₀ hC hX₀ hlt
  have hA : (EMLTree.const (0 : Real)).depth ≤ j := by simp only [EMLTree.depth]; omega
  exact hk (EMLTree.const 0) C X₀ hA hC hX₀ hlt

/-- **The height-zero terminal cell IS the conjecture.** Restricting the left germ to a single leaf
— the state the recursion is designed to reach — costs nothing at all beyond a depth shift, so the
number of peels being bounded by `j + 1` buys nothing. This is the file's result. -/
theorem peelTerminalConstZero_iff_emlGermApproach :
    PeelTerminalConstZero ↔ EmlGermApproach :=
  ⟨fun h => emlGermApproach_of_decayFloor (decayFloor_of_peelTerminalConstZero h),
   peelTerminalConstZero_of_emlGermApproach⟩

/-- **Both terminal cells are the same obligation**, stated together so the route's two exits are
known to be one wall and not two coincidences. -/
theorem peel_terminal_cells_are_the_conjecture :
    (PeelTerminalNoCancel ↔ EmlGermApproach) ∧ (PeelTerminalConstZero ↔ EmlGermApproach) :=
  ⟨⟨fun h => emlGermApproach_of_growthEnvelope (growthEnvelope_of_peelTerminalNoCancel h),
    fun h => peelTerminalNoCancel_of_growthEnvelope
      (growthEnvelope_of_decayFloor (decayFloor_of_emlGermApproach h))⟩,
   peelTerminalConstZero_iff_emlGermApproach⟩

end MachLib
