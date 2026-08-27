import MachLib.EMLDecayFloorIsGrowth

/-!
# How closely can `exp ∘ A` approach an EML germ from above?

`(dn)` named the missing input as `EmlNodeSeparation`, the literal node form
`exp (A x) − log (B x)` with `0 < B` assumed. **That was under-restricted, by the criterion `(dn)`
itself adopted**: put into the obligation whatever the downstream proof actually needs, and nothing
else. The downstream proof never uses a general positive `B` — every `B` it supplies is an `eTree`,
because that is how `posEmbed` manufactures a positive right child. So the positivity was an
*assumed hypothesis* standing in for a *structural fact*.

Writing `B = eTree C` and cancelling `log ∘ exp` leaves

```
exp (A x) − log ((eTree C).eval x)  =  exp (A x) − C.eval x
```

and the obligation becomes an **approach** question between two germs, with one fewer hypothesis to
discharge and the depth cost down from `+3` to `+2`:

```
EmlGermApproach :
  ∀ j, ∃ k, ∀ A C X₀,  A.depth ≤ j → C.depth ≤ j → 1 ≤ X₀ →
    (∀ x ≥ X₀, C.eval x < exp (A.eval x)) →
    ∃ X₁ ≥ X₀, ∀ x ≥ X₁, exp (-(towerFn k x)) ≤ exp (A.eval x) - C.eval x
```

> **An EML germ that stays strictly below `exp ∘ A` on a ray stays below it by an effective
> envelope.**

Same quantifier order and same floor shape as `DecayFloor`; `k` from the depth bound and never from
the germs. This replaces `EmlNodeSeparation` rather than joining it — four names for one obligation
would be worse than three.

## Still an equivalence, and still said out loud

```
Approach j   ⟸ DecayFloor (j+2)     the tree  eml A (eTree C)
DecayFloor j ⟸ Approach (j+2)       the target  1 − t x,  with A := const 0
```

Both directions are proved. **This is not progress on difficulty**; it is the same obligation, stated
where an external theorem could meet it. What changed is that a hypothesis someone would have had to
supply is now discharged by the shape of the statement.

## Where cancellation cannot happen

`approach_gap_ge_exp_of_nonpos`: when the target is non-positive the gap is at least `exp (A x)`, so
nothing cancels and the floor is a plain lower bound on `A`. **Cancellation requires a positive
target.** That does not shrink the obligation — the positive-target branch still needs the envelope,
and `(di)` showed that branch re-embeds the whole problem — but it says where to look, and it is the
first thing a counterexample hunt has to stop wasting time on.

## Counterexample hunt, §3

Four probes, and the third is the one that changed how the statement reads.

* **exact meeting** — `C = eTree A` gives `C.eval x = exp (A x)` on the nose, so the gap is
  identically `0` and the strict hypothesis fails exactly there. Two EML germs **can** meet; where
  they do, no envelope exists. The hypothesis is load-bearing.
* **near-meeting of two arbitrarily fast-growing germs** — `gapTarget n c` puts both germs at tower
  height `n + 1` with gap exactly the constant `c`. **The floor needed is height `0` while the germs
  live at height `n+1`: approach is not controlled by growth rate**, which is why `(dm)`'s
  germ-height parameter was never the right instrument.
* **a gap that tends to zero** — `approachTarget decayFast` has gap `exp (1 − x)`, infimum `0`, and
  still meets the height-`0` floor. Read as *"bounded away from zero"* the obligation would be
  **false here**, on a member of its own class.
* **non-positive target** — no cancellation at all, above.

**No counterexample was found, and none of this is evidence that none exists.** What the probes
establish is narrower: the two ways to make the gap small that a first attempt reaches for —
outrunning the target by growth, and driving the gap to zero — are both *satisfied* instances rather
than counterexamples, and the hypothesis boundary sits exactly at germs meeting.

## Scope

**Bounds nothing, discharges nothing, assumes nothing.** No axiom; the row stays **open**; 243 axioms
pinned. An external mathematical input is not automatically an axiom — until it is deliberately
accepted without proof it is an obligation nobody has discharged, and `(dm)` is what lets the ledger
say which of the two it is.
-/

namespace MachLib

open Real

/-! ## §1 — the obligation -/

/-- **The approach the corpus actually needs.** `k` depends on the depth bound alone; per pair it
could be chosen after seeing the germs and the statement would evaporate. -/
def EmlGermApproach : Prop :=
  ∀ j : Nat, ∃ k : Nat, ∀ (A C : EMLTree) (X₀ : Real),
    A.depth ≤ j → C.depth ≤ j → 1 ≤ X₀ →
    (∀ x : Real, X₀ ≤ x → C.eval x < exp (A.eval x)) →
    ∃ X₁ : Real, X₀ ≤ X₁ ∧ ∀ x : Real, X₁ ≤ x →
      exp (-(EMLTree.towerFn k x)) ≤ exp (A.eval x) - C.eval x

/-! ## §2 — the reduction, both ways -/

/-- The target that turns a floor for `t` into an approach question: `1 − t x`. -/
noncomputable def approachTarget (t : EMLTree) : EMLTree :=
  EMLTree.eml (EMLTree.const 0) (eTree t)

theorem approachTarget_eval (t : EMLTree) (x : Real) :
    (approachTarget t).eval x = 1 - t.eval x := by
  show exp ((0 : Real)) - log ((eTree t).eval x) = _
  rw [exp_zero, eTree_eval, log_exp]

theorem approachTarget_depth (t : EMLTree) : (approachTarget t).depth = t.depth + 2 := by
  simp only [approachTarget, eTree, EMLTree.depth]
  omega

/-- `0 < a` gives `-a < 0`, without a named negation lemma. -/
private theorem neg_neg_of_pos {a : Real} (h : 0 < a) : -a < 0 := by
  have u := add_lt_add_left h (-a)
  have e1 : -a + 0 = -a := by mach_ring
  have e2 : -a + a = 0 := by mach_ring
  rw [e1, e2] at u; exact u

/-- **The approach buys `DecayFloor`, with no induction**, at `+2` depth. The germ being approached
is `1 − t x`, and `exp ∘ (const 0)` is the constant `1`: the gap *is* `t x`. -/
theorem decayFloor_of_emlGermApproach (hG : EmlGermApproach) : DecayFloor := by
  intro j
  obtain ⟨k, hk⟩ := hG (j + 2)
  refine ⟨k, ?_⟩
  intro t X₀ hdepth hX₀ hpos
  have hA : (EMLTree.const 0).depth ≤ j + 2 := by simp only [EMLTree.depth]; omega
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
    have u := add_lt_add_left (neg_neg_of_pos (hpos x hx)) (1 : Real)
    have e1 : (1 : Real) + -(t.eval x) = 1 - t.eval x := by mach_ring
    have e2 : (1 : Real) + 0 = 1 := by mach_ring
    rw [e1, e2] at u
    rw [approachTarget_eval]
    show (1 : Real) - t.eval x < exp ((0 : Real))
    rw [exp_zero]; exact u
  obtain ⟨X₁, hX₁, hf⟩ := hk (EMLTree.const 0) (approachTarget t) X₀ hA hC hX₀ hlt
  refine ⟨X₁, hX₁, fun x hx => ?_⟩
  have h := hf x hx
  rw [hgap x] at h
  exact h

/-- **And `DecayFloor` buys the approach back**, via the tree `eml A (eTree C)` whose value is the
gap on the nose. Stated so nobody reads the forward direction as a shrink. -/
theorem emlGermApproach_of_decayFloor (hD : DecayFloor) : EmlGermApproach := by
  intro j
  obtain ⟨k, hk⟩ := hD (j + 2)
  refine ⟨k, ?_⟩
  intro A C X₀ hA hC hX₀ hlt
  have hgap : ∀ x : Real, (EMLTree.eml A (eTree C)).eval x = exp (A.eval x) - C.eval x := by
    intro x
    show exp (A.eval x) - log ((eTree C).eval x) = _
    rw [eTree_eval, log_exp]
  have hd : (EMLTree.eml A (eTree C)).depth ≤ j + 2 := by
    simp only [eTree, EMLTree.depth]
    have h1 : C.depth ≤ j := hC
    have h2 : max C.depth 0 ≤ j := Nat.max_le.mpr ⟨h1, Nat.zero_le j⟩
    have h3 : max A.depth (1 + max C.depth 0) ≤ 1 + j :=
      Nat.max_le.mpr ⟨by omega, by omega⟩
    omega
  have hpos : ∀ x : Real, X₀ ≤ x → 0 < (EMLTree.eml A (eTree C)).eval x := by
    intro x hx
    rw [hgap x]
    have u := add_lt_add_left (hlt x hx) (-(C.eval x))
    have e1 : -(C.eval x) + C.eval x = 0 := by mach_ring
    have e2 : -(C.eval x) + exp (A.eval x) = exp (A.eval x) - C.eval x := by mach_ring
    rw [e1, e2] at u; exact u
  obtain ⟨X₁, hX₁, hf⟩ := hk (EMLTree.eml A (eTree C)) X₀ hd hX₀ hpos
  refine ⟨X₁, hX₁, fun x hx => ?_⟩
  have h := hf x hx
  rw [hgap x] at h
  exact h

/-- **One obligation, two names.** -/
theorem emlGermApproach_iff_decayFloor : EmlGermApproach ↔ DecayFloor :=
  ⟨decayFloor_of_emlGermApproach, emlGermApproach_of_decayFloor⟩

/-- Closes the ledger cycle in the corpus rather than only in the table. -/
theorem emlGermApproach_of_growthEnvelope (hG : GrowthEnvelope) : EmlGermApproach :=
  emlGermApproach_of_decayFloor (decayFloor_of_growthEnvelope hG)

/-! ## §3 — where cancellation cannot happen, and four probes -/

/-- **Cancellation requires a positive target.** A non-positive `C` leaves the gap at least
`exp (A x)`, so the floor is a plain lower bound on `A` and nothing cancels. -/
theorem approach_gap_ge_exp_of_nonpos (A C : EMLTree) (x : Real) (h : C.eval x ≤ 0) :
    exp (A.eval x) ≤ exp (A.eval x) - C.eval x := by
  have hn : (0 : Real) ≤ -C.eval x := by
    have u := neg_le_neg_wit h
    have e : -(0 : Real) = 0 := by mach_ring
    rw [e] at u; exact u
  have u := add_le_add_wit (le_refl (exp (A.eval x))) hn
  have e1 : exp (A.eval x) + 0 = exp (A.eval x) := by mach_ring
  have e2 : exp (A.eval x) + -C.eval x = exp (A.eval x) - C.eval x := by mach_ring
  rw [e1, e2] at u; exact u

/-- **Exact meeting.** `C = eTree A` matches `exp ∘ A` on the nose, so the gap is identically `0` and
the strict hypothesis fails exactly there. Two EML germs *can* meet; where they do no envelope
exists, so the hypothesis cannot be dropped. -/
theorem exact_meeting_gap_zero (A : EMLTree) (x : Real) :
    exp (A.eval x) - (eTree A).eval x = 0 := by
  rw [eTree_eval]; mach_ring

/-- The target of the near-meeting pair: `exp (towerFn n x) − c`. -/
noncomputable def gapTarget (n : Nat) (c : Real) : EMLTree :=
  EMLTree.eml (EMLTree.towerTree n) (EMLTree.const (exp c))

theorem gapTarget_depth (n : Nat) (c : Real) : (gapTarget n c).depth = n + 1 := by
  simp only [gapTarget, EMLTree.depth, EMLTree.towerTree_depth]
  omega

/-- **Near-meeting of two arbitrarily fast-growing germs.** Both `exp ∘ towerTree n` and
`gapTarget n c` grow like an `(n+1)`-fold tower, and the gap is **exactly `c`** — at every `x`, for
every `n`, for every `c`.

> The germs live at tower height `n + 1`; the floor their gap needs is height **0**.
> **Approach is not controlled by growth rate.** -/
theorem gapTarget_gap (n : Nat) (c x : Real) :
    exp ((EMLTree.towerTree n).eval x) - (gapTarget n c).eval x = c := by
  show exp ((EMLTree.towerTree n).eval x)
      - (exp ((EMLTree.towerTree n).eval x) - log (exp c)) = c
  rw [log_exp]; mach_ring

/-- The pair meets the height-`0` floor at every `n`, stated at `c = 1` so the arithmetic is exact. -/
theorem gapTarget_meets_floor (n : Nat) {x : Real} (hx : 0 ≤ x) :
    exp (-(EMLTree.towerFn 0 x))
      ≤ exp ((EMLTree.towerTree n).eval x) - (gapTarget n 1).eval x := by
  rw [gapTarget_gap]
  show exp (-x) ≤ (1 : Real)
  have hz : exp (0 : Real) = 1 := exp_zero
  rw [← hz]
  refine exp_monotone ?_
  have u := neg_le_neg_wit hx
  have e : -(0 : Real) = 0 := by mach_ring
  rw [e] at u; exact u

/-- **A gap that tends to zero and still meets the floor.** `approachTarget decayFast` sits below
`exp ∘ (const 0) = 1` with gap `exp (1 − x)`, whose infimum on the ray is `0`.

Read as *"bounded away from zero"* the obligation would be **false here**, on a member of its own
class. This is the concrete reason it is an envelope. -/
theorem decaying_gap_eval (x : Real) :
    exp ((EMLTree.const 0).eval x) - (approachTarget decayFast).eval x = exp (1 - x) := by
  rw [approachTarget_eval]
  show exp ((0 : Real)) - (1 - decayFast.eval x) = exp (1 - x)
  rw [exp_zero, decayFast_eval]
  mach_ring

theorem decaying_gap_meets_floor {x : Real} (hx : 1 ≤ x) :
    exp (-(EMLTree.towerFn 0 x))
      ≤ exp ((EMLTree.const 0).eval x) - (approachTarget decayFast).eval x := by
  rw [approachTarget_eval]
  show exp (-(EMLTree.towerFn 0 x)) ≤ exp ((0 : Real)) - (1 - decayFast.eval x)
  have e : exp ((0 : Real)) - (1 - decayFast.eval x) = decayFast.eval x := by
    rw [exp_zero]; mach_ring
  rw [e]
  exact decayFast_floor x hx

end MachLib
