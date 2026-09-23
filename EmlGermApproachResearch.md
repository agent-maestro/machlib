# `EmlGermApproach` — a research programme

**Status: OPEN research frontier, split out of MachLib engineering on 2026-08-27.**
Objective: **PROVE IT OR BREAK IT.** Not "find a Lean proof" — the falsification arm is first-class
and is where the next experiment should go.

This file exists so that no future session re-derives what is already known. Read it before writing
Lean. If you finish a session having learned something listed under §3, §4 or §6, this file was not
read.

---

## 1. The exact conjecture

`MachLib/EMLGermApproach.lean`, ledger row `EmlGermApproach`:

```lean
EmlGermApproach : Prop :=
  ∀ j : Nat, ∃ k : Nat, ∀ (A C : EMLTree) (X₀ : Real),
    A.depth ≤ j → C.depth ≤ j → 1 ≤ X₀ →
    (∀ x, X₀ ≤ x → C.eval x < exp (A.eval x)) →
    ∃ X₁, X₀ ≤ X₁ ∧ ∀ x, X₁ ≤ x →
      exp (-(EMLTree.towerFn k x)) ≤ exp (A.eval x) - C.eval x
```

> An EML germ that stays strictly below `exp ∘ A` on a ray stays below it **by an effective
> envelope**, with the envelope's tower height depending on the **depth bound alone**.

**The whole open content is the position of `∃ k`.** With `k` chosen *after* the pair
(`EmlGermApproachPerPair`, proved to follow) the statement is a corollary of Hardy 1912 — see §7.

**It is not "bounded away from zero."** That reading is false on ordinary members of the class:
`exp (1 − x)` and `e/x` are positive on the ray with infimum `0`. `decayFast_floor` floors one of
them. The floor is an *envelope*, and the tower shape was forced by the structure, not chosen (§7).

**Equivalent forms, all proved.** `EmlGermApproach ⇄ DecayFloor ⇄ GrowthEnvelope` — a three-row
reduction cycle in the obligations ledger, reported as **one** open obligation. Any "reduction"
between them is bookkeeping; check for a converse before believing otherwise (this was gotten wrong
once, `(dw)`, and corrected in `(dx)`).

---

## 2. What it actually buys — and the honest answer is "not much that is proved"

**Directly:** `DecayFloor`, `GrowthEnvelope`, and — via `decayFloor_of_ladderInputs` — the whole
per-depth ladder, hence `DecayFloorUpTo N` for every `N`.

**Intended, but NOT PROVED:** the depth programme's remaining lower-bound work. `TowerLowerBound`
(`d(Tₙ) = n` for all `n`) would turn the tower into an unbounded supply of certified depth-optimal
targets. `EMLCertifiedSynthesis` states plainly that the reduction from `TowerLowerBound` to the
growth/decay pair **is not established** and "is not a formality". So there is no proved implication
from this conjecture to any headline result.

**Compiler-facing value: none.** `FRONTIER_BRIEF_3` §4 Q3 pre-registered — before the size-indexed
envelope was built, and it held — that the growth envelope has **no eml-stdlib kernel consumer**:
they are all bounded or slow-growing. Nothing in Forge changes if this is proved. Confirmed again
2026-08-27 in a cross-session review with the Forge track.

**This matters for §8.** The third axiom criterion asks what assuming it unlocks. Today the honest
answer is *one more open obligation becomes provable, and its own downstream is unproved.* That is a
weak case for spending trust, and it should be re-evaluated rather than assumed to have improved.

---

## 3. Known adversarial families — build on these, do not re-derive them

All are in the corpus, all machine-checked. Each was built to break something and is now a fixture.

| family | construction | what it does |
|---|---|---|
| `recipTree t` | `eml (eml (const 0) t) (const 1)` | `e / t x` at **+2 depth**. The grammar already has `log`, so a reciprocal costs two nodes. Escapes germ-growth measures entirely (`recipTree_germ_bounded`: bounded by `e` when `t ≥ 1`). |
| `posEmbed t` | `eml (const 0) (eTree (eml (const 0) (eTree t)))` | `t x` at **+4 depth** with a right child positive *everywhere*. Puts the whole problem inside the positive-`B` branch — **but only from depth 8 up**, see §4. |
| `capNode n` | `eml (const 0) (towerTree (n+1))` | `1 − towerFn n x`, **non-positive on the ray**, right child is the `(n+1)`-tower. A node arbitrarily *flatter* than its own child. |
| `deepDecay m` | `eTree (eml (const 0) (eTree (towerTree (m+1))))` | `exp (1 − towerFn (m+1) x)` at depth **exactly `m+4`**, defeating the height-`m` floor. Pins the required height at `≥ d − 3`. |
| `gapTarget n c` | `eml (towerTree n) (const (exp c))` | Both germs at tower height `n+1`, gap **exactly the constant `c`**. **Approach is not controlled by growth rate.** |
| `eTree (eTree A)` | — | Exact meeting: gap identically `0`, right child positive everywhere. The hypothesis boundary sits precisely here. |

**The two obvious attacks are already known to be satisfied instances, not counterexamples:**
outrunning the target by growth (`gapTarget`) and driving the gap to zero (`approachTarget decayFast`,
gap `exp (1−x)`, infimum 0, still meets the height-`0` floor). **A counterexample is not of either
shape.**

---

## 4. The six failed descent mechanisms

All six are proved, footprint-clean, in `EMLLadderMeasure`, `EMLGermApproach`,
`EMLPolarityMeasure`, `EMLGermInvariance` and `EMLPeelRecursion`.

1. **Syntactic scalar measure.** Any `Nat`-valued measure descending to *both* children is a
   `LadderMeasure` with `step = 1` (`ofStrictDescent` — the hypothesis *is* the induction
   principle, not a chosen class). For every such measure `recipTree` costs `2 · step` while one
   ladder step buys `1 · step`: `recip_not_at_one_step`. Sharp on `depth` (+2) and `size` (+4).
2. **Germ-growth measure.** Escapes (1) — `recipTree` *lowers* it — but fails to descend to the
   **right** child, and the gap is unbounded: `capNode n` is non-positive while its right child is
   the `(n+1)`-tower. `tower_height_does_not_descend_right`.
3. **Peeling an exponential.** `gap_ge_target_mul_log_gap` shows `exp` cannot *manufacture* approach
   (`C x · (A x − log (C x)) ≤ exp (A x) − C x`), but `A − log C` sits one depth **above** `A` and
   `C`, so peeling moves **up** the ladder — the third independent sighting of the same direction of
   travel, found while looking for something else.
4. **Any measure into any well-founded order** (`EMLPolarityMeasure`, 2026-09-22). Drop `Nat`
   entirely. Let `μ : EMLTree → W` for **any** `W` under **any** well-founded `R`, descending
   strictly to **both** children. Then `recipTree = eTree ∘ negLogTree` is **two strict steps up** —
   one `log` edge in, one `exp` edge out — so `¬ R (μ (recipTree t)) (μ t)` and
   `μ (recipTree t) ≠ μ t` (`recip_not_below`, `recip_ne`); `posEmbed` is **four**
   (`posEmbed_not_below`). The proofs use **only well-foundedness** — three rotate-the-cycle lemmas,
   `no_cycle2/3/5` — and no arithmetic whatever. `no_wf_descent_of_cheap_recip` is
   `no_structural_induction_of_cheap_recip` with the codomain and the order universally quantified;
   `ofLadderMeasure` shows the new class contains the old, and `polDescent` that it is strictly
   larger (`no_nat_collapse`).
   **So mechanism (1)'s arithmetic was incidental.** *"`recipTree` costs `2 · step` while a rung
   buys `1 · step`"* is the `Nat` shadow of *"the transfer travels up"*, and a well-founded order
   has nothing to say against that whatever its order type. Lexicographic orders, vectors and
   ordinal ranks do not escape it, and neither does the polarity-indexed form — a measure carrying
   a bit the `log` edge flips — which fails at the flipped polarity (`PolWfDescent`,
   `pol_recip_not_below`).

5. **Any GERM-INVARIANT parameter at all** (`EMLGermInvariance`, 2026-09-23). Not a measure that
   *travels* badly — a class that is **empty**. If `μ` reads only the germ
   (`GermInvariant μ : ∀ s t, s.eval = t.eval → μ s = μ t`) then it cannot strictly descend to
   both children of an `eml` node in **any** well-founded order: `no_germInvariant_wfDescent`.
   The witness is §3's own `posEmbed`, which is **four `eml` edges above `t` and has exactly
   `t`'s germ** (`posEmbed_eval`, in the corpus since `(di)`) — so the four edges close a
   **4-cycle** on a germ-invariant `μ` and `no_cycle4` finishes it. No cheapness hypothesis, no
   `recipTree`, no arithmetic.
   **This corrects the width paragraph below, which was wrong.** A well-founded relation on germs
   is *not* outside (4) "by construction": it **is** a `WfDescent` at `W := Real → Real`,
   `μ := EMLTree.eval` (`GermDescent.toWfDescent`). The germ is a function of the tree.
   Three consequences, all proved: a relation on germs is empty (`no_germDescent`); so is the
   repair *"descend only where the germs differ"* (`no_germDescentNe` — the four germs round the
   `posEmbed var` cycle are pairwise distinct, so every guard discharges); and so is **one-sided**
   germ descent (`no_germDescentLeft`, `no_germDescentRight`), which this section had listed as
   untouched — the witnesses are depth-1 constant nodes whose germ *is* a child's,
   `exp 0 − log (exp 1) = 0` and `exp 0 − log 1 = 1`, refuted by irreflexivity alone.
   **And one-sided *guarded* descent, the last germ-invariant shape those leave standing, is
   empty too** (`no_germDescentLeftNe`, `no_germDescentRightNe`): two-edge cycles on a single
   side with a distinct intermediate germ — `var → eTree var → selfLeftNode var`, and
   `negGerm → rightStep1 → rightStep2` where `negGerm = 1 − exp (exp x)` is negative at **every**
   real, so totalised `log` erases it as a *function* and not merely on a ray. An `eml` node's
   other child is unconstrained, which is what makes one edge from a germ `g` able to reach a
   germ engineered to come back. **So the closure is complete: both children or one, guarded or
   not, no germ-invariant parameter descends anywhere.**
   **Both verdicts on one instrument:** `WfDescent` is inhabited (`wfDescent_inhabited`, by
   `polDescent`), and the hypothesis blamed is exactly what `polDescent` lacks —
   `polMeasure_not_germInvariant`: `posEmbed var` and `var` share a germ and measure `(2,3)` vs
   `(0,0)`. Inhabited when indexed by the tree, empty when indexed by the germ.

6. **A one-sided, syntax-reading recursion whose step is the PEEL** (`EMLPeelRecursion`,
   2026-09-23). This is the class the width paragraph listed as untouched, on **both** of its
   readings — *a measure descending on one side only that reads the syntax*, and *a relation on
   pairs `(A, C)` that a peeling step decreases*. **The measure works. The base case is the
   conjecture.**
   The peel takes the gap `exp (A x) − C x` to `A x − log (C x)`, and the merge
   (`peel_shape_pos`, `peel_shape_nonpos` — `log A₂ + log C = log (A₂·C)`, or the clamped branch
   where totalised `log` kills the term) rewrites that as `exp (A₁ x) − log (·)`: **the same shape
   at the LEFT CHILD of `A`**. So the recursion's parameter is `lspTree`, the leftmost-spine
   length. It descends strictly on the left (`lspTree_left_lt`), reads **no right child at all**
   (`lspTree_right_unbounded`), and bounds the leftmost-spine length by the depth bound
   (`peel_terminates`), so the recursion performs at most `lspTree A + 1` peels — one per `eml`
   node on that spine plus the first — hence at most `j + 1`, exactly as the route intends. Being
   syntactic it is outside
   (5); being one-sided it is outside (4); `recipTree` never travels up it because it is never
   asked to.
   **It dies on the terminal cell, and there are only two, and each is the whole obligation.**
   * `PeelTerminalNoCancel ↔ GrowthEnvelope` (`peelTerminalNoCancel_iff_growthEnvelope`, both
     directions, `+2` depth each way; `+1` height cell→envelope, none the other way). The route's own description of its base case is *"a
     germ pair with no cancellation left"*. `approach_gap_ge_exp_of_nonpos` reduces that cell to
     `exp (−towerFn k x) ≤ exp (A x)` — an **upper envelope on `−A`, uniform in depth**, which is
     `GrowthEnvelope`, the third name of this obligation. **The cancellation-free cell is not
     free.**
   * `PeelTerminalConstZero ↔ EmlGermApproach` (`peelTerminalConstZero_iff_emlGermApproach`). The
     other exit is *"nothing left to peel"*, `lspTree A = 0`. Fix `A` at the single leaf
     `const 0` — and `decayFloor_of_emlGermApproach` **never instantiates `A` at anything else**,
     so that one cell already implies `DecayFloor` at `−2` depth. Peeling the left germ down to a
     leaf is free and buys nothing.
   And the parameter cannot supply `k` either — it is **anti-correlated** with the height the
   floor needs. `deepDecay m` is priced at `2` for every `m` while forcing height `m + 1`;
   `gapTarget n c` is priced at `n + 1` while needing height `0` (`peel_measure_anticorrelated`;
   `peelCount_cannot_carry_floor` concludes `False`). **Both verdicts on one instrument:** the
   same argument does **not** refute `depth`, which grows on that family
   (`lspTree_refuted_where_depth_is_not`) — `lspTree` is refuted for being *constant* on the
   extremal family, not for being a tree parameter.
   **This is a failure of a different kind from (1)–(5).** Those die on the measure: the transfer
   travels up and no descent survives it. This one has a measure that descends, terminates in
   `≤ j` steps, and even **separates the meeting boundary** that (4)'s candidates are blind at
   (`lsp_separates_meeting`: `meetTree` and `posTree` have equal `depth` and equal four-vectors,
   and peel counts `1` and `2`). It dies on the **base case**. What is ruled out is therefore not
   peeling but **any recursion whose terminal cell is "no cancellation" or "left germ of
   exponential height 0"**, whatever reaches it.
   Two prices this route never got to pay, recorded so a seventh attempt does not re-derive them:
   the merge is **pointwise**, and a single right-hand germ for the whole tail needs eventual sign
   determination for every right child on the left spine — `evSign_all`, and with it the analytic
   axiom block (`rolle_ct`, `analytic_finite_zeros_compact`) that `EMLDecayFloorIsGrowth` is
   deliberately routed around; and the merged right-hand germ is a **product**, for which EML has
   no node. Neither is computed, because the T2 death is independent of both.

**Stated at the right width, and this has been got wrong twice:** what is killed is *local scalar
growth descent through the syntax tree* (1)-(3); — since (4) — **every measure on trees, into
any well-founded order, that descends to both children**; — since (5) — **every
germ-invariant parameter whatever, on either side or both**; and — since (6) — **every recursion,
of any shape, whose terminal cell is a cancellation-free pair or a height-`0` left germ**, because
those two cells are the obligation itself. That is still **not** the claim that no well-founded
induction can work. Untouched, precisely: a **mutual** induction over `(tree, polarity)` pairs with
*different* relations per polarity; a one-sided syntactic descent **with a terminal cell that is
neither of (6)'s two** — (6) closes the base case, not the measure, and `lspTree` survives as a
measure; and any non-structural argument. The sentence this paragraph used to carry — *"a
well-founded relation on germs … is outside (4) by construction"* — is **false**, and (5) is why.

**And the first of those classes is where the ladder already lives**, which is why a better measure
cannot help it: `decayFloor_of_ladderInputs` is a structural induction on the depth bound needing no
measure at all, and its residue is `NodeDecayBound` — an unproved rung, not a parameter. A measure
buys the *transfer* route, and the transfer route is what (4) closes.

**And one correction worth carrying:** `(di)`'s re-embedding is a **moving boundary**. It says the
positive branch at depth `k` is as hard as `DecayFloor` at depth `k − 4`. With depth ≤ 3 proved
(`decayFloorUpTo_three`), it first bites at **depth 8**, and that boundary rises by one per rung
proved. Read carelessly it retires four rungs without an argument.

---

## 5. Candidate asymptotic invariants — the main bet

The tree representation defines EML well and measures asymptotic separation badly. The bet is on an
**asymptotic normal form** in the middle:

```
EML syntax  →  [ asymptotic normal form ]  →  leading surviving scale  →  DecayFloor
```

`MachLib/EMLHeightInterface.lean` is the interface for exactly this, and its finding is a warning:

* `HeightModel`'s closure axioms (leaves `0`, `exp` `+1`, `log` `+0`, **subtraction ≤ max**) give
  `eh ≤ depth` in four lines — **lemma (1) is free**.
* `zeroModel` (height ≡ 0) satisfies **every** closure axiom and **refutes** the floor property
  outright. So the closure half carries no content.
* Wanted: the **coarsest germ-invariant height for which the floor still holds**. That is what
  transseries would have to supply, and it is *not* the closure.

Candidates, in the order I would try them. **All four are now DEAD** — 1 and 2 by the run of
2026-09-22, 3 and 4 by the run of 2026-09-23, both below. The semantic half of this bet is closed:
§4(5) shows no germ-invariant parameter descends at all, so an asymptotic normal form cannot be
the induction's parameter however it is built. It could still be the *content* of
`NodeDecayBound`; it cannot be the *ladder*.

1. ~~**A vector, not a scalar**~~ — `(exp-height, log-depth, alternation, size)` under a
   lexicographic order. **DEAD.** Killed by `recipTree`, and its last two components are provably
   never consulted.
2. ~~**A polarity-aware measure**~~ distinguishing left/`exp` from right/`log`. **DEAD**, in both
   the vector form and the strongest form (a polarity bit the `log` edge flips). It *does* answer
   mechanism (2) — see the positives below, they are real — and it dies on mechanism (4).
3. ~~**Hardy-field valuation / comparability class**~~ rather than a height integer. **DEAD**
   (run 2026-09-23, below), twice over: the comparability order on EML germs is **not
   well-founded**, and a class is germ-invariant so §4(5) closes its descent before
   well-foundedness is even reached.
4. ~~**A well-founded relation on germs**~~ that is not a function of the germ at all. **DEAD**
   (run 2026-09-23, below). The premise this line rested on was wrong: a relation on germs is
   *inside* §4(4), at `μ := EMLTree.eval`, and §4(5) shows the class is **empty**.

### ▸ RUN, 2026-09-23 — candidates 3 and 4, `MachLib/EMLGermInvariance.lean` + `MachLib/EMLComparability.lean`

**Both DEAD, and worse than dead: the classes they name are EMPTY, where 1 and 2 named classes
that were merely unable to run the transfer.** The mechanism is §4(5) and it is one theorem.

**Well-foundedness first, as §5 requires.** For candidate 4 the question does not arise — there is
no relation to ask it of. For candidate 3 it is asked and answered:

```
CompLe g h  :=  ∃ c > 0, ∃ X ≥ 1, ∀ x ≥ X,  log (g x) ≤ c · log (h x)
compLe_refl, compLe_trans    a genuine preorder, so CompLt is irreflexive
compLt_deepDecay (m)         CompLt (deepDecay (m+1)) (deepDecay m),  for EVERY m
compLt_not_wf                ¬ WellFounded CompLt
```

> **`deepDecay` is an infinite strictly descending chain in the comparability order.** The family
> §3 built to pin the floor height *from below* is, read as classes, an `ω*`. The order has no
> bottom, and the thing indexing the descent is the floor height itself.

The one asymptotic input is `lin_lt_exp` — *`K + T < c·exp T` for all large `T`, with `c` given in
advance* — which is where the arbitrary multiplier in `O(·)` is paid for. Proved from the corpus's
`exp_gt_two_x` and `exp_log` with **no division and no new axiom**: `c·exp T = exp (log c + T)`,
then `exp w > w + w`.

**Every §3 fixture, measured against the two relations.**

| §3 fixture | germ fact | verdict |
|---|---|---|
| `posEmbed t` | germ is **exactly `t`'s** (`posEmbed_eval`), four `eml` edges up | **KILLS both** — a 4-cycle, no side condition, every `t` |
| `recipTree t` | two germ-edges up (`negLogTree` then `eTree`); germ bounded by `e` when `t ≥ 1` | KILLED — §4(4)'s argument transports verbatim at `μ := eval` |
| `capNode n` | node germ `1 − towerFn n x` is non-positive, so totalised `log` sends it to `0`; child's log is `towerFn n x` | **FAILS right descent** — `compLt_capNode_right`: the node is strictly **below** its own right child, at every `n`. Mechanism (2), unchanged, in the valuation |
| `deepDecay m` | `log = 1 − towerFn (m+1) x` | **refutes well-foundedness** — `compLt_deepDecay`, and each sits strictly below the constant class (`compLt_deepDecay_one`) |
| `gapTarget n c` | gap is the **constant** `c` at operand height `n+1` (`gapTarget_gap_germ`) | the gap's class is the bottom class while the operands' is `n+1` — approach is no more controlled by the class than by the growth rate |
| `eTree (eTree A)` | gap identically `0` (`exact_meeting_gap_zero`); `log 0 = 0 = log 1` | **BLIND** — `compEquiv_zero_one` puts the no-floor gap in the **same class** as `gapTarget`'s height-`0` gap. A class cannot determine a floor one member has and another does not |

**The positive content of candidate 3, and it is one line.** `compLe_floor_of_floor`: a tower
floor for `t` **is** a comparability lower bound, `c = 1`, same `X₁`. So *"`DecayFloor` at depth
`j`"* and *"every eventually-positive depth-`j` germ has a class bounded below by a
tower-reciprocal, uniformly in `j`"* are the **same statement**, and the converse holds too —
absorbing the multiplier `c` costs one tower rung, which is what `lin_lt_exp` supplies. §9's rule
applies exactly as it did to the polarity reindexing: an equivalence with a converse is not
progress.

**What is now ruled out, as a bound on a class rather than as a failed attempt.** Let `μ` be any
parameter an induction on EML syntax could descend along. If `μ` factors through the germ, no
well-founded order on its values admits descent to either child, let alone both — so the entire
*semantic* half of §5's bet is closed, and the ladder's parameter must read the **syntax**. But
§4(4) already closed every syntactic measure that descends to both children. What survives is the
intersection neither theorem touches: a parameter that reads the syntax and descends on **one**
side, with the other side carried by a different argument; a relation on **pairs** `(A, C)`; and
non-structural arguments. The corpus's two blindness results now bracket it from both sides —
`measure_blind_at_meeting` (two trees, one measure, different germs) and
`polMeasure_not_germInvariant` (two trees, one germ, different measures). **A syntactic parameter
and a germ parameter are not refinements of one another in either direction**, so nothing is to be
had by making either finer.

**Scope.** No axiom; no ledger movement; the `DecayFloor` ⇄ `EmlGermApproach` ⇄ `GrowthEnvelope`
row stays open. 39 theorems, `sorryAx` 0, footprint the plain algebra/`exp` spine
(`exp_gt_two_x`, `exp_gt_one_plus_self`, `exp_log`, `exp_add`, `log_nonpos`, `log_exp` and the
order axioms) — nothing analytic.

### ▸ RUN, 2026-09-22 — candidates 1 and 2, `MachLib/EMLPolarityMeasure.lean`

**Both DEAD. The escape they predicted is real, and it is not enough.** What was built:

* **candidate 1** — `vecMeasure t = (ehTree t, ldTree t, altTree t, size t)` under the nested
  lexicographic order (`lexProd`, `natQuadLex_wf`);
* **candidate 2** — `polMeasure t = (ehTree t, ldTree t)`, the corpus's `ehTree` for the left/`exp`
  side and the new `ldTree` (log-depth, the exact dual: right edges cost one, left edges nothing)
  for the right/`log` side; plus `PolWfDescent`, a measure carrying the polarity **bit the `log`
  edge flips**, which is the bit the ladder's own recursion carries, since a floor for
  `exp (A x) − log (B x)` needs a *lower* bound on the left child and an *upper* bound on the right.

**Every §3 fixture, measured before any theorem was attempted.** The instrument is shown capable of
both verdicts — it PASSES `capNode`, the family that killed mechanism (2), and FAILS `recipTree`.

| §3 fixture | `polMeasure` | what it tests | verdict |
|---|---|---|---|
| `recipTree t` | `(max 1 eh + 1, ld + 1)`, i.e. `(eh+1, ld+1)` for `eh ≥ 1` | reciprocal within one rung? | **KILLED** |
| `posEmbed t` | `(eh + 2, max ld 1 + 2)` | re-embedding at its own level? | **KILLED**, four steps up |
| `capNode n` | `(n+1, 2)`, right child `(n+1, 1)` | descends to the right child? | **PASS** |
| `deepDecay m` | `(m+3, 2)` | floor height consistent? | PASS — forces `f (m+3, 2) ≥ m+1` |
| `gapTarget n c` | `(n+1, 1)` | is approach controlled by growth? | PASS, with slack `n` |
| `eTree (eTree A)` | `(2, 2)` — **equal to a positive tree's** | separates the meeting boundary? | **BLIND** |

**The three genuine positives, recorded so nobody rebuilds them.** Each is real; none is enough.

* The polarity pair is the **first measure in this corpus that strictly descends to both children**
  (`pol_left`, `pol_right`). On the right the `exp` component may tie — it does, with the gap of
  exactly zero that `ehTree_not_right_le` records — and `ldTree` breaks the tie unconditionally.
* It **passes `capNode` at every `n`** (`pol_descends_capNode`), where no germ-growth measure can:
  the node is non-positive while its right child is the `(n+1)`-tower.
* **`ehTree (recipTree t) = ehTree t + 1`** (`eh_recipTree_of_one_le`). The `exp` component pays
  **one** node for the reciprocal where `depth` and `size` pay two, both tightly
  (`depthMeasure_recip_sharp`, `sizeMeasure_recip_sharp`). **The predicted escape exists**, and it
  is genuinely outside §4(1): `no_nat_collapse` proves the order does not collapse to `Nat`, so
  `ofStrictDescent` cannot reach it.

**Why it dies anyway.** `recipTree = eTree ∘ negLogTree`: one `exp` node and one `log` node, so the
cost is **relocated, not reduced** — one node into each component — and §4(4) needs only the
direction of travel. The vector's last two components are never consulted, because every polarity
descent lifts to a vector descent (`vec_of_pol`); candidates 1 and 2 therefore stand or fall
together, and **adding components cannot rescue either**.

**Two further measurements, so the next candidate starts from them.**

* **`k` cannot come from the `log` component.** `deepDecay m` forces the floor height to `m + 1`
  while its `ldTree` stays pinned at `2` for every `m` (`pol_deepDecay`,
  `deepDecay_forces_first_component`). Whatever carries `k`, it is the `exp` side.
* **The reindexing is bookkeeping, in both directions** — `ehTree, ldTree ≤ depth ≤ ehTree + ldTree`
  (`reindexing_is_two_way`), so *"`k` from the depth bound alone"* and *"`k` from the polarity pair
  alone"* are the same statement. §9's rule turned on this session's own work: an equivalence with a
  converse is not progress, and this one has a converse.
* And both candidates are **blind at the hypothesis boundary**: `meetTree` (identically `0`) and
  `posTree` (`exp (1 − x)`, positive everywhere) have the *same* four-vector `(2, 2, 3, 7)`
  (`measure_blind_at_meeting`). Depth is blind there too; what the pair rules out is the hope that a
  finer **syntactic** parameter would see the difference.

---

## 6. Counterexample search — DESIGNED, NOT RUN

**No systematic search has been run.** Everything in §3 is hand-built. This is the highest-value next
experiment and it does not exist yet. Design:

* Enumerate EML trees to bounded depth/size over a small constant set, form pairs `(A, C)`, and
  estimate the eventual scale of `exp (A x) − C x`.
* **Do not evaluate naively.** Two recorded traps: double precision cannot decide this question (a
  528-configuration search reached machine epsilon, `1.11e-16`, and all ten sub-`1e-6` candidates were
  refuted only at **80 digits**); and a grid steps over singularities — a 400 001-point grid reported
  `sup |t₁| ≈ 15` for a germ that diverges. Work in **iterated-log coordinates** and evaluate *at*
  solved crossing points.
* The question is sharp: **can depth `d` produce arbitrarily deeper effective approach?** Search for
  a *family* where increasing syntactic complexity drives the gap below every tower floor at fixed
  depth — not for a single example.
* **A failed search proves nothing.** This corpus has a 12 208-sample grid that missed a
  transcendental witness. Record what the search *cannot* find, as those did.

### ▸ RUN, 2026-09-05 — `foundations/tools/germ_approach_search.py`

**No counterexample. The required height is bounded at fixed depth, and the bound is roughly
`depth − 2`.**

```
depth ≤ 2, constants {0,1} / {0,1,5} / {0,1,50} / {0,1,1000}
    223 248 pairs measured        required height: 0 for every one
depth ≤ 3, constants {0,1}, 6 000 pairs sampled at random from 21 612 trees
      2 978 pairs measured        required height: 0 (2 975), 1 (3)
positive controls                 height 1 at depth 3, height 3 at depth 4 — both FIRE
```

The metric: on the ray, `g(x) = exp(A x) − C(x) > 0`, `h(x) = −log g(x)`, and the required height
is the number of times `log` must be applied to `h(x)` before it falls to `x`. Read **in the
tail**, because the conjecture may start late.

**The result is only worth its instrument, and this instrument took four corrections to build.
Each one would have produced a confident wrong answer.**

1. **The height was maximised over the whole ray.** A *constant* gap — `exp(0) − log(exp 50)` is
   the constant `exp(−49)` — sits below the floor at `x = 2` and astronomically above it at
   `x = 10⁶`. Maximising reported height 2 for pairs that need 0. The conjecture says
   `∃X₁ ≥ X₀`, so the tail is the only part that counts.
2. **Values past the working range were returned as "no sample".** Every pair whose left side
   reaches the doubly-exponential regime therefore lost its tail and was scored on the *foot* of
   the ray — a truncation read as asymptotics, which is trap two of this section wearing a new
   hat. Fixed with a sentinel for "positively enormous" and a guard that refuses to score a pair
   whose far end produced nothing (`tail-unmeasured`, 13 000 of 163 000 at depth 2).
3. **The precision guard was absolute** (`|gap| < 10⁻⁹⁰ ⇒ undecided`). But the trap this guard
   exists for is *cancellation*: `exp(−exp x) − 0` is `10⁻⁹⁵⁶⁶` at `x = 10` and every digit is
   real. The absolute form rejected **both positive controls** and would have reported "height 0
   everywhere" from an instrument that was discarding exactly the interesting cases. The guard is
   now relative to the operands. It also cut the undecided count from ~260 to ~4 per sweep.
4. **The sample was strided, not random.** Striding an ordered product varies the second
   component fast and the first barely at all: a "6 000-pair sample" contained a handful of
   distinct left-hand trees. A census dressed as a sample, which this project has paid for before.

**Defect 3 was caught by the controls and by nothing else.** The rule — *an instrument must be
shown capable of both verdicts before either is read* — earned its keep here in the most literal
way available: the search was reporting a clean negative result while unable to report anything
else.

**What this search cannot find, stated so the next one does not re-derive it.**

* **It cannot see far.** How far the ray reaches is a function of depth: `x ≤ 10⁵` at depth 2,
  `x ≤ 13` at depth 3, `x ≤ 2.8` at depth 4, because the tower passes 120-digit precision there.
  A counterexample whose behaviour only separates beyond those points is invisible to it. This is
  the sharpest limitation and it gets worse exactly where the question gets interesting.
* **It samples thinly at depth 3** — 6 000 of ~4.7 × 10⁸ pairs, about 0.001 %.
* **Its constants are a tiny fixed set.** A counterexample requiring a particular transcendental
  constant is invisible, and this corpus has a recorded instance of exactly that miss.
* **It measures a finite ray and reads a trend.** It cannot certify an asymptotic claim, only
  fail to contradict one.

**What it does support.** The height rising with *depth* and not with constant magnitude at fixed
depth is the shape the conjecture predicts — `k` may depend on `j`. Nothing in 226 000 measured
pairs pushed the height up at fixed depth. That is weak evidence, of the only kind a search can
give, and it is now on the record rather than in nobody's head.

### ▸ THE DECAY FORM, SWEPT EXHAUSTIVELY — and `deepDecay` is EXTREMAL where it can be checked

`EmlGermApproach ⇄ DecayFloor ⇄ GrowthEnvelope` is a proved cycle, so the conjecture may be
attacked in whichever form is cheapest to search. **`DecayFloor` is enormously cheaper, because it
is a question about ONE tree rather than a pair** — `|S_j|` candidates instead of `|S_j|²`. That
turns a 0.001 % sample into an exhaustive sweep at depth 3, which is a different kind of statement.

| depth | coverage | max height | `j − 3` | verdict |
|---|---|---|---|---|
| 2 | **exhaustive**, 147 trees over `{0,1}`; 905 over `{0,1,5,50}` | 0 | 0 | matches |
| 3 | **exhaustive**, 21 612 trees over `{0,1}` | 0 | 0 | matches |
| 4 | 20 000 constructed at random, each nonzero reading re-checked | 1 | 1 | matches |
| 5 | 8 000 constructed at random | 1 | 2 | **under-resolved** — see below |

**The finding.** §3 records `deepDecay m` — `exp(1 − tower_{m+1}(x))` at depth `m + 4` — and says
it "pins the required height at `≥ d − 3`". That is a **lower** bound, by construction. What
nobody had was the other side. At every depth this search can resolve, **`d − 3` is also an upper
bound, and `deepDecay` is the family that attains it**: the extremal tree the depth-4 sweep
returns is `eml(eml(0, eml(eml(x,0), eml(x,0))), 1)`, which unfolds to `e·exp(−exp x)` — that
family, rediscovered by the sweep rather than supplied to it.

So at depths 2–4 the conjecture's `k` is pinned from both sides at `j − 3`. That is not a proof for
any depth (a sweep is not an induction), but it does say the *value* of `k` is not in doubt, and a
proof attempt should aim at exactly `j − 3` rather than search for the right constant.

**Depth 5 is under-resolved and the table says so.** Its ray reaches only `x ≈ 2.2`, so the search
cannot get to where a height-2 germ separates from a height-1 one; 354 of 8 000 readings were
rejected as unstable and 1 141 overflowed. A max of 1 there is the instrument running out, not
evidence about the class.

**Two more instrument defects, both found by checking a result rather than by reasoning.**

5. **The ray at depth 4 is too short to decide EVENTUAL POSITIVITY, not merely too short to
   resolve a rate.** A first depth-4 sample reported seven trees at height 2, beating the
   prediction — a counterexample, if true. The first one checked,
   `eml(x, eml(eml(x,0), x))`, is depth **3**, and on a longer ray it crosses zero at `x ≈ 5.9`:
   it is not a decaying germ at all, and the short ray had simply stopped before it went negative.
   §6's warning is about a grid stepping *over* a singularity; this is a ray stopping *short* of
   one, which is the same defect from the other side. Every nonzero height is now re-measured on a
   ray three times longer and dropped unless both agree (`unstable`, 91 of 20 000 at depth 4).
   The check is one-sided and the code says so: agreement does not prove a reading is asymptotic,
   disagreement proves it is not.
6. **Enumerate-then-sample is not sampling.** `trees_upto(4, {0,1})` is ~4.7 × 10⁸ trees; building
   it to take a 40 000-tree sample reached **58 GB resident with 1 GB of RAM free** before it was
   killed, on the machine whose editor an out-of-memory kill had already taken down that morning.
   Samples are now *constructed*, never filtered out of a construction.

**The prediction this table tests was itself corrected by the table.** A first draft of this
section predicted `j − 2`, from miscounting the extremal construction: the smallest positive germ
at depth `j` is `exp(1 − tower_{j−3})`, and the `exp` that makes it positive costs the extra level.
The exhaustive depth-3 sweep returned 0 where `j − 2` predicted 1, which is how the miscount was
found — the instrument correcting the prediction rather than the other way round, which is the
only direction that is worth anything.

---

## 7. Literature — what is settled and what is not

Full note with sources and its own limits:
`monogate-research/exploration/germ_approach_literature_2026_08_27/NOTE.md`.

**Classical, and it is most of the statement.** EML germs at infinity are Hardy
**logarithmico-exponential** germs (totalised `log` is first-order definable in `ℝ_exp`, so
totalisation does not leave the class). LE-functions form a **field**, so `1/gap` is again an
LE-function; and every Hardy-field germ is `o(exp^∘k)` for **some** `k`. Compose: per-pair floor.
**`recipTree` *is* that reciprocal** — the corpus walked backwards into a 1912 argument.

**Not classical: the uniformity.** Two near misses, both instructive:

* **Berarducci–Servi (2004)** — `ℝ_exp` is *effectively o-minimal*: component counts bounded
  computably in formula complexity. Right kind of syntactic uniformity, **wrong quantity** — a count
  cannot produce a floor, since `exp(−x)` has *no zeros* and infimum `0`.
* **Łojasiewicz** — the standard separation tool is **polynomially shaped**, and that shape provably
  does not extend to o-minimal expansions where `exp` is definable. **This is why the floor had to be
  tower-scale: the shape was forced.**

**Transseries** carries exactly the right vocabulary — exponential/logarithmic *depth* of a term,
exponential *height* of a germ, with height rising by one per `exp` on an unbounded argument — **for
a transmonomial**. *Differences* break the correspondence, and that break **is** this conjecture.

### The surgical question for a specialist

> Let `f`, `g` be distinct logarithmic-exponential germs represented by expressions of bounded EML
> complexity. Is there a complexity-dependent class of transmonomials `M_d` such that every nonzero
> `f − g` eventually satisfies `|f(x) − g(x)| ≥ c·m(x)` for some `c > 0` and `m ∈ M_d`?
>
> Equivalently: **does bounded defining complexity uniformly bound the asymptotic complexity of the
> leading surviving term after arbitrary cancellation?**

Send with the three things already learned: subtraction may collapse height arbitrarily; peeling `exp`
exposes a precursor gap but *raises* EML depth; totalised `log` destroys ordinary parent→child growth
descent.

**Search is exhausted from this end** — three web searches returned the same framing and no theorem.
The next step is a person, not a fourth search.

---

## 8. Exit criteria — decided in advance, not in the moment

**243 axioms stay pinned until all three hold.** Written down now so that `ASSUMED` is an
architectural choice rather than fatigue.

1. **Survives deliberate falsification.** §6 is run, at adequate precision, in iterated-log
   coordinates, and reports what it could not have found.
2. **External support.** A recognised theory supports it or supplies a nearby established theorem —
   the §7 question answered, or a citation located.
3. **Downstream worth the trade.** Assuming it unlocks enough that the explicit trust cost is
   justified. **Today it does not** (§2), and that is the criterion most likely to fail.

**If it is REFUTED:** the counterexample kills `DecayFloor` and `GrowthEnvelope` too — they are one
obligation — and the depth programme needs redesigning around the counterexample, not patching.

**If it is ASSUMED:** spend the axiom on the **uniformity alone**, never the whole statement. The
per-pair half is a theorem of 1912 and importing it would widen the disclosed surface for nothing
(`EmlGermApproachPerPair` exists so the split is visible at the point of use). Mark the ledger row
`assumed`, not `discharged` — `obligation_ledger_check.py` has carried that status and its checks
since `(dm)`, and the row must name the axiom.

---

## 9. What NOT to do

* **Do not start the depth-2 cell enumeration.** `NodeDecayBound 3` is the only thing between the
  ladder and `DecayFloorUpTo 4`, and its only known route is a `≈27 × 27` shape enumeration *before*
  parameter regimes — the scale `FRONTIER_BRIEF_3` §4 Q2 measured and rejected. Depth 3 was reachable
  only because that cost had already been paid one level down. A bounded rung does not move the
  ledger.
* **Do not add scaffolding around the conjecture.** The machinery is complete:
  `decayFloor_of_ladderInputs` shows the ladder reaches the obligation, and everything else is
  proved. More interfaces will not help.
* **Do not read any of the equivalences as progress.** Check for a converse first. `(dw)` claimed a
  factoring that `(dx)` had to withdraw.
* **Do not design a recursion whose base case is "no cancellation" or "height-`0` left germ".**
  Both cells are the conjecture — `peelTerminalNoCancel_iff_growthEnvelope` and
  `peelTerminalConstZero_iff_emlGermApproach`, §4(6). Price the **terminal cell** before the
  measure: (1)–(5) all died on the measure and (6) did not, which is exactly why the habit of
  checking only the measure is now a trap. The cheapest check is one line —
  `decayFloor_of_emlGermApproach` instantiates `A` at `const 0` and nothing else, so *any* cell
  containing that one instance contains the whole obligation.
