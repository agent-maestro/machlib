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

## 4. The eight failed descent mechanisms

All eight are proved, footprint-clean, in `EMLLadderMeasure`, `EMLGermApproach`,
`EMLPolarityMeasure`, `EMLGermInvariance`, `EMLPeelRecursion`, `EMLProductMerge` and
`EMLPairDescent`.

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
   strictly to **both** children. **It does NOT say no such descent exists** — `wfDescent_inhabited`
   exhibits one (`polDescent`). It says none of them also prices the reciprocal at one step, which
   is what the ladder needs. Then `recipTree = eTree ∘ negLogTree` is **two strict steps up** —
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
   **The second one is now computed — it is 115 depth levels per merge, and (7) is what paying it
   buys.** The first is still unpaid, and still not due.

7. **A class closed under products — the merge's own price, PAID** (`EMLProductMerge`, 2026-09-23).
   The obvious seventh attempt, and the one (6) invites: define the smallest class containing the
   EML germs and closed under multiplication, redo the peel there, and see what the terminal cells
   become. **There is no such extension.** `EMLRingClosure` (2026-09, never cited by this programme
   until now) proves `mulGen_eval (u v : EMLTree) (x : Real) : (mulGen u v).eval x = u.eval x *
   v.eval x` with **no hypothesis of any kind** — not positivity, not on `x` — and
   `EMLCharacterisation` identifies the class outright: `InEML f ↔ ExpLogClosure f`, the closure of
   the constants and `id` under `+`, `−`, `×`, `exp`, `log`. `prodClosure_iff_inEML` writes down the
   route's own class (EML germs, products, totalised `log`) and proves it **equal to EML, both
   ways**. Reciprocals were inside before that: `recipTree` is `e/t` at `+2`.
   **"EML has no product NODE" is true; "the class is not closed under products" is false**, and
   (6)'s price paragraph is where the two were run together.
   **So the price is payable, and it is `115` depth levels per merge** (`mergeTree_depth_le` =
   `mulGen_depth_le` 112 + `logTree_depth` 3; at `var` the product alone is 54,
   `mulGen_var_var_depth`). The merge multiplies the accumulator by exactly **one** germ per peel,
   so a run performs `lspTree A ≤ j` merges and the accumulated right-hand germ is an ordinary EML
   tree of depth **`≤ 116 · j`** (`peelAccum_depth_le`, `peel_accumulator_bounded`).
   **The crux — does the complexity bound survive the closure? — is answered YES, and that is what
   kills it.** A bounded class is a class (6) applies to:
   `PeelTerminalAccum ↔ EmlGermApproach`, **both directions**
   (`peelTerminalAccum_iff_emlGermApproach`). Forward costs nothing —
   `peelAccum (const 0) C = C` by `rfl`, so a leaf left germ performs **no merges** and the
   product-closed cell *contains* (6)'s `PeelTerminalConstZero` verbatim. The converse is where the
   `116 · j` is spent, so the cell is not harder either. Read as a reduction: **the peel with its
   price paid reduces the conjecture at depth `j` to the conjecture at depth `116 · j`** — the
   fourth sighting of the same direction of travel (`recipTree` `+2`, `posEmbed` `+4`,
   `A − log C` `+1`, the merge `+115` a step).
   **At the right width this is not about products at all.**
   `terminalCell_of_class_is_the_conjecture` takes **any** carrier, with **any** complexity measure,
   into which EML trees embed with bounded complexity, and concludes `EmlGermApproach` from its
   height-`0` terminal cell. **No enlargement of the right-hand germ class can shrink a terminal
   cell, because the cell quantifies over the class.** Transseries, Hardy fields, valuation rings:
   the cell grows with the class, and §5's asymptotic-normal-form bet cannot be rescued by making
   the class bigger any more than by making the parameter finer.
   **And the escape costs the measure.** Drop the syntax and `exp (log g) = g` restores the peel's
   shape at every positive germ, so the recursion never has to stop — but then nothing bounds it.
   `no_germInvariant_peel_bound`: **no function of the germ bounds the peel count**, because
   `selfLeftNode` re-presents any tree **two spine levels up with the same germ**, unconditionally,
   and iterates (`iterSelf_germ`, `iterSelf_lsp`). Any parameter that survives the closure is
   germ-invariant, and (5) proved that class empty. **Pay the price and you are in (6); refuse to
   stop and you are in (5).**
   Fixtures: every §3 verdict is unchanged, one column added. `deepDecay m` still merges **twice**
   for every `m` (`prod_peel_blind_on_deepDecay`) while forcing height `m + 1`; `gapTarget n c`
   still merges `n + 1` times for a floor of height `0` (`prod_peel_overworks_on_gapTarget`);
   `peelCount_cannot_carry_floor` is untouched. **The closure changes the arithmetic and no
   verdict.**

8. **A well-founded relation on PAIRS `(A, C)`** (`EMLPairDescent`, 2026-09-23). The class this
   file's own width paragraph put at the head of what is untouched, and the one that looked most
   alive: every mechanism before it measures **one tree**, while the conjecture is about a pair.
   **It is well-founded, the peel decreases it, the run terminates — and its minimal elements are
   (6)'s T2 cell.**
   The relation is the peel step itself, with no measure interposed: `PeelRel` sends
   `(eml A₁ A₂, C)` to `(A₁, mergeTree A₂ C)` — the merge of (7), proved and usable. **Well-foundedness
   first, as §5 requires**: `peelRel_wf`, by `lspTree ∘ fst`, and the class `PairDescent` — any
   measure on pairs into any well-founded order the peel decreases — is inhabited
   (`pairDescent_inhabited`).
   **Mechanism (4) does NOT transport, and that was checked first because it is one lemma either
   way.** The exact configuration (4) refutes is **realised** here: the pair measure prices
   `recipTree t` at `2` for every `t`, so on any left germ with two or more peels the reciprocal is
   *cheap* (`cheap_recip_survives_in_pairs`) and no contradiction follows — because the peel never
   asks for descent to a right child, and `lspTree` provably does not have it
   (`lspTree_not_right_descending`). `mechanism_four_does_not_transport` states the three facts
   together. **So (8) is a genuinely new class, not (4) in new clothes.**
   **The minimal elements, computed before any floor was attempted.**
   `pairMinimal_iff : PairMinimal (A, C) ↔ A.lspTree = 0`, both directions — an `eml` left germ
   always has a peel below it, a leaf left germ has nothing below it — and the first half survives
   for **every** `PairDescent` (`pairDescent_eml_not_minimal`), so the minimal set of any
   peel-decreased pair relation is contained in `{A.lspTree = 0}`. **That is T2 verbatim**, and
   `PairTerminalCell ↔ EmlGermApproach` (`pairTerminalCell_iff_emlGermApproach`), **with a
   converse**, at the same depth — where (7)'s converse cost `j ↦ 116·j`. The route's other exit is
   the peel step's own side condition `0 < c`, which is T1. **The same two cells, in new clothes.**
   **And the cell is not a choice.** `base_must_contain_constZero`: any sound peel-driven pair
   recursion whose base cases are `≺`-minimal contains `(const 0, C)` for every `C`. The proof is
   the run — instantiate the induction at `P A C := S (leftLeaf A) (peelAccum A C)`, whose step case
   is `rfl` because that substitution *is* a peel, and read the conclusion at `const 0`. **Both
   verdicts on the instrument**: the same theorem refutes the `var`-only base case
   (`var_only_base_is_unsound`), and the full leaf base case is sound (`pair_peel_induction`) — the
   pair recursion is a valid induction principle, machine-checked, `peel_run` reaching
   `(leftLeaf A, peelAccum A C)` in exactly `A.lspTree` steps.
   **The fixture row that decides it is sharper at pair width than it was for `lspTree`.** (6)
   records the peel count as *constant* on `deepDecay`; on pairs it is **zero** there, and not by
   accident — `decayFloor_of_emlGermApproach` routes **every** instance of `DecayFloor` through the
   pair `(const 0, approachTarget t)`, whose left germ is a leaf. So **the entire obligation the
   conjecture reduces to consists of `≺`-minimal pairs** (`decayFloor_reduction_is_minimal`): the
   route's engine never turns over on its own workload, and `pairCount_cannot_carry_floor` turns
   that into `False` (`deepDecay m` forces `m + 1 ≤ f 0` for every `m`).
   **Two escapes, priced.** The second coordinate cannot carry the descent —
   `no_accumulator_descent`: no measure of the accumulator alone descends along the merge in **any**
   well-founded order, because the merge iterates and `C, A₂·C, A₂·(A₂·C), …` would be an infinite
   descending chain. And dropping the syntax is closed at pair width too
   (`no_germInvariant_pair_bound`): no function of the **germ pair** bounds the peel count, by
   `selfLeftNode` exactly as in (7).
   **So the pair reading does not escape (6) — it IS (6)**, with the accumulator named and the
   measure read off the first coordinate. Fixtures: four of the six terminate at `const 0` (the T2
   cell verbatim — `fixtures_terminate_at_constZero`), `gapTarget n c` is the one that terminates at
   `var` (`leftLeaf_gapTarget`), and the meeting pair `(A, eTree A)` **never enters** the recursion
   at all (`pair_entry_fails_at_meeting`). **Pairs change the vocabulary and no verdict.**

**Stated at the right width, and this has been got wrong twice:** what is killed is *local scalar
growth descent through the syntax tree* (1)-(3); — since (4) — **every measure on trees, into
any well-founded order, that descends to both children**; — since (5) — **every
germ-invariant parameter whatever, on either side or both**; — since (6) — **every recursion,
of any shape, whose terminal cell is a cancellation-free pair or a height-`0` left germ**, because
those two cells are the obligation itself; and — since (7) — **every enlargement of the
right-hand germ class**, whatever it is closed under and however its complexity is measured,
because the terminal cell quantifies over the class and therefore grows with it; and — since (8) —
**every well-founded relation on PAIRS `(A, C)` that the peel step decreases**, whatever its carrier
and order type, because its minimal elements are contained in `{lspTree A = 0}` and no sound base
case can omit the `(const 0, C)` instances the peel itself carries every pair to. That is still
**not** the claim that no well-founded
induction can work. Untouched, precisely: a **mutual** induction over `(tree, polarity)` pairs with
*different* relations per polarity; a one-sided syntactic descent **with a terminal cell that is
neither of (6)'s two** — (6) closes the base case, not the measure, and `lspTree` survives as a
measure, though (7) says a **bigger class** is not how such a cell is obtained and (8) says a
**pair** is not either; and any non-structural argument. The sentence this paragraph used to carry
— *"a well-founded relation on germs … is outside (4) by construction"* — is **false**, and (5) is
why. The one it carried until (8) — *"a relation on pairs `(A, C)`"* as an untouched class — is
**closed**, and the reason is that a pair relation's descent has nowhere to live but the left germ's
syntax (`no_accumulator_descent`), which is (6)'s territory.

**And the first of those classes is where the ladder already lives**, which is why a better measure
cannot help it: `decayFloor_of_ladderInputs` is a structural induction on the depth bound needing no
measure at all, and its residue is `NodeDecayBound` — an unproved rung, not a parameter. A measure
buys the *transfer* route, and the transfer route is what (4) closes.

**And one correction worth carrying:** `(di)`'s re-embedding is a **moving boundary**. It says the
positive branch at depth `k` is as hard as `DecayFloor` at depth `k − 4`. With depth ≤ 3 proved
(`decayFloorUpTo_three` — which proves depth 3 at height **2**, not the sharp height 0 the §6 sweep
reports; the theorem and the measurement are different claims), it first bites at **depth 8**, and
that boundary rises by one per rung proved. Read carelessly it retires four rungs without an argument.

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
`NodeDecayBound`; it cannot be the *ladder*. And — since §4(7) — it cannot be rescued by working
in a **larger** class either: the terminal cell quantifies over the class, so transseries or a
Hardy-field completion enlarges the cell rather than the toolkit.

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
side, with the other side carried by a different argument; and non-structural arguments. (*A
relation on **pairs** `(A, C)`* stood in that list until §4(8), which closed it: the pair relation
is well-founded and the peel decreases it, but its minimal elements are (6)'s T2 cell and the
accumulator cannot carry a descent at all.) The corpus's two blindness results now bracket it from both sides —
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

So at depths 2–4 the conjecture's `k` is pinned from both sides at `j − 3` — **and the two sides
are not the same kind of statement.** The LOWER bound is machine-checked (`deepDecay m` is a
theorem). The UPPER bound is NUMERICAL ONLY, and over a **two-element constant alphabet** while
the grammar allows an arbitrary real constant at every leaf; §6 records that a counterexample
needing a particular transcendental constant is invisible to this instrument, and that this corpus
has one recorded instance of exactly that miss. A sweep is not an induction, and half of this pin
is not even a proof of a bound. **What it does say is that the value is not in doubt — but `j − 3` is the value of ONE of two
metrics, and this section reported it under the other.** `DecayFloor` is stated with a constant,
`t(x) ≥ exp(−(C + tower_k x))`; `EmlGermApproach` (§1) is stated **without** one,
`exp(−tower_k x) ≤ gap`. They are equivalent as *propositions* — that is the proved cycle — but
their **attained heights differ by exactly one**, and every table in this section measures
`−log t(x) ≤ tower_k(x)`, which is the strict form, over an alphabet that could not express the
difference.

The separating family is `exp(1 − tower_{j−3}(x) − M)` at depth `j`, built from `e^-M` at one
leaf (defect 7). Its `−log t` is `tower_{j−3}(x) + M − 1`, which **exceeds `tower_{j−3}(x)` at
every `x`** and is **below `C + tower_{j−3}(x)` with `C = M − 1`**. Measured 2026-09-23 with `M`
running `0, 1, 5, 50, 10⁶, 10⁴⁰`: the DecayFloor height stays at `j − 3` throughout, and the
strict height is `j − 2`. So:

* **`DecayFloor`'s `k(j) = j − 3`** — attained by `deepDecay (j−4)`, and the value every table in
  this section and in the 2026-09-23 run reports **at the tail**;
* **`EmlGermApproach`'s `k(j) = j − 2`** — attained by the offset family above, and the value the
  2026-09-05 tables would have reported had any sweep alphabet contained a constant in `(0,1)`.

**Both are bounded at fixed `j`, so neither is a counterexample** — the conjecture's content is
that `k` depends on `j` alone, not that it equals any particular function of `j`. But a proof
attempt must aim at the number belonging to the form it is proving, and **must not carry `j − 3`
across the equivalence.** The cycle costs a height when it is traversed, which is the same fact
§4(6) records as *"`+1` height cell→envelope, none the other way"*.

Read the tables accordingly. **The 2026-09-05 rows and the 2026-09-23 rows both report the
DecayFloor number**, the first by accident of its alphabet and the second because an additive
constant is below the working precision beside `tower_{j−3}(x)` in the tail. Neither has ever
measured the strict number except on the bounded window of `x` where `M` is still resolvable, and
that window shrinks like `log^{j−3}(M)`.

And the older caution survives intact and now cuts twice: the LOWER bound is machine-checked, the
UPPER bound is numerical only, **and until today the upper bound was not even a bound on the
quantity `EmlGermApproach` asks about.**

---

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

7. **THE CONSTANT ALPHABET HAD A HOLE, AND IT WAS EXACTLY THE ONE DIRECTION THAT MOVES THE
   READING.** `log₀ c` is `0` for `c ≤ 0` and for `c = 1`, **positive** for `c > 1`, and
   **negative** — the only case in which a leaf ADDS to a germ, since `eml A B = exp A − log₀ B` —
   for `0 < c < 1`. Every sweep alphabet of `germ_approach_search.py` lies inside
   `{0, 1, 5, 50, 1000}` (lines 503-519: `[0,1]`, `[0,1,5]`, `[0,1,50]`, `[0,1,1000]`,
   `[0,1,5,50]`), so **`log₀ c ≥ 0` at every leaf of every tree it ever examined** and no leaf
   could add anything to any germ. Every widening of `{0,1}` that section reports — to `{0,1,5}`,
   `{0,1,50}`, `{0,1,1000}`, `{0,1,5,50}` — added only constants that SUBTRACT, and a constant
   subtrahend is dominated in the tail by the subtree it sits beside. The constants that ADD are
   the ones that move the strict reading, and none was ever present.
   **The mechanism was in that file the whole time — inside its own controls.** `exp(−1)` occurs
   in `germ_approach_search.py` exactly twice, at lines **334 and 337**, both inside `controls()`,
   where `eml(var, const e⁻¹) = exp(x) + 1` is what makes control-1 fire. **The one leaf value able
   to move the reading was in the instrument's controls and never in its search.**
   With `e^-M` in the alphabet, `eml(tower_{n-1}, const e^-M) = tower_n(x) + M` at depth `n`, and
   `exp(1 − tower_n(x) − M)` at depth `n + 3` misses the strict height-`n` floor at **every** `x`,
   by the constant `M − 1`. That is the family PIECE 3 is about.
   **This is defect 3's shape, not defect 4's.** Defect 3 was a guard that rejected both positive
   controls — an instrument reporting a clean negative result while unable to report anything else.
   This is an alphabet that excluded the one constant its own controls depended on. Both are the
   same failure: *the search and the controls were not exercising the same machinery*, and only the
   controls were ever checked for it.

---

**The prediction this table tests was itself corrected by the table.** A first draft of this
section predicted `j − 2`, from miscounting the extremal construction: the smallest positive germ
at depth `j` is `exp(1 − tower_{j−3})`, and the `exp` that makes it positive costs the extra level.
The exhaustive depth-3 sweep returned 0 where `j − 2` predicted 1, which is how the miscount was
found — the instrument correcting the prediction rather than the other way round, which is the
only direction that is worth anything.

### ▸ RUN, 2026-09-23 — `foundations/tools/germ_tower{,_eml,_search}.py`

**No counterexample. `j − 3` held at depths 4-7, where the 2026-09-05 instrument could resolve
only depth 4 — and the search's own table now separates the two metrics that run conflated.**

```
depth ≤ 2, ≤ 3, constants {0,1}   EXHAUSTIVE, 147 and 21 612 trees   height 0 — reproduces 2026-09-05
depths 1-7, 16 constants + var    288 910 nodes formed, 78 369 distinct germs
                                  DecayFloor height 0,0,0,1,2,3,4  =  j − 3 at every depth
depth 5 alone                     52 440 nodes, 16 592 germs, 0 OVERFLOWS, 0 of 12 unstable
pair form, depth ≤ 2 / 3 / 4      287 346 pairs           height 0 / 1 / 2
positive controls                 deepDecay 0..5, depths 4-9, heights 1..6 — all SIX FIRE
```

**The old ray did not die of precision. It died of REPRESENTATION, and that is the whole design.**
§6 above records the reach as a function of depth — `x ≤ 10⁵` at depth 2, `x ≤ 13` at depth 3,
`x ≤ 2.8` at depth 4, `x ≈ 2.2` at depth 5 — and attributes it to the tower passing 120-digit
precision. The attribution is wrong in a way that matters: to know the *mantissa* of
`exp(exp(exp x))` to one digit you must know `exp(exp x)` to one **absolute** digit, i.e. to
`exp(x)/ln 10` significant digits. At `x = 20` that is 210 million digits. **No dps setting reaches
depth 5**; raising it buys about one unit of `x`. A value representation cannot be fixed here.

So `germ_tower.py` does not represent the value. It represents the **iterated-log spine**:

```
val((), m)          = m                        (m an ordinary mpf, any sign)
val((s,) + rest, m) = s * exp(val(rest, m))    (s = ±1)
```

canonical iff a nonempty spine's inner value exceeds `LOGBIG`, so every number has one form. Then
**`exp` is a spine push and `log` a spine pop, both EXACT with no arithmetic at all**, `neg` flips
the leading sign, and the only operation that can cost a digit is `+`. `exp(−exp(exp x))` at
`x = 10³⁰` is the three-symbol object `((+1,−1,+1), 1e30)`, compared and differenced exactly.
Reach stops being a function of depth: **one ray serves every depth**, scoring at
`x ∈ [6.18, 2.85 × 10⁶⁴]` and confirming at `x ∈ [6.18, 4.11 × 10¹²⁹⁴]`. The `overflow` and
`tail-unmeasured` buckets that defect 2 was built for are **empty by construction** — there is no
working range left to leave.

A sum is `a + b = sa·exp(A)·(1 + (sa·sb)·exp(B − A))`, a recursive difference of exponents
bottoming out on two ordinary mpfs, and *that* bottom is the one place cancellation destroys
digits. The guard there is **relative**, inherited from defect 3 and not re-derived.

**The error bias is one-way, and a reader should know which way.** When `|b|` falls below the
working precision beside `|a|`, `a + b` returns `a` — the term is ABSORBED. In a difference that
makes the computed `|t|` **larger** than the truth and the computed height **smaller**. So this
instrument can **MISS** a counterexample and **cannot INVENT** one. Every absorption is counted, so
a result landing on exact zero after one is reported in its own bucket (`zero-after-absorption`)
rather than read as a germ that meets its target.

**What precision each depth actually needed — measured, not assumed.** The same beam run at
15 / 30 / 60 / 120 / 240 dps:

| dps | depth 2 | depth 3 | depth 4 | depth 5 |
|---|---|---|---|---|
| 15 | 0 / 0 unresolved | 0 / 5 | 1 / 0 | 2 / 113 |
| 30 | 0 / 0 | 0 / 3 | 1 / 0 | 2 / 44 |
| 60 | 0 / 1 | 0 / 0 | 1 / 0 | 2 / 2 |
| 120 | 0 / 1 | 0 / 0 | 1 / 0 | 2 / 0 |
| 240 | 0 / 0 | 0 / 0 | 1 / 0 | 2 / 0 |

**The height verdict is already correct at 15 digits at every depth, and settles at 30.** Only the
unresolved count moves. The 2026-09-05 run's fixed 120 digits were never the binding constraint —
which is the same finding as the paragraph above, arriving from the other end.

**The depth-5 verdict, which is what the table above could not give.** DecayFloor height **2**,
`= j − 3`, confirmed. 52 440 nodes formed at depth 5 over 16 592 distinct germs; **0 overflows, 0 of
12 re-measurements unstable**, 307 refused as `zero-after-absorption` and 4 as `unresolved` — 0.6 %
of readings discarded against 2026-09-05's **354 unstable plus 1 141 overflowed out of 8 000**,
18.7 %. The extremal tree is `eml(eml(0, eml(eml(eml(x,1),1),1)), 0)`, i.e. `exp(1 − exp(exp x))`:
**`deepDecay 1`, rediscovered by the sweep rather than supplied to it**, exactly as the depth-4
sweep rediscovered `deepDecay 0`.

| depth | coverage | DecayFloor height | `j − 3` | verdict |
|---|---|---|---|---|
| 2 | **exhaustive**, 147 trees over `{0,1}` | 0 | 0 | matches |
| 3 | **exhaustive**, 21 612 trees over `{0,1}` | 0 | 0 | matches |
| 4 | beam, 59 712 nodes / 11 774 germs | 1 | 1 | matches |
| 5 | beam, 52 440 nodes / 16 592 germs | 2 | 2 | **matches — was under-resolved** |
| 6 | beam, 54 808 nodes / 15 302 germs | 3 | 3 | matches |
| 7 | beam, 55 776 nodes / 16 781 germs | 4 | 4 | matches |

**Three controls, because a failed search proves nothing.**

* **Positive.** `deepDecay 0..5`, depths 4 to 9, must report heights 1 to 6. All six fire. The
  2026-09-05 instrument could run this family to `m = 1` at best.
* **Regression.** The exhaustive depth-≤2 and depth-≤3 sweeps over `{0,1}` return **147** and
  **21 612** trees at height 0 — the 2026-09-05 rows reproduced tree for tree by an instrument
  sharing no arithmetic with it.
* **No-seed.** The beam is seeded with §3's families, so the obvious objection is that it found
  `deepDecay` because it was handed `deepDecay`. Run with the seed list emptied it reaches the same
  heights — 0,0,0,1,2,3 at depths 1-6 over 192 096 nodes — via entirely different trees
  (`eml(eml(eml(eml(-1,x),0),eml(eml(x,0),0)),0)` at depth 4). **The reading is not an artifact of
  the seeds.**

**And the specimens were re-verified away from the instrument that found them**: the depth-4, 5, 6
and 7 extremals re-measured at **40, 200 and 1 000 dps** on a ray reaching `x = 3.22 × 10⁷⁰⁶⁸³`
return identical heights, with the germ printing symbolically as `exp(−exp^k(x))`. The depth of
every reported tree is now **asserted** rather than assumed — see defect 5, which was a depth
mislabelling as much as a ray-length one.

---

7. **It cannot certify the cancelling case, only probe it.** The growth recurrences give DecayFloor
   height `j − 3` free to every tree whose top node has `log₀ B ≤ 0`; the whole open content is the
   cancelling case, and there the instrument reports only what it happened to construct.

---

## 7. Literature — what is settled and what is not

Full note with sources and its own limits:
`monogate-research/exploration/germ_approach_literature_2026_08_27/NOTE.md`.

**Classical, and it is most of the statement.** EML germs at infinity are Hardy
**logarithmico-exponential** germs (totalised `log` is first-order definable in `ℝ_exp`, so
totalisation does not leave the class). LE-functions form a **field**, so `1/gap` is again an
LE-function; and every germ in Hardy's class `𝓛` is `o(exp^∘k)` for **some** `k`. Compose:
per-pair floor. **Say `𝓛`, not "Hardy field":** the `o(exp^∘k)` step is FALSE for Hardy fields in
general — transexponential ones exist, containing germs that outgrow every iterate of `exp`. This
file said "every Hardy-field germ" until 2026-09-23; the argument only ever needed `𝓛`, where it
is correct, and EML germs lie in `𝓛` (`EMLCharacterisation.eml_eq_expLogClosure` gives the
`exp`/`log` closure of `ℝ`; that this closure sits inside `𝓛` is classical and argued in prose
here, not formalised).
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


* **Do not hunt a counterexample in the growth mechanism — it is closed by three recurrences, and
  the only opening is cancellation, which cannot bootstrap.** From `eml A B = exp A − log₀ B`:
  `max_d = exp(max_{d−1}) − log(pos_{d−1})`, `min_d = −log(max_{d−1})`, and
  `pos_d ≥ exp(min_{d−1})` **whenever the top node has `log₀ B ≤ 0`** — so every such tree meets
  DecayFloor at height `d − 3` for free, with no induction and no search. Breaking the bound
  therefore requires `log₀ B > 0` cancelling against `exp A`, and to reach height `d − 2` the
  cancellation must itself be of tower height `d − 2`: **it has to be as deep as the thing it is
  trying to build.** Measured 2026-09-23 by a hunt that indexes the pool by `log (log₀ B)` and
  pairs each `A` with its nearest `B`: 5 342 deliberately near-meeting nodes at depth 7 reached
  cancellation heights `{0: 5 278, 1: 35, 2: 15, 3: 14}` against the **5** needed, and their best
  confirmed result was `j − 4` — **one height BELOW what the growth bound hands out for nothing**.
  The shape they all take is `eml(D, const e)` = `exp(D) − 1 ≈ D`, with `D` the extremal germ one
  level down: a whole depth level spent REPRODUCING a decay rather than deepening it. That is
  what "cancellation cannot bootstrap" looks like when you watch it happen.
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
* **Do not propose a bigger germ class.** EML is already closed under `+`, `−`, `×`, `exp` and
  totalised `log`, with **no hypotheses** (`EMLRingClosure`, `EMLCharacterisation`), so *"the class
  closed under products"* names the class we are already in (`prodClosure_iff_inEML`) — and for
  **any** class whatever the terminal cell grows with it
  (`terminalCell_of_class_is_the_conjecture`, §4(7)). The rule below says price the terminal cell
  before the measure; this one says **price the class before the cell**, and the cheapest check is
  one grep for the operation's own name — `grep -rln "mulGen" MachLib/` — which this programme had
  never run in fourteen months of asking whether EML expresses products. That gap is what made (7)
  look like a new class.
* **Do not reach for a relation on pairs, or on anything else, before computing its MINIMAL
  ELEMENTS.** §4(8) is the cheapest death in this file: the pair relation is well-founded, the peel
  decreases it, and `pairMinimal_iff` settles the whole route in two lines because a relation
  generated by one step has exactly the minimal elements that step cannot reach. The measure took a
  paragraph; the minimal elements took a `cases`. **Compute the minimal elements first** — it is the
  same rule as *price the terminal cell before the measure*, in the form a relation rather than a
  recursion presents it. And the cheapest sanity check on any candidate parameter is now one line:
  `decayFloor_of_emlGermApproach` instantiates the left germ at `const 0`, so **if the parameter is
  constant there, it is constant on the entire obligation**.
* **Do not design a recursion whose base case is "no cancellation" or "height-`0` left germ".**
  Both cells are the conjecture — `peelTerminalNoCancel_iff_growthEnvelope` and
  `peelTerminalConstZero_iff_emlGermApproach`, §4(6). Price the **terminal cell** before the
  measure: (1)–(5) all died on the measure and (6) did not, which is exactly why the habit of
  checking only the measure is now a trap. The cheapest check is one line —
  `decayFloor_of_emlGermApproach` instantiates `A` at `const 0` and nothing else, so *any* cell
  containing that one instance contains the whole obligation.
