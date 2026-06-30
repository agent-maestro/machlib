# Scoping: closing chain-2 Khovanskii — the reducer construction

**Goal.** Supply a chain-2 `StepwiseDecreaseReducer` so the `sdr_other` hook in
`singleExp_khovanskii_bound` closes, giving a machine-checked Khovanskii (finite-zero-count) bound for
depth-2 Pfaffian chains (`y₀ = exp x`, `y₁ = exp(exp x)`). This is the "any-depth Khovanskii
announcement" blocker. Grounded in the framework as it stands (`KhovanskiiReduction.lean` 1760 lines,
`ChainExp2SDR.lean` 666, `PfaffianChain.lean`).

**TL;DR.** Done: the well-founded backbone + the chain-aware measure (2 bricks, sorryAx-free,
regression-free). Remaining: one **deep descent theorem** (Phase 2 — the only genuinely hard part) plus
**mechanical assembly** (Phases 3–4). The assembly has a fork — **Path B (a chain-2-specific capstone on
`chain2Order_wf`) is strongly preferred**: it never touches the closed/audited single-exp proof, at the
cost of duplicating ~2 small assembly defs. Path A (migrate the generic `lexMeasure` type) is a
cross-cutting refactor with single-exp regression risk and is **not** recommended.

---

## What's done (Phase 1)

| Brick | Result | Commit |
|---|---|---|
| WF backbone | `LexProd.lexProd_wf` / `natTripleLex_wf` — lex-of-WF is WF, nests to any depth. **No axioms.** | `7c92203` |
| Chain-aware measure | `ChainExp2Measure.chain2Measure = (degreeY₁, singleExpMeasure(lcY₁))`; `chain2Order_wf` via the keystone; sorryAx-free, standalone | `d94f000` |

Plus the **reduce-direction lemmas already in `ChainExp2SDR.lean`** (sorryAx-free): `degreeY1` preserved
by `chainTotalDeriv`, the `c=0` leading-coefficient descent identity, and the flat-second strict descent
`chain2_polyTrueDegreeStrict_scaledReduction_zero_lt` (line 561).

**Phase 2 — structural half done** (`ChainExp2Reducer`, sorryAx-free): `chain2Measure_fst_reducePoly`
(first component `degreeY₁` preserved by the real reduce poly `sub (cTD p) (mul (const 0) p)`) +
`LexProd.lexProd_of_snd` (axiom-free lex helper) ⇒ `chain2_reduce_nestedLT_of_snd` collapses the full
`nestedLT` descent to a single second-component obligation `hsnd`. See Phase 2 below for the sharpened
characterisation of that remaining seam (it is **not** an unconditional descent — case-split + flat↔nested
gap).

## The obligation (what a reducer must produce)

`StepwiseDecreaseReducer = ∀ f hN, (measure f).1 > 0 → ReduceStep f hN`, where a `ReduceStep` carries a
smaller `result`, a `counter`, an `IsKhovanskiiReducible f result counter` **witness** (a single
`scaledReduction`/`step`), and `lex_decrease` — a **strict decrease of the measure**. The capstone
`buildReducer` (Step 3f) does strong recursion on the measure's WF; `khovanskii_bound_via_sdr` (Step 3g)
turns the witness into the zero-count bound.

**The crux** (corrected mechanism — *not* "drop-soundness"): the reduce step's `lex_decrease` must hold,
and under the *flat* `lexMeasure` it provably cannot at `(degreeY₁ = d>0, second = 0)` (e.g. `p=y₀·y₁`:
`mP2PFL(lcY₁)=0`). Under `chain2Measure` it can — the chain-aware second `singleExpMeasure(lcY₁ p)` is
nonzero there. So the whole closure rests on proving the reduce decreases **`chain2Measure`**.

---

## The fork: Path A vs Path B

The reducer/`buildReducer`/`witness_via_sdr` are all written against the **generic** `lexMeasure : Nat ×
Nat`. Two ways to give chain-2 a measure it can actually descend:

| | **Path B — chain-2-specific capstone (RECOMMENDED)** | Path A — migrate the generic measure |
|---|---|---|
| Idea | New `Chain2ReduceStep` / `Chain2SDR` / `buildChain2Reducer` over `chain2Order`, recursing on `chain2Order_wf` | Change `lexMeasure`'s type to the nested measure everywhere |
| Touches single-exp? | **No** (standalone, like `ChainExp2Measure`) | **Yes** — re-verify the closed/audited single-exp proof as the 2-element case |
| Risk | Low (duplicates ~2 assembly defs: a `ReduceStep` analog + a `buildReducer` analog) | High (cross-cutting; regression risk to a shipped result) |
| Cost | Re-derive Step 3f/3g for `chain2Order` (~150–250 lines, mostly mirroring) | Edit `lexLT`/`lexLT_wf`/`ReduceStep`/`buildReducer` + every descent lemma + single-exp |

`chain2Order_wf` was built precisely to make Path B's recursion available without the refactor. **Take
Path B.**

---

## Remaining phases

**Phase 2 — the reduce-step descent theorem (the only deep part).**
Prove `chain2Order (scaledReduction f) f`, i.e. `chain2Measure(scaledReduction f) <ₗ chain2Measure(f)`,
for `degreeY₁ f > 0`. Decompose by the nested-lex structure:
- **First component** `degreeY₁`: preserved by the reduce ⇒ ties ⇒ must descend the second. **DONE**
  (`ChainExp2Reducer`, sorryAx-free): `chain2Measure_fst_reducePoly` proves it on the *real* reduce poly
  `reducePoly p = sub (cTD p) (mul (const 0) p)` (not bare `cTD p`) — both summands keep the `y₁`-degree,
  so the `Nat.max` over the `sub` is `degreeY₁ p`. `chain2_reduce_nestedLT_of_snd` then reduces the whole
  `nestedLT` descent to a single second-component hypothesis `hsnd` via `LexProd.lexProd_of_snd`.
- **Second component** `singleExpMeasure(lcY₁ ·)` — **a MACHINE-CHECKED no-go for the naive reduce**:
  - The c=0 `scaledReduction` (`reducePoly`) does **not** descend `chain2Measure`. The chain-2 total
    derivative injects a `y₀` factor into `lcY₁` (since `y₁' = y₀·y₁`), so `degreeY₀(lcY₁ ·)` — the inner
    *first* component of `singleExpMeasure` — strictly *increases*. Witness `p = y₁`: `lcY₁ p = 1` (inner
    `degreeY₀ = 0`) but `lcY₁ (reducePoly p) = y₀·1 − 0·1` (inner `degreeY₀ = 1`). This is now PROVEN in
    `ChainExp2Reducer` — `chain2_reducePoly_not_nestedLT` (+ the two `rfl` numeric facts
    `chain2_inner_degreeY0_yOne = 0`, `chain2_inner_degreeY0_reduce_yOne = 1`), sorryAx-free. So Phase 2's
    `hsnd` is *unprovable* for `reducePoly`; `chain2_reduce_nestedLT_of_snd` (the conditional Phase-2
    reduction) stands as the template for whatever the *correct* reduce turns out to be.
  - **The correct reduce is genuine new construction.** It must reduce `lcY₁` *as a single-exp object*
    (without injecting `y₀`) — the chain total derivative cannot. This **reduce arm is still open** (the
    crux).
  - **Trim arm — DONE** (`ChainExp2Trim.lean`, sorryAx-free): the *other* dispatch branch is built. The
    `MultiPoly 1` `dropLeadingY` machinery is lifted to a generic `dropLeadingYAt {n} (i)` (the primitives
    `reconstructY`/`yCoeffsAt`/`degreeY_reconstructY_lt`/`listEvalAuxN_dropLast_eq_of_last_eval_zero` are
    all `{n}`-generic, so the two lemmas port verbatim), and instantiated at `⟨1⟩ : Fin 2` to give
    `chain2_canonicalTrim_step` — a sound `Chain2ReduceStep` for the canonically-zero-`lcY₁` corner
    (phantom `y₁`-leading term): `lex_decrease` is the first-component (`degreeY₁`) drop (`Or.inl`),
    witnessed by `IsKhovanskiiReducible.trim`. This handles `degreeY₁ p > 0 ∧ lcY₁ p ≡ 0`; the
    complementary `lcY₁ p ≢ 0` is the open reduce arm.
  - **Flat↔nested gap (separate issue)**: the proven seam `chain2_polyTrueDegreeStrict_scaledReduction_zero_lt`
    descends `trueDeg(mP2PFL(lcY₁ ·))` — the *flat* `y→0` projection — whereas the chain-aware inner second
    is `trueDeg(mP2PFL(lcY₀(lcY₁ ·)))` (an extra `lcY₀`). That seam is about the flat measure and does not
    by itself feed the nested descent.
- Risk: **higher than first scoped.** Phase 2's reduce is now known to be a new operation (not the chain
  total derivative), and the trim arm needs porting from `MultiPoly 1`. This is research, not mirroring.

**Phase 3 — assemble the chain-2 `Chain2SDR`.** Package Phase 2: given `degreeY₁ > 0`, emit the
`Chain2ReduceStep` (result = `scaledReduction`, witness = one `IsKhovanskiiReducible.step`, `lex_decrease`
= Phase 2). Mechanical once Phase 2 lands.

**Phase 4 — the chain-2 capstone + hook.** Mirror Step 3f/3g over `chain2Order_wf`:
`buildChain2Reducer` (drop on `degreeY₁=0`, recurse on Phase 3 otherwise) → witness → bound; then close
`sdr_other` for chain-2. Mechanical (mirrors existing `buildReducer`/`witness_via_sdr`).

---

## Effort, risk, payoff

- **Effort** (revised after the machine-checked obstruction): Phase 2 is **research, not mirroring**. It
  needs (i) a *new* chain-2 reduce that reduces `lcY₁` as a single-exp object without injecting `y₀` (the
  chain total derivative provably won't — `chain2_reducePoly_not_nestedLT`), and (ii) the trim arm ported
  from `MultiPoly 1` to `MultiPoly 2` (`dropLeadingY` + `degreeY_dropLeadingY_lt` +
  `eval_dropLeadingY_of_last_canonically_zero`). Phases 3–4 stay mechanical once a *descending* reduce
  exists. Total: **more than 2–4 sessions**; Phase 2 may need a design iteration on the reduce/measure.
- **Risk**: concentrated in Phase 2, now *characterised* (not just suspected): the naive reduce is ruled
  out by proof. Path B keeps the closed single-exp proof untouched, so the stall costs *only* chain-2.
- **Payoff**: closes chain-2 Khovanskii (the announcement blocker); the WF backbone (`natTripleLex_wf` /
  `natQuadLex_wf`) and the structural reduction (`chain2_reduce_nestedLT_of_snd`) already scale to chain-`n`.

**Recommendation.** Path B. The structural half + the obstruction are shipped (sorryAx-free). Next concrete
step: **design the descending chain-2 reduce** — candidate: an explicit "reduce-the-leading-coefficient"
operator that applies the *single-exp* reduce to `lcY₁ p` (a genuine `MultiPoly` in `x, y₀`) and
reconstructs, so the inner `singleExpMeasure` descends by the proven single-exp lemma while `degreeY₁` is
preserved. Validate it against `chain2_reduce_nestedLT_of_snd` (it plugs straight into `hsnd`). In
parallel, port the `MultiPoly 1` trim machinery to `MultiPoly 2` for the canonically-zero `lcY₁` corner.
