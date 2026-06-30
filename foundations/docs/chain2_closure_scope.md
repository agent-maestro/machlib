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
- **Second component** `singleExpMeasure(lcY₁ ·)` — **the open seam, sharper than first stated**:
  - It is **not** an unconditional descent. `singleExpMeasure(lcY₁ p) = (degreeY₀(lcY₁ p), trueDeg(…))`,
    and `degreeY₀(lcY₁ ·)` can *increase* under the naive reduce when `lcY₁ p` is constant in the chain
    values — worked counterexample `p = y₁`: `lcY₁ p = 1` (inner `(0,0)`) but `lcY₁ (reducePoly p) = y₀`
    (inner `(1,…)`), so the second component goes **up**. So the reducer must **case-split**: `lcY₁ p`
    non-constant (inner measure `>0`) → seam-style single-exp reduce descends the inner `trueDeg`; `lcY₁ p`
    constant (inner `=0`, but `degreeY₁>0`) → a **distinct** `degreeY₁`-lowering move is required (the
    `scaledReduction 0` does not descend here).
  - **Flat↔nested gap**: the proven seam `chain2_polyTrueDegreeStrict_scaledReduction_zero_lt` descends
    `trueDeg(mP2PFL(lcY₁ ·))` — the *flat* `y→0` projection — whereas the chain-aware inner second is
    `trueDeg(mP2PFL(lcY₀(lcY₁ ·)))` (an **extra** `lcY₀`). Bridging flat→nested `trueDeg` is part of the
    remaining seam, on top of the inner `degreeY₀` tie.
- Risk: real proof work (the case-split + the flat↔nested bridge + the inner `degreeY₀` accounting),
  reusing proven lemmas on both sides; this is the bulk of the remaining effort.

**Phase 3 — assemble the chain-2 `Chain2SDR`.** Package Phase 2: given `degreeY₁ > 0`, emit the
`Chain2ReduceStep` (result = `scaledReduction`, witness = one `IsKhovanskiiReducible.step`, `lex_decrease`
= Phase 2). Mechanical once Phase 2 lands.

**Phase 4 — the chain-2 capstone + hook.** Mirror Step 3f/3g over `chain2Order_wf`:
`buildChain2Reducer` (drop on `degreeY₁=0`, recurse on Phase 3 otherwise) → witness → bound; then close
`sdr_other` for chain-2. Mechanical (mirrors existing `buildReducer`/`witness_via_sdr`).

---

## Effort, risk, payoff

- **Effort**: Phase 2 is the bulk (a focused multi-session theorem); Phases 3–4 are mechanical mirroring
  (~1 session combined). Total: realistically **2–4 focused sessions**.
- **Risk**: concentrated in Phase 2 (the chain-2-↔-single-exp reduce seam). Path B keeps the closed
  single-exp proof untouched, so a Phase-2 stall costs *only* chain-2, never a regression.
- **Payoff**: closes chain-2 Khovanskii (the announcement blocker); the same nested-measure pattern then
  generalises to chain-`n` (`natQuadLex_wf` already shows the WF backbone scales).

**Recommendation.** Path B. Next concrete step: **Phase 2**, starting from
`chain2_polyTrueDegreeStrict_scaledReduction_zero_lt` (the flat-second descent already proven) and
lifting it to the chain-aware second via the single-exp reduce on `lcY₁`. If Phase 2's seam proves
intractable in a session, that is itself the answer (chain-2 needs a different reduce), and it costs
nothing already shipped.
