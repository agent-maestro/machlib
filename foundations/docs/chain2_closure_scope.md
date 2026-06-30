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
- **First component** `degreeY₁`: preserved by `chainTotalDeriv` (`degreeY1_chainTotalDeriv_eq_IterExp2`,
  done) ⇒ ties ⇒ must descend the second.
- **Second component** `singleExpMeasure(lcY₁ ·)`: this is where the **single-exp reduce descent plugs
  in**. `lcY₁ (scaledReduction f)` must have a strictly smaller *single-exp* measure than `lcY₁ f`. The
  bridge: `lcY₁` of the chain-2 reduce relates to the single-exp reduce of `lcY₁ f` (the
  `lcY1_cTD_eval_zero_IterExp2` / leading-coefficient descent lemmas are the seam), and `lcY₁ f` is a
  genuine SingleExp object, so the **already-proven single-exp reduce strict-descent** applies to it.
- Risk: this is real proof work (connecting the chain-2 reduce to the single-exp reduce on `lcY₁`), but
  it reuses proven lemmas on both sides; estimate the bulk of the remaining effort here.

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
