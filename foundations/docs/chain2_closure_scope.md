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
  - **The correct reduce — now identified.** The Rolle-sound chain-2 reduce is `R(P) = P' − m·P` with a
    **polynomial multiplier** `m = d·y₀ + c` (`d = degreeY₁ P`). It cancels the `d·y₀·a_d` injection so
    that `lcY₁(R P) = a_d' − c·a_d` — exactly the *single-exp reduce* of the leading coefficient `a_d =
    lcY₁ P`. (Compare single-exp, which reduces with the *constant* `c = degreeY₀`: `lcY₀(P'−d·P) =
    (lcY₀ P)'`; chain-2's cancellation term carries a `y₀`, so a constant multiplier cannot do it — the
    multiplier must be the polynomial `d·y₀ + c`.) **Soundness:** `R(P) = e^{∫m}·(P·e^{−∫m})'`, and
    `e^{−∫m} = y₁^{−d}·e^{−cx}` is nonzero along the chain (`y₁ = e^{y₀}` ⇒ `e^{−d·y₀} = y₁^{−d}`), so
    Rolle on `P·e^{−∫m}` gives `#zeros(P) ≤ #zeros(R P) + 1`. This needs a **framework extension**:
    `IsKhovanskiiReducible`'s `reduce` constructor only allows a *constant* `c`; a polynomial-multiplier
    reduce (and its zero-count transfer) must be added.
  - **The MEASURE must be canonicalised too (machine-checked).** Even the correct `R` does *not* descend
    the *current* `chain2Measure`, because its inner first component is the **syntactic** `degreeY₀` and
    `R` produces `lcY₁` as a non-canonical `sub`/`add` AST whose `y₀` cancellation is only semantic.
    `ChainExp2Reducer.chain2_correctReduce_not_nestedLT` proves it for `p = x·y₁` (`lcY₁(R p)` is
    canonically `1` but syntactic `degreeY₀ = 1`, so the inner second goes `0 → 1`). **So the inner first
    component must be a CANONICAL `y₀`-degree, not `MultiPoly.degreeY ⟨0⟩`** — the operator alone is
    insufficient; `chain2Measure` needs redesign (or `lcY₁` must be canonicalised before measuring).
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

## Reconciliation with the prior `InnerKhovanskiiExpWF` framework

`MachLib/InnerKhovanskiiExpWF.lean` (the `InnerKhovanskiiExp` measured-framework track, distinct from this
`KhovanskiiReduction`/`StepwiseDecreaseReducer` track) attacked the *same* chain-2 wall earlier and
independently found the `degreeY₀`-raising obstruction (its lines 128–174). Reconciling the two:

- **This track's `chain2Measure` IS that file's "Fix A"** — "track `degreeY₀` and `degreeY₁` separately",
  a nested `(degreeY₁, (degreeY₀, …))`. So the two efforts converged on the same measure shape.
- **`chain2_correctReduce_not_nestedLT` (this track) is the rigorous proof that Fix A is *not enough*.**
  That file's prose left Fix A as a promising open path; the machine-checked obstruction shows that with
  the *syntactic* `degreeY₀`, Fix A still fails — *even with the correct operator* — because the `y₀`
  cancellation is only semantic. The resolution is a **canonical** `y₀`-degree (this is new vs both
  earlier files).
- **Premise correction.** That file's Fix-A rationale (lines 156–159) states `chainTotalDeriv` "reduces
  `d₁` by 1". It does **not** — `degreeY1_chainTotalDeriv_eq_IterExp2` proves `degreeY₁` is *preserved*
  (the `y₁`-leading term stays at degree `d₁`, gaining a `y₀` factor in its coefficient). The descent must
  come from the *inner* measure on `lcY₁`, not from `d₁`.

**The correct operator is now concrete in code** (this track): `ChainExp2Reducer.chain2Reduce c p = P' −
((degreeY₁ P)·y₀ + c)·P`, with `chain2Reduce_fst_preserved` (first component preserved). Its inner-descent
is gated on Piece 1 below.

### Piece 1 — canonical `y₀`-degree — FOUNDATION DONE (`ChainExp2CanonMeasure.lean`, sorryAx-free)

Built: `cdegY0 q` (drop trailing canonically-zero `y₀`-coefficients via `CanonicallyZero (polyCoeffs
(mP2PFL c))`, `length − 1`), `canonLcY0`, `singleExpMeasureCanon`, `chain2MeasureCanon` (first component
`degreeY₁` stays syntactic — the *trim* lowers it; only the inner is canonicalised), `chain2OrderCanon_wf`
(trivial via `InvImage.wf` + `natTripleLex_wf`), and the refinement `cdegY0_le_degreeY0` (`cdegY0 q ≤
degreeY ⟨0⟩ q` — the canonical measure never exceeds the syntactic, only forgets phantom leading terms).

Structural half against the canonical measure — DONE: `chain2MeasureCanon_fst_chain2Reduce` (first
component preserved by `chain2Reduce`, verbatim from `chain2Reduce_fst_preserved` since the canonical
measure keeps `degreeY₁` syntactic) + `chain2Reduce_nestedLT_canon_of_snd` (the full canonical `nestedLT`
descent collapses to a single canonical *inner* obligation `hsnd`). So Piece 3 is now isolated to exactly
the **canonical inner descent** `hsnd`: `singleExpMeasureCanon(lcY₁(chain2Reduce c p)) <ₗ
singleExpMeasureCanon(lcY₁ p)`.

Remaining (Piece 3 proper, the last deep proof): prove `hsnd`. It is *not* `rfl` (`cdegY0`/`CanonicallyZero`
are `noncomputable`): it needs the general `leadingCoeffY`-under-`cTD` identity (to show `lcY₁(chain2Reduce
c p) = a_d' − c·a_d`, the single-exp reduce of `a_d`) plus `CanonicallyZero` reasoning + the single-exp
canonical descent on `a_d`. Validation checkpoint: the `x·y₁` case flips from the machine-checked *increase*
to a canonical *descent* `(0,1) → (0,0)`.

### Piece 3 — step 1 DONE, step 2 (the descent) hits the closure's fundamental fork

**Step 1 — DONE** (`ChainExp2Descent.lean`, sorryAx-free): `chain2Reduce_lcY1_eval` — the cancellation.
`eval(lcY₁(chain2Reduce c p)) = eval(cTD₂(lcY₁ p)) − c·eval(lcY₁ p)`, i.e. `lcY₁` of the reduce **is** the
single-exp reduce of `lcY₁ p` (eval-level). The general identity's injected `d·y₀·lcY₁` term cancels the
multiplier's `d·y₀` part. This is the operator's defining property, machine-checked.

**Step 2 — the descent — is the closure's fundamental fork** (mapped, not yet crossed). The obstacle is
sharp: the chain-2 reduce **inflates the syntactic `degreeY₀` of `lcY₁`** (via the `d·y₀·lcY₁` injection),
whereas the single-exp framework relies on its reduce *preserving* syntactic `degreeY₀`
(`degreeY_chainTotalDeriv_eq_SingleExp`) — that is why single-exp needs no eval-invariant degree. Two routes,
each with a substantial remaining piece:

- **Nested measure (current `chain2MeasureCanon`)**: handles the corner (gives `cdegY0` room), but the
  descent needs **`cdegY0` eval-invariance** — a `y₀`-analog of `polyTrueDegreeStrict_eq_of_evalCoeffs_eq`
  (which exists only for the *x*-degree). No `y₀`-template exists; it must be built (a poly-identity in
  `y₀`: `eval = 0 ∀ y₀ ⟹ coefficients canonically zero`). Then the cancellation transfers the descent to
  the single-exp reduce of `lcY₁ p` (whose flat measure the framework already descends).
- **Flat measure + framework extension**: the flat second `trueDeg(mP2PFL(lcY₁))` descends off the corner
  (the projection `mP2PFL` kills the `y₀`-inflation, and the proven seam + eval-invariance of `trueDeg`
  apply), but at the corner `(degreeY₁>0, flat-second=0)` neither reduce nor trim fires — that corner needs
  the **nested Rolle bound** (`#zeros(P) ≤ #zeros(P') + #zeros(lcY₁ P) + 1`), i.e. a two-sub-problem
  `ReduceStep` the current single-result framework can't express.

Both are genuine sub-arcs (comparable to the `y₁`-identity). The nested route is more self-contained
(build `cdegY0` eval-invariance, then reuse the single-exp descent via the cancellation); the flat route
needs a framework extension. **Recommendation: the nested route** — its one missing brick (`cdegY0`
eval-invariance) has a clear x-template to mirror, versus the flat route's open-ended framework extension.

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

**Recommendation.** Path B. Shipped (sorryAx-free): structural half, both obstructions, **trim arm**, and
the **reduce-arm design** (above). The reduce arm now decomposes into three well-specified pieces, in order:

1. **Canonicalise the inner measure.** Replace `chain2Measure`'s inner first component (syntactic
   `MultiPoly.degreeY ⟨0⟩`) with a *canonical* `y₀`-degree (the `y₀`-analog of `polyTrueDegreeStrict`), or
   canonicalise `lcY₁` before measuring. Without this, `chain2_correctReduce_not_nestedLT` shows *no*
   operator descends. Re-establish `chain2Order_wf` for the canonical measure (the `LexProd` backbone is
   unchanged).
2. **Add the polynomial-multiplier reduce to the framework.** Extend `IsKhovanskiiReducible` with `R(P) =
   P' − m·P` for `m = d·y₀ + c` and prove its zero-count transfer (the Rolle argument on `P·y₁^{−d}
   e^{−cx}`). **Analytic heart DONE** (`ChainExp2PolyMultRolle.lean`, sorryAx-free): the integrating-factor
   vehicle `vehicleM f d c = f.eval x · exp(−(d·eˣ + c·x))` (`= f·y₁^{−d}·e^{−cx}`), its same-zero-set
   (`vehicleM_zero_iff`), its `HasDerivAt` (`hasDerivAt_vehicleM` — assembled from the `MachLib.Real`
   `HasDerivAt` add/mul/comp/exp rules), the factoring `f'·E + f·(E·u') = E·(f' − m·f)`
   (`vehicleM_derivative_factored`), and the **Rolle bridge** `polyMultReduce_eval_zero_of_vehicle_deriv_zero`:
   a zero of the vehicle's derivative (Rolle's gift between consecutive zeros of `f`) is a zero of
   `f' − (d·eˣ + c)·f`. This is the exact polynomial-multiplier analog of `scaledReduction`'s
   `mulNegExpX_aux`/`…_eval_zero_of_g_deriv_zero`, holding for every `(d, c)`.
   **Zero-count step DONE** (same file): `zero_count_polyMultReduce_transfer` — `#zeros(f) ≤ N + 1` when `N`
   bounds the zeros of the reduce value `f' − (d·eˣ + c)·f`, via the framework Rolle step
   `zero_count_bound_by_deriv` applied to the vehicle. **`#print axioms` = clean** (no
   `zero_count_bound_classical`, no `analytic_finite_zeros_compact`, no `sorry`; only
   `zero_count_bound_by_deriv` + Real foundations). This is the counting content the dirty axiom asserts,
   now derived by *reduction*. **Remaining for piece 2:** thread this transfer through the iteration
   (`IsKhovanskiiReducible`-style, interleaved with `dropLast`) — bookkeeping, mirrors
   `zero_count_iter_bound_scaledReduction`.
3. **Prove the inner descent + assemble.** With (1)+(2): `lcY₁(R P) = a_d' − c·a_d` (single-exp reduce of
   `a_d`), so the canonical inner measure descends by the *proven single-exp* descent; feed it into
   `chain2_reduce_nestedLT_of_snd`. Then the dispatch = `chain2_canonicalTrim_step` (inner `=0`) vs this
   reduce (inner `>0`), and Phases 3–4 mirror `buildReducer`/`witness_via_sdr` over `chain2Order_wf`.

Effort: (1) moderate (a canonical-degree function + WF re-derivation), (2) the heavy analysis piece, (3)
moderate once (1)+(2) land. Path B keeps single-exp untouched throughout.
