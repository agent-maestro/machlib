# Changelog

All notable changes to MachLib are recorded here. Format roughly follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). Versions are
release-snapshot identifiers; see the release manifests for the authoritative
per-release status.

## [Unreleased] — 2026-07-09

### New — absolute, cancellation-tolerant forward-error fold (`MachLib/AbsoluteError.lean`)

The certifier's `ForwardError.Renc` is a *relative* enclosure: it composes only on a cancellation-FREE
tree of non-negative quantities (`cosh`, `x²+y²`). General EML arithmetic cancels (`a − b` with `a ≈ b`),
where the relative bound is vacuous. This adds the honest general answer — the **absolute** running-error
bound (Higham, *Accuracy and Stability*, §3.4): **`MachLib.Real.AbsEnc E fl e := |fl − e| ≤ E`**, with
`sorryAx`-free node lemmas `absenc_exact` / `absenc_round` (leaves) and `absenc_add` / `absenc_sub` /
`absenc_mul` (arithmetic). The **`sub` node carries the SAME bound as `add`** — cancellation destroys
*relative* accuracy, never the *absolute* bound, which is exactly what makes this fold general.

Capstone **`absenc_sub_rounded`** reproduces the *exact* `u·(2+u)·(|xe|+|ye|)` bound that
`CompositeRuntimeError.eml_fwd_reduces_to_primitives` proves by hand for `eml = exp x − log y`, now a
two-line instance of the general `absenc_sub` fold (one ring identity). The bespoke composite-error proof
is thereby subsumed by a reusable per-node accumulation. `MachLib.Real`-only, no Mathlib.

**Wired through the emitted C (`MachLib/AbsoluteBridge.lean`).** `FloatRealBridge`'s `pipeline_*`
connected T1's emitted C to T3's *relative* forward error, but only for cancellation-free trees. The
absolute fold now closes that gap on the canonical CANCELLING kernel — the 2×2 determinant / cross-product
`x·y − z·w` (`detEML`). **`pipeline_det`**: the value the *emitted C* computes (`evalC ∘ emitC`), through
`toR`, is within `u·(2+u)·(|X·Y|+|Z·W|)` of the exact `X·Y − Z·W` — the same EML→emitC→evalC→toR span as
the relative pipeline, now VALID UNDER CANCELLATION (`X·Y ≈ Z·W`, where `Renc` is vacuous) and with NO
sign hypothesis on the inputs. `sorryAx`-free; assembled from two `br.mul` roundings + one `br.sub` via
`absenc_sub_rounded` + `emitC_correct`.

### Hardened — the unsound open `rolle` axiom is RETIRED; the library has no Rolle but the sound `rolle_ct` (`MachLib/Rolle.lean`)

Grounding MachLib.Real against Mathlib's ℝ surfaced that the old `rolle` axiom was **unsound as stated**: it
asked only for OPEN-interval differentiability (`a < c → c < b`) with **no** endpoint continuity, so it is not a
theorem of ℝ — counterexample `f x = x` on `(0,1)` with `f 0 = f 1 = 0` (differentiable on the open interval,
`f 0 = f 1`, yet `f' ≡ 1 ≠ 0`). This release completes the repair begun with `rolle_ct` (the sound
closed-interval form, witnessed verbatim against Mathlib ℝ by `MonogateEML.RealModel.rolle_witnessed`):

* **Every** consumer migrated to `rolle_ct` / `mean_value_theorem_ct`: the whole Khovanskii footprint
  (pure-exp explicit + unconditional bounds, the mixed exp/log barrier, the `…_le_47` and
  `eml_barrier_bounded_zeros` showcases) plus every utility (Sturm non-oscillation, Wronskian proportional,
  trig / hyperbolic Lipschitz — all differentiate entire functions or on strict subintervals, so closed diff
  is always available).
* The unsound `axiom rolle` **and** the open-hypothesis `theorem mean_value_theorem` (itself proved from
  `rolle`, hence unsound-as-stated) are **DELETED**. `rolle_ct` is now the library's only Rolle. Any future use
  of an open-interval Rolle is a compile error — it no longer exists.
* **Regression gate:** `tools/claim_audit/claim_audit.py` gains `forbid_axioms_exact` (whole-token axiom
  matching — a plain substring forbid can't tell `MachLib.Real.rolle` from the sound `MachLib.Real.rolle_ct`);
  the 8 Khovanskii flagship claims now forbid `MachLib.Real.rolle` exactly. `#print axioms` on all flagships:
  `rolle_ct` only, no bare `rolle`, no `sorryAx`. Claim-audit PASS (16/16), self-test PASS.

### Concrete showcase — `e^(e^x) − x·e^x` has at most 47 real zeros, machine-checked (`MachLib/KhovanskiiConcrete.lean`)

**`MachLib.KhovanskiiConcrete.eexp_barrier_zero_count_le_47`** — a named instance of the explicit Khovanskii
bound. The barrier `y₁ − x·y₀` is, along the depth-2 tower (`y₀ = eˣ`, `y₁ = e^(eˣ)`), exactly
`e^(e^x) − x·e^x`; it is a degree-1 chain-2 polynomial, so its zero count on any interval where it is
somewhere nonzero is `≤ Ndep 0 1`, and `Ndep 0 1` **computes to 47** (`Ndep` is a genuine kernel-reducible
`Nat` recurrence — the `= 47` is discharged by `decide`, not `native_decide`, so no `ofReduceBool` enters the
footprint). Non-vanishing is witnessed at `x = 0`, where the value is `e^(e^0) = e > 0` (`iterExp_pos`). This
turns the "at most 47 real zeros" figure from a hand-evaluated recurrence into a theorem, resting on `rolle`
alone — no `sorryAx`, no `zero_count_bound_classical`, and (being a pure-exp barrier) no analyticity, log, or
reciprocal.

The same file also exercises the **mixed** capstone on a genuinely exp+log function.
**`MachLib.KhovanskiiConcrete.eml_barrier_bounded_zeros`**: `e^x − log x` (the fundamental `eml` operation
applied to `x`) has finitely many zeros on any interval in the positive reals containing `1`, a machine-checked
instance of `eml_eval_boundedZeros_unconditional`. This one is qualitative (a finite ceiling exists) and carries
the honest *mixed* footprint — `rolle` plus the real-analyticity identity theorem
(`analytic_finite_zeros_compact`) and the logarithm — but is still `sorryAx`- and
`zero_count_bound_classical`-free. Together the two showcases pin the honest distinction concretely: the
pure-exp bound is Rolle-only with a literal ceiling; the mixed bound adds the identity theorem and gives
finiteness without an explicit constant.

### exp arm CLOSED — the full mixed exp/log/reciprocal EML barrier bound is unconditional (`MachLib/PfaffianExpHard.lean`)

**`MachLib.eml_eval_boundedZeros_unconditional`** — the Khovanskii-type finiteness bound for arbitrary-depth
**mixed** exp/log/reciprocal EML barriers, machine-checked. Both classical arms are discharged: the exp arm
(`exp_hard`) via the new `expEliminate` construction (B1–B4 in `PfaffianExpEliminate` / `PfaffianExpTrim` /
`PfaffianExpWronskian` / `PfaffianExpHard`), the log arm via `log_hard_proof`. `#print axioms` →
`propext` / `Classical.choice` / `Quot.sound`, the `Real` interface, `rolle`, plus the real-analyticity
package (`analytic_finite_zeros_compact` and the identity-theorem family) and the logarithm / reciprocal
derivative rules — with **no `sorryAx` and no `zero_count_bound_classical`**.

Honest scoping, held to on the public page too: the mixed bound is *qualitative* (a finite ceiling exists,
without an explicit constant), and its analytic footprint is genuinely **larger than Rolle** — the degenerate
"proportional" leaves are retired by the identity theorem (a real-analytic function has finitely many zeros
on a compact interval unless it vanishes identically). Rolle carries the descent; analyticity enters only for
those leaves.

By contrast the pure iterated-exponential bound stays Rolle-only, and is now *effective*.
**`MachLib.IterExpDepthN.chainN_khovanskii_bound_explicit`** gives the explicit ceiling `Ndep m D`; its
`#print axioms` footprint has **no analyticity, no logarithm, no reciprocal** — `rolle` is the sole analytic
input. `Ndep` is now a genuinely computable, `#eval`-able closed-form recurrence (a gratuitous
`noncomputable` on `budgetMax` was removed), though its values are a height-`m` tower of exponentials, so
evaluating beyond a small depth overflows the interpreter.

Both claims are pinned in `tools/claim_audit/claims.json` so the distinction (pure-exp = Rolle-only; mixed =
Rolle + identity theorem, still `sorryAx`- and `zero_count_bound_classical`-free) is a standing CI gate.

### Hardened — analytic base collapses to a single axiom: `zero_count_bound_by_deriv` is now a THEOREM (`MachLib/Rolle.lean`)

**`MachLib.Real.zero_count_bound_by_deriv`** — previously an `axiom`, now **derived from `rolle`**. The whole
iterated-exponential tower's analytic foundation therefore bottoms out at the SINGLE axiom `rolle` (plus the
field/order interface); the separate zero-count axiom is gone. `#print axioms zero_count_bound_by_deriv` →
`propext`, `Classical.choice`, `Quot.sound`, `rolle`, and the `Real` order / `HasDerivAt` primitives — **NO
`sorryAx`, NO `zero_count_bound_classical`, NO `analytic_finite_zeros`**.

Construction (all supporting defs `private` to `Rolle.lean`): sort the `Nodup` zeros of `f` into strictly
increasing order via `List.mergeSort` with a classical `≤`-comparator (`leB`), then `interleave_from` applies
`rolle` between each consecutive pair to produce a zero of `f'` strictly between them. Those bracket points are
themselves strictly increasing (each lands in a disjoint sub-interval, enforced by the `> hd` recursion
invariant), hence `Nodup` and of length `zeros_f.length − 1`; feeding that list to `hf'_bound` gives
`zeros_f.length ≤ N + 1`. Uses Lean 4.14 core `List.mergeSort` / `List.Perm` / `List.Pairwise` (no Mathlib).
All 138 modules rebuild; every downstream consumer (`KhovanskiiReduction`, `SingleExpKhovanskii`,
`InnerKhovanskii`, `PolynomialRootCount`, …) picks up the theorem by name — signature unchanged.

### Added — Khovanskii ∀N: **ARC CLOSED** — the UNCONDITIONAL arbitrary-depth bound (`MachLib/IterExpDepthNBoundUncond.lean`)

**`MachLib.IterExpDepthN.chainN_khovanskii_bound_unconditional`** — for **every** depth and every chain-`N`
polynomial not identically zero on `(a,b)`, `chainNFn p` has finitely many zeros. NO hypothesis. `#print axioms`
→ `propext`, `Classical.choice`, `Quot.sound` + the honest `MachLib.Real` analytic interface (`rolle`, `exp`,
`HasDerivAt` calculus): **NO `sorryAx`, NO `zero_count_bound_classical`, NO `analytic_finite_zeros`** — the
forbidden-axiom grep is empty. (As of the hardening entry above, `zero_count_bound_by_deriv` is itself a
theorem derived from `rolle`, so it no longer appears in this footprint — `rolle` is now the sole analytic axiom.)

The reduce arm's `Reducing` precondition — previously the explicit hypothesis `hRD` of
`chainN_khovanskii_bound_of_reducing` — is now a **theorem**, `establish_hnz_or_trim` (for any `q ≢ 0`, either
`hnzTower m q` (the deepest true-degree is nonzero, so the absorbed reduce descent `chainNReduce_descends_hnz`
fires) OR an eval-equal `synMeasure`-smaller phantom-trim). The assembly runs on the augmented measure `M5⁺`
(`chainNMeasure5p` = `(chainNMeasureCanon, synMeasure(inner))`), since the eval-invariant `chainNMeasureCanon`
cannot be lowered by an eval-preserving trim — the deep phantom-trim (`liftInner`) ties it and drops `synMeasure`.
Double-, triple-, and arbitrary-depth: all unconditional, all clean.

### Added — Khovanskii ∀N: PHASE C CLOSED — the reduce-descent for every depth (`MachLib/IterExpDepthNDescentInduction.lean`)

**`chainNReduce_descends`** — for a reducing `q : MultiPoly (k+2)` at ANY depth `k`, the reduce with the
full graded multiplier strictly lowers the eval-invariant measure `chainNMeasureEI k` in `nestedOrder (k+2)`.
This is the ∀N analog of the deep depth-2 `chain2MeasureCanonEvalInv_descends`, now proven for **every depth**
by induction. `#print axioms` → `propext`, `Classical.choice`, `Quot.sound` + the honest `MachLib.Real`
interface (incl. `rolle`): **NO `sorryAx`, NO `zero_count_bound_classical`, NO `analytic_finite_zeros`**.

The induction, assembled from the whole Phase C stack:
- **`fullMult k q`** — the recursive graded multiplier: depth-2 base at `k=0`; at `k+1`, `gradedTop` +
  `liftLastY` of the lower multiplier for the projected leading coefficient (`dropLastY_liftLastY` recovers
  it — the multiplier-threading resolved).
- **`Reducing k q`** — the recursive reducing predicate (depth-2 conditions at `k=0`; non-phantom + positive
  top degree + `Reducing` of the projected leading coefficient at `k+1`).
- Base = `chainNReduce_evalinv_descent_base` (the transported depth-2 descent, via `chainNReduce 0 =
  chain2Reduce` + `chainNMeasureEI 0 = chain2MeasureCanonEvalInv`); step = the D-step
  `chainNReduce_evalinv_descent` fed the IH through `dropLastY_liftLastY`.

The ∀N reduce-descent — the tower's well-founded step — is complete. Remaining for the full ∀N Khovanskii
bound: Phase D (generalise Rolle/vehicle + the outer WF induction into `chainN_khovanskii_bound_unconditional`).

### Added — `liftLastY`, a right inverse of `dropLastY` (`MachLib/MultiPolyLiftLastY.lean`)

The ∀N descent's D(k)-by-induction wiring needs to thread the graded multiplier down the recursion: the
D-step's inner reduce carries multiplier `dropLastY m_rest`, and for the inductive `D(M)` (a *graded* reduce)
to match, `m_rest` must be the lifted lower multiplier. That requires a `dropLastY` right inverse, which did
not exist — this supplies it.

- **`liftLastY : MultiPoly n → MultiPoly (n+1)`** — embed as a polynomial free of the new top variable
  (structural: `y_i ↦ y_i` at a lower `Fin (n+1)` index; `const`/`varX` kept).
- **`dropLastY_liftLastY`** (`dropLastY (liftLastY x) = x`) and **`degreeY_top_liftLastY`** (`liftLastY x` is
  top-free). Pure structural induction; `#print axioms` clean.

Next: the recursive full graded multiplier (`fullMult`), the recursive reducing predicate, the base
reconciliation (`chainNReduce 0 (gradedTop 0 + const c) p = chain2Reduce c p`, holds since `Ffac 0 = y₀`),
and the `D(k)`-by-induction — then Phase D.

### Added — Khovanskii ∀N Phase C (brick 3b, steps 2a+2b): the S(k) and D(k) descent assembly (`IterExpDepthNDescent.lean`, `IterExpDepthNDescentD.lean`)

The mechanical core of the reduce-descent, both steps, given the inner descent:

- **`chainNReduce_syntactic_descent`** (S(k)) — the *syntactic* measure `(degreeY_top, chainNMeasureEI M of
  dropLastY(leadingCoeffY_top ·))` strictly drops under the depth-`(M+3)` graded reduce, given `hInner`
  (the depth-`(M+2)` reduce lowers the inner measure). Top degree preserved (`chainNReduce_fst_preserved`),
  inner drops via the transport + `hInner`, via `nestedOrder_of_snd`.
- **`chainNReduce_evalinv_descent`** (D(k)) — the *eval-invariant* measure `chainNMeasureEI (M+1)` strictly
  drops, via the phantom / non-phantom split: non-phantom ⇒ both measures = syntactic (brick 2) ⇒ S(k);
  phantom ⇒ `cdegYAt` of the reduce drops below `degreeY_top p` (brick 1) ⇒ first-component descent. The
  literal top index is confined to two `rw [Fin.ext hi]` wrappers; the main proof runs at the abstract index.

Both compile clean (`#print axioms` free of `sorryAx` / classical-citation). This is the ∀N analog of
`chain2MeasureCanonEvalInv_descends`, parameterized on `hInner`. What remains of Phase C: wire the
`D(k)`-by-induction (base `D(0)` = `chain2MeasureCanonEvalInv_descends`; step feeds `D(k)` as `hInner` to
`chainNReduce_evalinv_descent`) — the remaining subtlety is threading the *graded multiplier* + reducing
hypotheses through the recursion so the inductive `D(k)` matches `hInner`'s inner reduce.

### Added — Khovanskii ∀N Phase C (brick 3b, step 1): the inner-descent transport (`MachLib/IterExpDepthNDescent.lean`)

**`chainNMeasureEI_reduce_inner_eq`** — the eval-invariant measure of the depth-`(M+3)` graded reduce's
dropped top coefficient equals the measure of the depth-`(M+2)` reduce of `dropLastY (lcY_top p)`. Immediate
from brick 3a (full-env recursion) + Phase B (`chainNMeasureEI_eq_of_eval_eq`). This is the exact bridge the
syntactic descent `S(k)`'s inner step needs — with it, `S(k)`'s inner descent is `rw [this]; exact D(k−1)`.
Compiled first try; `#print axioms` clean. Remaining Phase C: the `S(k)/D(k)` induction proper (the fst-preserved
outer + this transport + the phantom split + the reducing-hypothesis threading).

### Added — Khovanskii ∀N Phase C (brick 3a): the recursion brick, FULL-ENV (`MachLib/IterExpDepthNRecursionFull.lean`)

`chainNReduce_dropLastY_recursion` closes the depth-`(M+3)`→`(M+2)` recursion **only on the chain values**;
the measure descent needs it on **every** environment (the eval-invariant measure's eval-invariance
quantifies over all envs — exactly why depth-3 needed the separate `chain3Reduce_dropLastY_lcY2_eval_eq_full`).

- **`chainNReduce_dropLastY_recursion_full`** — the ∀N, full-env version: the depth-`(M+3)` graded reduce's
  dropped top coefficient, at *any* environment, equals a depth-`(M+2)` reduce of `dropLastY (lcY_top p)`
  with multiplier `dropLastY m_rest`. Re-derived by replacing the chain-values `dropLastY_eval_IterExp'` with
  the framework `MultiPoly.eval_dropLastY` (env-restriction bridge `extEnv`/`dropLastY_eval_full'`) +
  `dropLastY_cTD_commute`, keeping the abstract-index discipline (top index a variable `i`, `hi : i.val =
  M+2`; `[local irreducible]` on the stuck recursors). Compiled first try. `#print axioms` clean.
- This closes the sub-gap that stood between Phase B and the descent: the descent's inner step
  (`chainNMeasureEI k (dropLastY lcY_top(reduce)) = chainNMeasureEI k (reduce_{k+2} of dropLastY lcY_top)`)
  now has its full-env eval-equality. Remaining Phase C: brick 3b, the S(k)/D(k) mutual induction assembling
  3a + the phantom bridge + `chainNReduce_fst_preserved` + D(k−1).

### Added — Khovanskii ∀N Phase C (brick 2): eval-invariant measure = syntactic on non-phantom (`MachLib/IterExpDepthNMeasureSyn.lean`)

**`chainNMeasureEI_eq_syntactic_of_nonphantom`** — for `q : MultiPoly (j+3)` whose top `y`-coefficient is
non-phantom, the eval-invariant measure `chainNMeasureEI (j+1) q` equals the *syntactic* form `(degreeY_top q,
chainNMeasureEI j (dropLastY (leadingCoeffY_top q)))`. Depth-generic analog of the depth-2
`chain2MeasureCanonEvalInv_eq_chain2MeasureCanon_of_nonphantom`; assembled from Phase C brick 1
(`cdegYAt_eq_degreeYAt_of_top`, `canonLcYAt_eval_eq_leadingCoeffY_of_nonphantom`) + Phase B
(`chainNMeasureEI_eq_of_eval_eq`, `dropLastY_eval_eq_of_topfree`). This is the swap that lets the
eval-invariant descent `D(k)` fall through to the syntactic descent `S(k)` on the non-phantom branch.
Compiled first try; `#print axioms` clean. Remaining Phase C: the `S(k)/D(k)` induction (S(k) assembles the
reduce machinery around the recursion brick + D(k−1); D(k) from S(k) + the phantom drop).

### Added — Khovanskii ∀N Phase C (brick 1): the phantom / non-phantom bridge (`MachLib/IterExpDepthNCanonBridge.lean`)

The base descent `chain2MeasureCanonEvalInv_descends` works by a **phantom / non-phantom split**: when the
top `y_i`-coefficient is *non-phantom* the canonical measure equals the syntactic one (deep syntactic
descent applies); when *phantom* the canonical degree `cdegYAt` strictly drops (first-component descent
outright). This is the key that turns the canonical-outer descent D(k) into a well-defined induction. This
brick supplies both directions of the split, index/depth-generic (the depth-2 originals were `MultiPoly 2`,
index `⟨1⟩`):

- **`ytopAt i q`** — the syntactic top `y_i`-coefficient (`getLast` of `yCoeffsAt`).
- **`cdegYAt_eq_degreeYAt_of_top` / `canonLcYAt_eq_ytop`** — non-phantom ⇒ canonical = syntactic.
- **`cdegYAt_lt_degreeYAt_of_top`** — phantom (+ positive syntactic degree) ⇒ `cdegYAt` strictly drops.
- **`canonLcYAt_eval_eq_leadingCoeffY_of_nonphantom`** — non-phantom ⇒ canonical leading coeff eval-equals
  syntactic `leadingCoeffY` (what the measure-equality consumes next).
- `#print axioms` clean (no `sorryAx`, no classical-citation). Next: the syntactic top-level measure
  `chainNMeasureSyn` + `chainNMeasureEI = chainNMeasureSyn` on the non-phantom branch, then the S(k)/D(k)
  mutual induction (S(k) from the recursion brick + D(k−1); D(k) from S(k) + the phantom drop).

### Added — Khovanskii ∀N Phase B: the uniform eval-invariant measure by recursion on depth (`MachLib/IterExpDepthNMeasureEI.lean`)

The depth-3 descent used the fully eval-invariant depth-2 measure (`chain2MeasureCanonEvalInv`) as its
inner nested component. The tower needs that inner measure at every depth, uniformly — this builds it.

- **`chainNMeasureEI k : MultiPoly (k+2) → NestedNat (k+2)`** — the depth-`(k+2)` eval-invariant canonical
  measure. Base `k=0` is *literally* `chain2MeasureCanonEvalInv` (so every induction bottoms out in the
  existing, already-proven depth-2 machinery — nothing to reconcile); step `k+1` pairs the canonical
  top-degree `cdegYAt` (Phase A) with the measure of the canonical leading coefficient projected one
  variable down via `dropLastY`.
- **`chainNMeasureEI_eq_of_eval_eq`** — the measure is **eval-invariant at every depth**, by induction:
  base `chain2MeasureCanonEvalInv_eq_of_eval_eq`; step combines Phase A's `cdegYAt_eq_of_eval_eq` (outer),
  `canonLcYAt_eval_eq_of_eval_eq` + the new `dropLastY_eval_eq_of_topfree` (the projected coefficient stays
  eval-equal), and the inductive hypothesis (inner).
- `#print axioms` → `propext`, `Classical.choice`, `Quot.sound` + honest `MachLib.Real`; **no `sorryAx`**.
- **Next (Phase C, the hard frontier)**: the reduce-descent — that this measure strictly decreases under
  the graded reduce. The algebraic engine is already ∀N (`chainNReduce_dropLastY_recursion`) and the
  eval-invariance just landed transports it; the genuinely-uncertain step is the canonical-outer descent
  `D(k)→D(k+1)`, which generalizes depth-3's reduce/trim/inner-trim case analysis.

### Added — Khovanskii ∀N Phase A: the index-generic canonical `y`-degree + eval-invariance (`MachLib/IterExpDepthNCanonDegree.lean`)

The measure the ∀N descent will use is *eval-invariant* — it forgets phantom leading `y`-terms that only
cancel semantically. Depth-2/3 built that per index (`cdegY0` at `⟨0⟩`, `cdegY1` at `⟨1⟩`, both in
`MultiPoly 2`); the tower needs it at the **top index of any depth**, uniformly. This brick supplies it.

- **`canonZeroB c`** — the one index-specific ingredient (the coefficient canon-zero test) made generic
  by a single **classical** definition: `decide (c vanishes everywhere)`. This makes canon-zero congruent
  under eval-equality by construction, so eval-invariance is nearly free. Every list-level helper reused
  (`rdw_cons`, `dropWhile_all`, `rdw_zero_of_all`, `listSubN`, `yCoeffsAt_entry_eval_zero_of_eval_zero`,
  `eval_eq_of_env_agree_off`) was already index-generic.
- **`cdegYAt i q`** (canonical `y_i`-degree) + **`cdegYAt_eq_of_eval_eq`** — degree eval-invariance ∀
  index, ∀ depth. Generic analog of `cdegY1_eq_of_eval_eq`.
- **`canonLcYAt i q`** (canonical leading `y_i`-coefficient) + **`canonLcYAt_eval_eq_of_eval_eq`** — the
  leading coefficient is eval-invariant at EVERY point (the classical test gives everywhere-agreement
  directly, so — unlike the structural depth-2 `canonLcY1` proof — no `env0` restriction is needed).
- `#print axioms` → `propext`, `Classical.choice`, `Quot.sound` + the honest `MachLib.Real` interface;
  **no `sorryAx`**, no classical-citation axiom. Phase B (the uniform eval-invariant measure by recursion
  on depth) plugs `cdegYAt`/`canonLcYAt` in at the top index and recurses via `dropLastY`.

### Added — Khovanskii ∀N: the depth-generic well-founded measure backbone (`MachLib/IterExpDepthNMeasure.lean`)

Next brick of the depth-N tower, on the critical path to the WF capstone. The depth-2/3 capstones each
cite a hand-built well-foundedness keystone for their arity (`natTripleLex_wf`, `natQuadLex_wf`); the ∀N
induction needs that family *uniformly*. This supplies it:

- **`MachLib.IterExpDepthN.NestedNat n`** — the depth-`(n+2)` measure codomain (`(n+1)`-deep nested `Nat`
  product); **`nestedOrder n`** — its nested lexicographic order (definitionally `nestedOrder 2` is the
  depth-2 `nestedLT`); **`nestedOrder_wf n`** — **well-founded for every `n`** by induction on depth
  (base `Nat.lt`, step `lexProd_wf`). `natPairLex/​natTripleLex/​natQuadLex_wf` are its `n = 1,2,3` slices.
- **`nestedOrder_of_fst` / `nestedOrder_of_snd`** — the two generic descent-lifting lemmas the capstone's
  arms need (drop the top component / tie it and drop the tail).
- `#print axioms` → **depends on NO axioms** (pure order theory; not even `propext`). This is the
  well-founded skeleton the ∀N reduce-descent will hang on. The algebraic heart of that descent — "the
  dropped top coefficient of the reduce IS a depth-(N−1) reduce" — is already machine-checked ∀N
  (`chainNReduce_dropLastY_recursion`). Still ahead: the uniform *eval-invariant* measure and its descent
  by induction on depth (base = chain2), then the ∀N Rolle/vehicle step and the capstone assembly.

### Added — verified day-count & accrual: coupon periods compose exactly (`MachLib/FinanceDayCount.lean`)

The second finance kernel — the lane is not a one-off. Same discipline as amortization, aimed at the
property a bond desk and an auditor argue about: **splitting a coupon period at an intermediate date must
preserve accrued interest.** Uses the **30E/360 (Eurobond)** convention, where every date `(y,m,d)` has a
single serial `360·y + 30·m + min(d,30)` and the day-count is the serial difference.

- **`MachLib.Finance.days30E360_additive`** — the headline: `days(A,B) + days(B,C) = days(A,C)` for ANY
  intermediate date. The day-count analogue of amortization's telescoping reconciliation — interest can't
  be manufactured by moving the accrual boundary. **Honest domain point**: this holds for 30E/360 because
  each date has one serial; the US 30/360 "bond basis" is *not* additive (its end-of-month rule depends on
  the other endpoint), so picking 30E/360 is a deliberate correctness decision.
- **`MachLib.Finance.accrual_additive`** — the money corollary: accrued interest (`notional·rateNum·days`)
  composes exactly across a split, because it is linear in an additive day-count.
- **`MachLib.Finance.days30E360_months`** — regularity: same day-of-month, `m` whole months apart ⇒ exactly
  `30·m` days. Equal calendar spacing ⇒ equal day-count ⇒ equal accrual (fair level coupons).
- **`MachLib.Finance.days30E360_full_year`** (`= 360`) and **`days30E360_nonneg`** (forward periods aren't
  negative).
- `#print axioms` (all five) → `propext`, `Quot.sound` ONLY — pure `Int`, not even `Classical.choice`
  (same minimal footprint as `amortization_reconciles`; calendars and money are exact integer objects, no
  float). Registered in `tools/claim_audit`. Runtime witness: `forge/reproduce/sims/daycount_sim.py`.

### Added — verified amortization (the finance-assurance lane opens) (`MachLib/FinanceAmortization.lean`)

- **`MachLib.Finance.amortization_reconciles`** — a fixed-rate amortization schedule in **integer
  cents** reconciles to the penny **exactly**: with per-period principal `b k − b (k+1)`, starting at
  the loan `P` and closing at `b N = 0`, the principal payments sum to exactly `P`. Exact (`=`, not
  `≤ ε`) and **rounding-mode-independent** (the final payment absorbs the accumulated rounding — how
  real schedules are built). `#print axioms` → `propext`, `Quot.sound` only (pure Int; not even the
  axiomatized-Real base — money is decimal fixed-point, and this proof never touches a float).
- **`MachLib.Finance.roundHalfEven_half_ulp`** — round-half-to-even (banker's rounding) is correct to
  within half a cent per period: `−den ≤ 2·(den·round − num) ≤ den`. `#print axioms` → Lean's three
  only, no `sorryAx`.
- **Why this lane**: the finance-translatable core of the project is the fixed-point/decimal-rounding
  + contraction infrastructure (FPModel / FixedPointCertifier / ClosedLoopSafety) — *not* the
  Khovanskii frontier, which is pure symbolic math with no dollar attached. This is the first brick
  pointing that infrastructure at money: the runtime schedule (`forge/reproduce/sims/amortization_sim.py`),
  certified.

### Added — the accumulated rounding error stays inside a certified envelope (`MachLib/FinanceEnvelope.lean`)

Deepens the amortization kernel from *reconciles* + *½¢-per-period* to a **global** bound: how far the
rounded balance trajectory can drift from the exact-arithmetic one over the whole loan. The drift obeys
`e_{k+1} = g·e_k + ρ_k`, `e_0 = 0`, `|ρ_k| ≤ c` (`g = 1+r`, `c = ½` cent) — a linear recurrence with
bounded input.

- **`MachLib.Real.error_within_envelope`** — the abstract core, the **expansion dual** of
  `MachLib.Real.safe_envelope_invariant`: for `g ≥ 1`, `|e_k| ≤ errEnvelope g c k` for all `k`. The
  safety envelope is a *contraction* (`g<1`) settling into a fixed box `X=δ/(1−ρ)`; this is the *growth*
  regime (`g>1`) where the compounded error still lives inside a growing, explicit envelope
  `cap_k = c·(gᵏ−1)/(g−1)`. Same proof shape (triangle + `mul_le_mul_of_nonneg_left` + `add_le_add_both`
  under induction).
- **`MachLib.Real.errEnvelope_eq_geomSum` / `geomSum_closed`** — `cap_N = c·Σ_{j<N} gʲ` and
  `(g−1)·Σ_{j<N} gʲ = gᴺ−1`, i.e. the recognizable `c·(gᴺ−1)/(g−1)`, both proven **without division**.
- **`MachLib.Real.amortization_drift_within_envelope`** — the punchline: the rounded schedule `b`
  (`b_{k+1}=g·b_k−pmt+ρ_k`) never leaves `cap_k` around the exact schedule `B` (`B_{k+1}=g·B_k−pmt`),
  for ANY per-period rounding `|ρ_k| ≤ c`. With `c=½` cent this bounds how far per-period interest
  rounding can push the balance off the exact-arithmetic path — connecting the local ½¢ fact to a global
  guarantee. For the zoo's `$250k @ 6% / 360mo` loan the certified **worst-case** `cap_N ≈ $5.02` (every
  rounding adverse and fully compounding); the **measured** drift is only `~$0.05`, because real
  per-period roundings mostly cancel — the rounded trajectory sits well inside the envelope, exactly as
  the safety envelope's margin works. (That worst-case cap is a separate quantity from the ~$3.66
  final-payment adjustment, which is dominated by rounding the level payment, not the per-period interest.)
- `#print axioms` (all four) → `propext`, `Classical.choice`, `Quot.sound` + the honest `MachLib.Real`
  interface ONLY: **no `sorryAx`**, no classical-citation math axiom — same footprint class as the
  safety envelope. **Mechanization note**: `mach_mpoly` reifies its bracket atoms in the *outer*
  elaboration context, so it cannot see an `induction`-introduced local (`geomSum g n`); each ring
  identity is therefore proven once as a top-level lemma over plain variables and `exact`-ed at the use
  site. (`mach_ring` avoided per its known silent-`sorry` failure mode.)

## [Unreleased] — 2026-07-01

### Added — Frontier-1 lemma (1) proven for EVERY depth `N` (`33a819a`)

- **`MachLib.IterExpDepthN.leadingCoeffYtop_cTD_eval_IterExpN`** — the
  top-`leadingCoeffY`-under-`chainTotalDeriv` product-injection identity, now
  proven for **every** depth `N = M+2` (not just the closed depths 2 and 3):
  `eval(lcY_top(cTD p)) = eval(cTD(lcY_top p)) + (degreeY_top p)·eval(Ffac M · lcY_top p)`,
  top `⟨M+1⟩`, injection factor `Ffac M = y₀·…·y_M`. This is the first genuinely
  general-`N` brick of the depth-N tower and the step the frontier notes called
  "the one genuinely uncertain algebraic step". `#print axioms` → `propext` +
  `Quot.sound` + the honest `MachLib.Real` interface ONLY: **NO `sorryAx`, NO
  `zero_count_bound_classical`, NO `analytic_finite_zeros`** — and not even
  `Classical.choice` (the identity is purely algebraic). Verified by `tools/claim_audit`.
- **Why it was blocked, and the actual fix** (`MachLib/IterExpDepthNTopIdentity.lean`):
  the earlier `∀M` attempt diverged; the cause was **not** `whnf` of `prodVarYUpTo M`
  (marking the factor `irreducible` does not help) but `rw`'s `kabstract` re-`whnf`ing
  the *stuck* `leadingCoeffY`/`degreeY` recursors at the **literal symbolic index**
  `⟨M+1, by omega⟩`. Fix: keep the top index an **abstract variable** `i` with
  `hi : i.val = M+1`, confining the one unavoidable literal to three one-equation
  wrapper lemmas. Worst step: divergent → 0.5 s; whole file 0.8 s. Reusable for the
  rest of the tower.
- **The reduce operator, `∀N`** (`MachLib/IterExpDepthNReduce.lean`, also clean —
  `propext`/`Quot.sound`/`MachLib.Real.*` only): `chainNReduce M m p = cTD p − m·p`, with
  `chainNReduce_fst_preserved` (preserves the top y-degree) and `chainNReduce_lcY_top_eval`
  (its top leading coefficient, evaluated, `= eval(cTD(lcY_top p)) + degreeY_top p·eval(Ffac M)·
  eval(lcY_top p) − eval(m)·eval(lcY_top p)`) — the depth-N → depth-(N-1) recursion seam, for any
  top-free multiplier `m`, driven by lemma (1). When `m`'s top term is `degreeY_top p·Ffac M` the
  injection cancels, leaving a depth-(N-1) reduce of `lcY_top p`.
- **The graded-multiplier cancellation, `∀N`** (`MachLib/IterExpDepthNGraded.lean`, clean —
  `sorryAx`-free, no classical-citation axiom): `chainNReduce_graded_cancels` — with the top graded
  term `gradedTop = (degreeY_top p)·Ffac M`, lemma (1)'s injection cancels *exactly* and the reduce's
  top coefficient collapses to `eval(cTD(lcY_top p)) − eval(m_rest)·eval(lcY_top p)` — an honest
  reduce of `lcY_top p` by the remainder `m_rest`, for ANY top-free `m_rest`. This is the depth-`N` →
  depth-`(N-1)` step (the recursion's heart), the generic-`N` analog of chain-2's
  `chain2Reduce_lcY1_eval` and depth-3's `chain3Reduce_lcY2_eval`. The specific nested-degree
  `m_rest` plugs in later without redoing the cancellation.
- **The `dropLastY` bridge, `∀N`** (`MachLib/IterExpDepthNBridge.lean`, clean — `sorryAx`-free, no
  classical-citation axiom): the ∀M analog of `IterExpDepth3Bridge`, so the depth-`(M+2)` reduce's
  dropped top coefficient can be read as a depth-`(M+1)` object and fed to the induction hypothesis.
  `chainValues_restrict_eq` (the `(M+2)`-chain restricted to `M+1` slots IS the `(M+1)`-chain),
  `dropLastY_eval_IterExp` (top-free `q`: `eval q [IExp(M+2)] = eval (dropLastY q) [IExp(M+1)]`),
  `dropLastY_prodVarYUpTo` (the relation polys `y₀·…·y_{k-1}` match under the drop), and
  `dropLastY_cTD_commute` (top-free `q`: `dropLastY (cTD_{M+2} q) = cTD_{M+1} (dropLastY q)`).
- **The recursion closes, `∀N`** (`MachLib/IterExpDepthNRecursion.lean`, clean — `sorryAx`-free, no
  classical-citation axiom): `chainNReduce_dropLastY_recursion` — the depth-`(M+3)` graded reduce's
  dropped top coefficient, evaluated one chain down, **IS a depth-`(M+2)` reduce** of
  `dropLastY (lcY_top p)`, with multiplier just `dropLastY (m_rest)`. So the recursion is carried by
  `dropLastY`; no separate closed-form nested multiplier is needed. Assembled term-mode from bricks
  3+4 + `degreeYtop_cTD_eq'`. The generic-`N` analog of depth-3's `chain3Reduce_dropLastY_lcY2_eval_eq`,
  and the depth-induction's actual step. **Mechanization note**: the top index MUST be an abstract
  variable (`i` with `hi : i.val = M+2`), not the literal `⟨M+2,…⟩` — the literal makes `whnf` diverge
  on the stuck recursors at a symbolic index (rw / conv / term-mode / irreducible all diverge); two
  one-line wrappers confine the literal. This is the lemma-(1) fix, one level deeper.

### Added — depth-3 (triple-exponential) Khovanskii bound, unconditional and dirty-axiom-free (`ab77c5b`)

- **`MachLib.IterExpDepth3Bound.chain3_khovanskii_bound_unconditional`** — the
  finite-zero bound for the **depth-3 triple-exponential** Pfaffian chain
  (`y₀ = eˣ, y₁ = e^{eˣ}, y₂ = e^{e^{eˣ}}`), **proven, not cited**. For a chain-3
  polynomial nonzero at *some* interior point of `(a,b)`, the number of zeros on
  `(a,b)` is finitely bounded — NO `terminal_nonzero` hypothesis. `#print axioms`
  → only the honest `MachLib.Real` interface (`rolle`, `zero_count_bound_by_deriv`,
  the ring/order/field axioms, `natCast`) plus Lean's `propext`/`Classical.choice`/
  `Quot.sound`: **NO `sorryAx`, NO `zero_count_bound_classical`, NO
  `analytic_finite_zeros`**. Verified by `tools/claim_audit`.
- **How the climb works** (the `IterExpDepth3*` files): `WellFounded.induction` on
  an augmented measure `chain3Order5` (`(chain3MeasureCanon, degreeY₁ q)`), four
  arms — base (`degreeY₂ = 0` → the depth-2 bound above) / `degreeY₂`-trim /
  inner-trim (drop the phantom leading `y₁`-term of `lcY₂ p`; the crux — its own
  `reconstructY`/`leadingCoeffY` toolkit) / reduce (graded multiplier, then the
  integrating-factor vehicle for `reduct ≡ 0` or Rolle `+1`). The depth-2/single-exp
  frameworks are untouched.
- **Meaning + honest scope.** Frontier 1 (the depth-N iterated-exponential tower) is
  closed at **depth 3** — the depth-2 closure provably extends one level up by depth
  induction, entirely from honest Rolle. This does **not** discharge the
  arbitrary-depth axiom: `PfaffianFunction.zero_bound` still cites
  `zero_count_bound_classical` for general depth; only depths 1–3 are counted, not
  quoted.

### Added — depth-2 Khovanskii bound, unconditional and dirty-axiom-free (`dda2a58`)

- **`MachLib.ChainExp2NoZeros.chain2_khovanskii_bound_unconditional`** — the
  finite-zero bound for the **depth-2 double-exponential** Pfaffian chain
  (`x, eˣ, e^{eˣ}`), **proven, not cited**. For a chain-2 polynomial nonzero at
  *some* interior point of `(a,b)`, the number of zeros on `(a,b)` is finitely
  bounded. `#print axioms` → `propext, Classical.choice, Quot.sound`, the `Real`
  base, and the honest Rolle corollary `zero_count_bound_by_deriv`; **no
  `zero_count_bound_classical`, no `sorryAx`**. This is the first depth beyond the
  single-exponential case where the reducibility witness is *constructed* rather than
  supplied/assumed.
- **How the witness is built** (the `ChainExp2*` files): a *chain-aware nested
  descent measure* (`chain2MeasureCanon`, canonical y₀-degree so the reduce cannot
  inflate it), a *polynomial-multiplier Rolle transfer*
  (`zero_count_polyMultReduce_transfer`, the reduce `P' − ((degreeY₁ P)·y₀ + c)·P`),
  and — for the terminal `reduct ≡ 0` case that pure exponentials hit — an
  *integrating-factor vehicle argument*: `V = f·exp(−(d·eˣ+c·x))` has `V' = E·(reduct)`,
  so `reduct ≡ 0 ⇒ V` constant (MVT) ⇒ `f` nonzero everywhere once nonzero at one point.
  The single-exponential framework (`SingleExpKhovanskii`, `KhovanskiiReduction`) is
  untouched.
- **Honest scope.** This does **not** discharge the arbitrary-depth axiom. The legacy
  `zero_count_bound_classical` (Khovanskii 1991) still stands for the general
  `PfaffianFunction` bound; depth-3+ would mirror the depth-2 arc with a deeper nested
  measure. Tier summary now reads: *single-exp proven, depth-2 proven, arbitrary-depth
  cited.* See [`what_is_proven.md` §7](foundations/docs/what_is_proven.md).

## [Unreleased] — 2026-06-26

### Added — `MachLib.FPModel`: verified f64 forward-error (cross-target equivalence, leg 2)

- **`MachLib.FPModel`** — the first proof (not regression test) relating a
  kernel's IEEE-754 `f64` evaluation to its exact `Real` semantics. Adopts the
  standard model of FP arithmetic (Higham §2.2) as three Mathlib-free axioms
  (`u`, `0 ≤ u`, `u ≤ 1`; `u = 2⁻⁵³` for binary64). `length_sq2_fwd_error` and
  `length_sq3_fwd_error` (the `vec3_length_sq` kernel) prove the `f64` result is
  within the tight relative bound `(1+u)ⁿ − 1 ≈ n·u` of the exact value, for
  *every* rounding. `#print axioms` → only `propext` + the `Real` base + the 3
  `u` axioms; no `sorryAx`. EML's straight-line scalar restriction is what makes
  this a closed-form bound rather than a CompCert-scale semantics theorem.
  Full write-up: [`docs/cross_target_equivalence_2026_06_26.md`](foundations/docs/cross_target_equivalence_2026_06_26.md).
- **Conditioned bounds + precision-generic model** (same module): `RoundsW w`
  parameterizes the standard model over the precision's unit roundoff (f64 2⁻⁵³,
  f32 2⁻²⁴, bf16 2⁻⁸) — one theorem, every target, and *no* `u` axiom (rests
  only on `propext` + the `Real` base). `dot2_fwd_error` handles the mixed-sign /
  cancellation-prone case `length_sq` avoids: `|fl(a·b+c·d) − exact| ≤
  ((1+w)²−1)·(|a·b|+|c·d|)` — absolute error against the conditioning quantity,
  the honest statement when the result can cancel to ≈0. Helpers `roundsW_abs`,
  `abs_le_one_add`, `mul_one_add_sub`.

## [Unreleased] — 2026-06-25

### Added — ring-v3, the decompose-first toolkit, and a close-rate harness

- **`MachLib.MPolyRing` (ring-v3)** + the `mach_mpoly` tactic: a nested multivariate
  polynomial normal form. Reify once, normalise once, compare once — polynomial in
  the monomial count, not exponential in the variable count. Closes identities the
  recursive multivariate tactic could not: the 8-variable Euler four-square
  (quaternion-norm) identity goes from *not finishing in 50 minutes* to *seconds*,
  `sorryAx`-free.
- **`MachLib.Decompose`** — four reusable "decompose before nlinarith" lemmas
  (`abs_le_sqrt`, `mul_mem_symm_band`, `lerp_le_of_le`, `quad_denom_pos`) + the
  `mach_decompose` tactic, safe-by-construction (apply/exact + assumption; fails
  cleanly, never silent-`sorry`).
- **`foundations/scripts/closerate.sh`** — a reproducible close-rate harness for the
  Forge `@verify(lean)` corpus. Compiles each emitted obligation independently
  (recursively over all sub-corpora) and counts which `mach_positivity | rfl | sorry`
  cascades genuinely close vs fall through. Current figure: **387 / 581 = 66.6%**
  auto-close, 251 files, 0 build errors (up from 364 / 582 = 62.5%: a 2026-06-26
  refresh brought 16 Discovered obligations up to current `eml-compile`
  emission — the committed copies were stale bare-`sorry` output predating the
  `first | mach_positivity | rfl | sorry` cascade; +23 close, −1 theorem from a
  shadow_pcf re-emit). (The textual `sorry` fallback is in every
  emitted proof, so file-grep is NOT the close-rate — only compilation is.)

Full write-up: [`docs/verification_automation_2026_06_25.md`](docs/verification_automation_2026_06_25.md).

## [Unreleased] — 2026-06-14

### Calibration note — interim audit figures over-counted

In-flight prose around the Khovanskii closure on 2026-06-14 quoted an
audit summary of "210 Forge `@verify` obligations proven-in-place,
80%/19% gap-vs-discharged" and a related sorry count of "269 discovered
sorries (up from 222)". Both figures came from a local working tree
that contained, alongside the publicly-tracked files, ~62 ungated
Discovered/ stubs auto-emitted by the local `auto_prove.py` workflow
(blanket-ignored under `foundations/MachLib/Discovered/.gitignore`),
plus 32 duplicate `.eml` files in a forge `build/` artifact directory.
Neither was visible to a fresh public clone.

The CI-emitted `status.json` (`.github/workflows/status.yml`, lands on
the `status-data` branch on every master push) reports the
public-verifiable figures: 1088 `@verify` obligations total, 36
proven-in-place, 225 placeholder, 823 open, gap_pct 96.3%,
discharged_pct 3.7%, 198 discovered sorries. Those are the numbers a
stranger running `lake build` at the recorded SHA can reproduce.

The 4 strengthened Forge contracts shipped this cycle (Butler-Volmer,
plasma concentration, defibrillator discharge, critically-damped spring)
are publicly tracked and verified, and counted in both the local and
public audits. The over-count was concentrated in `proven_in_place`
(stubs the Forge backend auto-emitted with concrete-enough bodies that
the audit's heuristic classifier didn't flag them).

Follow-up: `forge_verify_audit.py` now defaults to `git ls-files`-aware
file enumeration so a local audit gives the same number as CI. The
`--include-untracked` flag preserves the full local view for callers
who want it. Until the 62 ungated stubs are reviewed and pushed, the
CI figure is the right one to quote.

### Added

- `MachLib.Applications.PlasmaConcentrationNonneg` — pharma kernel
  proof. Bi-exponential IV-bolus central-compartment concentration is
  non-negative under the Forge kernel preconditions. Domain: TCI
  anaesthesia pumps, ICU monitors. Safety class: IEC 62304 Class C, FDA
  510(k). Also closed the `sorry` for `plasma_concentration_nonneg`
  inline in `MachLib/Discovered/pk_two_compartment.lean`.
- `MachLib.Applications.DischargeVoltageSafety` — defibrillator kernel
  proof. Strengthens the Forge `True := by trivial` placeholder for
  `discharge_voltage_decays_exponentially` to sign preservation under
  non-negative initial voltage (no polarity inversion mid-phase). IEC
  62304 Class C. Pointer comment added to the Discovered stub.
- `MachLib.Applications.SpringCriticallyDamped` — game-animation kernel
  proof. Khovanskii-localised positivity of the critically-damped
  harmonic spring `A · (1 + ω·t) · exp(-ω·t)`. ExpPoly length 1, total
  degree 2; the lone zero at `t = -1/ω` is excluded by the animation
  window `t ≥ 0`. Sign-preserving + strictly-positive variants ship;
  the underdamped (cos-bearing) branch remains open pending
  trig-Khovanskii. From `eml-stdlib/gaming/animation/spring.eml`'s
  `spring_critical_signed` obligation.
- `MachLib.SingleExpKhovanskii` — constructive Khovanskii zero bound for
  polynomial-in-(x, eˣ), three resolution paths:
  - `expPoly_khovanskii_bound` (parametric capstone; user supplies an
    `IsKhovanskiiReducibleExp` witness).
  - `expPoly_auto_bound_with_propagation_aux` (strong-induction auto-bound
    over `length + Σ degreeUpper(polySimplify coeffs)`, parametric in a
    propagation hypothesis).
  - `expPoly_ode_no_zeros` (MVT-based ODE corner case: when
    `f' - c·f ≡ 0` on `(a, b)`, `f` is zero-free).
- `MachLib.KhovanskiiReduction` — `khovanskii_bound_full` for general
  triangular Pfaffian chains, parametric in a reduction witness
  (`IsKhovanskiiReducible` with `reduce` + `drop` constructors).
- `MachLib.MultiPolyToPoly` — `MultiPoly 0 → Poly` conversion + the
  chainLength-0 base-case zero bound.
- `MachLib.Applications.ButlerVolmerKhovanskii` — Forge kernel proof for
  the Butler-Volmer electrode-kinetics safety contract: current = 0 iff
  overpotential = 0. Strengthens the `True := by trivial` placeholder
  in `MachLib/Discovered/butler_volmer.lean` (pointer comment added).
  Domain: BMS, fuel cell controllers, corrosion engineering.
- `foundations/AxiomAudit.lean` — reproducible `#print axioms` over the
  headline theorems, run via `lake env lean AxiomAudit.lean`.
- `foundations/KhovanskiiExamples.lean` — three worked applications.

### Foundations note

Results are proven **modulo MachLib's axiomatized analytic base**: a Rolle
zero-counting corollary (`zero_count_bound_by_deriv`), the `HasDerivAt`
rules + `HasDerivAt_unique`, `exp_pos` / `exp_zero`, and `MachLib.Real`
arithmetic / order. In mathlib every one of these is a theorem, not an
axiom — grounding the base in mathlib is open work, not done here.

`zero_count_bound_by_deriv` does the core analytic work; the Khovanskii
layer added in this release is the reduction and the explicit-bound
bookkeeping on top of it. The audit (`AxiomAudit.lean`) makes the
dependency set fully visible.

The release added no assumptions beyond that documented base.

### Notes

- The textbook Khovanskii operator `f' - c·y_n'·f` does not drop degree
  in single-exp chains. The operator that works is `scaledReduction c f :=
  f' - c·f` (see the git history around the `4fe434a` commit for the
  discovery).
- `expPoly_ode_no_zeros` does not invoke `Classical.choice` in its Lean
  dependency closure. This is **not** a constructive-analysis claim — the
  MVT it rests on is classical in spirit and only escapes the dependency
  list because the MVT itself is axiomatized in MachLib.
- 3 `sorry`-warnings exist in 2 non-headline modules (`MachLib.ForgeTest`
  and `MachLib.HighDimensional`, work-in-progress queues unrelated to this
  release). Transitive-import closure of the headline theorems and the
  audit (25 modules) confirms neither is in the dependency chain.

### Verification

- `lake build` of the foundations target is green.
- Headline files have zero `sorry`.
- `lake env lean foundations/AxiomAudit.lean` reproduces the per-theorem
  axiom listing.

### Attribution

Formalization developed by an AI agent (Claude Code) driving MachLib
commits. Coordination on behalf of the Monogate research team.
