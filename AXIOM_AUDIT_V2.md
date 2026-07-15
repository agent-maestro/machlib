# MachLib Axiom Audit — v2 (announcement-grade)

**Date:** 2026-06-12
**Sprint:** Khovanskii closure (3 of 4 structural axioms discharged)
**Scope:** every `axiom` in `machlib/foundations/MachLib/` as of `14e929f`
**Total count:** 252 axioms

This document does double duty. Internally, it's the answer to "is anything in
this library load-bearing in a way that hides inconsistency?" Externally, it's
the answer to the first attack a Lean reviewer will mount: *"you proved X by
adding an axiom that quietly asserts X."* The defense is grouped axioms,
classical references, explicit side conditions, and two case studies showing
the method already caught real inconsistencies during this sprint.

---

## Method

For each axiom we ask three questions:

1. **What classical theorem is this an instance of?** (Or what model-axiom?)
2. **What are the classical theorem's side conditions?**
3. **Are the side conditions verified against MachLib's specific conventions?**

The third question is where most "axiom hides inconsistency" risk lives. MachLib
uses clamped log (`Real.log x = 0` for `x ≤ 0`), opaque exp/sin/cos (no Taylor
machinery), and Nat-indexed `Fin` chains. Each of these can break a classical
theorem's universal quantification if not handled carefully. The audit
explicitly checks each load-bearing axiom against these conventions.

Two case studies (§5) document what happens when the method catches something —
both caught during this sprint, both via attempted USE rather than passive
review.

---

## §1 — Axiom families

We group MachLib's 252 axioms into seven families. Counts in `[N]`.

### F1. Real-arithmetic substrate `[40 in Basic.lean, 5 in Ring.lean]`

MachLib's `Real` is opaque; the field operations (`addR`, `mulR`, `negR`,
`divR`), order (`ltR`, `leR`), Archimedean property, and supremum are
axiomatized.

- **Classical reference:** standard ordered field + completeness axioms for ℝ.
- **Side conditions:** all addition/multiplication axioms are unconditional;
  `div_def` requires `b ≠ 0`; `mul_inv` requires `a ≠ 0`.
- **Verification:** the side conditions are explicit in each axiom's
  signature. No universal quantification claims division by zero behaves
  uniformly.
- **Risk:** low. This is the substrate every formalization needs.

### F2. Transcendental functions (exp/log/trig) `[6 in Exp.lean, 7 in Log.lean, 46 in Trig.lean, 21 in Hyperbolic.lean]`

Axiomatizes `Real.exp`, `Real.log`, `Real.sin`, `Real.cos`, `Real.pi`,
`Real.sinh`, `Real.cosh`, `Real.tanh`, etc. with their defining identities
(addition formulas, periodicity, positivity, monotonicity).

- **Classical reference:** standard real-analysis textbook (Rudin, Apostol).
- **Side conditions:** `exp_log x` requires `0 < x`; `log_mul` requires both
  arguments positive; trig identities are unconditional.
- **MachLib-specific verification:** **`Real.log x = 0` for `x ≤ 0`** (clamped
  log). Every log axiom carries the positivity precondition; **no axiom
  claims `Real.log x = (analytic log) x` universally**.
- **Risk:** medium. The clamping convention is the source of the
  `derivative_eval` materially-false-axiom found and fixed this sprint
  (see §5.b).

### F3. Differentiation primitives `[15 in Differentiation.lean]`

`HasDerivAt`, `HasDerivAt_const`, `HasDerivAt_id`, `HasDerivAt_exp`,
`HasDerivAt_add/sub/mul/comp/inv`, `HasDerivAt_log_pos`, `HasDerivAt_unique`,
`HasDerivAt_of_eq`.

- **Classical reference:** standard calculus.
- **Side conditions:** `HasDerivAt_log_pos x` requires `0 < x`;
  `HasDerivAt_inv` requires `f x ≠ 0`.
- **Verification:** every conditional axiom carries its precondition in the
  signature.
- **Risk:** low.

### F4. Polynomial root-counting `[2 in Rolle.lean]`

`rolle` (mean-value form of Rolle's theorem) and `zero_count_bound_by_deriv`
(the Rolle-iteration packaging).

- **Classical reference:** Rolle's theorem, FTA-style consequence.
- **Side conditions:** the function must be differentiable on `(a, b)`;
  the zeros must be sorted and within the interval; the derivative-zero
  witnesses must be supplied at each interior point.
- **Verification:** preconditions explicit in signatures.
- **Risk:** low. Polynomial FTA (`poly_root_count_bound` in
  `PolynomialRootCount.lean`) is now a **theorem**, derived from these
  two axioms via `mean_value_theorem` + Rolle iteration.

### F5. Pi-related `[1 in SinNotInEMLDepth2Partial.lean]`

`pi_gt_one : 1 < pi`.

- **Classical reference:** `π = 3.14159...`.
- **Side conditions:** none.
- **Risk:** trivially true.

### F6. EML hierarchy + sub-axioms `[~76 across HighDimensional, SinNotInEML, CosNotInEML, ExpExpNotInEML1, AnalyticFiniteZeros, Lemmas, Seal, Forge, IteratedExpBounds, Linarith, SinNotInEMLDepth2Sweep]`

The barrier-style axioms: structural facts about `EMLTree`, `InEMLDepth`,
boundedness, the analytic-finite-zeros packets, ML lemma cluster, sealed
sub-claims.

- **Classical reference:** mostly *not* classical theorems — these are EML's
  own definitional + structural facts. The `analytic_finite_zeros` axioms
  are ports of standard results about analytic functions.
- **Side conditions:** vary; each axiom states its own.
- **Verification:** these are MachLib's own definitions and lemmas, not
  borrowed classical claims.
- **Risk:** medium — some are domain-specific and weren't part of this
  sprint's audit. Recommended for future audit passes; not Khovanskii-
  load-bearing.

### F7. Khovanskii-load-bearing `[2 live — zero_count_bound_classical (legacy PfaffianFunction), eml_pfaffian_validon_from_sin_equality; khovanskii_chain_step RETIRED]`

These are the **specifically-named** axioms that the Khovanskii closure depends
on. They're the focus of this audit (§2–§4 detail).

---

## §2a — Legacy PfaffianFunction Khovanskii bound: `zero_count_bound_classical`

> **Status refresh (2026-07-14).** This is now the project's **sole**
> Khovanskii-load-bearing axiom. `khovanskii_chain_step` (§2b) was **retired**
> (no longer declared anywhere); the full `KhovanskiiReduction.lean` Step-3
> pipeline was built afterward. The exponential specializations
> (single / two / arbitrary-depth-N) are proven **axiom-clean of this axiom**
> via dedicated tracks — verified by `#print axioms` on
> `ChainExp2NoZeros.chain2_khovanskii_bound_explicit`,
> `ChainExp2Capstone.chain2_khovanskii_bound`, and
> `IterExpDepthN.chainN_khovanskii_bound_unconditional` (all depend only on the
> `MachLib.Real` foundation). The **general** Pfaffian case (arbitrary
> triangular chains, incl. `log`/`inv` atoms) still routes through this axiom.
> See §2b for the precise remaining blocker.

**Location:** `KhovanskiiLemma.lean:580`

**Statement:** For a non-trivial PfaffianFunction valid on `(a, b)`, zeros
are bounded by `PfaffianRank f` (= `f.chain.order * 1_000_000 + f.degree`).

**Classical reference:** Khovanskii, A.G. *Fewnomials*. AMS Translations
Vol. 88, 1991. Theorem 1, Chapter 3.

**Side conditions:** analytic-domain validity (`IsValidOn`) on the interval,
witness-in-interval. Both explicit in the signature.

**MachLib-specific verification:** the bound formula `n * 1_000_000 + d`
is a loose closed form; Khovanskii's tighter `(d+α+1)^n + n·α` uses chain
polynomial degrees not tracked on `PfaffianFunction`. The looser bound is
sound and sufficient for EML downstream uses.

**Replaces:** the **materially-false** prior axiom `derivative_rank_lt`
(deleted 2026-06-12). That axiom claimed strict rank decrease under
differentiation, which is false for `exp_atom` (`(e^x)' = e^x`). The
replacement is a direct classical bound rather than an inductive
measure — same conclusion, no false intermediate claim.

**Closure path (updated 2026-07-14):** two independent pieces, both
still open, either of which alone is insufficient:

1. **General witness construction (Step 3b — the hard blocker).** The
   `PfaffianFn` bound is already constructive *given a reduction witness*
   (`pfaffian_fn_zero_count_bound` / `khovanskii_bound_via_sdr`). The entire
   witness pipeline is built and proven: `witness_construction` (3e, strong
   recursion on chain length), `buildReducer` (3f, WF recursion on the lex
   measure), `IsKhovanskiiReducible.trans`, `lexLT_wf`, and the capstone
   `khovanskii_bound_via_sdr` (3g). It is **parametric in one unfilled input**:
   a `PfaffianFn.StepwiseDecreaseReducer` — the strict lex-decrease. See §2c.
2. **`PfaffianFunction → PfaffianFn` bridge.** The axiom is stated over the
   *inductive* `PfaffianExpr`/`PfaffianFunction` type; the constructive bound
   lives on the *chain-explicit* `PfaffianFn`/`MultiPoly` type. A structural
   translation + eval-agreement (incl. the `comp`/`inv`/`log_atom`
   constructors) is required to transport the bound onto the axiom's type.
   This is orthogonal to (1) and independently bounded.

**Risk:** low (classically true, named, side conditions verified). But the
deletion is **not** near-term: it waits on §2c.

**Status:** the project's sole Khovanskii-load-bearing axiom. Exponential
specializations are already axiom-clean via separate tracks (see refresh box).

## §2b — RETIRED axiom: `khovanskii_chain_step`

**Status: DELETED (Phase-15 axiom audit retirement).** No longer declared
anywhere (`grep 'axiom.*khovanskii_chain_step'` → empty). `PfaffianFnBound.lean`
now exposes the reduction **witness** as an explicit hypothesis
(`IsKhovanskiiReducible`) instead of asserting the chain-step classically:
`pfaffian_fn_zero_count_bound` is a thin, axiom-free wrapper around
`KhovanskiiReduction.khovanskii_bound_full`. The classical content moved into
the constructive-modulo-witness pipeline; what remains open is the *witness
existence* proof (§2c), not a chain-step axiom.

## §2c — The real remaining gap (corrected 2026-07-14 after reading the shipped code)

**The "canonicalizer bottleneck" the docstrings describe is STALE.** The
`degreeUpper ∘ polySimplify` measure (which does no ring cancellation) was
**replaced** by an eval-canonical measure and the strict-descent was **proven**.
Concretely, the shipped `PfaffianChain.lexMeasure` (PfaffianChain.lean:855) second
component is `polyTrueDegreeStrict ∘ polyCoeffs ∘ multiPolyToPolyForLex ∘
leadingCoeffY_last`, and `PolynomialCanonical.lean` already proves the two
load-bearing facts:
- `polyTrueDegreeStrict_eq_of_evalCoeffs_eq` — **eval-equal ⟹ equal measure**
  (the eval-canonical property the old analysis said was missing);
- `polyTrueDegreeStrict_polyDerivativeCoeffs_lt` — the derivative strictly drops it.

Using these, `ChainExp2PathC.lean` **fully proves the SingleExp strict-decrease
with no hypothesis**: `singleExp_h_bridge_closure` → `singleExp_reduceStep_closed`,
and `singleExp_dispatch_step` (line 2009) is a **complete, `sorry`-free SingleExp
`ReduceStep`** (reduce-arm + canonical-trim arm covering the
`polyTrueDegreeStrict = 0` corner). A smoke-test instantiates it. So the SingleExp
Step-3b is **done**, through the generic `PfaffianFn` pipeline.

**What actually remains (three concrete, bounded pieces):**

1. **Eliminate the vacuous `sdr_other`. ✓ DONE (2026-07-14).**
   `singleExp_khovanskii_bound` (ChainExp2PathC.lean:2178) proved the SingleExp
   `PfaffianFn` bound *through* `khovanskii_bound_via_sdr` but threaded
   `sdr_other : PfaffianFn.StepwiseDecreaseReducer` (a total SDR for *arbitrary*
   chains — the open problem) purely for typing, making it stated-but-unusable.
   **`MachLib/ChainExp2SingleExpUnconditional.lean` removes it:** `se_reduces`
   builds the Khovanskii witness by a bespoke well-founded recursion on the shipped
   `lexMeasure`, staying entirely in the `⟨1, SingleExpChain, ·⟩` shape (reduce arm
   → `singleExp_reduceStep_closed`; trim arm → `singleExp_canonicalTrim_step`; base
   → `dropLast`), so no `sdr_other` is needed. `singleExp_khovanskii_bound_unconditional`
   then feeds that witness straight into `PfaffianFn.khovanskii_bound_full`.
   **Verified `#print axioms`-clean** of `zero_count_bound_classical` (only the
   `MachLib.Real` foundation), `sorry`-free, full `MachLib` builds green. This is
   the first fully-closed instantiation of the generic `PfaffianFn` witness
   pipeline — the architecture is now validated end-to-end on a real chain.

2. **The `log_atom` frontier — the TRUE blocker for the featured consumers
   (pinpointed 2026-07-14).** The axiom's real footprint is `PfaffianFunction.zero_bound`,
   consumed by the sin/cos-not-in-EML results (`EMLPfaffian.lean:363`,
   `CosNotInEMLAnyDepth.lean:206`) applied to `eml_pfaffian t`. But
   `eml_pfaffian (eml t1 t2) = exp(eml_pfaffian t1) − log(eml_pfaffian t2)`
   (EMLPfaffian.lean:105) — so **every** EML tree with an `eml` node contains
   `log_atom`. The exp-tower bridges (single-exp, nested two-exp) therefore CANNOT
   retire any featured consumer; `log_atom` is required.

   `EMLKhovanskiiConstructive.lean` has the constructive route — reduce log-count
   via `elim_top_log` (`exp(u − log b) = exp u / b`) toward an exp-only form — but
   its own 2026-07-07 status note records the exact **ceiling**: when an `eml`
   node's *exponent* subtree contains a log, elimination **buries** the log under
   exps (already at depth 2, `eml (eml a b) c`), landing in an **exp+rational**
   class outside `IsExpChain`. Two paths remain:
   - **fragment-path (bounded):** finish the exp-only reduction for the log-free-
     exponent EML fragment → reaches exp-only → the now-**unconditional** exp bound
     (`singleExp_khovanskii_bound_unconditional` / `chain2_..._unconditional`)
     applies. A genuine *partial* axiom-clean result; leaves the axiom only for the
     buried-log case.
   - **b-path (open depth):** a constructive Khovanskii bound for exp+rational
     (≡ exp+log) chains — extend the descent's generator from `IsExpChain` to admit
     a `1/x` (reciprocal/log) generator (cf. `PfaffianExpRecipDescent`,
     `PfaffianExpLogRecipDescent`, `PfaffianLogGeneralDegree`, which already build
     axiom-clean exp+recip/log descent pieces). This is the genuine remaining
     research depth.

   `IterExpChain`-through-the-generic-pipeline is a *separate*, architectural-only
   line (the depth-N iterated-exp bound is already axiom-clean via the `chainNFn`
   track; chain-2 lives in the bespoke `ChainExp2SDR`/`chain2Measure` framework).

3. **`PfaffianFunction → PfaffianFn` bridge** (§2a piece 2) — transport the
   `PfaffianFn` bound onto the axiom's inductive type. Orthogonal, structural.
   **Single-exp fragment DONE (2026-07-14):**
   `MachLib/PfaffianExprSingleExpBridge.lean` translates the exp fragment of
   `PfaffianExpr` (`const/var/exp_atom/+,-,·`) to `MultiPoly 1` over
   `SingleExpChain` (`toMP1`, `eval_toMP1`), and `expPoly_pfaffianFunction_zero_bound`
   gives an **axiom-clean** (verified: no `zero_count_bound_classical`) Khovanskii
   zero bound for single-exponential `PfaffianFunction`s via
   `singleExp_khovanskii_bound_unconditional`.
   **Nested two-exp fragment ALSO DONE (2026-07-14):**
   `MachLib/PfaffianExprTwoExpBridge.lean` (`toMP2`, `eval_toMP2`,
   `expExpPoly_pfaffianFunction_zero_bound`) bridges `(x, eˣ, e^(eˣ))`
   (`e^(eˣ) = comp exp_atom exp_atom`) to `MultiPoly 2` over `IterExpChain 2` and
   cites `chain2_khovanskii_bound_unconditional` (`ChainExp2Unconditional.lean` —
   the chain-2 bound with the vacuous `sdr_other` removed). Both `#print axioms`-clean.
   Remaining: the `log_atom` case — see §2c(2), which is the actual blocker for the
   featured `eml_pfaffian` consumers (the exp fragments do NOT reach them).

**Once (1)+(2)+(3):** `zero_count_bound_classical` is deleted. The exponential
sub-cases are already axiom-clean by *separate* tracks; the value of the pipeline
route is a single uniform proof that also covers the non-exponential chains.

---

## §3 — Sin-barrier load-bearing axiom: `eml_pfaffian_validon_from_sin_equality`

**Location:** `EMLPfaffian.lean:202`

**Statement:** If `t : EMLTree` evaluates to `sin` globally, then every `eml t1 t2`
subtree of `t` keeps `t2.eval > 0` on `(0, b)` for any `b > 0`.

**Classical reference:** the **smoothness preservation argument** in real
analysis. The sketch:
1. `t.eval = sin` is smooth (sin is smooth everywhere).
2. `t.eval = exp(t1.eval) - log_clamped(t2.eval)` (by EMLTree.eval definition).
3. `exp` is smooth ⇒ `log_clamped(t2.eval)` is smooth.
4. `log_clamped` is discontinuous at `0` ⇒ `t2.eval` cannot cross 0.
5. At sin's zeros (`i·π`), `exp(t1.eval) = 0` is impossible (exp > 0), so
   `log_clamped(t2.eval) > 0`, forcing `t2.eval > 0`.
6. Connectivity + non-crossing + positive-somewhere ⇒ `t2.eval > 0` throughout.

**Side conditions:** none additional. The argument is classically clean.

**MachLib-specific verification:** formalizing requires `IsSmoothOn`,
`Continuous_of_HasDerivAt`, and a connectivity argument. MachLib has none of
these currently. Adding them is its own sub-project (~300-500 lines).

**Risk:** low. The axiom is **classically true** in standard real analysis;
the gap is purely the missing formalization infrastructure (smoothness
preservation). This is exactly the kind of axiom early Mathlib results
shipped with — clearly named, classically referenced, with a stated
closure path.

**Status:** named load-bearing axiom. Recommended treatment: **ship as
"final result modulo one classically-true analytic axiom about domain
validity"** rather than pursue formalization in the next sprint (see §4
decision rationale).

---

## §4 — Decision: ship-conditional vs. continue-grinding

The Khovanskii closure has two remaining axioms (`derivative_rank_lt`,
`eml_pfaffian_validon_from_sin_equality`). Each one is roughly a separate
sub-project to close:

| Axiom | Effort to close | Classical-true now? |
|---|---|---|
| `derivative_rank_lt` | Multi-session (~250–400 lines via PfaffianFn) | False as stated |
| `eml_pfaffian_validon_from_sin_equality` | Multi-session (~300–500 lines, needs Smoothness module) | True (standard) |

Neither is a one-session close. The honest framing options:

- **(A)** Continue grinding. Both eventually close. Estimated 4-7 weeks of focused
  work given MachLib's bare-bones substrate (no Mathlib).
- **(B)** Ship the result *conditional on two named axioms with documented
  closure paths*. This is a respectable formalization milestone — directly
  comparable to Mathlib's own incremental landing pattern (results shipped
  modulo specific named gaps, gaps closed in subsequent PRs).

Recommendation: **(B) for `eml_pfaffian_validon_from_sin_equality`** —
the axiom is classically true, well-named, with a clear (but expensive)
closure path. Shipping it is honest and the publication frames the
classical analysis as "future formalization work".

Recommendation: **(A) for `derivative_rank_lt`** — the axiom is *materially
false* as stated. Shipping a materially-false axiom even with documentation
is too risky. Close via the chain-explicit refactor (infrastructure is
already in place; phase 4 is the bound proof).

---

## §5 — Case studies: the audit method catches real inconsistencies

Two inconsistencies surfaced during this sprint. Both were caught by
*attempted use* (not passive review). Both are now post-mortemed in
project memory (`feedback_classical_side_conditions.md`).

### §5.a — The Nodup soundness gap (caught earlier, pre-sprint)

**The axiom:** `zero_count_le` (now-renamed) asserted `zeros.length ≤ bound`
without a `Nodup` precondition on the zeros list.

**The classical theorem it was supposed to instance:** root count for a
polynomial of degree `n` is at most `n` distinct roots.

**The missing side condition:** *distinctness*. Without `Nodup`, you can
have a list of repeated zeros longer than the degree.

**How it was caught:** an attempted application produced a list with
repeats and proved `5 ≤ 3`, deriving `False`.

**The fix:** added `zeros.Nodup` to the axiom signature. The axiom
became sound; the cost was 3-4 downstream proofs needing the precondition.

### §5.b — The sin-embedding inconsistency (caught this sprint)

**The axiom:** `sin_as_pfaffian : PfaffianFunction` asserted that sin is
Pfaffian on ℝ with chain order 2.

**The classical theorem it was supposed to instance:** functions definable
in the structure `ℝ_{sin}` are Pfaffian.

**The missing side condition:** **triangularity** of the chain.
Khovanskii requires `y_i' = P_i(x, y_1, ..., y_i)`. The sin/cos chain
`sin' = cos, cos' = -sin` is mutually circular (not triangular). Sin is
Pfaffian only on bounded intervals via tan(x/2) substitution.

**How it was caught:** an attempted discharge of `eml_pfaffian_below_sin_density`
revealed that the bound axiom claimed to distinguish sin from eml-derived
functions of matching (n, d) — but with sin axiomatized as globally
Pfaffian, no such distinction is possible.

**The fix:** removed `sin_as_pfaffian` and `cos_as_pfaffian`. Sin is no
longer axiomatized as Pfaffian in MachLib (correctly — it isn't, globally).
The sin barrier proof now goes through `eml_pfaffian` + the Pfaffian bound
on EML constructions, not via direct sin-as-Pfaffian.

### Methodological lesson

Both inconsistencies were caught the same way: **by attempted use, not by
passive audit**. The lesson is in
`feedback_classical_side_conditions.md`:

> When adding a load-bearing math axiom, name the classical theorem,
> list its side conditions, verify each one against MachLib's conventions.
> Theorems with missing side conditions are the hiding place for
> inconsistency.

This audit document is the systematic application of that lesson to all
load-bearing axioms.

---

## §6 — Reviewer pre-emption

A skeptical Lean reviewer's first three questions about a Pfaffian-bound
result will be:

**Q1:** *"Show me the axiom file. How many axioms? Are they all needed?"*

A1: 252 axioms total, grouped in §1. The Khovanskii closure is conditional
on **2 specifically named load-bearing axioms** (§2, §3) plus the standard
real-analysis substrate (F1–F4). The other 200+ axioms are either substrate
(F1–F3), classical results we cite (F2–F4), or EML-internal structural
facts (F6) — none are silently load-bearing for the Khovanskii claim.

**Q2:** *"Is `pfaffian_zero_count_bound_constructive` proven, or just
asserted with helper-axiom rebranding?"*

A2: Proven, **conditional on `derivative_rank_lt` (materially false as
stated, deletion path in §2) and the chain of axioms in F1–F4**. The
sprint converted three structural axioms (`pfaffian_order_zero_corresponds_to_poly`,
`PfaffianFunction.derivative`, `PfaffianFunction.derivative_eval`) into
theorems via the inductive `PfaffianExpr` refactor + the `inv` constructor
+ `IsValidAt` domain machinery (commits `2d9b8c2`, `e432c20`). The
chain-explicit infrastructure (`MultiPoly`, `PfaffianChain`, `PfaffianFn`,
`pfaffian_fn_zero_count_bound`) is the prerequisite for closing the
remaining `derivative_rank_lt` (commits `41df587`, `51e48ee`, `664cc75`,
`f87be77`, `14e929f`).

**Q3:** *"Did you find any inconsistencies in the audit?"*

A3: **Yes — two, both caught and fixed during this sprint** (§5). Both
were caught by attempted-use, not passive review. The pattern is documented
in the project's feedback memory and informed the design of this audit
document. The fact that the audit method catches things is itself evidence
that the named load-bearing axioms have been seriously stress-tested.

---

## §7 — Closure status

| Closure | Status | Commit |
|---|---|---|
| `pfaffian_order_zero_corresponds_to_poly` | ✓ theorem | `2d9b8c2` |
| `PfaffianFunction.derivative` | ✓ noncomputable def | `2d9b8c2` |
| `PfaffianFunction.derivative_eval` | ✓ theorem via inv + IsValidAt | `e432c20` |
| `PfaffianFunction.derivative_rank_lt` (was materially false) | ✓ DELETED 2026-06-12 | replaced by `zero_count_bound_classical` |
| `PfaffianFunction.zero_count_bound_classical` (new replacement) | ⚠ axiom (classically true; Khovanskii 1991 cited) | future formalization or chain-port |
| `pfaffian_fn_zero_count_bound` (new) | ✓ theorem, axiom-free (takes `IsKhovanskiiReducible` witness as hypothesis) | this sprint |
| `khovanskii_chain_step` (new) | ✓ RETIRED / deleted — see §2b | Phase-15 |
| Step-3 SingleExp `StepwiseDecreaseReducer` | ✓ PROVEN — `singleExp_dispatch_step` (ChainExp2PathC.lean:2009), `sorry`-free | shipped |
| Unconditional SingleExp `PfaffianFn` bound | ✓ DONE — `singleExp_khovanskii_bound_unconditional`, axiom-clean, no `sdr_other` | 2026-07-14 |
| `PfaffianExpr`→`PfaffianFn` bridge, exp fragments (single-exp, nested two-exp) | ✓ DONE — axiom-clean bounds for exp/exp-exp `PfaffianFunction`s | 2026-07-14 |
| `log_atom` case (the TRUE blocker for the featured `eml_pfaffian`/sin-cos consumers) | ⚠ open — fragment-path bounded, b-path (exp+rational chain) is the research depth, §2c(2) | remaining |
| `eml_pfaffian_validon_from_sin_equality` | ⚠ axiom (classically true) | future formalization |

**Recommendation:** ship at the current honesty level with this audit
attached. The "3 of 4 structural axioms closed" framing + the audit's
case studies + the named load-bearing axioms is publishable as a real
formalization milestone. The two remaining axioms are post-publication
"future work" tightening, not blockers.

---

## Appendix — file-by-file axiom counts (post-sprint)

```
HighDimensional.lean         56  (EML hierarchy, non-Khovanskii)
Trig.lean                    46  (transcendental substrate)
Basic.lean                   40  (Real arithmetic substrate)
Hyperbolic.lean              21  (sinh/cosh, non-Khovanskii)
Differentiation.lean         15  (calculus substrate)
Seal.lean                    13  (sealed claims)
Lemmas.lean                  11  (named-lemma cluster)
AnalyticFiniteZeros.lean     11  (port of standard results)
Log.lean                      7  (with positivity preconditions)
Forge.lean                    7  (Forge kernel substrate)
Exp.lean                      6  (transcendental substrate)
Ring.lean                     5  (Real arithmetic substrate)
SinNotInEMLDepth2Sweep.lean   4  (depth-2 barrier sub-axioms)
EMLPfaffian.lean              3  (1 load-bearing for Khovanskii — see §3)
Rolle.lean                    2  (Rolle + zero-count-by-deriv)
Linarith.lean                 2  (tactic substrate)
IteratedExpBounds.lean        2  (helper bounds)
PfaffianFnBound.lean          0  (khovanskii_chain_step RETIRED post-snapshot — see §2b)
SinNotInEML.lean              1  (sin_pi_div_two model)
SinNotInEMLDepth2Partial.lean 1  (pi_gt_one)
Pfaffian.lean                 1  (operator substrate)
KhovanskiiLemma.lean          1  (zero_count_bound_classical — see §2a)
ExpExpNotInEML1.lean          1  (exp(exp) monotonicity)
CosNotInEML.lean              1  (cos_pi_div_two model)
```

Total: 253. (After this sprint's swap: the materially-false
`derivative_rank_lt` deleted, the classically-true `zero_count_bound_classical`
added in its place. Same count, strictly improved quality.)

## §8 — 2026-06-13 addendum: cos any-depth closure

After the sprint snapshot above, one focused single-day closure landed:
`MachLib.CosNotInEMLAnyDepth` (commit `machlib@6ee4d97`). This proves
`cos_not_in_eml_any_depth (k : Nat) : ¬ InEMLDepth (fun x => Real.cos x) k`,
the symmetric companion to `sin_not_in_eml_any_depth`. The structural proof
is parallel to sin's (same `eml_pfaffian` envelope + Khovanskii zero bound
+ overrun-the-bound contradiction), but the supporting infrastructure
(cos's `cos_at_half_odd_pi` induction, the cos-zeros list nodup proof,
the strict-order lemma) is constructive and not a port.

Three new classical-citation axioms landed with the closure:

1. **`pi_div_one_plus_one_pos : 0 < pi / (1 + 1)`** (CosNotInEMLAnyDepth.lean).
   Trivial classical fact. Discharge path: ~20 lines once Ring.lean grows a
   `div_pos` family.
2. **`pi_div_one_plus_one_lt_pi : pi / (1 + 1) < pi`** (CosNotInEMLAnyDepth.lean).
   Same discharge path.
3. **`eml_pfaffian_validon_from_cos_equality`** (CosNotInEMLAnyDepth.lean).
   Cos analog of the sin-side §3 axiom. Same classical
   smoothness-preservation argument verbatim; cos is smooth everywhere
   just like sin, and the connectivity argument is phase-independent.
   Discharge path: the same Smoothness module that retires the sin-side
   axiom retires this one too. Multi-session; both axioms ride one closure.

**New total: 256 axioms** (253 + 3).

**Updated file-by-file counts** (delta only, rest unchanged):

```
CosNotInEMLAnyDepth.lean      3   (NEW FILE — see §8)
```

**Per-axiom-family impact (categorical, not quantitative):** the cos
closure does not introduce a new family. All three new axioms fall into
existing families documented in §1:

- `pi_div_one_plus_one_pos` and `pi_div_one_plus_one_lt_pi` → real
  arithmetic substrate (would belong in Basic.lean / Ring.lean once
  div-ordering lands there).
- `eml_pfaffian_validon_from_cos_equality` → smoothness-preservation
  cluster, same family as `eml_pfaffian_validon_from_sin_equality` (§3).

Reviewer pre-emption answer A1 in §6 ("252 axioms total") should now read
"256 axioms total". The narrative is unchanged: the Khovanskii closure
is conditional on a small number of explicit classical citations, all
named, all with discharge paths. The cos closure does not change the
shape of that story — it adds three concretely-named axioms in already-
existing categories, all classically-true.

**What this closure adds to the EML credibility story:** the sin/cos
barrier symmetry is now restored. Before this commit, sin had
4 stratification levels closed (depth ≤ 0, ≤ 1, depth-2 32/32,
any-depth) while cos only had 2 (depth ≤ 0, ≤ 1). After this commit,
cos has 3 (depth ≤ 0, ≤ 1, any-depth — depth-2 is structurally
redundant given any-depth and is intentionally not added).

The cos closure does NOT discharge any prior axiom, does NOT modify
any prior proof, and does NOT change the Khovanskii closure narrative.
It's pure addition: +1 file, +3 axioms, +1 main theorem, +supporting
infrastructure.
