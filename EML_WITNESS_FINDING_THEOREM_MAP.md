# Option D — Theorem Map

Companion to `EML_WITNESS_FINDING_DECISION_2026_07_15.md` (the full dated narrative). That document
is a research log — 72 rounds, written chronologically, including dead ends. This one is the
opposite: a map of the FINAL spine only, in dependency order, for someone who wants the result
without the history. Non-invasive by design — no file was moved or renamed to produce this map,
it is a reading guide over the existing tree.

**What counts as "spine" is not a judgment call made by this document.** It is exactly
`optionDSpineModules` in `foundations/AxiomLedger.lean`, and `AxiomLedger.lean`'s whole-module guard
(invariant 5, added cont. 72) mechanically fails the build if any theorem in these 16 files leaks an
axiom outside `trustedFootprint`. If a file isn't in this list, it isn't checked by that guard,
which is itself a good definition of "exploratory" — the spine is the part of the codebase this
project is willing to stake a CI failure on.

## The spine, in dependency order

Each entry: file → what it adds → the headline declaration(s).

1. **`WitnessResidualTailSign.lean`** — `TailSign` (inductive: a function is eventually `.pos`,
   `.neg`, or `.zero`) proved for the "B eventually non-positive" half of the induction over EML
   tree structure, with zero dependence on the sibling subtree `A`.
2. **`WitnessResidualRCEPTailSign.lean`** — supporting machinery for the harder half
   (`RightChildrenEverywherePositive` case), building `EMLPfaffianValidOn` facts needed downstream.
3. **`WitnessResidualEventualValidTailSign.lean`** — generalizes validity-from-`0` to validity on an
   arbitrary tail `[a, ∞)`, matching what the harder induction case can actually supply.
   `evalid_tailSign`, the `evalidZero`/`evalid_zero_past` family.
4. **`WitnessResidualNormalFormClosure.lean`** — **first capstone.** `eml_eventually_valid_repr`:
   every EML tree has a representative that is valid AND value-matching on some tail. `TailSign`
   holds **unconditionally**, for every tree, no hypothesis:
   `eml_tailSign_unconditional : ∀ T, TailSign T.eval`. `no_tree_eq_sin_unconditional`: no finite
   EML tree equals `sin`, full stop.
5. **`WitnessResidualNestedTargetTailSign.lean`** — extends the closure to the `nestedTarget cs`
   family (`nestedTarget [] = sin`, `nestedTarget (c::cs) x = log(c + nestedTarget cs x)`) under a
   straddle condition (`nestedLo cs ≤ 0`). `no_tree_eq_nestedTarget_unconditional`.
6. **`WitnessResidualNestedTargetDepth2Straddle.lean`** — a reusable one-level straddle criterion;
   the first genuine depth-2 instance (`cs = [1, 2]`).
7. **`WitnessResidualNestedTargetTower.lean`** — the depth-2 fixed point generalizes to an infinite
   tower, one closure at every nesting depth.
8. **`WitnessResidualNestedTargetBWitness.lean`** — `EMLWitnesses` conjunct `0 < B.eval x0`
   generalized across the whole nested-target family (not just `1<c2<2`).
9. **`WitnessResidualConstSiblingUnconditional.lean`** — wires the unconditional closure back to the
   ORIGINAL depth-2 residual this whole document started from.
10. **`EMLPfaffianValidOnSinEqualityProved.lean`** — **the axiom, discharged.**
    `eml_pfaffian_validon_from_sin_equality_proved`: the `EMLPfaffian.lean` axiom's exact statement,
    proved — vacuously, since its hypothesis (a tree equaling `sin` everywhere) is now known
    unsatisfiable via step 4's `no_tree_eq_sin_unconditional`.
11. **`WitnessResidualCosTailSign.lean`** — the `cos` sibling, same mechanism, cheaper (TailSign
    machinery doesn't care which target is being ruled out). `no_tree_eq_cos_unconditional`,
    `eml_pfaffian_validon_from_cos_equality_proved`.
12. **`CosNotInEMLAnyDepth.lean`** — the pre-existing depth-bounded `cos ∉ EML_k` result (mirrors
    `sin_not_in_eml_any_depth`), which step 11 builds on.
13. **`EMLAnyDepthBarrierUnconditional.lean`** — `sin_not_in_eml_any_depth`/`cos_not_in_eml_any_depth`
    re-derived as one-line corollaries of steps 4/11 — the depth bound `k` is never inspected, so
    the unconditional result subsumes the depth-bounded one for every `k` simultaneously.
14. **`WitnessResidualNestedTargetFullyUnconditional.lean`** — **second capstone.** The FULL
    `nestedTarget` closure, no straddle condition, no restriction on the tree:
    `no_tree_eq_nestedTarget_fully_unconditional`. This is what actually closes `c2 ≥ 2`, via
    tail-restricted zero-counting run entirely inside the region `eml_eventually_valid_repr`
    supplies — no multi-session Khovanskii rebuild needed.
15. **`WitnessResidualRecurringTargetMetaLemma.lean`** — extracts step 14's argument into an
    abstract meta-lemma over any recurring zero family `Z` and recurring witness family `W`:
    `no_tree_eq_recurring_target_fully_unconditional`.
16. **`WitnessResidualContinuousTargetMetaLemma.lean`** — **third capstone, the general interface.**
    Strengthens step 15 to need only continuity + `¬TailSign`, no explicit zero family:
    `no_tree_eq_target_of_not_tailSign (TARGET) (L) (hcont) (hnts) (T) (heq) : False`. New IVT-based
    zero construction for arbitrary continuous targets (`target_zero_between`/`target_zero_past`),
    mirroring the tree-side `rcep_zero_between` mechanism. This is the fully target-independent
    interface Track B's B1 confirmed needs no further bundling (checked cont. 72: zero live call
    sites besides its own sanity-check instantiation, so a `TailOscillatoryTarget`-style wrapper
    would add ceremony with no current benefit).

## The shape, read top to bottom

```
TailSign machinery (1–3)
        |
        v
eml_eventually_valid_repr  ──────────►  TailSign holds unconditionally (4)
        |                                        |
        v                                        v
nestedTarget straddle family (5–9)      no_tree_eq_sin_unconditional (4)
        |                                        |
        v                                        v
c2 ≥ 2 fully closed (14)              axiom discharge: sin (10), cos (11–13)
        |                                        |
        v                                        v
   meta-lemma, explicit zero family (15)    depth-any-k subsumption (13)
        |
        v
   meta-lemma, continuity only (16)  ◄── the general reusable interface
```

Steps 4, 10, 14, and 16 are the four load-bearing capstones; everything else either builds toward
one of them or is a direct corollary.

## What is NOT the spine

Everything outside `optionDSpineModules` — the majority of `foundations/MachLib/*.lean`. This
includes, by category (not an exhaustive catalog — see the dated entries in the decision doc for
the full narrative of each):

- **Superseded routes.** Cont. 38–57's earlier attempts at the residual (Taylor-coefficient
  matching, validity-free Khovanskii extension, graph-shape classification) — explicitly ruled out
  before the tail-invariant pivot that produced step 4.
- **Superseded straddle-specific results.** The pre-cont.69 `nestedTarget` family (straddle
  condition `nestedLo cs ≤ 0 < nestedHi cs`) is subsumed by step 14's unconditional version, but the
  files still exist and are still individually sound (and still spine-checked, since steps 5–9 feed
  step 14's own construction).
- **Depth-specific elementary results** (`WitnessResidualSimpleT1Application.lean`,
  `WitnessResidualBOneLevelCompound.lean`, `EMLDepth1Fragment.lean`, and similar) — hand-verified
  special cases from before the general closure existed, kept for independent cross-checking
  (several are cited as "REAL, independent confirmation" in the decision doc) but not on the
  critical path to any headline.
- **`EMLSmoothness.lean`** — a large (2900+ line) exploratory file toward closing the axiom via a
  smoothness/analyticity bridge, superseded by the vacuous discharge (step 10) which needed none of
  it.
- **`EMLExplicitBoundSinBarrier.lean`/`EMLExplicitBoundCosBarrier.lean`** — a genuinely separate,
  still-open frontier (deriving an EXPLICIT numeric depth-bound rather than existence), not
  superseded, just a different question. This is the one place a legacy discharge axiom is still
  called directly (see A4, `AxiomLedger.lean` invariant 6, which pins this as the exact allowed set
  and fails the build if a new call site appears anywhere else).

No file in this category was deleted, moved, or marked deprecated as part of this document —
consistent with the "non-invasive" framing of the B2 task this document answers.

## Beyond the spine: what's been built since (cont. 74–90)

`optionDSpineModules` was deliberately frozen at the 16 files above when this guard was built
(cont. 72) — extending it is a separate decision, not made here, and everything below is real,
`sorryAx`-free, individually pinned as an `AxiomLedger.lean` headline (not whole-module-guarded the
way the spine is) rather than folded into the spine list itself. This section exists so a reader of
THIS map isn't left with a 2026-07-22-morning picture of the arc — a great deal was built the same
day and the days after, none of it superseding the spine above, all of it extending what it reaches.

**Track C — general-purpose extensions of the spine's own machinery, six closed:**

- **C1 — `LogDivergenceWall.lean`.** No finite EML tree valid on an interval containing `0` equals
  `Real.log` on the positive side — a DIFFERENT obstruction (continuity-at-a-point vs. `log`'s own
  divergence near `0`), not `TailSign`/oscillation-counting.
- **C3 — `LogImplicitRepresentability.lean`.** `log` is IMPLICITLY representable everywhere `x > 0`
  (invert `exp`'s own EML representative) despite C1's wall on every EXPLICIT route — a genuine
  separation theorem between the two notions of "representable."
- **C6 — `QuantitativeNonApproximation.lean`.** No finite EML tree stays within any `ε < 1` of `sin`
  for ALL sufficiently large `x` — closed, then SUPERSEDED on the practically relevant question by
  the compact-interval theorem below (cont. 79–80), which the research note's own "what this
  doesn't claim" section used to flag as open. It no longer is; see the research note's own update.
- **C7 — `CertcomTotalErrorFloor.lean`.** The lemma-shaped core of "no compiled artifact gets
  arbitrarily close to `sin` forever," combining C6's floor with an abstract rounding-error bound —
  superseded on its own practical form by the Certcom handshake below.
- **C8 — `NonRepresentabilityCensusSinSq.lean`.** One additional target instantiation, `sin²x` — a
  genuinely different oscillation shape (non-negative, recurring to `0` AND `1`) through the same
  general meta-lemma (step 16 above), zero target-specific calculus.
- **C9 — `ExtremeValueAttainment.lean` + `GeneralPeriodicTargetBarrier.lean`.** The general
  form the spine's own `sin`/`nestedTarget` results were always an instance of:
  `no_tree_eq_periodic_target` — **no finite EML tree equals ANY nonconstant, everywhere-continuous,
  periodic target**, full stop, not just `sin` and its nested-log relatives. Built genuine Extreme
  Value Theorem attainment machinery to get there, then found (erratum, not assumed) that EVT isn't
  actually what the theorem needed — periodicity alone makes every value recur arbitrarily far out,
  the same fact `sin_not_tailSign` already exploited by hand. `no_tree_eq_sin_via_periodic_barrier`
  confirms the general theorem re-derives step 4's `sin` conclusion, not just a plausible-looking
  generalization of it.
- **C2, C4 — investigated, deliberately not built.** C2 (can the grammar be extended to build
  `x²`?) is checked-not-assumed scope, already stated up front in the research note. C4 (cell
  stratification for exactness on the negative axis) has no identified consumer; both external
  reviews that proposed Track C ranked it lowest priority themselves.
- **C5, C10 — investigated in depth, genuinely still open, not just re-flagged.** C5 (a
  chain-order hierarchy theorem) found that `EMLTree`'s own encoder and the separate
  `IterExpDepthN` iterated-exponential-tower development are literal instances of the same
  `PfaffianChain n` type (a real, previously-unconfirmed bridge — see `EMLTowerSubsumesIterExp.lean`
  for the one concrete piece this turned into: EML reaches every depth of that tower family
  exactly) — but also found the muses' proposed obstruction mechanism (`TailSign` + chain order)
  doesn't combine, because they're orthogonal axes (`sin` is chain order 2 classically, yet EML
  can't represent it for reasons that have nothing to do with chain order). C10 (make a validity
  threshold explicit) traced to a `Classical.byContradiction` core inside `evalid_tailSign` — it
  proves the threshold exists without ever constructing it, a genuine constructive/classical
  obstacle, not a "just hasn't been done yet" gap. See decision doc cont. 90 for the full technical
  account of both.

**The compact-interval theorem and the Certcom handshake — the practically-relevant closure C6/C7
were originally reaching for, now actually reached (cont. 79–88):**

```
no_tree_eps_close_to_sin_compact_interval (cont. 79-80)
  — the REAL answer to "how long can a tree stay ε-close to sin on a BOUNDED interval" —
    M an EXPLICIT function of tree structure (EMLExplicitBound.combinedBoundE), not
    an abstract "eventually" threshold
        |
        v
certcom_total_error_floor_compact_interval (cont. 81)
  — combined with an ABSTRACT rounding-error bound: total error against true sin exceeds
    ε−δ WITHIN the interval once it's long enough — still abstract in `hround`
        |
        v
eml_var_var_pipeline / eml_var_var_certcom_witness (cont. 82-83)
  — wires the abstract `hround` to Certcom's REAL compiled pipeline for one hand-built tree
    (eml var var), closing the uniformity + Real→Float quantization gaps
        |
        v
eml_var_var_certcom_witness_grounded (cont. 84-86)
  — grounded against Certcom's ACTUAL disclosed rounding axioms, then a full retroactive
    audit fixed 10 of 14 primitive rounding axioms that were quietly false/imprecise
    before this round (cont. 86) — no free hypothesis left beyond genuine math quantities
    or Certcom's own disclosed IEEE-754 trust floor
        |
        v
eml_tree_grounded (cont. 87-88)  ◄── the capstone
  — generalizes from ONE hand-built tree to the FULL EMLTree grammar (const/var/eml, any
    depth/shape) via one structural induction — any tree this arc studies inherits a
    grounded Certcom pipeline connection automatically, with an explicit, machine-computed
    closed-form error bound
```

This is the one piece of the whole arc that connects an ABSTRACT non-representability result to an
ACTUAL compiled artifact with real IEEE-754 rounding — genuinely the most externally-relevant
addition since the spine itself, and worth a reader's attention even though (by design) it lives
entirely outside `optionDSpineModules`.

Full narrative, every round dated: `EML_WITNESS_FINDING_DECISION_2026_07_15.md`, cont. 74 onward.
