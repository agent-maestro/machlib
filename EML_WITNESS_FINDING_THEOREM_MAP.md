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
