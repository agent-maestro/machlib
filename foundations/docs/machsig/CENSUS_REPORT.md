# MachSig Phase 1 — Census Report

`MachSig-census/v0.1` · commit `5830f6607e81` · **13486 declarations**

Authoritative output: `artifacts/machsig_census.jsonl` — **not committed**. It is 17 MB and
regenerates deterministically in ~5 s:

```
lake env lean tools/machsig/extract.lean > artifacts/machsig_raw.tsv
python3 tools/machsig/census.py
```

Reproducibility was checked, not assumed: two independent runs at the same commit produce a
byte-identical JSONL (`sha256 7a9513c6741ab970…`). That is the Phase 1 exit criterion, and it is the
reason the extractor rather than its output is what lives in git.
`artifacts/machsig_census.csv` is a flattened union with explicit blanks and is convenience only.

## Population, and what it is NOT

The population is **MachLib Lean declarations** — every non-internal constant under the `MachLib`
namespace, taken from `getEnv`. That is 13486 objects, which is roughly 2.5× the ~5,455 figure
this project's notes carry for "declarations"; that older number was a narrower scope (theorems
reached by the sorry audit), and the two should not be quoted interchangeably.

**The grammar-level features of Phase 0.5 are absent from this census, and absent is not null.**
`eml_node_count`, `fOcc` and `trans1_head_counts` are properties of *terms*. A Lean declaration does
not *have* an `EMLTree` unless one occurs inside it, so these are recorded as
`grammar_term_features: not_applicable` at declaration scope. Extracting them needs a separate
term-level walker over the specific grammars, which Phase 1 has not built.

## Declaration kinds

| kind | count |
|---|---:|
| `theorem` | 8887 |
| `def` | 3645 |
| `ctor` | 450 |
| `axiom` | 221 |
| `rec` | 140 |
| `inductive` | 140 |
| `opaque` | 3 |

## Feature statistics

| feature | coverage | null rate | distinct | min | max | median |
|---|---:|---:|---:|---:|---:|---:|

| `source_views[0].structural_features.binder_count` | 13486 | 0.0 | 44 | 0 | 69 | 3.0 |
| `source_views[0].structural_features.prop_binder_count` | 13486 | 0.0 | 25 | 0 | 47 | 0.0 |
| `source_views[0].structural_features.non_prop_binder_count` | 13486 | 0.0 | 28 | 0 | 28 | 3.0 |
| `proof_structure.axiom_dependency_count` | 13486 | 0.0 | 85 | 0 | 88 | 8.0 |
| `proof_structure.type_direct_const_count` | 13486 | 0.0 | 59 | 0 | 95 | 8.0 |
| `proof_structure.value_direct_const_count` | 3645 | 0.7297 | 45 | 1 | 101 | 8 |
| `derived_metrics.prop_binder_fraction` | 12329 | 0.0858 | 133 | 0.0 | 1.0 | 0.2 |


## Shape of the corpus — first look

| quantity | observed |
|---|---|
| `axiom_dependency_count` range | 0 – 88 |
| mode | **1** (1,829 declarations) |
| zero-axiom declarations | **1,256** (9.3%) — purely structural lemmas |
| `binder_count` range | 0 – 69 |
| heaviest footprints (88) | `mse_lower_bound`, `gaussian_mgf_tendsto`, `posteriorMSE_tendsto` |

The heaviest declarations being the Kalman/Gaussian analytic results is a sanity check on the
extractor, not a finding: those are exactly where the deepest dependencies should sit. The
distribution is interpretable rather than degenerate, which is the first evidence that
`axiom_dependency_count` carries information. It is also the one column here with real trust
weight, being the kernel's own transitive footprint rather than anything this tooling computed.

## Epistemic status of every column above

All of them are `computed` — machine-counted from the kernel's own data structures. **None is a
mathematical measurement**, and none is a bound. Specifically:

* `binder_count` / `prop_binder_count` count `∀`-binders in the declaration's *type*, with
  `prop_binder_count` decided by `Meta.isProp`. They are syntactic properties of a statement, not
  of the mathematics it describes.
* `axiom_dependency_count` is `Lean.collectAxioms` — the kernel's transitive axiom footprint. It is
  exact and machine-checked, and it is the one column here with real trust weight.
* `type_direct_const_count` / `value_direct_const_count` are **direct** surface references, not the
  transitive closure. They are deliberately not called dependencies-of-the-proof.

## Sorry status

`depends_on_sorry = true`: **1** of 13486. This should agree with
`tools/sorry_audit.lean`; if it does not, one of the two is wrong and the disagreement is the
finding. See `PHASE1_ISSUES.md`.

## What is deliberately empty

| family | availability | why |
|---|---|---|
| `canonical_views` | `unsupported_representation` | Phase 0 Finding 3: no canonicalizer exists for a Lean declaration. Substituting the source form would make Phase 6's drift gate unable to fire. |
| `certified_bounds` | `not_computed` | Phase 0 Finding 4: counts like `ZeroCountOn` are *propositions carrying a bound as a parameter*. Extracting them needs statement-shape analysis, not a counter. |
| `transitive_dependency_count` | `not_computed` | `collectAxioms` gives the transitive *axiom* view; a general transitive const closure was not computed. |
| `proof_dependency_depth` | `not_computed` | No depth calculation exists. Per the amendment, it is not called `proof_depth` and not guessed. |
| grammar term features | `not_applicable` | wrong scope — see above. |
