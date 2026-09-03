# MachSig Feature Registry — `MachSig-census/v0.1`

Four independent axes per the Phase 1 amendment. They are **not** interchangeable:

* `representation_scope` — *which grammar or object class the feature belongs to*
* `semantic_kind` — *what concept it measures*
* `value_type` — *the shape of the value*
* `epistemic_type` — *what warrant supports it*

`epistemic_type` vocabulary: `metadata`, `observed_structure`, `computed`, `derived`,
`proved_exact`, `proved_upper_bound`, `proved_lower_bound`, **`definition_read`**.

> `definition_read` means the relation was established by inspecting an implementation or
> definition, and is **not** represented as a theorem checked by Lean. It must never be merged into
> `proved_*`. Phase 0.5 produced the first instance.

---

## Features emitted at `MachSig-census/v0.1`

| feature_id | representation_scope | semantic_kind | value_type | epistemic_type | extractor |
|---|---|---|---|---|---|
| `identity.object_name` | LeanDeclaration | identifier | string | `metadata` | `getEnv` |
| `identity.declaration_kind` | LeanDeclaration | constant class | enum | `observed_structure` | `ConstantInfo` |
| `identity.source_module` | LeanDeclaration | provenance | string | `metadata` | `getModuleIdxFor?` |
| `source_views[].structural_features.binder_count` | LeanDeclarationType | syntactic ∀-binder count | integer | `computed` | `forallTelescopeReducing` |
| `source_views[].structural_features.prop_binder_count` | LeanDeclarationType | syntactic hypothesis count | integer | `computed` | `+ Meta.isProp` |
| `source_views[].structural_features.non_prop_binder_count` | LeanDeclarationType | syntactic data-binder count | integer | `derived` | subtraction |
| `proof_structure.axiom_dependency_count` | LeanDeclaration | transitive kernel axiom footprint | integer | `computed` | `Lean.collectAxioms` |
| `proof_structure.depends_on_sorry` | LeanDeclaration | transitive `sorryAx` reachability | boolean | `computed` | `Lean.collectAxioms` |
| `proof_structure.type_direct_const_count` | LeanDeclarationType | **direct** surface constant references | integer | `computed` | `Expr` walk |
| `proof_structure.value_direct_const_count` | LeanDeclarationValue | **direct** surface constant references | integer | `computed` | `Expr` walk |
| `derived_metrics.prop_binder_fraction` | LeanDeclarationType | hypothesis density | float | `derived` | `prop/binder`, guarded |

**`type_direct_const_count` is not a dependency count.** It is the declaration's own surface, not a
transitive closure. The two are kept apart deliberately; only `axiom_dependency_count` is transitive.

## Feature relations

Relations are not features. They record *why* a column is absent, so redundancy can be removed
without losing the reason.

| relation_id | representation_scope | statement | epistemic_type |
|---|---|---|---|
| `emltree.eval_exp_occurrence` | EMLTree | `eval`-exp syntactic occurrences **=** `eml_node_count` | `definition_read` |
| `emltree.eval_log_occurrence` | EMLTree | `eval`-log syntactic occurrences **=** `eml_node_count` | `definition_read` |
| `fterm.f_expansion` | FTerm | each `F` expands via `Fmix a b c x = a·exp x + b·log x + c` to one syntactic `exp` and one syntactic `log` | `definition_read` |
| `netdepth.tree_dag_agreement` | EMLTree ↔ EMLInstr | `netDepth_eq_depth` — depth is invariant under DAG sharing | `proved_exact` |

The last row is the only one of the four that Lean checks. That contrast is the point of having the
`definition_read` category at all.

## Declared-but-not-emitted, with typed availability

| feature family | availability | reason |
|---|---|---|
| `canonical_views` | `unsupported_representation` | Phase 0 Finding 3 — no canonicalizer for a Lean declaration |
| `certified_bounds` | `not_computed` | Phase 0 Finding 4 — bounds live as propositions carrying `K` as a parameter |
| grammar term features (`eml_node_count`, `fOcc`, `trans1_head_counts`, `elet_count`, `cond_node_count`) | `not_applicable` | wrong scope: these are properties of **terms**, and a declaration does not have a term unless one occurs inside it |
| `transitive_dependency_count` | `not_computed` | `collectAxioms` is transitive for axioms only |
| `proof_dependency_depth` | `not_computed` | no depth calculation exists; deliberately **not** named `proof_depth` |
| `ElementaryEMLErf` family | `feature-family-unassessed` | Phase 0.5 — left open rather than forced into the exp/log model |

## Banned field names

`depth` — invalid at any scope (four distinct notions across two codebases).
`branch_count` — reserved for a mathematical branch count that does not exist; a syntactic `cond`
must be called `cond_node_count`.
`zero_count`, `component_count`, `interval_count` — no computed referent; only `*_upper_bound`
forms are admissible, and only when the underlying theorem says so.
