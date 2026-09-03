# MachSig Phase 2C — Feature Stability Matrix

Stability was established from **naturally occurring** corpus cases, not synthetic edits. No MachLib
statement or proof was modified to generate evidence.

## Method, and its limit

225 theorem groups share a `StatementDigest`. Within a group the statement representation is
identical by construction, so any feature that differs across the group is **statement-insensitive**,
and any feature constant across all groups while varying corpus-wide is a candidate discriminator.

**Limit, stated plainly:** this gives strong evidence for Classes A and D (both observed) and for
statement-sensitivity (Class B, by construction of the digest). It gives **no measured evidence** for
Class C (cosmetic source rewrites) — binder-name and `mdata` insensitivity is a property of the
encoding, established by reading it, not by experiment. That row is marked `definition_read`.

## Matrix

| feature | coverage | variation | classification | warrant |
|---|---:|---|---|---|
| `StatementDigest` | 7,569 theorems | 7,305 distinct | `STATEMENT_SENSITIVE`, `PROOF_STABLE` | `computed` |
| `statement_expr_node_count` | 100% | 538 distinct | `STATEMENT_SENSITIVE` | `computed` |
| `statement_expr_depth` | 100% | 60 distinct | `STATEMENT_SENSITIVE` | `computed` |
| `distinct_constant_reference_count` | 100% | 57 distinct | `STATEMENT_SENSITIVE` | `computed` |
| `implication_count` | 100% | 32 distinct | `STATEMENT_SENSITIVE` | `computed` |
| `equality_head_count` | 100% | 13 distinct | `STATEMENT_SENSITIVE` | `computed` |
| `conjunction_count` | 100% | 14 distinct | `STATEMENT_SENSITIVE` | `computed` |
| `disjunction_count` | 100% | **5 distinct**, median 0 | `DEGENERATE` | `computed` |
| `existential_count` | 100% | **9 distinct**, median 0 | `DEGENERATE` | `computed` |
| `proof_expr_fp64` | 7,569 theorems | 204/225 groups differ | `PROOF_SENSITIVE`, `STATEMENT_STABLE` | `computed` |
| `proof_approx_depth` | 7,569 theorems | wide | `PROOF_SENSITIVE` | `computed` |
| `axiom_dependency_count` | 100% | 0–88 | **`TRUST_SURFACE_SIGNAL`**, `STATEMENT_STABLE` | `computed` |
| `depends_on_sorry` | 100% | 1 true | `TRUST_SURFACE_SIGNAL`, near-degenerate | `computed` |
| `syntactic_node_count` (term) | 786 decls (7%) | median 1 | `REPRESENTATION_LOCAL`, `DEGENERATE` | `computed` |
| `emltree_depth` (term) | 786 decls (7%) | 5 distinct | `REPRESENTATION_LOCAL`, `DEGENERATE` | `computed` |
| `elet_count`, `cond_node_count` | 17 decls (0.2%) | 5 total each | `DEGENERATE` | `computed` |
| binder-name insensitivity | encoding-wide | — | `SOURCE_NOISE`-immune | **`definition_read`** |

## Coverage dimension

The directive's warning is borne out. `elet_count` is perfectly well-defined and exists on **0.2%**
of declarations with five occurrences corpus-wide; `axiom_dependency_count` has 100% coverage and
89 distinct values. Coverage and variation together, not either alone, decide what belongs in a
signature.

## Verdict

The statement and proof layers both carry corpus-wide, interpretable, stable-in-the-right-way
variation. The term layer does not, and should annotate rather than discriminate.
