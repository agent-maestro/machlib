# MachSig Phase 0 — Repository Reconnaissance

**Scope:** what MachLib already exposes, verified by reading definitions and signatures.
**Non-goal:** no theorem logic was modified, and no glyph/letter design was considered.
**Commit basis:** machlib `1f295d84`, Lean `v4.32.2`, 13 gates green.

---

## How "Available now?" was determined, and why that matters

Every `Available now?` cell is an **absence-or-presence claim about this corpus**, and this corpus
punishes the lazy form of that claim. Names here track the *shape of the thing named*, not a
positional convention: the depth-2 analogue of `depth_le_one_log_le_linear` is called
`depth_le_two_log_le_exp`, because the bound changed from linear to exponential. Searching by
extrapolated name returns "missing" for things that exist.

So each row below was checked by **reading the definition or signature**, not by matching a name
pattern. Rows marked *unverified* say so. Before this table is trusted for Phase 1 feature
selection, `tools/absence_audit.py` should be run over any claim of absence it contains.

---

## Finding 1 — There are FOUR distinct "depth" notions, in two codebases

`docs/` and the frontier register already warn that "depth" is ambiguous. Reconnaissance finds one
more than that warning lists, and the extra one is in Lean:

| notion | where | what it counts |
|---|---|---|
| `EMLTree.depth` | `SinNotInEML.lean:72` | nesting of `eml` nodes in a **tree** |
| `netDepth` | `EMLNetlistDepth.lean:125` | combinational depth of a straight-line **DAG** program |
| `eml_cost.eml_depth` | Forge python tool | SuperBEST routing-tree depth; `Add`/`Mul` cost `1 + max` |
| `eml_cost.predict_chain_order_via_additivity` | Forge python tool | Pfaffian **chain order**; `Add`/`Mul` are free |

**MachSig must never emit a bare `depth` field.** Any depth feature has to name its measure, or the
census will silently mix two scales — the same defect the register logged in 2026-08-16 when KL
divergence read as depth 4 and depth 1 simultaneously, both correct.

## Finding 2 — Tree and DAG node counts are genuinely different features

`netDepth_eq_depth` proves depth is **invariant** under DAG sharing, while unfolding a DAG to a tree
can blow the node count up **exponentially** (`EMLNetlistDepth`, module docstring). So
`canonical_tree_nodes` and `canonical_dag_nodes` are not two views of one quantity, and a signature
carrying only one of them loses the sharing structure. Both are worth collecting; their *ratio* is
probably the more informative derived feature.

## Finding 3 — There is NO general canonical form. "CANONICAL SIGNATURE" has no single referent

This is the finding that most affects the roadmap. Normalisation in MachLib is
**representation-specific**, and nothing canonicalises an arbitrary object:

| normaliser | operates on | file |
|---|---|---|
| `pnorm` | `List Real` coefficient lists (drops trailing zeros) | `PolyBasics` |
| `normalizeCoeff`, `normalizedProduct*` | `CoeffPoly` | `NormalizedPolynomialRootCount` |
| `PfaffianFn.simplify` | `PfaffianFn` | `PfaffianChain:113` |
| `simplifyCoeffs` | `List Poly` | `SingleExpKhovanskii:649` |
| `mach_mpoly` | **goals during a proof** — a tactic, not a data-level function | tactic |

Consequence: a `CanonicalSig` must be defined **per representation** (`EMLTree`, coefficient list,
`PfaffianFn`, `FTerm`, …), and objects outside those representations have **no canonical form at
all** and must report null rather than falling back to the source form. Silently using the source
tree as "canonical" would make Phase 6's canonicalisation-drift gate structurally unable to fire.

## Finding 4 — Component / branch / interval counts are PROPOSITIONS, not computable numbers

`ZeroCountOn (p : Real → Prop) (a b : Real) (K : Nat) : Prop` (`ZeroCountGlue:48`) takes the count
`K` as a **parameter** and asserts a bound on it. `RealSetFinite (s : RealSet) : Prop`
(`AnalyticFiniteZeros:70`) asserts `∃ n`, every `Nodup` list drawn from `s` has length `≤ n`.

Neither computes a count. There is no function returning the number of components, branches, or
intervals. The roadmap's `canonical_component_count`, `canonical_branch_count`,
`canonical_interval_count` and `number_of_connected_components` therefore have **no extractable
numeric referent today**, and inventing one would violate the roadmap's own rule against placeholder
mathematical values. They belong in the "needs instrumentation" bucket, not Phase 1.

## Finding 5 — The proof-side extractor already has a working precedent

The hardest-sounding features are the most available. `AxiomLedger.lean` enumerates axioms from the
environment (`getEnv`, `.axiomInfo`) and takes footprints from **the kernel's own dependency graph**
(`Lean.collectAxioms`, the `#print axioms` mechanism). `tools/sorry_audit.lean` already walks every
MachLib declaration and computes transitive `sorryAx` dependence. `tools/axiom_ledger/emit_ledger.py`
already writes machine-readable output (`axiom_ledger.json`).

MachSig's proof features should reuse that path rather than re-deriving it.

> **Caution before reuse:** `axiom_ledger.json` records `total_axioms: 220` while the live gate
> reports **243 axioms pinned**. The two are probably differently scoped, but the discrepancy is
> unresolved and the json must not be treated as the current count without checking.

---

## The table

Legend — **Available now?**: `YES` = extractable today from an existing definition;
`TOOL` = exists but only in the Forge python tools, outside this repo;
`INSTR` = needs new instrumentation; `NO REFERENT` = nothing in the corpus computes this.

| Candidate invariant | Existing source | Available now? | Stable? | Notes |
| --- | --- | ---: | ---: | --- |
| `object_name`, `namespace`, `object_kind` | `getEnv` / `ConstantInfo` | YES | high | same path as `sorry_audit.lean` |
| `source_file` | Lean decl ranges | YES | high | |
| `source_tree_nodes` | `EMLTree` structural recursion | INSTR | high | trivial to write; none exists |
| `source_depth` | `EMLTree.depth` | YES | high | **must be labelled `tree_depth`** — Finding 1 |
| `source_exp_count` / `log_count` | `EMLTree` recursion | INSTR | high | `eml` node = one `exp` + one `log` by `eval`; counts are derivable from node count, so likely **redundant** |
| `source_add/mul/neg/div_count` | — | NO REFERENT | — | `EMLTree` has only `const`/`var`/`eml`; arithmetic is not in this grammar |
| `source_quantifier_count`, `source_hypothesis_count` | `Expr` telescope of the decl type | INSTR | high | straightforward `forallTelescope` |
| `canonical_tree_nodes` | per-representation | INSTR | med | Finding 3: only for representations that HAVE a normal form |
| `canonical_dag_nodes` | `EMLInstr` / `ProgWf` | INSTR | high | distinct from tree nodes — Finding 2 |
| `canonical_depth` | `EMLTree.depth` post-normalisation | INSTR | high | |
| `canonical_net_depth` | `netDepth` | YES | **very high** | `netDepth_eq_depth`: invariant under sharing |
| `canonical_component_count` | — | NO REFERENT | — | Finding 4 |
| `canonical_branch_count` | — | NO REFERENT | — | Finding 4 |
| `canonical_interval_count` | — | NO REFERENT | — | Finding 4 |
| `normalization_reduction_ratio` | derived | INSTR | med | only meaningful where a normaliser exists |
| `degree` | `PfaffianExpr.degree` (`Pfaffian:126`), `PfaffianFunction.degree` (`:187`) | YES | high | **only for the Pfaffian representation**; null elsewhere |
| `minimal_degree`, `relation_degree`, `degree_drop_count` | `GermIntervalMinimal`, degree-drop lemmas | INSTR | unknown | exist as *theorems about* minimality, not as extractable numbers — needs study |
| eventual / tail classification | `EvSign`, `EvZeroF`, `EvDom`, `RatGerm` | YES (as flags) | high | predicates, so extract as booleans-with-provenance, never as magnitudes |
| positivity requirements | hypothesis inspection of the decl type | INSTR | med | e.g. the `0 < t.eval x` that distinguishes `decay_on_ray` from its unconditional form |
| `proof_dependency_count` | `Lean.collectAxioms` / const deps | YES | high | Finding 5 |
| `proof_depth` | dependency DAG longest path | INSTR | med | derivable from the same graph |
| `local_lemma_count` / `external_lemma_count` | const deps partitioned by module | YES | high | |
| `axiom_count` | `AxiomLedger` path | YES | **very high** | already gated |
| `sorry_count` | `tools/sorry_audit.lean` | YES | **very high** | already gated |
| `obligation_count` | `tools/check_obligations.sh` (22 rows, 4 open) | YES | high | corpus-level, not per-object; needs mapping |
| `certificate_state` | `ForgeCheck/*.lean`, `Certcom` | YES (coarse) | med | per-certificate, not per-theorem |

---

## Exit criterion — what can be extracted, what needs instrumentation, what must not be measured

**Extractable today (Phase 1 can start here):** identity fields; `EMLTree.depth`; `netDepth`;
Pfaffian `degree`; the eventual/tail predicate flags; and the whole proof block (dependencies,
axioms, sorry) via the `AxiomLedger` / `sorry_audit` path.

**Needs instrumentation (cheap, mechanical):** node counts for tree and DAG; quantifier and
hypothesis counts by telescoping the declaration type; proof-DAG longest path; per-representation
canonical forms where a normaliser already exists.

**Must NOT be measured yet:** component, branch and interval counts (Finding 4 — no referent);
arithmetic operator counts (not in the `EMLTree` grammar); and any `CanonicalSig` for objects
outside the representations that have a normaliser (Finding 3). Emitting these as nulls is correct;
emitting a fallback value would defeat Phase 6 before it is built.

**Open question for Phase 1:** whether `source_exp_count` / `source_log_count` carry information
beyond node count, given that every `eml` node contributes exactly one of each. If they do not, they
are redundant by construction and should be dropped before the census rather than after.
