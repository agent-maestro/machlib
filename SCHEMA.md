# MachLib record schema (v1.0.0)

> The full data specification. Every field documented. Copy-paste
> examples below. This is the contract MachLib makes with anyone
> consuming the dataset.

## Top-level structure

A MachLib record is a JSON object with seven required sections:

```json
{
  "schema_version": "1.0.0",
  "theorem":             { ... },
  "proofs":              [ ... ],
  "difficulty":          { ... },
  "common_mistakes":     [ ... ],
  "tactic_trace":        { ... },
  "structural_profile":  { ... },
  "relationships":       { ... },
  "metadata":            { ... }
}
```

`schema_version` is a [SemVer](https://semver.org/) string. Major
version bumps are breaking; minor and patch are additive.

## `theorem` — what is being proved

```json
{
  "id": "eml_is_exp_v001",
  "base_id": "eml_is_exp",
  "variant_strategy": "constant_swap",
  "statement": {
    "informal": "eml(x, 1) equals exp(x) for all real x",
    "formal_lean": "theorem eml_is_exp (x : R) : eml x 1 = Real.exp x",
    "formal_eml_lang": "fn eml_one(x: Real) -> Real { eml(x, 1) }"
  },
  "domain": "eml",
  "lane": 1,
  "tags": ["identity", "exp", "single-operator"]
}
```

| Field | Type | Notes |
|---|---|---|
| `id` | string, unique | `<base_id>_v<NNN>` for variants; bare `<base_id>` for base records |
| `base_id` | string | The original theorem this record derives from. Equal to `id` for base records. |
| `variant_strategy` | string \| `null` | One of the 10 generation strategies, or `null` for hand-authored records. |
| `statement.informal` | string | One-sentence English description. |
| `statement.formal_lean` | string | The exact Lean 4 declaration. Verifiable by the kernel. |
| `statement.formal_eml_lang` | string \| `null` | Optional EML-lang source for the same statement. |
| `domain` | string | One of: `eml`, `analysis`, `algebra`, `chemistry`, `physics`, `finance`, `engineering`. |
| `lane` | integer 1–6 | Curriculum lane; see `docs/for-agent-builders/curriculum_guide.md`. |
| `tags` | array of strings | Free-form discoverability. |

## `proofs` — multiple proofs per theorem, ranked by cost

```json
[
  {
    "id": "p1",
    "tactics": ["unfold eml", "simp [Real.log_one]"],
    "tactic_count": 2,
    "eml_node_cost": 1,
    "style": "definitional",
    "is_optimal": true,
    "discovered_by": "human",
    "discovery_date": "2026-04-15"
  },
  {
    "id": "p2",
    "tactics": ["unfold eml", "ring_nf", "simp"],
    "tactic_count": 3,
    "eml_node_cost": 1,
    "style": "algebraic",
    "is_optimal": false,
    "discovered_by": "proof_gym_agent_007",
    "discovery_date": "2026-05-20"
  }
]
```

Each entry is one valid proof of the theorem. Multiple entries are
the rule, not the exception. All entries have been kernel-verified.

| Field | Type | Notes |
|---|---|---|
| `id` | string, unique within the record | Conventionally `p1`, `p2`, … |
| `tactics` | array of strings | The Lean tactic sequence, in order. |
| `tactic_count` | integer | `len(tactics)`. Cached for ranking. |
| `eml_node_cost` | integer | Cost in EML AST nodes (the `eml-cost` metric). |
| `style` | string | One of: `definitional`, `algebraic`, `simp`, `rewrite`, `induction`, `contradiction`, `automation`. |
| `is_optimal` | boolean | True for the lowest-cost proof in the array. Exactly one per record. |
| `discovered_by` | string | `human`, the seed-author handle, an agent ID, or `forge_mining`. |
| `discovery_date` | ISO 8601 date | YYYY-MM-DD. |

## `difficulty` — agent-attempt-calibrated

```json
{
  "lane": 1,
  "label": "beginner",
  "calibrated_from_attempts": 47,
  "average_hint_level_at_solve": 0.8,
  "prerequisite_skills": ["unfold", "simp"]
}
```

| Field | Type | Notes |
|---|---|---|
| `lane` | integer 1–6 | Mirrors `theorem.lane`; included here for downstream filtering. |
| `label` | string | One of: `beginner`, `intermediate`, `advanced`, `expert`, `frontier`. |
| `calibrated_from_attempts` | integer ≥ 0 | Number of agent attempts informing this label. `0` means seed-author-assigned, not yet recalibrated. |
| `average_hint_level_at_solve` | number 0.0–4.0 | Mean hint level (0=none, 4=tactic name) at which agents solved the theorem. |
| `prerequisite_skills` | array of strings | Tactic names the prover should be fluent with. |

## `common_mistakes` — failure data

```json
[
  {
    "tactic": "ring",
    "why_fails": "ring operates on semirings; exp/ln are not ring operations",
    "frequency": 12
  }
]
```

Sourced from real agent failures in the gym, not invented. Empty
array if no failure data has been collected for this theorem.

## `tactic_trace` — what works and what doesn't

```json
{
  "successful": {"unfold eml": 42, "simp": 38, "rfl": 5},
  "failed":     {"ring": 12, "omega": 5},
  "success_rate_by_tactic": {"unfold eml": 0.95, "ring": 0.0}
}
```

| Field | Type | Notes |
|---|---|---|
| `successful` | object map (tactic → count) | Tactic appearances in successful proofs. |
| `failed` | object map (tactic → count) | Tactic appearances in failed attempts. |
| `success_rate_by_tactic` | object map (tactic → 0.0–1.0) | Per-tactic success ratio across all attempts. |

## `structural_profile` — chain order, cost class, drift

```json
{
  "chain_order": 1,
  "cost_class": "p1-d1-w1-c0",
  "eml_depth": 1,
  "dynamics": {"oscillations": 0, "decays": 0},
  "drift_risk": "LOW",
  "fpga_estimate": {"exp_units": 1, "ln_units": 0, "luts": 150}
}
```

The Pfaffian / EML-cost metadata. Computed by `eml-cost analyze`.
Some fields (e.g. `chain_order`) depend on the Khovanskii
zero-count gap discussed in `PHILOSOPHY.md`; those are computed
empirically and labelled "unverified" in the gap-affected fields.

| Field | Type | Notes |
|---|---|---|
| `chain_order` | integer ≥ 0 | Pfaffian chain order. |
| `cost_class` | string | `p<P>-d<D>-w<W>-c<C>` — Pfaffian / depth / width / complexity. |
| `eml_depth` | integer ≥ 0 | EML AST depth. |
| `dynamics.oscillations` | integer ≥ 0 | Count of oscillatory components. |
| `dynamics.decays` | integer ≥ 0 | Count of exponential-decay components. |
| `drift_risk` | string | One of: `LOW`, `MEDIUM`, `HIGH`. fp16 drift risk. |
| `fpga_estimate` | object | Coarse FPGA resource estimate. |

## `relationships` — graph structure

```json
{
  "parent": "eml_is_exp",
  "siblings": ["exp_is_eml", "ln_via_eml"],
  "depends_on": ["eml_def"],
  "structural_siblings": ["rc_circuit_decay", "beer_lambert"]
}
```

| Field | Type | Notes |
|---|---|---|
| `parent` | string \| `null` | The base theorem this is a variant of. `null` for base records. |
| `siblings` | array of theorem IDs | Direct algebraic or definitional siblings. |
| `depends_on` | array of theorem IDs | Lemmas required by `proofs[*]`. |
| `structural_siblings` | array of theorem IDs | Theorems with the same cost class in different domains. |

## `metadata` — provenance and verification

```json
{
  "verified": true,
  "verification_method": "lean4_kernel",
  "generated_by": "machlib_generator_v1",
  "creation_date": "2026-05-01"
}
```

| Field | Type | Notes |
|---|---|---|
| `verified` | boolean | True iff every proof in the `proofs` array kernel-verifies on the pinned Lean toolchain. |
| `verification_method` | string | Currently always `lean4_kernel`. |
| `generated_by` | string | Pipeline identifier. |
| `creation_date` | ISO 8601 date | YYYY-MM-DD. |

## Validation

Records are validated against a JSON Schema bundled at
`schemas/record_v1.schema.json` (added in Phase 0.5). The
`machlib verify` CLI runs both schema validation and kernel
re-verification.

## Versioning

Within v1.x:

  - Adding new optional fields: minor bump (1.0.x → 1.1.0).
  - Adding new required fields: major bump (1.0.x → 2.0.0).
  - Renaming or removing fields: major bump.

Records are forwards-compatible within a major version: a v1.0
reader will silently ignore fields added in v1.1.
