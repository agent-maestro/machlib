# eml-records

`eml-records` is a pre-alpha package for validating EML-style JSON records used
in Monogate/MachLib evidence workflows.

It is a schema and record-shape helper. It is not a theorem prover, not a proof
validator, not a safety certifier, not production controller evidence, not a
replacement for Mathlib, and not a public theorem/proof/open-problem claim.

## Status

- Version: `0.0.1`
- Published for early testing.
- Intended for local record validation and CI-style checks.
- Does not upload, deploy, publish, or handle tokens.

## Install

```bash
python -m pip install eml-records
```

For repository development:

```bash
python -m pip install -e package_candidates/eml_records
```

Or run with `PYTHONPATH`:

```bash
PYTHONPATH=package_candidates/eml_records/src \
  python -m eml_records.cli validate path/to/records --strict
```

## CLI Examples

```bash
eml-records validate corpus/eml_function_classes_draft --json
eml-records validate corpus/eml_stochastic_hybrid_draft --family stochastic-hybrid --strict
eml-records validate record.json --family function-class
eml-records validate records/ --include "*.json" --exclude-dir node_modules
```

JSON output includes:

```json
{
  "scanned_file_count": 1,
  "record_count": 2,
  "valid_count": 2,
  "warning_count": 0,
  "failure_count": 0,
  "family_counts": {
    "FUNCTION_CLASS": 1,
    "UNKNOWN": 1
  }
}
```

Exit code behavior:

- `0` when no failures are present.
- nonzero in `--strict` mode when failures are present.
- non-strict mode may return `0` while still reporting warnings/failures for
  exploratory review.

## Scope

The package validates required fields, false guardrail booleans, allowed draft
statuses, `not_claimed` boundary concepts, JSON lists and nested lists, and
simple record-family-specific shape checks.

Supported families:

- Lane seed records
- Function-class records
- Stochastic/hybrid records
- Generic evidence records
- Unknown records

Family markers:

- `lane` or `draft_eml_seed`: lane seed
- `function_class`: function-class record
- `process_class`: stochastic/hybrid record
- `evidence_type` or `validation_trace`: evidence record
- no marker: unknown

## Limitations

- Schema and record-shape checks only.
- Does not execute MachLib harnesses.
- Does not validate theorem/proof content.
- Does not create release artifacts.
- Does not change Forge compiler behavior.
- Does not upload, deploy, or publish anything.
