# eml-records

`eml-records` is a local draft package candidate for validating EML-style JSON
records used in the MachLib corpus.

This package is a local draft only. It is not published to PyPI. PyPI name
availability has not been checked. No PyPI token handling has occurred. This
draft is not release-ready, not upload-ready, and not a public
theorem/proof/open-problem claim.

## Local Use

Install from source only in a local development environment:

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
  exploratory local review.

## Scope

The draft validates required fields, false guardrail booleans, allowed draft
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

This is a schema and record-shape helper. It is not a theorem prover, not a
proof validator, not a release gate by itself, and not a publication approval
tool. It does not execute MachLib harnesses, check PyPI availability, create
release artifacts, or change Forge compiler behavior.
