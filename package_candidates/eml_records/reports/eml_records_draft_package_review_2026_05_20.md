# eml-records draft package review - 2026-05-20

## Scope

`eml-records` extracts local schema and validation utilities for EML-style JSON
records used by MachLib.

## Why This Package Candidate Exists

MachLib now has multiple local draft corpora. A small shared validator can make
record-shape checks reusable without pulling in harness execution or proof
claims.

## Source Validators It Draws From

- `tools/validate_eml_lane_seeds.py`
- `tools/validate_function_class_records.py`
- `tools/validate_stochastic_hybrid_records.py`

## What It Validates

- Required fields
- False guardrail booleans
- Allowed draft statuses
- `not_claimed` boundary concepts
- Basic family classification
- Function-class and stochastic/hybrid shape requirements

## What It Does Not Validate

- It does not prove theorems.
- It does not validate public proof readiness.
- It does not execute MachLib harnesses.
- It does not publish or upload package artifacts.

## Not Release-Ready

This is a local draft package candidate. PyPI name availability is
UNKNOWN_NOT_CHECKED.

## No Publish Performed

No package publish, PyPI upload, or PyPI token handling occurred.

## Next Hardening Steps

- Compare against more corpus fixtures.
- Add JSON schema export.
- Add richer no-go phrase classification.
- Freeze a public CLI contract only after a separate review.
