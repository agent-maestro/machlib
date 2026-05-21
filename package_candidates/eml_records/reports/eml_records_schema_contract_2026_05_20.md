# eml-records schema contract - 2026-05-20

## Generic Record Schema

Required fields:

- `record_id`
- `status`
- `public_ready`
- `upload_allowed`
- `release_ready`
- `mathlib_dependency`
- `forge_compiler_change_required`
- `hardware_required`
- `limitations`
- `not_claimed`

## Family Classifiers

- `LANE_SEED`: `lane` or `draft_eml_seed`
- `FUNCTION_CLASS`: `function_class`
- `STOCHASTIC_HYBRID`: `process_class`
- `EVIDENCE_RECORD`: `evidence_type` or `validation_trace`
- `UNKNOWN`: no family marker

## Family-Specific Checks

Function-class records require `function_class` and certificate shape fields.
Stochastic/hybrid records require `process_class`, certificate fields, and
stochastic no-overclaim boundary concepts.

## Required False Booleans

- `public_ready`
- `upload_allowed`
- `release_ready`
- `mathlib_dependency`
- `forge_compiler_change_required`
- `hardware_required`

## Status Values

Allowed values are `DRAFT_INTERNAL`, `DRAFT_INTERNAL_VALIDATED`, `OBSERVATION`,
`NEEDS_REVIEW`, and `BLOCKED_NO_GO`.

## JSON Output Contract

The CLI emits `scanned_file_count`, `record_count`, `valid_count`,
`warning_count`, `failure_count`, `family_counts`, `warnings`, and `failures`.
