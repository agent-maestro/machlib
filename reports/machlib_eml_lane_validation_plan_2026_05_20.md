# MachLib EML Lane Validation Plan (2026-05-20)

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## Required Local Checks

1. Validate JSON syntax for every file under `corpus/eml_lanes_draft`.
2. Run `python tools/check_zero_mathlib_dependency.py`.
3. Run `python tools/check_zero_mathlib_dependency.py --release-target`.
4. Run `python tools/check_zero_mathlib_dependency.py --repo-wide`.
5. Scan new files for forbidden public-readiness, upload, marketplace, token-like, and risky claim text.
6. For Lane 1, run exact-vs-numeric spot checks once an owned algebra validator exists.
7. For applicable lanes, run eFrog roundtrip and Forge parse checks once local validators accept the draft schema.

## Lane Notes

- Lane 1 can start with symbolic normalization and exact candidate solutions.
- Lane 2 needs MachLib-owned primitive definitions before release validation.
- Lane 3 can use finite witnesses and bounded evaluation tables.
- Lane 4 needs a structure layer with local law slots.
- Lane 5 needs proof-layer and evidence-row schema design.
- Lane 6 is compatibility planning only and never a default dependency path.

## No-Go Items

No Hugging Face upload, PETAL upload, package publish, hardware action, Forge compiler behavior change, public result claim, or token handling is part of this plan.
