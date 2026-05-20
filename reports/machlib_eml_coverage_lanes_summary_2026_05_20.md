# MachLib EML Coverage Lanes Summary (2026-05-20)

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## Existing Format Discovered

MachLib records use JSON with `schema_version`, `theorem`, `proofs`, `difficulty`, `common_mistakes`, `tactic_trace`, `structural_profile`, `relationships`, and `metadata` sections. The lane packet keeps that core shape and adds `draft_eml_seed` because the requested planning fields are not part of the older release schema.

## Lane Packet

- Lane 1, EML algebra core: 4 seeds.
- Lane 2, calculus and special functions: 3 seeds.
- Lane 3, discrete algorithms: 3 seeds.
- Lane 4, typeclass-lite structures: 3 seeds.
- Lane 5, proof and evidence records: 3 seeds.
- Lane 6, legacy compatibility: 3 seeds.

Total seed records: 19.

## Coverage Position

The packet is an expansion map, not a claim of complete coverage. Algebra identities and finite discrete transforms are the nearest-term lanes. Special functions require MachLib-owned primitives. Typeclass-lite and evidence lanes require schema design. Legacy compatibility remains opt-in only.
