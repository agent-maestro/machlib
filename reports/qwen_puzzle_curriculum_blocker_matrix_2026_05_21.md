# Qwen Puzzle Curriculum Blocker Matrix

Date: 2026-05-21

| Source | Blocker | Decision |
| --- | --- | --- |
| `accepted_internal_capcard_pack_rows.jsonl` row 2 | `validation_status=warn`, `solver_status=unknown` | still blocked |
| `accepted_internal_capcard_pack_rows.jsonl` row 3 | `validation_status=warn`, `solver_status=unknown` | still blocked |
| command-center pasted rows | exact current rows not used as direct evidence | stale reference only |

Exact fix list:

1. Repair or replace row 2 with accepted evidence.
2. Repair or replace row 3 with accepted evidence.
3. Add a human review note if an unknown solver status is intentionally bounded rather than repaired.
4. Re-run the marketplace validator.
