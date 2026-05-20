# MachLib Lane 4 Typeclass-Lite Results (2026-05-20)

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## typeclass_lite_magma_record_v0
- Classification: TYPECLASS_LITE_MAGMA_RECORD
- Status: PASS
- Fixture: {"carrier": [0, 1, 2], "operation": "add_mod_3", "operation_table": [[0, 1, 2], [1, 2, 0], [2, 0, 1]]}
- Checks: [{"actual": true, "expected": true, "name": "closure"}, {"actual": true, "expected": true, "name": "operation_table_exists"}, {"actual": false, "expected": false, "name": "associativity_claimed", "note": "not claimed for magma-lite"}, {"actual": false, "expected": false, "name": "identity_claimed", "note": "not claimed for magma-lite"}]
- Warnings: 0
- Failures: 0

## typeclass_lite_monoid_record_v0
- Classification: TYPECLASS_LITE_MONOID_RECORD
- Status: PASS
- Fixture: {"carrier": [0, 1, 2], "identity": 0, "operation": "add_mod_3"}
- Checks: [{"actual": true, "expected": true, "name": "closure"}, {"actual": true, "expected": true, "name": "associativity"}, {"actual": true, "expected": true, "name": "identity_left_right"}, {"actual": false, "expected": false, "name": "imported_hierarchy_claimed"}]
- Warnings: 0
- Failures: 0

## typeclass_lite_ordered_carrier_v0
- Classification: TYPECLASS_LITE_ORDERED_CARRIER
- Status: PASS
- Fixture: {"carrier": [0, 1, 2], "relation": "integer_lte_restricted"}
- Checks: [{"actual": true, "expected": true, "name": "reflexive"}, {"actual": true, "expected": true, "name": "antisymmetric"}, {"actual": true, "expected": true, "name": "transitive"}, {"actual": true, "expected": true, "name": "total", "note": "finite ordered-carrier convention"}, {"actual": false, "expected": false, "name": "imported_hierarchy_claimed"}]
- Warnings: 0
- Failures: 0
