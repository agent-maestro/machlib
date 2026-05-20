# MachLib Lane 3 Discrete Harness Results (2026-05-20)

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## finite_graph_path_check_v0
- Classification: FINITE_GRAPH_PATH_CHECK
- Status: PASS
- Checks: [{"actual": true, "expected": true, "query": "A->D"}, {"actual": false, "expected": false, "query": "D->A"}, {"actual": true, "convention": "zero-length path", "expected": true, "query": "A->A"}]
- Warnings: 0
- Failures: 0

## recurrence_fib_step_v0
- Classification: BOUNDED_RECURRENCE_STEP
- Status: PASS
- Checks: [{"actual": 1, "expected": 1, "n": 2}, {"actual": 2, "expected": 2, "n": 3}, {"actual": 3, "expected": 3, "n": 4}, {"actual": 5, "expected": 5, "n": 5}]
- Warnings: 0
- Failures: 0

## tiny_sat_clause_eval_v0
- Classification: FINITE_CLAUSE_EVAL
- Status: PASS
- Checks: [{"assignment": "assignment1", "clause_values": [true, true, true], "expected": true, "satisfied": true}, {"assignment": "assignment2", "clause_values": [true, true, false], "expected": false, "satisfied": false}]
- Warnings: 0
- Failures: 0
