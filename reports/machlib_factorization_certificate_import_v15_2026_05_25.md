# MachLib Factorization Certificate Import v15

Date: 2026-05-25

Status: `MACHLIB_FACTORIZATION_CERTIFICATE_IMPORT_V15_READY`

## Scope

This validates explicit factorization certificates for nonzero constants
times linear factors. It does not discover factorizations and does not
prove the arbitrary root-count target.

## Results

- Certificates: 7
- PASS: 7
- FAIL: 0
- WARNINGS: 1

| certificate | status | degree | dedup roots | notes |
| --- | --- | ---: | ---: | --- |
| `linear_pair_distinct_v15` | PASS | 2 | 2 | ok |
| `repeated_cubic_v15` | PASS | 3 | 1 | repeated roots deduplicated |
| `scaled_pair_v15` | PASS | 2 | 2 | ok |
| `constant_only_v15` | PASS | 0 | 0 | ok |
| `staged_triple_linear_v15` | PASS | 3 | 3 | ok |
| `fractional_roots_v15` | PASS | 2 | 2 | ok |
| `linear_known_quadratic_shape_v15` | PASS | 3 | 3 | ok |

## Boundary

- No arbitrary root discovery claim.
- No `RootCountInductionTarget` proof claim.
- No Forge compiler or eFrog behavior change.
- No public theorem/proof/open-problem claim.
- No package publish, PETAL/API upload, Hugging Face upload, or marketplace modification.
