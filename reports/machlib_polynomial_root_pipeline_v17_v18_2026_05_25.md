# MachLib Polynomial Root Pipeline v17/v18

Date: 2026-05-25

Status: `MACHLIB_POLYNOMIAL_ROOT_PIPELINE_V17_V18_READY`

## Scope

v17 adds residual packets for every bounded rational-root search case.
v18 adds a small quadratic classifier for residual degree-two cases.
This is still a bounded exact arithmetic pipeline, not arbitrary root discovery.

## Summary

- Cases: 10
- Certificates generated: 6
- Blocked: 4
- Residual packets: 10
- Quadratic classifications: 3

| case | search | residual | quadratic classification | blocker |
| --- | --- | --- | --- | --- |
| `quadratic_two_integer_roots_v16` | CERTIFICATE_GENERATED | `[1]` | NOT_QUADRATIC | RESIDUAL_NOT_DEGREE_TWO |
| `cubic_three_integer_roots_v16` | CERTIFICATE_GENERATED | `[1]` | NOT_QUADRATIC | RESIDUAL_NOT_DEGREE_TWO |
| `irreducible_over_rational_window_v16` | BLOCKED | `[1, 0, 1]` | NEGATIVE_DISCRIMINANT_NO_REAL_ROOTS_IN_QUADRATIC_STUB | NO_COMPLETE_LINEAR_FACTORIZATION_FOUND_WITHIN_BOUND |
| `repeated_cubic_root_v16` | CERTIFICATE_GENERATED | `[1]` | NOT_QUADRATIC | RESIDUAL_NOT_DEGREE_TWO |
| `scaled_pair_v16` | CERTIFICATE_GENERATED | `[2]` | NOT_QUADRATIC | RESIDUAL_NOT_DEGREE_TWO |
| `fractional_roots_v16` | CERTIFICATE_GENERATED | `[3]` | NOT_QUADRATIC | RESIDUAL_NOT_DEGREE_TWO |
| `constant_only_v16` | CERTIFICATE_GENERATED | `[7]` | NOT_QUADRATIC | RESIDUAL_NOT_DEGREE_TWO |
| `quadratic_irrational_roots_v18` | BLOCKED | `[-2, 0, 1]` | IRRATIONAL_ROOTS_BLOCKED_IN_RATIONAL_LAYER | NO_COMPLETE_LINEAR_FACTORIZATION_FOUND_WITHIN_BOUND |
| `quadratic_large_rational_root_outside_window_v18` | BLOCKED | `[10, 1]` | NOT_QUADRATIC | NO_COMPLETE_LINEAR_FACTORIZATION_FOUND_WITHIN_BOUND |
| `quadratic_rational_square_outside_window_v18` | BLOCKED | `[56, -15, 1]` | RATIONAL_DISCRIMINANT_SQUARE_FACTORABLE | NO_COMPLETE_LINEAR_FACTORIZATION_FOUND_WITHIN_BOUND |

## Boundary

- Bounded rational search only.
- Quadratic classifier only classifies residuals; it does not prove a general root-count theorem.
- No arbitrary factorization discovery claim.
- No Forge compiler or eFrog behavior change.
- No public theorem/proof/open-problem claim.
