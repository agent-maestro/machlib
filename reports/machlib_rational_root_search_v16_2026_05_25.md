# MachLib Rational Root Search v16

Date: 2026-05-25

Status: `MACHLIB_RATIONAL_ROOT_SEARCH_V16_READY`

## Scope

This is a bounded exact rational-root search over a small candidate
window. It emits v15-compatible factorization certificates when a
complete linear factorization is found, and exact blockers otherwise.

## Results

- Cases: 7
- Certificates generated: 6
- Blocked: 1

| case | status | roots | remaining | blocker |
| --- | --- | --- | --- | --- |
| `quadratic_two_integer_roots_v16` | CERTIFICATE_GENERATED | `[2, 3]` | `[1]` |  |
| `cubic_three_integer_roots_v16` | CERTIFICATE_GENERATED | `[1, 2, 3]` | `[1]` |  |
| `irreducible_over_rational_window_v16` | BLOCKED | `[]` | `[1, 0, 1]` | NO_COMPLETE_LINEAR_FACTORIZATION_FOUND_WITHIN_BOUND |
| `repeated_cubic_root_v16` | CERTIFICATE_GENERATED | `[2, 2, 2]` | `[1]` |  |
| `scaled_pair_v16` | CERTIFICATE_GENERATED | `[1, 4]` | `[2]` |  |
| `fractional_roots_v16` | CERTIFICATE_GENERATED | `[-1, '1/2']` | `[3]` |  |
| `constant_only_v16` | CERTIFICATE_GENERATED | `[]` | `[7]` |  |

## Boundary

- Bounded rational search only.
- No arbitrary factorization discovery claim.
- No general root-count theorem claim.
- No Forge compiler or eFrog behavior change.
- No public theorem/proof/open-problem claim.
