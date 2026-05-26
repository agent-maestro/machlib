# MachLib Degree/Root Evidence Card v20

Status: `MACHLIB_ROOT_CERTIFICATE_PIPELINE_V19_V20_READY`

This internal card is shaped for Explorer/CapCard consumption. It
summarizes coefficient inputs, found roots, residuals, blockers, and
safe certificate conversion status.

| case | status | roots | residual | classification |
| --- | --- | --- | --- | --- |
| `quadratic_two_integer_roots_v16` | V16_CERTIFICATE_AVAILABLE | `[2, 3]` | `[1]` | NOT_QUADRATIC |
| `cubic_three_integer_roots_v16` | V16_CERTIFICATE_AVAILABLE | `[1, 2, 3]` | `[1]` | NOT_QUADRATIC |
| `irreducible_over_rational_window_v16` | V18_CLASSIFIED_BLOCKER | `[]` | `[1, 0, 1]` | NEGATIVE_DISCRIMINANT_NO_REAL_ROOTS_IN_QUADRATIC_STUB |
| `repeated_cubic_root_v16` | V16_CERTIFICATE_AVAILABLE | `[2, 2, 2]` | `[1]` | NOT_QUADRATIC |
| `scaled_pair_v16` | V16_CERTIFICATE_AVAILABLE | `[1, 4]` | `[2]` | NOT_QUADRATIC |
| `fractional_roots_v16` | V16_CERTIFICATE_AVAILABLE | `[-1, '1/2']` | `[3]` | NOT_QUADRATIC |
| `constant_only_v16` | V16_CERTIFICATE_AVAILABLE | `[]` | `[7]` | NOT_QUADRATIC |
| `quadratic_irrational_roots_v18` | V18_CLASSIFIED_BLOCKER | `[]` | `[-2, 0, 1]` | IRRATIONAL_ROOTS_BLOCKED_IN_RATIONAL_LAYER |
| `quadratic_large_rational_root_outside_window_v18` | BOUNDED_SEARCH_BLOCKER | `[1]` | `[10, 1]` | NOT_QUADRATIC |
| `quadratic_rational_square_outside_window_v18` | V19_CERTIFICATE_CONVERTIBLE | `[]` | `[56, -15, 1]` | RATIONAL_DISCRIMINANT_SQUARE_FACTORABLE |

## Boundary

- Internal evidence card only.
- No public-ready or marketplace-ready claim.
- No public theorem/proof/open-problem claim.
