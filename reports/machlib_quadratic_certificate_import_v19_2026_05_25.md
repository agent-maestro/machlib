# MachLib Quadratic Certificate Import v19

Date: 2026-05-25

Status: `MACHLIB_ROOT_CERTIFICATE_PIPELINE_V19_V20_READY`

## Summary

v19 converts only residual quadratic rows with rational-square
discriminants into v15-compatible factorization certificates.

- Source cases: 10
- v18 quadratic classifications: 3
- v19 imported certificates: 1
- v19 validation failures: 0

| certificate | status | roots |
| --- | --- | --- |
| `quadratic_rational_square_outside_window_quadratic_import_v19` | PASS | `[7, 8]` |

## Boundary

- This is certificate conversion for rational-square quadratic residuals only.
- It does not claim arbitrary root discovery.
- It does not prove the general root-count theorem.
- It does not change Forge or eFrog behavior.
