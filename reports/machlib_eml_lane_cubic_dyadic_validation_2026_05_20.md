# MachLib EML Lane Cubic Dyadic Validation (2026-05-20)

Tier: OBSERVATION
Status: DRAFT_INTERNAL

Record: `cubic_dyadic_equilibrium_v0`

## Spot Check

- `x + x = 2x` is classified as an identity.
- `x^3 = 2x` is classified as a constraint, not an identity.
- The normalized form contains `x * (x^2 - 2) = 0`.
- Candidate real solution strings are `-sqrt(2)`, `0`, and `sqrt(2)`.
- Numeric spot checks passed for `0`, `sqrt(2)`, and `-sqrt(2)`.
- The negative check rejects `x = 1`.

## Boundary

This is a validator spot check for a draft seed. It is not a theorem claim, not a proof claim, not an open-problem result, and not public-ready.
