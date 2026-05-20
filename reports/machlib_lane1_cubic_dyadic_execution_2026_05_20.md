# MachLib Lane 1 Cubic Dyadic Execution (2026-05-20)

Tier: OBSERVATION
Status: DRAFT_INTERNAL

Record: `cubic_dyadic_equilibrium_v0`

## Execution

- Expression: `x^3 = x + x`
- Normalization: `x * (x^2 - 2) = 0`
- Candidate roots: `-sqrt(2)`, `0`, `sqrt(2)`
- Numeric spot checks pass for `0`, `sqrt(2)`, and `-sqrt(2)`.
- Negative checks reject `x = 1` and `x = 2`.

## Identity vs Constraint

`x + x = 2x` is an identity. `x^3 = 2x` is a constraint true only at selected roots in this draft check.

## Boundary

This is a local executable seed check. It is not a theorem claim, not a proof claim, not an open-problem result, and not public-ready.
