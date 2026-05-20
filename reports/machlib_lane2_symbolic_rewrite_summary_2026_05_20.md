# MachLib Lane 2 symbolic rewrite summary

Date: 2026-05-20
Tier: OBSERVATION
Scope: local-only guarded symbolic rewrite checks for Lane 2 draft primitives.

## Inputs consumed
- Lane 2 draft seed records.
- `primitive_spec_draft_2026_05_20.json`.

## Lane 2 seed count
- Seeds analyzed: 3
- Passed: 3
- Warned: 3
- Failed: 0

## Guarded rewrite summary
- `log(exp(x)) -> x` only with `FORMAL_SYMBOLIC_INVERSE_GUARD`.
- `exp(log(x)) -> x` only with `POSITIVE_DOMAIN_GUARD`.
- `sin(x)^2 + cos(x)^2 -> 1` only with `TRIG_SYMBOLIC_IDENTITY_GUARD`.
- `sqrt(x)^2 -> x` only with `NONNEGATIVE_DOMAIN_GUARD`.

## Blocked unsafe rewrite summary
- Unguarded rewrites are blocked.
- `sqrt(x^2) -> x` is blocked because sign information is missing.
- `sqrt(x^2) -> abs(x)` is not accepted without structure/proof-layer design.

## Primitive needs
- exp/log/sin/cos/pow/sqrt symbolic primitives.
- symbolic domain guard primitive.

## Zero-Mathlib status
- PASS

## Remaining no-go gates
- No uploads, package publishing, hardware action, compiler behavior change, or public proof/open-problem claim.
