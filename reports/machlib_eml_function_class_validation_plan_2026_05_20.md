# MachLib EML Function-Class Validation Plan (2026-05-20)

## Scope

DRAFT_INTERNAL validation plan. This plan does not upload, publish, push, deploy, change Forge behavior, or make public theorem/proof/open-problem claims.

## Current Validation

The local validator checks:

- JSON parse for records and manifests.
- Minimum record count and category minimums.
- Required field presence.
- Required false booleans.
- DRAFT_INTERNAL status.
- Function-class payload shape.
- Limitation text.
- Boundary non-overclaim relation payloads.
- No external formal-library dependency strings.
- No token-like secrets.

## Future Validation

- Symbolic record validation for D-finite ODE payloads.
- Finite ODE parser for order and polynomial coefficients.
- Analytic local series schema and radius metadata checks.
- Smooth finite-jet and boundary derivative checks.
- Continuity epsilon-delta and local-modulus schema checks.
- eFrog default zero-Mathlib rendering check.
- Forge local artifact probe that treats expected unsupported draft schema as warning.
- Guardrails against public proof claims, upload readiness, release readiness, package publish, and command-center deploy.

## No-Go Boundary

No function-class record should become public-ready, upload-ready, release-ready, or proof/result-bearing without explicit future approval and stronger evidence.
