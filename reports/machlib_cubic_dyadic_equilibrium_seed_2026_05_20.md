# Cubic Dyadic Equilibrium Seed (2026-05-20)

Tier: OBSERVATION
Status: DRAFT_INTERNAL

Record: `cubic_dyadic_equilibrium_v0`
Path: `corpus/eml_lanes_draft/lane_1_algebra_core/cubic_dyadic_equilibrium_v0.json`

## Object

Expression: `x^3 = x + x`
Normalized form: `x * (x^2 - 2) = 0`
Candidate real solutions: `-sqrt(2)`, `0`, `sqrt(2)`

## Framing

This is a bounded EML algebra seed where nonlinear amplification equals dyadic duplication. The identity `x + x = 2x` is separated from the constraint `x^3 = 2x`, which is true only at the listed candidate real solutions.

## Checks

- Recognize `x + x = 2x`.
- Recognize `x^3 = 2x` is not an identity.
- Factor `x^3 - 2x` as `x * (x^2 - 2)`.
- Return a finite candidate real solution set.
- Preserve explicit limitations and no public result claim.

## Not Claimed

- Not a new theorem.
- Not a physical claim.
- Not a public proof result.
- Not a theorem-prover benchmark claim.
