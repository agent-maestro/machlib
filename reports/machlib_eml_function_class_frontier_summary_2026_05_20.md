# MachLib EML Function-Class Frontier Summary (2026-05-20)

## Scope

OBSERVATION-tier and DRAFT_INTERNAL. This packet explores EML records for D-finite, analytic, smooth, continuous, and boundary/non-example function classes without adding Mathlib dependency and without making public theorem, proof, open-problem, upload, package, or release claims.

## Why This Matters

Function-class metadata is a natural next layer after the six-lane EML corpus. It lets MachLib represent local symbolic evidence: finite ODE certificates, local series stubs, derivative-jet records, continuity templates, and relation boundaries. These are record-level scaffolds, not full real-analysis formalizations.

## D-Finite vs Analytic vs Smooth vs Continuous

- D-finite records use finite symbolic ODE certificates with polynomial coefficients.
- Analytic records use local series, Taylor-jet, or coefficient-pattern payloads.
- Smooth records use derivative towers, finite jets, and boundary checks.
- Continuous records use epsilon-delta, local-modulus, or discontinuity witness payloads.
- Boundary records prevent oversimplified subset claims: continuous does not imply smooth, smooth does not imply analytic, and analytic does not imply D-finite.

## Record Counts

- D-finite: 5
- Analytic: 4
- Smooth: 4
- Continuous: 4
- Boundary/non-example: 3
- Total: 20

## What Is Validated

The validator checks JSON parse, required fields, required false booleans, DRAFT_INTERNAL status, category minimums, function-class payload shape, limitation text, non-overclaim boundary relations, zero-Mathlib guardrails, no upload/release/public readiness flags, and token-like secret absence.

## What Is Not Claimed

This packet does not claim full real-analysis formalization, public theorem results, public proof results, open-problem results, external-library replacement, package release readiness, Hugging Face upload readiness, PETAL verification, CapCard certification, or command-center deployment.

## Zero-Mathlib Status

The existing zero-Mathlib checker passed in default, release-target, and repo-wide modes before this packet was created. The function-class records introduce no external formal-library dependency.

## Next Safe Experiments

- Add a finite ODE certificate parser.
- Normalize polynomial coefficient payloads.
- Add singularity/domain guard schemas.
- Add local series/radius evidence records.
- Add finite jet and local modulus validators.
- Later, generate local /tmp artifacts for eFrog/Forge probes without changing compiler behavior.
