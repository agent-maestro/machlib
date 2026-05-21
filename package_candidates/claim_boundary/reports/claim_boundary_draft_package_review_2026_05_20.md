# claim-boundary Draft Package Review - 2026-05-20

## Scope

Local draft package candidate for scanning evidence artifacts for claim, readiness, action, and token-risk language.

## Why This Package Candidate Exists

Monogate and MachLib reports repeatedly need to distinguish allowed boundary language from positive overclaims. This draft extracts that scanner pattern into a small local CLI/library.

## Source Tool Lineage

The package is inspired by guardrail grep patterns and no-go reports used across the MachLib evidence workbench, function-class harnesses, stochastic/hybrid frontier, and product-readiness packets.

## Relationship To Monogate Guardrail Stack

It is a local helper candidate only. It does not replace human review, release review, security review, or repository-specific validation.

## What It Detects

It detects positive theorem/open-problem/safety/production claims, upload/publish/deploy/action claims, forbidden true readiness booleans, and token-like strings. It separately classifies negated no-go text and policy boundary text.

## What It Does Not Claim

It does not claim public theorem/proof/open-problem results, certified safety, production readiness, or complete security coverage.

## Not Release-Ready

The package name availability was not checked, the package was not published, and no PyPI token was handled.

## No Publish Performed

No build upload, twine command, PyPI token handling, package publishing, or release artifact creation occurred.

## Next Hardening Steps

Add more fixture corpora, tune pattern severity, document integration boundaries, and review naming/license language before any separate approved PyPI task.
