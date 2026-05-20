# MachLib Public-Safe Hugging Face Card Review (2026-05-20)

## Scope

DRAFT, local only. No Hugging Face upload performed. No Hugging Face API call performed. No package publish performed. No release performed. No public theorem, proof, or open-problem claim is made by this review.

## Card Posture

The card should be drafted as a future-review artifact, not as evidence of dataset availability. It must say that human approval is required before upload and that the current six-lane corpus remains DRAFT_INTERNAL.

## Required Card Elements

- Dataset/card name placeholder.
- Intended use.
- Not intended use.
- Zero-Mathlib dependency statement.
- DRAFT_INTERNAL corpus status.
- Limitations.
- No public proof claim.
- No theorem-prover claim.
- No mathlib-equivalence claim.
- No upload performed.
- Human approval required before upload.

## Safe Card Summary

MachLib is a machine-native Lean/EML corpus and tooling project. The current public default tree and release target are zero-Mathlib gate-backed by local audit tooling. The six-lane EML corpus is an internal draft validation corpus and is not a public dataset release.

## Required Limitations

- Lane 2 symbolic special-function rewrites are draft placeholders with explicit guards.
- The corpus does not claim real-analysis formalization.
- The corpus does not claim mathlib equivalence.
- The corpus does not claim public proof status.
- Failed attempts and evidence records are tracked as records, not accepted results.
- Legacy compatibility remains opt-in only and is not a release dependency.

## Upload Boundary

Before any Hugging Face publication, require:

- human approval,
- final claim audit,
- zero-Mathlib gate rerun,
- token handling review outside this task,
- package/public/release readiness decision,
- explicit confirmation that the card does not imply certification, PETAL public verification, or public theorem status.
