# MachLib Public Claim Boundary Matrix (2026-05-20)

## Scope

DRAFT, local only. No upload performed. No package publish performed. No release performed. No public theorem, proof, or open-problem claim is made by this matrix.

| Claim | Classification | Required qualifier |
| --- | --- | --- |
| Zero-Mathlib gate-backed claim | SAFE_PUBLIC_IF_AUDIT_ATTACHED | Must cite `tools/check_zero_mathlib_dependency.py` and current tree/release-target scope. |
| Six-lane DRAFT_INTERNAL corpus | SAFE_PUBLIC_WITH_DRAFT_QUALIFIER | Must say internal draft corpus, not public/release/upload ready. |
| eFrog zero-Mathlib default | SAFE_PUBLIC_WITH_VERSION_CONTEXT | Must state reviewed local/default output context. |
| eFrog/Forge roundtrip | SAFE_PUBLIC_WITH_LOCAL_VALIDATION_CONTEXT | Must say local draft/internal validation evidence. |
| Lane 2 symbolic rewrites | INTERNAL_OR_QUALIFIED_ONLY | Must say guarded symbolic placeholders, not real-analysis formalization. |
| Full mathlib replacement | NO_GO_PUBLIC | Do not claim replacement or equivalence. |
| Theorem/proof/open-problem claims | NO_GO_PUBLIC | Do not claim new public mathematical results. |
| HF dataset availability | NO_GO_UNLESS_UPLOADED_AND_APPROVED | Must not imply public dataset availability before approval and upload. |
| Package release | NO_GO_UNLESS_RELEASE_APPROVED | Must not imply package release before explicit release approval. |
| Command-center feed | INTERNAL_ONLY | Must remain internal display language. |

## Public-Safe Copy Pattern

Use:

> MachLib is zero-Mathlib in the current public default tree and release target, gate-backed by local audit tooling.

Avoid:

> MachLib replaces mathlib or establishes public proof results.

## Internal-Only Copy Pattern

Use:

> DRAFT_INTERNAL six-lane EML corpus with local validation and roundtrip evidence.

Avoid:

> Public-ready dataset, upload-ready dataset, release-ready package, public certification, or public verification.
