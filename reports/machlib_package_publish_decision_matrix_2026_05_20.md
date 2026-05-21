# MachLib Package Publish Decision Matrix

Date: 2026-05-20
Tier: OBSERVATION

| Rank | Candidate | Publish readiness | Strengths | Main blockers | Next safe task |
| ---: | --- | --- | --- | --- | --- |
| 1 | zero-mathlib-checker | NEAREST_CANDIDATE_BUT_NOT_APPROVED | narrow scope; 15 tests; hardened draft; clear CLI | name check, license review, public copy review, API freeze, dry-run build review, human approval | M053_ZERO_MATHLIB_CHECKER_PUBLIC_COPY_LICENSE_API_REVIEW_NO_PUBLISH |
| 2 | claim-boundary | NOT_READY_NEEDS_HARDENING | useful boundary scanner; 35 tests | hardening pass, license review, public copy review | M052A_CLAIM_BOUNDARY_HARDENING_NO_PUBLISH |
| 3 | eml-records | NOT_READY_NEEDS_API_COMPAT_REVIEW | hardened draft; 30 tests; schema/loader/CLI coverage | schema API and compatibility review | EML_RECORDS_API_COMPAT_LICENSE_REVIEW_NO_PUBLISH |
| 4 | review-branch-packet | NOT_READY_NEEDS_OPERATIONAL_BOUNDARY_REVIEW | hardened draft; 41 tests; read-only packet workflow | operational command boundary review | REVIEW_BRANCH_PACKET_OPERATIONAL_BOUNDARY_REVIEW_NO_PUBLISH |
| 5 | machlib-workbench | NOT_READY_NEEDS_API_DESIGN | central workbench/service direction | package boundary and API design | MACHLIB_WORKBENCH_API_DESIGN_NO_PUBLISH |
| 6 | service/revenue path | SERVICE_PATH_NOT_PACKAGE_PUBLISH_DECISION | closest revenue path via review service and Evidence Workbench | service boundary and public copy review | EVIDENCE_WORKBENCH_SERVICE_BOUNDARY_REVIEW_NO_DEPLOY |

Every row has `publish_now: false`, `pypi_token_required_now: false`, `package_name_availability: UNKNOWN_NOT_CHECKED`, and `release_artifacts_created: false` in the JSON matrix.

## Why No Name Check Or Token Handling

This review is intentionally before a publish gate. Checking package-name availability or handling PyPI tokens would create a different operational task and requires separate explicit approval. The current output only records readiness blockers and next safe local review steps.
