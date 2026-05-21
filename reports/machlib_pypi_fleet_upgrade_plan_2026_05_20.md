# Monogate PyPI Fleet Upgrade Plan

Phase: PHASE 1 - draft plan only.

## Upgrade Candidates

- `eml-control` `0.1.1` > PyPI `0.1.0`; tests and build/twine dry-run passed; still requires explicit Phase 2 approval and temporary PyPI token.

## Blocked Packages

- `monogate-graph`: NOT_UPLOADABLE_VERSION_NOT_GREATER; blockers: local version equals PyPI version; duplicate older migration dry-run path exists at monogate-graph 0.1.0
- `eml-units`: NOT_UPLOADABLE_VERSION_NOT_GREATER; blockers: local version equals PyPI version
- `eml-signal`: NOT_UPLOADABLE_VERSION_NOT_GREATER; blockers: local version equals PyPI version
- `monogate-forge`: NOT_UPLOADABLE_VERSION_NOT_GREATER; blockers: local version equals PyPI version
- `efrog`: NOT_UPLOADABLE_VERSION_NOT_GREATER; blockers: local version equals PyPI version
- `monogate-forge-mcp`: NOT_UPLOADABLE_VERSION_NOT_GREATER; blockers: local version equals PyPI version
- `monogate-capcard-cli`: NOT_UPLOADABLE_VERSION_NOT_GREATER; blockers: local version equals PyPI version
- `eml-cost`: NOT_UPLOADABLE_VERSION_NOT_GREATER; blockers: local version equals PyPI version; older exploration eml-cost 0.1.0a0 exists and is not selected
- `eml-stdlib`: NOT_UPLOADABLE_VERSION_NOT_GREATER; blockers: local version equals PyPI version
- `eml-cost-torch`: HELD_BACK_DO_NOT_PUBLISH; blockers: held back for separate license/readme/package-contract review and PyTorch/CUDA dependency review
- `zero-mathlib-checker`: NEW_PROJECT_REQUIRES_NAME_APPROVAL; blockers: new project requires name approval; publish gate closed; local package candidate publish gate remains closed
- `claim-boundary`: NEW_PROJECT_REQUIRES_NAME_APPROVAL; blockers: local draft not approved for PyPI; publish gate closed; local package candidate publish gate remains closed
- `eml-records`: NEW_PROJECT_REQUIRES_NAME_APPROVAL; blockers: new project requires name/API/license approval; publish gate closed; local package candidate publish gate remains closed
- `review-branch-packet`: NEW_PROJECT_REQUIRES_NAME_APPROVAL; blockers: new project requires name/API/operational-boundary approval; publish gate closed; local package candidate publish gate remains closed
- `capcard-ai`: NOT_UPLOADABLE_VERSION_NOT_GREATER; blockers: discovered package outside named M053 fleet; local version equals PyPI version
- `capcard-benchmark`: UNKNOWN_NEEDS_REVIEW; blockers: discovered package outside named M053 fleet; public PyPI JSON returned 404
- `blackwell-agent`: UNKNOWN_NEEDS_REVIEW; blockers: discovered package outside named M053 fleet; public PyPI JSON returned 404
- `eml-memory`: NOT_UPLOADABLE_VERSION_NOT_GREATER; blockers: discovered package outside named M053 fleet; local version equals PyPI version
- `eml-memory-curate`: NOT_UPLOADABLE_VERSION_NOT_GREATER; blockers: discovered package outside named M053 fleet; local version equals PyPI version
- `monogate`: NOT_UPLOADABLE_VERSION_NOT_GREATER; blockers: discovered package outside named M053 fleet; local version equals PyPI version
- `monogate-core`: UNKNOWN_NEEDS_REVIEW; blockers: discovered package outside named M053 fleet; public PyPI JSON returned 404
- `capcard-distributed-sandbox`: UNKNOWN_NEEDS_REVIEW; blockers: discovered sandbox package outside named M053 fleet; public PyPI JSON returned 404
- `eml-genome`: UNKNOWN_NEEDS_REVIEW; blockers: discovered package outside named M053 fleet; public PyPI JSON returned 404
- `eml-rewrite`: NOT_UPLOADABLE_LOCAL_VERSION_LOWER; blockers: discovered package outside named M053 fleet; local version is lower than PyPI version 0.6.0

Held-back package: `eml-cost-torch`, held back for separate license/readme/package-contract review and PyTorch/CUDA dependency review.

## MachLib Future Publish Target

`machlib` is now included as a desired future PyPI target, but it is broader than `zero-mathlib-checker` and is not ready for publication.

MachLib is desired for a future PyPI publish plan. MachLib is broader than zero-mathlib-checker. MachLib is not publish-ready. MachLib was not uploaded. MachLib name availability was not checked. MachLib build dry-run was skipped unless separately approved. MachLib requires public copy, package boundary, API, and license review.

Blockers:
- package boundary review required
- public copy review required
- license review required
- API surface review required
- no-public-claim review required
- build dry-run not yet approved
- explicit human publish approval required

Proposed CLI surface for later review: `machlib check-zero-mathlib`, `machlib validate-lanes`, `machlib validate-function-classes`, `machlib validate-stochastic-hybrid`, `machlib build-workbench`, and `machlib build-phase-spine`.
