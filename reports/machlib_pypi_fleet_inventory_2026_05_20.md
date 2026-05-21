# Monogate PyPI Fleet Inventory

Date: 2026-05-20
Phase: PHASE 1 - no token, no publish

| Package | Class | Local | PyPI | Version relation | Test | Build/twine | Upload now |
| --- | --- | --- | --- | --- | --- | --- | --- |
| monogate-graph | PUBLISHED_PACKAGE | 0.1.1 | 0.1.1 | local = PyPI | PASS: 12 passed | BUILD_AND_TWINE_CHECK_PASS | false |
| eml-units | PUBLISHED_PACKAGE | 0.1.0 | 0.1.0 | local = PyPI | PASS: 12 passed | BUILD_AND_TWINE_CHECK_PASS | false |
| eml-signal | PUBLISHED_PACKAGE | 0.1.1 | 0.1.1 | local = PyPI | PASS: 18 passed | BUILD_AND_TWINE_CHECK_PASS | false |
| eml-control | PUBLISHED_PACKAGE | 0.1.1 | 0.1.0 | local > PyPI | PASS: 18 passed | BUILD_AND_TWINE_CHECK_PASS | false |
| monogate-forge | PUBLISHED_PACKAGE | 0.12.1 | 0.12.1 | local = PyPI | PASS: 1049 passed | BUILD_AND_TWINE_CHECK_PASS | false |
| efrog | PUBLISHED_PACKAGE | 0.7.0 | 0.7.0 | local = PyPI | PASS: completed locally | BUILD_AND_TWINE_CHECK_PASS | false |
| monogate-forge-mcp | PUBLISHED_PACKAGE | 0.3.0 | 0.3.0 | local = PyPI | PASS: completed locally | BUILD_AND_TWINE_CHECK_PASS | false |
| monogate-capcard-cli | PUBLISHED_PACKAGE | 1.2.0 | 1.2.0 | local = PyPI | PASS: completed locally | BUILD_AND_TWINE_CHECK_PASS | false |
| eml-cost | PUBLISHED_PACKAGE | 0.20.2 | 0.20.2 | local = PyPI | PASS: 583 passed, 6 skipped | BUILD_AND_TWINE_CHECK_PASS | false |
| eml-stdlib | PUBLISHED_PACKAGE | 0.4.0 | 0.4.0 | local = PyPI | PASS: 11 passed | BUILD_AND_TWINE_CHECK_PASS | false |
| eml-cost-torch | HELD_BACK | 0.5.2 | 0.5.2 | local = PyPI | SKIPPED_HELD_BACK | BUILD_DRY_RUN_SKIPPED_HELD_BACK | false |
| zero-mathlib-checker | LOCAL_PACKAGE_CANDIDATE | 0.0.0.dev0 | none | no public PyPI project or not compared | PASS: 15 passed | BUILD_AND_TWINE_CHECK_PASS | false |
| claim-boundary | LOCAL_PACKAGE_CANDIDATE | 0.0.0.dev0 | none | no public PyPI project or not compared | PASS: 35 passed | BUILD_AND_TWINE_CHECK_PASS | false |
| eml-records | LOCAL_PACKAGE_CANDIDATE | 0.0.0.dev0 | none | no public PyPI project or not compared | PASS: 30 passed | BUILD_AND_TWINE_CHECK_PASS | false |
| review-branch-packet | LOCAL_PACKAGE_CANDIDATE | 0.0.0.dev0 | none | no public PyPI project or not compared | PASS: 41 passed | BUILD_AND_TWINE_CHECK_PASS | false |
| capcard-ai | UNKNOWN_NEEDS_REVIEW | 0.1.4 | 0.1.4 | local = PyPI | TEST_COMMAND_UNKNOWN | BUILD_DRY_RUN_SKIPPED_WITH_REASON | false |
| capcard-benchmark | UNKNOWN_NEEDS_REVIEW | 0.1.0 | none | no public PyPI project or not compared | TEST_COMMAND_UNKNOWN | BUILD_DRY_RUN_SKIPPED_WITH_REASON | false |
| blackwell-agent | UNKNOWN_NEEDS_REVIEW | 0.1.0 | none | no public PyPI project or not compared | TEST_COMMAND_UNKNOWN | BUILD_DRY_RUN_SKIPPED_WITH_REASON | false |
| eml-memory | UNKNOWN_NEEDS_REVIEW | 0.1.0 | 0.1.0 | local = PyPI | TEST_COMMAND_UNKNOWN | BUILD_DRY_RUN_SKIPPED_WITH_REASON | false |
| eml-memory-curate | UNKNOWN_NEEDS_REVIEW | 0.1.0 | 0.1.0 | local = PyPI | TEST_COMMAND_UNKNOWN | BUILD_DRY_RUN_SKIPPED_WITH_REASON | false |
| monogate | UNKNOWN_NEEDS_REVIEW | 2.5.0 | 2.5.0 | local = PyPI | TEST_COMMAND_UNKNOWN | BUILD_DRY_RUN_SKIPPED_WITH_REASON | false |
| monogate-core | UNKNOWN_NEEDS_REVIEW | 0.1.0 | none | no public PyPI project or not compared | TEST_COMMAND_UNKNOWN | BUILD_DRY_RUN_SKIPPED_WITH_REASON | false |
| capcard-distributed-sandbox | UNKNOWN_NEEDS_REVIEW | 0.1.0 | none | no public PyPI project or not compared | TEST_COMMAND_UNKNOWN | BUILD_DRY_RUN_SKIPPED_WITH_REASON | false |
| eml-genome | UNKNOWN_NEEDS_REVIEW | 0.2.0 | none | no public PyPI project or not compared | TEST_COMMAND_UNKNOWN | BUILD_DRY_RUN_SKIPPED_WITH_REASON | false |
| eml-rewrite | UNKNOWN_NEEDS_REVIEW | 0.1.0a0 | 0.6.0 | local < PyPI | TEST_COMMAND_UNKNOWN | BUILD_DRY_RUN_SKIPPED_WITH_REASON | false |

| machlib | BROAD_PACKAGE_CANDIDATE | none | not checked | not checked | PASS: zero-Mathlib gates | SKIPPED_NOT_APPROVED_FOR_MACHLIB_BOUNDARY_REVIEW | false |

## MachLib Future Publish Target

- Local package path: `/home/monogate/monogate/machlib` found.
- Pyproject: not found at MachLib repo root.
- Proposed boundary: undecided; must choose CLI/tools-only versus corpus/report/feed inclusion.
- Readiness: `NOT_READY_REQUIRES_BOUNDARY_API_LICENSE_PUBLIC_COPY_REVIEW`.
- Build dry-run: skipped; MachLib boundary review has not been approved.
- Publish now: false.

MachLib is desired for a future PyPI publish plan. MachLib is broader than zero-mathlib-checker. MachLib is not publish-ready. MachLib was not uploaded. MachLib name availability was not checked. MachLib build dry-run was skipped unless separately approved. MachLib requires public copy, package boundary, API, and license review.

No token was requested or received. No PyPI upload, package publish, or twine upload occurred.
