# eml-records hardening report - 2026-05-20

## Scope

This local-only hardening pass improves the `eml-records` draft package
candidate without publishing, uploading, or creating release artifacts.

## Changes

- Adds explicit schema helper functions for required fields, false booleans,
  status checks, `not_claimed` concept checks, and family detection.
- Adds file/path validation entry points.
- Extends loaders with include filtering and skip-directory support.
- Extends CLI support for include/exclude directory options.
- Expands tests beyond the original draft coverage.

## Boundaries

This remains a local draft package candidate. It is not release-ready, not
upload-ready, and not a theorem/proof/open-problem validator.

## Next Safe Steps

- Add more corpus fixture snapshots.
- Add optional JSON-schema export.
- Review package API naming before any future publication task.
