# zero-mathlib-checker Hardening Report - 2026-05-20

## Scope

This local-only hardening pass improves the draft scanner API, CLI flags, tests, and documentation without publishing or checking package name availability.

## Improvements

- Added `scan_path` API with recursive directory scanning.
- Added text suffix filtering and `--include` support.
- Added default skipped directories for caches, build outputs, virtual environments, and dependency folders.
- Added `--exclude-dir` support.
- Added explicit evidence classes for imports, from-imports, dot references, and dependency declarations.
- Kept stable nonzero exit behavior when dependency evidence is found.

## Boundary

The package remains draft-only. It is not release-ready, not upload-ready, and not a public certification tool.

## Next Safe Steps

- Add fixture corpus coverage.
- Review naming and license language.
- Run a separate human-approved name-availability check only if requested later.
