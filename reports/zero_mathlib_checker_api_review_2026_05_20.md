# zero-mathlib-checker API Review

Date: 2026-05-20

Status: API_OK_FOR_DRY_RUN_REVIEW

This local-only review inspected the package API and CLI behavior. It did not publish, upload, check PyPI name availability, handle tokens, or create release artifacts.

## API Surface

- Package exports: `ScanResult`, `scan_path`, `scan_root`
- Scanner entrypoint: `zero_mathlib_checker.scanner.scan_path`
- Console script: `zero-mathlib-checker = zero_mathlib_checker.cli:main`
- CLI command: `zero-mathlib-checker scan <root>`
- CLI options: `--json`, `--allow-policy-text`, `--include`, `--exclude-dir`

## Checks

| Check | Result |
| --- | --- |
| scanner.scan_path exists | PASS |
| scan_root exists | PASS |
| JSON output behavior defined | PASS |
| evidence class names stable enough | PASS |
| include/exclude behavior documented | PASS |
| default skip dirs present in code | PASS |
| CLI scan command documented | PASS |
| exit codes documented | PASS |
| no token handling | PASS |
| no upload/publish action | PASS |

## Default Excluded Directories

`.git`, `.venv`, `__pycache__`, `node_modules`, `dist`, `build`, `.mypy_cache`, `.pytest_cache`

## Followups

- A future dry-run build review should verify installed console-script behavior in an isolated environment.
- A future API freeze should decide whether `Evidence` field names and `ScanResult.to_dict` output are final for public consumers.

No PyPI upload, token handling, package publish, or release artifact creation was performed.
