# zero-mathlib-checker CLI Contract - 2026-05-20

## Commands

```bash
zero-mathlib-checker scan <path>
zero-mathlib-checker scan <path> --json
zero-mathlib-checker scan <path> --allow-policy-text
zero-mathlib-checker scan <path> --include "*.lean"
zero-mathlib-checker scan <path> --exclude-dir node_modules
python -m zero_mathlib_checker.cli scan <path>
```

## Exit Behavior

- `0`: no dependency evidence found.
- `1`: dependency evidence found.

## JSON Contract

The JSON summary includes `root`, `scanned_files`, `skipped_files`, `direct_match_count`, `dependency_evidence_count`, `policy_text_count`, `passed`, and `evidence`.

## Evidence Classes

- `IMPORT_MATHLIB`
- `FROM_MATHLIB`
- `MATHLIB_DOT_REFERENCE`
- `MATHLIB_DEPENDENCY_DECLARATION`
