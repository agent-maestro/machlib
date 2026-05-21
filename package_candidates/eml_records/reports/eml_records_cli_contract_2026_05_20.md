# eml-records CLI contract - 2026-05-20

## Commands

```bash
eml-records validate <path>
eml-records validate <path> --json
eml-records validate <path> --family function-class
eml-records validate <path> --family stochastic-hybrid
eml-records validate <path> --strict
eml-records validate <path> --include "*.json"
eml-records validate <path> --exclude-dir node_modules
```

## JSON Output

The CLI emits:

- `scanned_file_count`
- `record_count`
- `valid_count`
- `warning_count`
- `failure_count`
- `family_counts`
- `warnings`
- `failures`

## Exit Codes

- `0` when no strict failure blocks the command.
- nonzero when `--strict` is set and failures are present.

## Boundaries

The CLI validates local JSON record shape. It does not publish packages, upload
artifacts, check PyPI name availability, or validate theorem/proof truth.
