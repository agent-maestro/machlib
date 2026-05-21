# zero-mathlib-checker draft

Local draft package candidate for scanning a repository or fixture tree for direct Mathlib import/dependency evidence.

This package candidate is not published, not release-ready, not upload-ready, and has not had its package name availability checked. No PyPI token is needed or handled.

## Local Draft Status

- Version: `0.0.0.dev0`
- Package name availability: `UNKNOWN_NOT_CHECKED`
- Publish status: no package publish performed
- Upload status: no PyPI upload performed
- Token status: no PyPI token handling performed
- Release status: not release-ready

## Install From Source Locally

Use a local editable install only after human review:

```bash
python -m pip install -e package_candidates/zero_mathlib_checker
```

No upload, build, or twine command is required for local testing.

## Usage

```bash
zero-mathlib-checker scan .
zero-mathlib-checker scan . --json
zero-mathlib-checker scan . --allow-policy-text
zero-mathlib-checker scan . --include "*.lean"
zero-mathlib-checker scan . --exclude-dir node_modules
python -m zero_mathlib_checker.cli scan . --json
```

## JSON Output Example

```json
{
  "dependency_evidence_count": 0,
  "direct_match_count": 0,
  "evidence": [],
  "passed": true,
  "policy_text_count": 0,
  "root": "/path/to/repo",
  "scanned_files": 1,
  "skipped_files": 0
}
```

## Exit Codes

- `0`: no dependency evidence found
- `1`: dependency evidence found

## Scanner Scope

The scanner recursively reads text-like files, skips common cache/build/vendor directories, and detects:

- `IMPORT_MATHLIB`
- `FROM_MATHLIB`
- `MATHLIB_DOT_REFERENCE`
- `MATHLIB_DEPENDENCY_DECLARATION`

Policy or historical text can be ignored only when the line is explicitly marked and `--allow-policy-text` is set.

## Relation To MachLib

This draft is inspired by MachLib's local zero-Mathlib checker, but it is a smaller package-shaped prototype. It does not replace the repository gate.

## Limitations

- String-pattern scanner only
- No package name availability check
- No publish or upload path
- No certification of a repository
- No theorem/proof/open-problem claim
