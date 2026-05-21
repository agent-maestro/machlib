# zero-mathlib-checker

`zero-mathlib-checker` is a pre-alpha package for scanning a repository or
fixture tree for direct Mathlib import/dependency evidence.

Mathlib is valuable. This tool is only for projects that intentionally choose a
no-Mathlib dependency boundary.

## Status

- Version: `0.0.1`
- Published for early testing.
- Not a theorem prover.
- Not a safety certifier.
- Not production controller evidence.
- Not a replacement for Mathlib.
- No public theorem/proof/open-problem claim.

## Install

```bash
python -m pip install zero-mathlib-checker
```

For repository development:

```bash
python -m pip install -e package_candidates/zero_mathlib_checker
```

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

The scanner recursively reads text-like files, skips common cache/build/vendor
directories, and detects:

- `IMPORT_MATHLIB`
- `FROM_MATHLIB`
- `MATHLIB_DOT_REFERENCE`
- `MATHLIB_DEPENDENCY_DECLARATION`

Policy or historical text can be ignored only when the line is explicitly
marked and `--allow-policy-text` is set.

## Relationship To Monogate/MachLib

This package is a small evidence-boundary helper used around Monogate/MachLib
workflows. It can support a no-Mathlib dependency policy, but it does not
replace repository-specific gates, review, or human judgment.

## Limitations

- String-pattern scanner only.
- Does not certify a repository.
- Does not validate proofs or theorem content.
- Does not upload, deploy, or publish anything.
- Does not handle credentials or tokens.
