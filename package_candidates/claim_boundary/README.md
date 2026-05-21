# claim-boundary draft

Local draft package candidate for scanning evidence artifacts for claim, action, readiness, and token-risk language.

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
python -m pip install -e package_candidates/claim_boundary
```

No upload, build, twine, or PyPI name check is required for local testing.

## Usage

```bash
claim-boundary scan .
claim-boundary scan . --json
claim-boundary scan . --include "*.md"
claim-boundary scan . --exclude-dir node_modules
claim-boundary scan . --fail-on suspicious
python -m claim_boundary.cli scan . --json
```

## JSON Output Example

```json
{
  "boundary_text_count": 1,
  "findings": [],
  "passed": true,
  "policy_text_count": 0,
  "scanned_file_count": 1,
  "suspicious_finding_count": 0,
  "token_like_secret_count": 0
}
```

## Exit Codes

- `0`: no suspicious findings, or `--fail-on never`
- `1`: suspicious findings exist and `--fail-on suspicious`

## Relationship To Monogate / MachLib

This draft extracts the claim/no-go scanner pattern used across Monogate and MachLib reports. It helps separate boundary text such as “not certified safety” from positive overclaims.

## Limitations

- String-pattern scanner only
- No package name availability check
- No publish or upload path
- No certification of a repository
- No public theorem/proof/open-problem claim
