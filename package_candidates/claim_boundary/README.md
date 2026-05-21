# claim-boundary

`claim-boundary` is a pre-alpha package for scanning evidence artifacts for
claim, action, readiness, and token-risk language.

It helps separate boundary text such as “not a safety certificate” from positive
overclaims. It is not a theorem prover, not a safety certifier, not production
controller evidence, not a replacement for Mathlib, and not a public
theorem/proof/open-problem claim.

## Status

- Version: `0.0.1`
- Published for early testing.
- Intended for local review workflows and CI-style checks.
- Does not upload, deploy, publish, or handle tokens.

## Install

```bash
python -m pip install claim-boundary
```

For repository development:

```bash
python -m pip install -e package_candidates/claim_boundary
```

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

## Relationship To Monogate/MachLib

This package extracts the claim/no-go scanner pattern used across Monogate and
MachLib reports. It is evidence tooling for public-copy and guardrail review,
not a certification authority.

## Limitations

- String-pattern scanner only.
- Does not prove or disprove claims.
- Does not certify safety.
- Does not execute deployments or uploads.
- Does not manage credentials or tokens.
