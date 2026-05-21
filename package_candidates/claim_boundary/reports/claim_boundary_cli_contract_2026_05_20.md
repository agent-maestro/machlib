# claim-boundary CLI Contract - 2026-05-20

## CLI Commands

```bash
claim-boundary scan <path>
claim-boundary scan <path> --json
claim-boundary scan <path> --include "*.md"
claim-boundary scan <path> --exclude-dir node_modules
claim-boundary scan <path> --fail-on suspicious
python -m claim_boundary.cli scan <path>
```

## JSON Schema

The JSON summary includes `scanned_file_count`, `skipped_file_count`, `suspicious_finding_count`, `boundary_text_count`, `policy_text_count`, `token_like_secret_count`, `passed`, and `findings`.

## Finding Classes

The scanner emits public theorem, open problem, certified safety, production controller, CapCard, PETAL, package publish, Hugging Face upload, PETAL/API upload, command-center deploy, Forge compiler change, hardware action, readiness boolean, token-like secret, policy boundary, and negated no-go classes.

## Exit Codes

- `0`: no suspicious findings, or `--fail-on never`
- `1`: suspicious findings exist and `--fail-on suspicious`

## Allowed Boundary Text

Negated statements such as “not certified safety”, “no package publish performed”, and `public_ready: false` are boundary text and do not count as suspicious findings.

## Suspicious Finding Behavior

Positive claims and forbidden true booleans count as suspicious findings.
