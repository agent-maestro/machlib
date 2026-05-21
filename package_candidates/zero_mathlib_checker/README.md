# zero-mathlib-checker draft

Local draft package candidate for scanning a repository or fixture tree for direct Mathlib import/dependency evidence.

This package candidate is not published, not release-ready, not upload-ready, and has not had its package name availability checked. No PyPI token is needed or handled.

## Local examples

```bash
zero-mathlib-checker scan .
zero-mathlib-checker scan . --json
zero-mathlib-checker scan . --allow-policy-text
```

## Boundary

This draft does not claim theorem/proof/open-problem results and does not certify any repository. It only reports bounded local string-pattern evidence.
