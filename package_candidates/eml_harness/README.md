# eml-harness

`eml-harness` is a local draft package candidate for bounded harness result
records. It stores small local result summaries and does not execute the full
MachLib harness stack.

This package is not published, not uploaded, not release-ready, and not a public
theorem/proof/open-problem claim. It is not safety certification and not
production controller evidence.

## Local Use

```bash
python -m pip install -e package_candidates/eml_harness
eml-harness summarize result.json --json
PYTHONPATH=package_candidates/eml_harness/src python -m eml_harness.cli summarize result.json
```

## Scope

- Validate bounded harness result dictionaries.
- Summarize pass/fail counts.
- Avoid credentials, uploads, deploys, hardware commands, and token handling.
