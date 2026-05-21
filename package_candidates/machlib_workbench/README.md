# machlib-workbench

`machlib-workbench` is a local draft package candidate for summarizing MachLib
evidence-workbench outputs. It is a small report collector, not a deploy tool
and not the full MachLib repository.

This package is not published, not uploaded, not release-ready, and not a public
theorem/proof/open-problem claim. It does not certify safety, does not describe
a production controller, and does not claim that MachLib replaces mathlib.

## Local Use

```bash
python -m pip install -e package_candidates/machlib_workbench
machlib-workbench summarize reports --json
PYTHONPATH=package_candidates/machlib_workbench/src python -m machlib_workbench.cli summarize reports
```

## Scope

- Count local evidence/report files by suffix.
- Emit a bounded JSON or text summary.
- Avoid credentials, network calls, deploys, uploads, and hardware actions.

## Limitations

This draft does not run MachLib harnesses, does not deploy Command Center, does
not upload to PyPI, does not handle tokens, and does not create release
artifacts in the repository.
