# hybrid-trace-eml

`hybrid-trace-eml` is a local draft package candidate for bounded hybrid trace
utilities: increment reconstruction, transition extraction, transition matrix
summaries, and alignment metadata.

This package is not published, not uploaded, not release-ready, and not a public
theorem/proof/open-problem claim. It is not stochastic calculus formalization,
not an SDE theorem, not a Markov theorem, not safety certification, and not a
production controller.

## Local Use

```bash
python -m pip install -e package_candidates/hybrid_trace_eml
hybrid-trace-eml summarize trace.json --json
PYTHONPATH=package_candidates/hybrid_trace_eml/src python -m hybrid_trace_eml.cli summarize trace.json
```

## Scope

- Compute increments from numeric samples.
- Extract adjacent transitions.
- Count transition pairs.
- Emit local JSON summaries without network or upload actions.
