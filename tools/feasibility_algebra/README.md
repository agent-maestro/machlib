# Feasibility Algebra Stress Lab

Internal research tooling for separating formal asymptotic labels from bounded
resource feasibility. The central adversarial example is `n^1000`: polynomial
in the abstract, but absurd under ordinary resource profiles almost
immediately.

This is not a theorem prover, not a new certified algebra, not a replacement
for complexity theory, and not production controller evidence.

Run:

```bash
python -m tools.feasibility_algebra.cli run-stress \
  --out-dir product_readiness/feasibility_stress_lab_2026_05_23 \
  --strict
```
