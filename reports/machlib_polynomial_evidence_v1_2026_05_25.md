# MachLib Polynomial Evidence v1

Date: 2026-05-25

Status: `MACHLIB_POLYNOMIAL_EVIDENCE_V1_READY`

## Purpose

This packet turns the finite-root foothold from the analytic identity
feasibility pass into a reusable MachLib substrate: a tiny polynomial AST,
an evaluator, and checked root facts.

It does not claim analytic continuation, infinite zero-set behavior, or a
proved analytic identity theorem.

## Checked Facts

- `poly_eval_zero`
  - Lean: `MachLib.PolynomialEvidence.Poly.eval_zero`
  - statement: `eval zero x = 0`
  - meaning: The explicit zero polynomial evaluates to zero at every input.
- `poly_eval_var`
  - Lean: `MachLib.PolynomialEvidence.Poly.eval_var`
  - statement: `eval var x = x`
  - meaning: The variable polynomial evaluates to the supplied input.
- `linear_factor_root`
  - Lean: `MachLib.PolynomialEvidence.Poly.eval_linearFactor_at_root`
  - statement: `eval (x - r) at r = 0`
  - meaning: A linear factor vanishes at its named root.
- `factor_mul_root`
  - Lean: `MachLib.PolynomialEvidence.Poly.eval_factorMul_at_root`
  - statement: `eval ((x - r) * q) at r = 0`
  - meaning: Any polynomial multiplied by a vanishing factor vanishes at that root.
- `repeated_factor_root`
  - Lean: `MachLib.PolynomialEvidence.Poly.eval_repeatedFactor_at_root`
  - statement: `eval ((x - r) * (x - r)) at r = 0`
  - meaning: A repeated linear factor also vanishes at its named root.

## Explorer Use

The Explorer may show this as an internal/prototype evidence card:
finite polynomial/root evidence is checked, while the analytic identity
theorem remains blocked until the analytic substrate exists.

## Boundary

- Internal/prototype evidence only.
- Not public-ready.
- Not marketplace-ready.
- No package publish, PETAL/API upload, or Hugging Face upload.
- No safety-certification or controller-status claim.
- No public theorem/proof/open-problem claim.
