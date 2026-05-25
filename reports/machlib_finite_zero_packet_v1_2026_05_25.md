# MachLib Finite Zero Packet v1

Date: 2026-05-25

Status: `MACHLIB_FINITE_ZERO_PACKET_V1_READY`

## Purpose

This packet gives five finite polynomial/root evidence samples over the
tiny `MachLib.PolynomialEvidence` AST.

It is not an analytic identity theorem and does not claim infinite-zero
or analytic-continuation behavior.

## Samples

- `zero_poly_everywhere`
  - polynomial: `0`
  - root witness: `x`
  - Lean: `MachLib.FiniteZeroPacket.sample_zero_poly_root`
  - statement: `eval zero x = 0`
- `linear_factor_at_named_root`
  - polynomial: `x - r`
  - root witness: `r`
  - Lean: `MachLib.FiniteZeroPacket.sample_linear_factor_root`
  - statement: `eval (x - r) r = 0`
- `factor_product_left_root`
  - polynomial: `(x - r) * q(x)`
  - root witness: `r`
  - Lean: `MachLib.FiniteZeroPacket.sample_factor_product_left_root`
  - statement: `eval ((x - r) * q) r = 0`
- `repeated_factor_at_named_root`
  - polynomial: `(x - r) * (x - r)`
  - root witness: `r`
  - Lean: `MachLib.FiniteZeroPacket.sample_repeated_factor_root`
  - statement: `eval ((x - r) * (x - r)) r = 0`
- `two_factor_right_root`
  - polynomial: `(x - r) * (x - s)`
  - root witness: `s`
  - Lean: `MachLib.FiniteZeroPacket.sample_two_factor_right_root`
  - statement: `eval ((x - r) * (x - s)) s = 0`

## Next Research Gate

`POLYNOMIAL_DEGREE_ROOT_COUNT_FEASIBILITY`: define what degree,
multiplicity, finite roots, and root-count bounds would require in
MachLib before moving toward analytic zero-set claims.

## Boundary

- Internal evidence only.
- Not public-ready.
- Not marketplace-ready.
- No package publish, PETAL/API upload, or Hugging Face upload.
- No safety-certification or controller-status claim.
- No public theorem/proof/open-problem claim.
