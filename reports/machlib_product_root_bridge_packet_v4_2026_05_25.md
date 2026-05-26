# MachLib Product-Root Bridge Packet v4

Date: 2026-05-25

Status: `MACHLIB_PRODUCT_ROOT_BRIDGE_PACKET_V4_READY`

## What This Adds

This packet bridges the normalized coefficient-list root-count route
to two missing pieces: a linear coefficient-list representation and
product-root splitting. Product splitting now depends on a derived
theorem for the real zero-product property.

## Derived Theorem

The derived theorem is `mul_eq_zero_or_left_or_right`: if `a * b = 0`,
then `a = 0` or `b = 0`. It is derived in MachLib from the existing
field axioms rather than added as a new axiom.

## Checked Results

- `degree_bound_linear_coeff` — linearCoeff r has degree bound one (MACHLIB_CHECKED)
- `linear_coeff_last_nonzero` — linearCoeff r is normalized because its last coefficient is one (MACHLIB_CHECKED)
- `eval_linear_coeff_eq_linear_factor` — coefficient-list linear factor evaluates like the AST linear factor (MACHLIB_CHECKED)
- `linear_coeff_root_iff_linear_factor_root` — normalized and AST linear-factor roots are equivalent (MACHLIB_CHECKED)
- `product_root_split` — a root of a semantically certified product is a root of one factor (MACHLIB_CHECKED_WITH_DERIVED_ZERO_PRODUCT_THEOREM)
- `product_root_right_of_left_nonroot` — if the left factor is nonzero at x, product root implies right root (MACHLIB_CHECKED_WITH_DERIVED_ZERO_PRODUCT_THEOREM)
- `product_root_left_of_right_nonroot` — if the right factor is nonzero at x, product root implies left root (MACHLIB_CHECKED_WITH_DERIVED_ZERO_PRODUCT_THEOREM)

## Unlocked

- linear coefficient-list representation now matches the existing AST linear-factor packet
- semantic product certificate gives a safe place to attach future convolution normalizers
- product-root splitting is available under an explicit real integral-domain derived theorem
- root-count induction can now target factor/product splitting instead of only base cases

## Still Blocked

- keep the derived zero-product theorem as a regression while product induction expands
- implement coefficient-list convolution plus MulEvalSound proofs for concrete products
- root-list union/deduplication across product factors
- degree arithmetic for convolution products
- linear-factor packet for normalized coefficient lists with singleton root list
- full induction proof for RootCountInductionTarget

## Boundary

- This is product-root bridge evidence, not the general degree/root-count theorem.
- `RootCountInductionTarget` remains defined but not proved.
- It does not prove analytic identity behavior.
- It is not public-ready and not marketplace-ready.
- No package publish, PETAL/API upload, or Hugging Face upload.
- No safety-certification or controller-status claim.
- No public theorem/proof/open-problem claim.
