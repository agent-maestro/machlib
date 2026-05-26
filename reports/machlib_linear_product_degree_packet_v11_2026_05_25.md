# MachLib Linear Product Degree Packet v11

Date: 2026-05-25

Status: `MACHLIB_LINEAR_PRODUCT_DEGREE_PACKET_V11_READY`

## Checked

v11 proves the first true arbitrary-family product-degree bridge:
multiplication on the left by `linearCoeff r` preserves normalized
leading-coefficient evidence and gives exact degree growth for any
normalized nonempty coefficient list `p`.

- `addCoeff_nil_right`
- `addCoeff_zero_singleton_right_of_LastNonzero`
- `mulCoeff_one_left_of_LastNonzero`
- `addCoeff_scalar_cons_self_lastNonzero`
- `degreeBound_addCoeff_scalar_cons_self`
- `mulCoeff_linearCoeff_shape`
- `linearMulCoeffLastNonzero`
- `linearMulCoeffLastNonzeroTarget_checked`
- `linearMulCoeffDegreeGrowth`
- `linearMulCoeffDegreeGrowthTarget_checked`

## Still Open

- right-linear product degree growth: normalizedProductCoeff p (linearCoeff r)
- arbitrary normalized product degree growth: normalizedProductCoeff p q
- general leading-coefficient preservation for normalized convolution products
- full RootCountInductionTarget assembly

## Boundary

- This proves the left-linear arbitrary normalized product bridge, not the full arbitrary product theorem.
- The general root-count theorem is still not proved.
- No Forge compiler or eFrog behavior was changed.
- No public theorem/proof/open-problem claim is made.
- No package publish, PETAL/API upload, Hugging Face upload, or marketplace modification.
