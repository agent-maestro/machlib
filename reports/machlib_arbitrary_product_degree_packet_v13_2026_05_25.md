# MachLib Arbitrary Product Degree Packet v13

Date: 2026-05-25

Status: `MACHLIB_ARBITRARY_PRODUCT_DEGREE_PACKET_V13_READY`

## Checked

v13 proves the arbitrary normalized product-degree bridge for
`mulCoeff` and `normalizedProductCoeff`: normalized nonzero inputs
produce a normalized nonzero product with enough degree budget for
root-list union. It also adds a generic product packet constructor for
known finite-root packets.

- `MulCoeffLastNonzeroTarget`
- `degreeBound_scalarMulCoeff`
- `addCoeff_left_lower_degree_lastNonzero`
- `degreeBound_addCoeff_left_lower_degree`
- `mulCoeff_lastNonzero_and_raw_growth`
- `mulCoeff_lastNonzero`
- `degreeBound_mulCoeff_raw_growth`
- `normalizedProductCoeff_lastNonzero`
- `mulCoeffLastNonzeroTarget_checked`
- `normalizedProductCoeffDegreeGrowth`
- `normalizedMulCoeffDegreeGrowthTarget_checked`
- `normalizedProductFiniteRootPacket`
- `ProductPacketAssemblyTarget`
- `productPacketAssemblyTarget_checked`

## Still Open

- full arbitrary root enumeration for every normalized coefficient list
- RootCountInductionTarget construction for arbitrary coefficients
- algorithmic root-list extraction rather than composition from known packets
- higher-level Forge/eFrog emission of product/root certificates

## Boundary

- This is the arbitrary product degree-growth bridge, not a full root enumeration theorem.
- `RootCountInductionTarget` remains defined but not proved.
- Product packets can now compose known finite-root packets without a manual product-degree certificate.
- No Forge compiler or eFrog behavior was changed.
- No public theorem/proof/open-problem claim is made.
- No package publish, PETAL/API upload, Hugging Face upload, or marketplace modification.
