# MachLib Normalized Product Evaluation Packet v10

Date: 2026-05-25

Status: `MACHLIB_NORMALIZED_PRODUCT_EVAL_PACKET_V10_READY`

## Checked

- `eval_eq_zero_of_normalizeCoeff_eq_nil`
- `normalizeCoeff_evalSound`
- `normalizeCoeffEvalSoundTarget_checked`
- `scalarMulCoeff_lastNonzero`
- `normalizedProductCoeff_evalSound`
- `normalizedProductFiniteRootPacketWithDegreeGrowthCert`

## Named But Not Proved

- `LinearMulCoeffLastNonzeroTarget`
- `LinearMulCoeffDegreeGrowthTarget`
- `NormalizedMulCoeffDegreeGrowthTarget`

## Forge / eFrog Compatibility

See `reports/machlib_forge_efrog_polynomial_packet_compatibility_2026_05_25.md`. No Forge compiler or eFrog behavior was changed.

## Boundary

- Normalizer evaluation soundness is checked.
- Normalized product evaluation soundness is checked.
- Arbitrary normalized product degree growth is not proved.
- Linear-times-arbitrary normalized product degree growth is not proved.
- No public theorem/proof/open-problem claim is made.
- No package publish, PETAL/API upload, Hugging Face upload, or marketplace modification.
