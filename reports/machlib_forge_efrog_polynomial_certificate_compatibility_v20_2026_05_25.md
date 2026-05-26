# Forge/eFrog Polynomial Certificate Compatibility v20

Status: `REPORT_ONLY_NO_BEHAVIOR_CHANGE`

This report defines the future certificate shape that Forge/eFrog
could emit for MachLib polynomial evidence packets. It is report-only.

## Future Shape

- `coeffs`: low-to-high normalized coefficient list.
- `constant`: leading coefficient for the linear-factor product.
- `linear_roots`: ordered exact roots when known.
- `expected_product_coeffs`: normalized coefficients to validate against.
- `expected_dedup_roots`: deduplicated roots for finite root-count packets.
- `normalized`: must be true.

## Boundary

- No Forge compiler behavior changed.
- No eFrog behavior changed.
- No general root-count theorem claim.
