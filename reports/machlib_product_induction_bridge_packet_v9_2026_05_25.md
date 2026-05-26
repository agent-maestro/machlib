# MachLib Product-Induction Bridge Packet v9

Date: 2026-05-25

Status: `MACHLIB_PRODUCT_INDUCTION_BRIDGE_PACKET_V9_READY`

## What This Unlocks

v9 replaces several certificate-only root examples with checked finite-root
packet constructors. Linear-linear, repeated-linear, nonzero constant-scaled
linear, and staged triple-linear products now have full packet constructors.

It also adds a generic `mulCoeff` packet bridge: if a caller supplies the
two still-hard product-degree facts for the concrete convolution output,
MachLib can assemble the finite-root packet by checked root splitting,
deduplication, and cardinality arithmetic.

## Checked Bridges

- `stagedTripleLinearCoeff_evalSound`: CHECKED - explicit staged triple-linear coefficient list evaluates as product
- `linearLinearFiniteRootPacket`: CHECKED_PACKET_CONSTRUCTOR - full finite-root packet for (x-r)(x-s)
- `repeatedLinearFiniteRootPacket`: CHECKED_PACKET_CONSTRUCTOR - full finite-root packet for (x-r)^2
- `scaledLinearFiniteRootPacket`: CHECKED_PACKET_CONSTRUCTOR - full finite-root packet for nonzero constant times linear
- `stagedTripleLinearFiniteRootPacket`: CHECKED_PACKET_CONSTRUCTOR - full finite-root packet for staged (x-r)(x-s)(x-t)
- `linearQuadraticFiniteRootPacketWithCertificate`: CHECKED_CERTIFICATE_CONSUMER - linear times quadratic can consume a full quadratic packet when available
- `mulCoeffFiniteRootPacketWithDegreeGrowthCert`: CHECKED_GENERIC_BRIDGE - generic convolution root packet constructor once normalized product degree-growth facts are supplied

## Named Targets

- `NormalizedMulCoeffDegreeGrowthTarget`: TARGET_NAMED_NOT_PROVED - arbitrary normalized nonzero product has degree budget equal to factor-degree sum
- `NormalizeCoeffEvalSoundTarget`: TARGET_NAMED_NOT_PROVED - trailing-zero normalization preserves coefficient-list evaluation

## Still Blocked

- prove NormalizeCoeffEvalSoundTarget so normalizedProductCoeff inherits mulCoeff root soundness
- prove LastNonzero (mulCoeff p q) for normalized nonzero p and q
- prove ProductDegreeGrowthCert (normalizedProductCoeff p q) p q for arbitrary normalized nonzero p and q
- derive the full root-count induction theorem from the generic product packet bridge
- replace the linear-quadratic certificate consumer with a complete quadratic root enumerator

## Boundary

- This packet does not prove arbitrary normalized product degree growth.
- This packet does not prove the general polynomial root-count theorem.
- It names the exact remaining theorem targets and supplies checked packet bridges around them.
- No public theorem/proof/open-problem claim is made.
- No package publish, PETAL/API upload, Hugging Face upload, or marketplace modification.
