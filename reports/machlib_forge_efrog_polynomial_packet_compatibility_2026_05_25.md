# MachLib Forge/eFrog Polynomial Packet Compatibility

Date: 2026-05-25

Status: `COMPATIBILITY_REPORT_ONLY`

## Purpose

This report defines the future certificate shape Forge and eFrog should emit if
they want to target MachLib's coefficient-list polynomial root-count scaffold.

No Forge compiler behavior is changed here. No eFrog behavior is changed here.

## Future Certificate Shape

A future polynomial packet should emit:

- `coeffs`: low-to-high coefficient list.
- `normalized_coeffs`: coefficient list after trailing-zero normalization.
- `normalization_eval_sound`: reference to `normalizeCoeff_evalSound`.
- `product_eval_sound`: reference to `normalizedProductCoeff_evalSound` when the packet is a product.
- `last_nonzero`: evidence that the normalized coefficient list has a nonzero last coefficient.
- `degree_growth`: evidence for `ProductDegreeGrowthCert`.
- `roots`: finite root candidate list.
- `root_sound`: evidence for `RootListSound`.
- `root_distinct`: evidence for `RootListDistinct`.
- `root_degree_bound`: evidence for `RootListDegreeBound`.

## Forge Integration Direction

Forge should eventually be able to emit a coefficient-list certificate alongside
generated polynomial code:

```text
source expression
-> normalized coefficient list
-> optional product factorization
-> MachLib packet references
-> evidence card
```

The first safe Forge target is not a compiler rewrite. It is an optional
sidecar certificate for small polynomials.

## eFrog Integration Direction

eFrog can use the same shape as an evidence-card generator:

```text
input coefficient list
-> normalizeCoeff
-> root packet candidate
-> MachLib check
-> root/degree evidence card
```

The first safe eFrog demo should be tiny:

- nonzero constant packet
- linear packet
- linear x linear packet
- repeated linear packet
- staged triple-linear packet

## Required Boundary

- This is not a Forge compiler behavior change.
- This is not an eFrog behavior change.
- This does not prove the general root-count theorem.
- This does not prove arbitrary normalized product degree growth.
- This does not make a public theorem/proof/open-problem claim.
- This does not publish a package.
- This does not upload to PETAL/API or Hugging Face.
- This does not modify a production marketplace.

## Current Missing Bridges

- `LinearMulCoeffLastNonzeroTarget`
- `LinearMulCoeffDegreeGrowthTarget`
- `NormalizedMulCoeffDegreeGrowthTarget`

These are the exact theorem targets needed before Forge/eFrog should treat
general product root packets as routine.
