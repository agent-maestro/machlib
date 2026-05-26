# MachLib Exact Product Degree Normalizer Packet v8

Date: 2026-05-25

Status: `MACHLIB_EXACT_PRODUCT_DEGREE_NORMALIZER_PACKET_V8_READY`

## What Changed

v8 adds a small coefficient normalizer and names the normalized product output.
It then expands the checked product-degree example suite across five targeted
classes: quadratic-linear, quadratic-quadratic, repeated roots, constant-scale
products, and cleanup cases.

## Normalizer Layer

- `normalizeCoeff_nil`
- `normalizeCoeff_singleton_zero`
- `normalizeCoeff_singleton_nonzero`
- `normalizeCoeff_of_LastNonzero`
- `degreeBound_normalizeCoeff_eq_of_LastNonzero`
- `normalizeCoeff_linearCoeff`
- `scaledLinearCoeff_evalSound`
- `linearLinearCoeff_evalSound`
- `linearQuadraticCoeff_evalSound`

## Targeted Example Classes

- `quadratic_times_linear`: 5 checked examples
- `quadratic_times_quadratic`: 5 checked examples
- `repeated_roots`: 5 checked examples
- `constant_scale_products`: 5 checked examples
- `trailing_zero_cleanup`: 5 checked examples

## Root Packet Examples

- `example_v8_root_packet_linear_linear`: (x-r)(x-s) (CHECKED_DEGREE_BOUND_PACKET)
- `example_v8_root_packet_repeated_linear`: (x-r)^2 (CHECKED_DEGREE_BOUND_PACKET)
- `example_v8_root_packet_staged_triple`: (x-r)(x-s)(x-t) (CHECKED_STAGED_DEGREE_BOUND_PACKET)
- `example_v8_root_packet_scaled_linear`: constant * (x-r) (CHECKED_DEGREE_BOUND_PACKET)
- `example_v8_root_packet_linear_quadratic_with_certificate`: (x-r) * monic_quadratic(a,b) (CHECKED_CERTIFICATE_INTERFACE)

## Still Blocked

- prove full product degree growth for arbitrary normalized nonzero convolution products
- prove normalized leading-coefficient preservation for mulCoeff without specializing product shapes
- derive root-list union cardinality strong enough for the general induction theorem
- replace certificate interfaces for quadratic root packets with complete checked root enumerators
- assemble RootCountInductionTarget after product-degree arithmetic is general

## Boundary

- This packet does not prove the general polynomial root-count theorem.
- It does not prove arbitrary normalized product degree growth.
- Certificate interfaces remain explicit where full root enumeration is not available.
- No public theorem/proof/open-problem claim is made.
- No package publish, PETAL/API upload, Hugging Face upload, or marketplace modification.
