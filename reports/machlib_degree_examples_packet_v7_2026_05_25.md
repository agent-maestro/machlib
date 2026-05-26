# MachLib Degree-Growth Examples Packet v7

Date: 2026-05-25

Status: `MACHLIB_DEGREE_EXAMPLES_PACKET_V7_READY`

## What This Adds

This packet removes the explicit zero-product bridge axiom by deriving
`mul_eq_zero_or_left_or_right` from MachLib's existing field axioms.
It also adds checked example coverage for product degree growth and
root-list union/cardinality handoff.

## Degree-Growth Examples

- `example_growth_const_const`
- `example_growth_const_linear`
- `example_growth_linear_const`
- `example_growth_linear_linear`
- `example_growth_linear_quadratic`

## Root-Union Examples

- `example_product_linear_linear_degreeBound`
- `example_product_repeated_linear_degreeBound`
- `example_union_two_singletons_distinct`
- `example_union_repeated_singleton_length`
- `example_union_three_singletons_length`

## Still Blocked

- prove exact degree growth for arbitrary normalized nonzero convolution products
- connect explicit product coefficient examples back to canonical mulCoeff normal forms
- prove leading-coefficient nonzero preservation for normalized products
- assemble the full RootCountInductionTarget proof

## Boundary

- This does not prove the general polynomial root-count theorem.
- Five degree-growth examples are checked, but the arbitrary normalized product theorem remains open.
- Zero-product splitting is derived in this module; no new bridge axiom is introduced.
- No public theorem/proof/open-problem claim is made.
- No package publish, PETAL/API upload, Hugging Face upload, or production marketplace change.
