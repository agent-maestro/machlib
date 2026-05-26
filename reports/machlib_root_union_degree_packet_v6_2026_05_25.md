# MachLib Root-Union + Degree Packet v6

Date: 2026-05-25

Status: `MACHLIB_ROOT_UNION_DEGREE_PACKET_V6_READY`

## What This Adds

This packet closes the root-list union side of the product induction
bridge: duplicate preservation, union cardinality, and the product
root-list degree-bound handoff are now checked. It also clarifies
that the remaining product-degree bridge must be a growth/equality
certificate, not only an upper-bound theorem.

## Checked Results

- `root_list_distinct_insert_unique_root` — unique insertion preserves duplicate-free root lists (MACHLIB_CHECKED)
- `root_list_distinct_union_unique_roots` — unique union preserves duplicate-free factor root lists (MACHLIB_CHECKED)
- `length_insert_unique_root_le_succ` — unique insertion increases root-list length by at most one (MACHLIB_CHECKED)
- `length_insert_unique_root_eq_of_mem` — inserting an existing root leaves root-list length unchanged (MACHLIB_CHECKED)
- `length_union_unique_roots_le_add` — unique union length is bounded by sum of factor-list lengths (MACHLIB_CHECKED)
- `product_root_list_distinct_union` — product root-list union is duplicate-free when factor lists are duplicate-free (MACHLIB_CHECKED)
- `product_root_list_length_union_le_add` — product root-list union cardinality is bounded by sum of factor-list cardinalities (MACHLIB_CHECKED)
- `product_root_list_degree_bound_union_of_cert` — bounded factor root lists produce a bounded product root list under a product degree-growth certificate (MACHLIB_CHECKED_WITH_DEGREE_GROWTH_CERTIFICATE)

## Unlocked

- root-list duplicate preservation is checked for product unions
- root-list union cardinality is checked against the sum of factor-list lengths
- product root-list degree bounds now have an explicit certificate interface
- the exact missing degree bridge is identified as product degree growth/equality, not merely an upper bound

## Still Blocked

- construct ProductDegreeGrowthCert for normalized nonzero convolution products
- prove exact degree arithmetic for nonzero normalized products
- connect LastNonzero normalization to nonzero product leading coefficient evidence
- derive zero-product splitting from MachLib's field substrate instead of the bridge axiom
- assemble the full RootCountInductionTarget proof

## Boundary

- This does not prove the general polynomial root-count theorem.
- Product degree growth/equality is defined as a certificate interface, not constructed generally.
- The existing zero-product bridge axiom remains explicit.
- No public theorem/proof/open-problem claim is made.
- No package publish, PETAL/API upload, Hugging Face upload, or production marketplace change.
