# MachLib Convolution + Root-Union Packet v5

Date: 2026-05-25

Status: `MACHLIB_CONVOLUTION_ROOT_UNION_PACKET_V5_READY`

## What This Adds

This packet turns the previous product-root bridge into a concrete
coefficient-list product path. It adds recursive convolution, proves
that convolution evaluates as product evaluation, and adds root-list
union machinery for product-root packets.

## Checked Results

- `eval_add_coeff` — coefficient-list addition evaluates to pointwise addition (MACHLIB_CHECKED)
- `eval_scalar_mul_coeff` — coefficient scalar multiplication evaluates to scalar multiplication (MACHLIB_CHECKED)
- `eval_shift_coeff` — coefficient shift evaluates as multiplication by x (MACHLIB_CHECKED)
- `eval_mul_coeff` — recursive convolution evaluates as product of operand evaluations (MACHLIB_CHECKED)
- `mul_coeff_eval_sound` — mulCoeff produces a semantic product certificate (MACHLIB_CHECKED)
- `mem_insert_unique_root_of_mem` — existing root membership survives unique insertion (MACHLIB_CHECKED)
- `mem_insert_unique_root_self` — inserted root is present after unique insertion (MACHLIB_CHECKED)
- `mem_union_unique_roots_left` — left root-list membership survives unique union (MACHLIB_CHECKED)
- `mem_union_unique_roots_right` — right root-list membership survives unique union (MACHLIB_CHECKED)
- `product_root_list_sound_union` — product root-list soundness transfers to union of factor root lists (MACHLIB_CHECKED_WITH_BRIDGE_AXIOM)
- `mul_coeff_root_list_sound_union` — convolution product root-list soundness transfers to union of factor root lists (MACHLIB_CHECKED_WITH_BRIDGE_AXIOM)
- `product_degree_bound_nil_left` — product degree arithmetic base case for empty left operand (MACHLIB_CHECKED)

## Unlocked

- coefficient-list convolution now has checked evaluation soundness
- mulCoeff can feed the existing product-root splitting bridge
- root-list union/dedup primitives now preserve factor-list membership
- product root-list soundness can be built from sound factor root lists
- degree arithmetic has a named target plus a checked empty-left base case

## Still Blocked

- prove full ProductDegreeBoundTarget for normalized convolution products
- prove RootListDistinct preservation for unionUniqueRoots
- prove root-list cardinality bound for product unions
- replace mul_eq_zero_or_left_or_right bridge axiom with a derived integral-domain theorem
- connect normalized product degree arithmetic to full RootCountInductionTarget

## Boundary

- This does not prove the general polynomial root-count theorem.
- Degree arithmetic is named and has a checked base case, but the general theorem is not proved.
- Root-list union soundness is checked; distinctness/cardinality preservation remains open.
- The existing zero-product bridge axiom remains explicit.
- No public theorem/proof/open-problem claim is made.
- No package publish, PETAL/API upload, Hugging Face upload, or production marketplace change.
