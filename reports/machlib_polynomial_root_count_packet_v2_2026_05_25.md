# MachLib Polynomial Root-Count Packet v2

Date: 2026-05-25

Status: `MACHLIB_POLYNOMIAL_ROOT_COUNT_PACKET_V2_READY`

## What This Adds

This packet upgrades the v1 scaffold from a distinct-root-pair
obstruction into a finite root-list packet for the first degree-one
case. The checked Lean result is still deliberately small:
`(x - r)` has a singleton root list `[r]`, that list is distinct,
and its length is bounded by the syntactic degree upper bound.

## New Primitive Layer

- `Root`: classify an input as a zero of a polynomial evaluator
- `NonzeroWitness`: represent nonzero-polynomial evidence by one nonzero evaluation witness
- `DistinctRootPair`: state the first finite root-count obstruction shape
- `degreeUpper`: compute a syntactic degree upper bound over the tiny polynomial AST
- `RootListSound`: require every actual root to appear in a finite root list
- `RootListDistinct`: track duplicate-free root lists without importing a finite-set library
- `RootListDegreeBound`: state that a finite root list length is bounded by syntactic degree
- `FiniteRootPacket`: bundle polynomial, roots, soundness, distinctness, and degree bound

## Checked Results

- `degree_upper_linear_factor` — degreeUpper (x - r) = 1
- `degree_upper_factor_mul` — degreeUpper ((x - r) * q) = 1 + degreeUpper q
- `linear_factor_root_unique` — if eval (x - r) at x is zero, then x = r
- `linear_factor_no_distinct_root_pair` — a linear factor cannot have two distinct roots
- `linear_factor_root_list_sound` — the singleton list [r] contains every root of x - r
- `singleton_root_list_distinct` — the singleton root list [r] has no duplicate roots
- `linear_factor_root_list_degree_bound` — the singleton root list [r] has length bounded by degreeUpper (x - r)
- `linear_factor_finite_root_packet` — a checked finite-root packet exists for x - r

## Still Blocked

- normalized coefficient-list representation for arbitrary polynomial syntax
- proof that normalized degree agrees with evaluator semantics
- finite root-set representation beyond list membership
- root-list union/deduplication across products
- multiplicity accounting
- induction showing a degree-n nonzero polynomial has at most n distinct roots

## Boundary

- This is a checked finite-root packet for a linear factor, not a
  general degree/root-count theorem.
- It does not prove analytic identity behavior.
- It is not public-ready and not marketplace-ready.
- No package publish, PETAL/API upload, or Hugging Face upload.
- No safety-certification or controller-status claim.
- No public theorem/proof/open-problem claim.
