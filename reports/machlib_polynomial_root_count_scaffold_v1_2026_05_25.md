# MachLib Polynomial Root-Count Scaffold v1

Date: 2026-05-25

Status: `MACHLIB_POLYNOMIAL_ROOT_COUNT_SCAFFOLD_V1_READY`

## What This Adds

This packet defines the first root-count primitives over the tiny
`MachLib.PolynomialEvidence` AST and proves one degree-1 foothold:
a linear factor cannot have a pair of distinct roots.

## Primitives

- `Root`
  - Lean: `MachLib.PolynomialRootCount.Root`
  - purpose: classify an input as a zero of a polynomial evaluator
- `NonzeroWitness`
  - Lean: `MachLib.PolynomialRootCount.NonzeroWitness`
  - purpose: represent nonzero-polynomial evidence by one nonzero evaluation witness
- `DistinctRootPair`
  - Lean: `MachLib.PolynomialRootCount.DistinctRootPair`
  - purpose: state the first finite root-count obstruction shape
- `degreeUpper`
  - Lean: `MachLib.PolynomialRootCount.degreeUpper`
  - purpose: compute a syntactic degree upper bound over the tiny polynomial AST

## Checked Footholds

- `degree_upper_linear_factor`
  - Lean: `MachLib.PolynomialRootCount.degreeUpper_linearFactor`
  - statement: degreeUpper (x - r) = 1
- `linear_factor_root_unique`
  - Lean: `MachLib.PolynomialRootCount.linearFactor_root_unique`
  - statement: if eval (x - r) at x is zero, then x = r
- `linear_factor_no_distinct_root_pair`
  - Lean: `MachLib.PolynomialRootCount.linearFactor_no_distinct_root_pair`
  - statement: a linear factor cannot have two distinct roots

## Still Blocked

- general degree arithmetic for normalized polynomials
- finite root-set representation beyond distinct pairs
- root-list uniqueness and cardinality bounds
- nonzero polynomial predicate tied to degree
- multiplicity accounting
- induction showing a degree-n nonzero polynomial has at most n distinct roots

## Boundary

- This is a tiny checked root-count foothold, not the general theorem.
- It does not prove analytic identity behavior.
- It is not public-ready and not marketplace-ready.
- No package publish, PETAL/API upload, or Hugging Face upload.
- No safety-certification or controller-status claim.
- No public theorem/proof/open-problem claim.
