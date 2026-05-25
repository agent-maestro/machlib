# Analytic Identity Theorem Feasibility

Date: 2026-05-25

Status: `FEASIBILITY_BLOCKED_NEEDS_ANALYTIC_SUBSTRATE`

## Scope

This note asks what MachLib would need before it could even state, much less
check, an analytic identity theorem in the familiar form:

> if an analytic function has zeros with an accumulation point inside a
> connected domain, then the function is identically zero on that domain.

MachLib does not claim that result. The current pass only records the missing
substrate and lands tiny finite polynomial/root footholds that the current
algebra layer can check.

## Required Concepts

### Zero Set

A future zero-set definition needs:

- a function space, such as `Real -> Real` or a future complex function type;
- a domain predicate `D : Real -> Prop` or future topological domain type;
- equality-to-zero membership: `x ∈ zero_set f D` iff `D x` and `f x = 0`;
- finite and infinite set vocabulary;
- set inclusion and equality.

Current status: `MISSING_SET_SUBSTRATE`.

### Accumulation Point

A future accumulation-point definition needs:

- metric or topological neighborhoods;
- deleted neighborhoods, so the point itself is not the only witness;
- quantification over every radius/neighborhood;
- sequences or filters, depending on the chosen proof route;
- domain membership and closure semantics.

Current status: `MISSING_TOPOLOGY_LIMIT_SUBSTRATE`.

### Analytic Function

A future analytic definition needs:

- power series or local Taylor expansion data;
- radius of convergence or local neighborhood validity;
- coefficient sequence representation;
- convergence/equality of functions on neighborhoods;
- operations preserving analyticity.

Current status: `MISSING_POWER_SERIES_SUBSTRATE`.

## Missing Primitives

- Sets and domains.
- Natural-number indexed coefficient sequences.
- Finite/infinite set classification.
- Metric balls or topological neighborhoods.
- Limits, convergence, and accumulation points.
- Power series evaluation and convergence.
- Function equality on a domain.
- Connectedness, or a deliberately weaker local identity theorem first.
- Polynomial degree and root-count machinery if a finite polynomial route is
  pursued first.

## Checked Foothold

`MachLib.AnalyticIdentityFeasibility` adds three small Lean-checked facts:

- `zero_polynomial_eval_checked`
- `linear_factor_known_root_checked`
- `repeated_factor_known_root_checked`

These are not analytic identity results. They are finite algebraic sanity
checks showing that the current `mach_ring` layer can certify simple
polynomial/root evidence shapes.

## Recommended Next Gate

Before attempting any analytic identity theorem:

1. Define a minimal polynomial AST and evaluator.
2. Prove root-at-factor facts over that AST.
3. Define finite zero evidence packets for polynomial examples.
4. Only then design local analytic-series semantics.
5. Keep global analytic continuation and infinite zero-set claims blocked until
   topology and convergence exist.

## Boundary

This pass does not introduce a public theorem/proof/open-problem claim. It does
not certify analytic continuation. It does not claim MachLib is a full analysis
library.
