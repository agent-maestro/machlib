# MachLib Lane 2 primitive feasibility summary

Date: 2026-05-20
Tier: OBSERVATION
Scope: local-only Lane 2 feasibility analysis for calculus and special-function symbolic primitives.

## Inputs consumed
- `corpus/eml_lanes_draft/lane_2_calculus_special_functions/`
- Existing M006 lane validator output

## Lane 2 seed count
- Seeds analyzed: 3
- Passed structurally: 3
- Warnings: 3
- Failures: 0
- Lane status: DRAFT_INTERNAL_FEASIBILITY_ONLY

## Primitive needs summary
- `mach_exp_symbolic_v0`
- `mach_log_symbolic_v0`
- `mach_sin_symbolic_v0`
- `mach_cos_symbolic_v0`
- `mach_pow_symbolic_v0`
- `mach_sqrt_symbolic_v0`
- `mach_symbolic_domain_guard_v0`

## Domain guard needs
- exp/log inverse placeholders need explicit formal and positive-domain guards.
- trig placeholders need a named owned trig primitive/spec guard.
- pow/sqrt placeholders need explicit nonnegative-domain guards.

## What can be symbolic today
- Guarded symbolic rewrite records can be represented as draft/internal EML metadata.
- The records can be checked for guardrail fields, primitive needs, and blocked claims.

## What remains blocked
- Complete real-analysis semantics.
- Release-ready special-function primitives.
- Public proof or theorem status.

## Zero-Mathlib status
- PASS

## No-go gates
- No uploads, package publishing, hardware action, compiler behavior change, or public proof/open-problem claim.
