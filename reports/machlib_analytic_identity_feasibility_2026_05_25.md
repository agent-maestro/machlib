# MachLib Analytic Identity Feasibility

Date: 2026-05-25

Status: `FEASIBILITY_BLOCKED_NEEDS_ANALYTIC_SUBSTRATE`

## Blunt Result

MachLib cannot currently state or check the analytic identity theorem honestly.
It lacks zero sets, accumulation points, topology, limits, power series,
convergence, connected domains, and infinite-set machinery.

## What Was Added

`foundations/MachLib/AnalyticIdentityFeasibility.lean` adds three checked
finite polynomial/root footholds:

- `zero_polynomial_eval_checked`
- `linear_factor_known_root_checked`
- `repeated_factor_known_root_checked`

These are deliberately tiny. They prove that the current algebra layer can
certify simple root evidence, not global analytic continuation.

## Missing Substrate

- set/domain vocabulary
- finite and infinite zero-set vocabulary
- neighborhoods and deleted neighborhoods
- sequence/filter convergence
- accumulation points
- power series and radius of convergence
- local equality and operation closure for analytic functions
- connected-domain propagation

## Recommended Path

1. Build a minimal polynomial AST and evaluator.
2. Prove root-at-factor facts over that AST.
3. Emit finite zero-evidence packets for polynomial examples.
4. Add local power-series records only after finite polynomial evidence is
   stable.
5. Keep infinite-zero and global analytic-continuation claims blocked until the
   missing substrate exists.

## Boundary

No analytic identity theorem is claimed here. No public theorem/proof/open
problem result is claimed. No package publish, PETAL/API upload, Hugging Face
upload, production marketplace modification, safety-certification claim, or
controller-status claim was performed.
