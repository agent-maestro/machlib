# MachLib EML Analytic Frontier (2026-05-20)

## Scope

DRAFT_INTERNAL research only. Analytic records are represented as local series, finite Taylor-jet, or coefficient-pattern records.

## Representation

An analytic draft record carries:

- local center or domain guard,
- coefficient payload,
- radius/convergence status,
- limitations,
- not-claimed boundaries.

## Examples

- `analytic_power_series_local_record_v0`: generic local coefficient record.
- `analytic_exp_series_stub_v0`: symbolic coefficient-pattern stub.
- `analytic_sin_cos_series_stub_v0`: alternating coefficient-pattern stub.
- `analytic_rational_local_except_pole_v0`: geometric local-series stub with pole guard.

## Limitations

The records do not prove convergence, radius bounds, analytic continuation, or complex-analysis properties. They are schema-frontier artifacts for future local validation.

## Not Claimed

No global analytic continuation claim, no full complex-analysis formalization, no public proof result, and no claim that analytic automatically means D-finite.
