# MachLib EML Smooth Frontier (2026-05-20)

## Scope

DRAFT_INTERNAL research only. Smooth records are represented by finite jets, derivative towers, and boundary-check payloads.

## Representation

A smooth draft record carries:

- symbolic object,
- local domain or piecewise boundary guard,
- derivative or jet payload,
- boundary checks where applicable,
- limitations and not-claimed boundaries.

## Examples

- `smooth_polynomial_finite_jet_v0`: finite derivative-jet placeholder.
- `smooth_exp_symbolic_derivative_tower_v0`: symbolic derivative tower placeholder.
- `smooth_bump_function_boundary_stub_v0`: all-order boundary stub requiring proof-layer design.
- `smooth_piecewise_warning_v0`: warning that piecewise smooth parts do not imply global smoothness.

## Limitations

Finite-jet payloads do not establish C-infinity claims by themselves. Piecewise records need boundary derivative matching, and all-order examples need a future proof/evidence layer.

## Not Claimed

No smooth-manifold theory, no distribution theory, no C-infinity proof claim, no public theorem result, and no claim that smooth automatically means analytic.
