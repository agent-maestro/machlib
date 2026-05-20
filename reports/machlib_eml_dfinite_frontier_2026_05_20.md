# MachLib EML D-Finite Frontier (2026-05-20)

## Scope

DRAFT_INTERNAL research only. D-finite records are treated as finite symbolic ODE-certificate records, not as a full holonomic proof system.

## Representation

A D-finite record carries:

- expression or symbolic function label,
- local domain or singularity guard,
- linear ODE order,
- polynomial coefficient payload,
- assumptions,
- validation checks,
- limitations and not-claimed boundaries.

## Examples

- `dfinite_exp_ode_certificate_v0`: first-order symbolic ODE certificate.
- `dfinite_sin_ode_certificate_v0`: second-order symbolic ODE certificate.
- `dfinite_cos_ode_certificate_v0`: second-order symbolic ODE certificate.
- `dfinite_polynomial_certificate_v0`: high-derivative-zero certificate.
- `dfinite_bessel_style_certificate_stub_v0`: polynomial-coefficient ODE stub with singularity guard.

## Guard Needs

D-finite certificates need leading-coefficient and domain/singularity guards before stronger analytic language. A finite ODE payload alone is not a global regularity, continuation, or solution theorem.

## Not Claimed

No full holonomic system, no public theorem/proof claim, no full real-analysis formalization, no external-library replacement, and no release-ready special-function semantics.
