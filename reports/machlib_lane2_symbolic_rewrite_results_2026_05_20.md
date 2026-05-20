# MachLib Lane 2 symbolic rewrite results

Date: 2026-05-20

## exp_log_formal_inverse_draft_v0
- Status: PASS
- Warning status: WARN_ALLOWED
- Required primitives: mach_exp_symbolic_v0, mach_log_symbolic_v0, mach_symbolic_domain_guard_v0
- Domain guards: FORMAL_SYMBOLIC_INVERSE_GUARD, POSITIVE_DOMAIN_GUARD
- Guarded rewrites:
  - `log(exp(x))` with `FORMAL_SYMBOLIC_INVERSE_GUARD` -> `x`: PASS
  - `exp(log(x))` with `POSITIVE_DOMAIN_GUARD` -> `x`: PASS
- Blocked rewrites:
  - `log(exp(x))` -> `None`: WARN_BLOCKED_BY_MISSING_GUARD
  - `exp(log(x))` -> `None`: WARN_BLOCKED_BY_MISSING_GUARD
- Not claimed: not a public theorem/proof claim; not a complete real-analysis formalization.

## pow_square_root_symbolic_draft_v0
- Status: PASS
- Warning status: WARN_ALLOWED
- Required primitives: mach_pow_symbolic_v0, mach_sqrt_symbolic_v0, mach_symbolic_domain_guard_v0
- Domain guards: NONNEGATIVE_DOMAIN_GUARD
- Guarded rewrites:
  - `sqrt(x)^2` with `NONNEGATIVE_DOMAIN_GUARD` -> `x`: PASS
- Blocked rewrites:
  - `sqrt(x)^2` -> `None`: WARN_BLOCKED_BY_MISSING_GUARD
  - `sqrt(x^2)` -> `x`: unsafe: sign information is missing
  - `sqrt(x^2)` -> `abs(x)`: NEEDS_STRUCTURE_LAYER or NEEDS_PROOF_LAYER_DESIGN before acceptance
- Not claimed: not a public theorem/proof claim; not a complete real-analysis formalization.

## trig_pythagorean_symbolic_draft_v0
- Status: PASS
- Warning status: WARN_ALLOWED
- Required primitives: mach_sin_symbolic_v0, mach_cos_symbolic_v0, mach_symbolic_domain_guard_v0
- Domain guards: TRIG_SYMBOLIC_IDENTITY_GUARD
- Guarded rewrites:
  - `sin(x)^2 + cos(x)^2` with `TRIG_SYMBOLIC_IDENTITY_GUARD` -> `1`: PASS
- Blocked rewrites:
  - `sin(x)^2 + cos(x)^2` -> `None`: WARN_BLOCKED_BY_MISSING_GUARD
- Not claimed: not a public theorem/proof claim; not a complete real-analysis formalization.
