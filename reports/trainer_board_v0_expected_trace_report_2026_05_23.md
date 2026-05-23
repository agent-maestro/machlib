# Trainer Board v0 Expected Trace Report

Date: 2026-05-23

The simulator generates exactly 62 Blackwell-side expected frames for
`threshold_reflex_v0`.

## Frame Shape

Each frame includes:

- `kernel_id`
- `mode`
- `input.pot_raw`
- `request.centered`
- `request.target`
- `request.requested_output`
- `guard_state`
- `guard_reason`
- `output.safe_output`
- `timestamp_ms`
- `source`

## Guard Behavior

The expected trace includes pass-through frames and clamp frames. The clamp
uses `safe_output_limit = 0.85`.

## Boundary

The trace is simulated only. It is not live serial, not hardware observed, and
not a hardware validation claim.
