# MachLib Lane 2 Roundtrip Probe Summary (2026-05-20)

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## Scope

This local probe reads Lane 2 symbolic draft seeds, primitive specs, and rewrite
results, writes EML-style artifacts under `/tmp`, checks eFrog default rendering,
and probes Forge local compile surfaces without changing compiler behavior.

## Summary

- Lane 2 seed count: 3
- EML artifacts: 3
- eFrog status: PASS
- Forge status: PASS
- Roundtrip status: PASS
- Temp root: `/tmp/machlib_lane2_roundtrip_probe_2026_05_20`

## Expected Symbolic Limitations

Lane 2 remains symbolic and draft/internal. Forge may reject direct special-
function artifacts until canonical symbolic primitive support exists; that is a
WARN when no dependency, upload, hardware, or compiler-mutation boundary is
violated.

## Warnings And Failures

- Warned rows: 0
- Failed rows: 0
- Evidence script status: PASS

## Remaining No-Go Gates

No upload, package publish, PETAL/API call, hardware action, Forge compiler
behavior change, or public theorem/proof/open-problem claim is authorized.
