# MachLib Zero-Mathlib Dependency Audit — 2026-05-20

## Scope

This is a local dependency-gate audit for MachLib. It does not push, upload to
Hugging Face, call Hugging Face APIs, publish packages, call PETAL/API
endpoints, modify CapCard marketplace assets, run hardware commands, change
Forge compiler behavior, create tokens, or create public theorem/proof or
open-problem claims.

## Validation Commands

```bash
python tools/check_zero_mathlib_dependency.py
python tools/check_zero_mathlib_dependency.py --release-target
python tools/check_zero_mathlib_dependency.py --repo-wide
```

## Current Results

| Mode | Result | Reason |
|---|---|---|
| Default / `--release-target` | `PASS` | No release-target dependency evidence and no release-target unknown-review hits. |
| `--repo-wide` | `PASS` | No raw Mathlib imports remain in the public default tree. |

Summary counts after quarantine:

- Total files scanned: 3638
- Lean files scanned: 273
- Repo-wide Mathlib import count: 0
- Release-target dependency evidence count: 0
- Legacy quarantine candidate count: 0
- Policy/historical text count: 85
- Unknown review count: 0
- Release-target unknown review count: 0

## Quarantine Action

The previous blockers were 55 raw imports in transitional legacy Lean files
under `foundations/legacy_eml/`. Those files were backed up locally under:

```text
/tmp/machlib_legacy_eml_mathlib_quarantine_2026_05_20/legacy_eml
```

The public default tree now keeps only a non-code README in
`foundations/legacy_eml/`, plus a quarantine manifest at:

```text
reports/machlib_legacy_eml_quarantine_manifest_2026_05_20.md
```

## Claim Guidance

Supported now:

- "MachLib has zero Mathlib dependency in the current public default tree and
  release target."
- "Every release claiming zero Mathlib dependency must pass
  `tools/check_zero_mathlib_dependency.py`."

Still not implied:

- Exact record counts without a dated release manifest.
- Public Hugging Face dataset availability.
- CapCard certification.
- PETAL verification/upload.
- Public theorem/proof/open-problem results.
