# MachLib Zero-Mathlib Public Copy Patch — 2026-05-20

## Purpose

Align README and site copy with the repo-wide zero-Mathlib quarantine result.
This is a local copy patch only. It does not push, upload to Hugging Face, call
Hugging Face APIs, publish packages, call PETAL/API endpoints, modify CapCard
marketplace assets, run hardware commands, change Forge compiler behavior,
create tokens, or create public theorem/proof/open-problem claims.

## Gate Result

All checker modes now pass:

- `python tools/check_zero_mathlib_dependency.py`
- `python tools/check_zero_mathlib_dependency.py --release-target`
- `python tools/check_zero_mathlib_dependency.py --repo-wide`

The public default tree now has:

- Repo-wide Mathlib import count: 0
- Release-target dependency evidence count: 0
- Legacy quarantine candidate count: 0

## README Changes

The README now says:

- MachLib is a machine-native Lean/EML library with zero Mathlib dependency in
  the current public default tree and release target.
- Every release claiming zero Mathlib dependency must pass
  `tools/check_zero_mathlib_dependency.py`.
- Historical legacy EML source was quarantined into a local out-of-repo backup
  and represented in-tree by a non-code note.

## Site Changes

The site now says:

- Zero Mathlib dependency is gate-backed.
- Mathlib import status is "Gate-backed zero."
- The current public default tree and release target are zero Mathlib
  dependency, backed by the local gate.

## Boundaries

This copy patch does not add exact record counts, public Hugging Face dataset
availability, CapCard certification, PETAL verification/upload, package
publication, hardware action, Forge compiler behavior changes, or public
theorem/proof/open-problem results.
