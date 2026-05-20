# MachLib Zero-Mathlib Release Gate — 2026-05-20

## Release Invariant

MachLib release artifacts must pass the zero-Mathlib dependency gate before
public zero-Mathlib claims are made.

## Required Commands

```bash
python tools/check_zero_mathlib_dependency.py
python tools/check_zero_mathlib_dependency.py --release-target
python tools/check_zero_mathlib_dependency.py --repo-wide
```

## Gate Definition

Release-target zero Mathlib means:

- No active `import Mathlib`.
- No active `from Mathlib`.
- No active `Mathlib.` dependency evidence.
- No Mathlib dependency declarations in release/build files.
- No unknown-review Mathlib hits in release-target files.

Repo-wide zero Mathlib means:

- No raw Mathlib imports anywhere in the public repository, except policy/audit
  text.
- No Mathlib dependency declarations anywhere in the public repository.

## Current Gate Status

Default / release-target gate: `PASS`

- Release-target dependency evidence count: 0
- Release-target unknown review count: 0

Repo-wide gate: `PASS`

- Repo-wide Mathlib import count: 0
- Legacy quarantine candidate count: 0

## Public Copy Rule

Current public copy may say "zero Mathlib dependency in the current public
default tree and release target" because both gate modes pass. The copy should
continue to name the gate command and avoid unrelated public claims.

## Release Checklist

Before any future release:

1. Run `python tools/check_zero_mathlib_dependency.py`.
2. Run `python tools/check_zero_mathlib_dependency.py --release-target`.
3. Run `python tools/check_zero_mathlib_dependency.py --repo-wide`.
4. Require all three commands to return `PASS`.
5. Keep record counts tied to a dated release manifest.
6. Do not imply Hugging Face publication, PETAL upload, CapCard certification,
   package publication, hardware action, or public theorem/proof/open-problem
   results from this gate.
