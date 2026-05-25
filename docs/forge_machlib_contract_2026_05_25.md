# Forge -> MachLib Contract

Date: 2026-05-25

Status: `INTERNAL_CONTRACT_DRAFT`

## Purpose

MachLib is Monogate's compact Lean check target for EML and Forge artifacts.
This contract defines the review boundary between Forge output and MachLib
checking without claiming production certification or broad theorem-library
replacement.

## Interface

Forge may emit:

- a Lean file importing `MachLib.*`;
- an EML source reference;
- a generated theorem or obligation name;
- declared domain guards;
- a replay/evidence path where available;
- a status field separating `checked`, `draft`, `blocked`, and `fixture`.

MachLib may accept:

- Lean source that imports only MachLib/local foundations;
- declarations whose dependencies pass the zero-Mathlib gate;
- explicit domain guards rather than implicit analytic assumptions;
- proof traces or tactic attempts as evidence metadata.

## What Lean Checks

Lean checks the submitted term/proof against the imported MachLib environment.
That is a kernel check of the artifact in that environment. It is not a
system-level safety certification, production controller approval, package
publish, or public theorem promotion.

## Evidence Classes

- `MACHLIB_CHECKED`: Lean accepted the artifact in the MachLib environment.
- `MACHLIB_DRAFT`: artifact shape is plausible but not checked.
- `MACHLIB_BLOCKED`: missing primitive, guard, or proof trace.
- `LEGACY_MATHLIB_REFERENCE`: historical or upstream reference only; not an
  active MachLib dependency claim.

## Public Copy Rule

Use:

> MachLib is Monogate's small Lean verification layer: a zero-Mathlib check
> target for EML/Forge artifacts when direct evidence is present.

Avoid:

- "MachLib replaces Mathlib."
- "Certified safety."
- "Production controller."
- "Public theorem proved" unless a reviewed public theorem artifact exists.
- "Mathlib lemmas" as marketplace/playbook value language.

## Gates

Before any release or public candidate claim:

- `python tools/check_zero_mathlib_dependency.py`
- `python tools/check_zero_mathlib_dependency.py --release-target`
- `python tools/check_zero_mathlib_dependency.py --repo-wide`
- docs/copy scan for stale Mathlib-first marketplace wording
- CapCard/marketplace scan for upload or public-readiness overclaims
