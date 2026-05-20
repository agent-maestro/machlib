# MachLib Public-Safe Copy Review (2026-05-20)

## Scope

DRAFT, local only. No upload performed. No package publish performed. No release performed. No public theorem, proof, or open-problem claim is made by this review.

This review covers public-facing language for the README, machlib.org site copy, Hugging Face card language, release notes, and command-center internal display language after the zero-Mathlib and six-lane EML work.

## Inputs Reviewed

- `README.md`
- `site/`
- `command_center_feeds/`
- `reports/`
- Zero-Mathlib checker in default, release-target, and repo-wide modes

## Current Surface Summary

README language is already mostly scoped to the current public default tree and release target. The strongest safe claim is that the current tree is zero-Mathlib gate-backed by `tools/check_zero_mathlib_dependency.py`.

Site language is more promotional and includes theorem/proof-oriented framing. Before public refresh, copy should avoid implying that MachLib proves new results, replaces mathlib, is release-ready, or is uploaded anywhere.

Command-center feed language is correctly internal-only and draft/internal. It should not be reused as public site copy without converting internal review language into conservative public qualifiers.

## Safe Public Language

Allowed with audit context:

- MachLib is zero-Mathlib in the current public default tree and release target, gate-backed by `tools/check_zero_mathlib_dependency.py`.
- eFrog default Lean output remains zero-Mathlib for the reviewed local version context.
- MachLib has a DRAFT_INTERNAL six-lane EML seed corpus.
- Lanes 1-6 have local draft/internal validation and eFrog/Forge roundtrip evidence.
- Lane 2 is symbolic/draft and does not claim real-analysis formalization.
- Legacy compatibility is opt-in only, never default, and never a release dependency.

## No-Go Public Language

Do not claim:

- MachLib replaces mathlib.
- MachLib proves new results.
- MachLib resolves open problems.
- MachLib is certified safe.
- CapCard has certified MachLib.
- PETAL has publicly verified MachLib.
- A Hugging Face dataset is public or uploaded.
- A package release is approved.
- The project is public-ready or upload-ready.

## README Recommendation

Keep the current README tone, but add a short "Draft corpus status" note if updating later:

> MachLib also includes a DRAFT_INTERNAL six-lane EML seed corpus used for local validation and toolchain probing. This corpus is not public-ready, upload-ready, release-ready, or a theorem/proof claim.

Do not edit README in this task.

## Site Recommendation

Future site copy should replace broad theorem/proof wording with "formal-library corpus records," "local validation evidence," and "draft/internal lane checks." The site should explicitly state that dataset upload, package release, public certification, and public proof claims require separate approval.

Do not edit the site in this task.

## Command-Center Display Recommendation

Keep command-center wording internal-only:

- MachLib Six-Lane Status
- Zero-Mathlib: PASS
- Draft internal validated
- Not public-ready
- Not upload-ready
- Not release-ready
- Push requires human approval
