# Qwen / CapCard Marketplace Source Inventory

Date: 2026-05-21

## Scope

This inventory reviews local Qwen, puzzle, PETAL, and CapCard evidence for possible internal marketplace candidates. It does not change any marketplace data, call PETAL/API endpoints, upload to Hugging Face, publish packages, deploy, or make public claims.

## Command Center Check

The original command-center repository was inspected read-only. It still has a pre-existing local modification in `data/proof-registry.jsonl`.

The exact pasted row IDs were not found by exact string match in the current command-center proof registry. Treat the pasted rows as stale or as references to the underlying 2026-05-16 research artifacts rather than current command-center rows.

## Inventory Summary

Primary source root:

`/home/monogate/monogate/monogate-research/exploration`

Important source groups:

- `Qwen_Puzzle_Curriculum_Pack_Evidence_Ledger_2026_05_16`
- `Qwen_Puzzle_Curriculum_Pack_Import_Dryrun_2026_05_16`
- `EML_Puzzle_Curriculum_Import_Gate_2026_05_16`
- `EML_Puzzle_Curriculum_Evidence_Ledger_2026_05_16`
- `EML_Puzzle_Evidence_Ledger_2026_05_16`
- `EML_Puzzle_Evidence_Quarantine_Review_2026_05_16`
- `EML_Puzzle_Proof_Kernel_2026_05_16`
- `EML_Puzzle_Proof_Kernel_Integration_2026_05_16`
- `PETAL_Local_Attempt_Ingestion_Simulator_2026_05_16`
- `PETAL_Public_Attempt_Logging_NoUpload_Gate_2026_05_16`

## Current Reading

The EML Puzzle Evidence Kernel has the cleaner evidence path: local bounded puzzle results, internal CapCard rows, quarantine review, integration validation, and explicit no-upload/no-public-claim boundaries.

The Qwen Puzzle Curriculum Pack has useful internal evidence, but the source findings and rows preserve repair signals: the pack dry run says structured CapCard row generation needed targeted repair, and accepted internal CapCard pack rows include warning status rows.

## Boundaries

- No production marketplace was changed.
- No draft marketplace entry was promoted.
- No PETAL/API upload was performed.
- No Hugging Face upload was performed.
- No package publish was performed.
- No Forge compiler behavior was changed.
- No public theorem/proof/open-problem claim was made.
- No certified safety or production controller claim was made.
