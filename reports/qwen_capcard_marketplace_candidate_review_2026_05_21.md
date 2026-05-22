# Qwen / CapCard Marketplace Candidate Review

Date: 2026-05-21

## Candidate 1: Qwen Puzzle Curriculum Pack

Readiness: `BLOCKED_WITH_EXACT_FIX_LIST`

Evidence basis:

- Qwen puzzle curriculum pack import dry run.
- Qwen puzzle curriculum pack evidence ledger.
- EML puzzle curriculum import gate.
- EML puzzle curriculum evidence ledger.
- Internal PETAL-style and CapCard-style rows.

What looks good:

- Local curriculum pack path exists.
- Evidence ledger result is pass.
- Review summary result is pass.
- Public-ready true count is zero.
- Upload true count is zero.
- Production CapCard changed count is zero.
- Forge compiler changed count is zero.

Exact blockers:

- The pack import findings record that structured CapCard row generation needed targeted repair before ingestion.
- Accepted internal CapCard pack rows include `validation_status=warn` and `solver_status=unknown` rows.
- Needs a final human review pass over repaired rows before any internal marketplace draft promotion.

Recommended status: keep as draft candidate, not recommended for immediate marketplace approval.

## Candidate 2: EML Puzzle Evidence Kernel

Readiness: `READY_FOR_HUMAN_MARKETPLACE_APPROVAL`

Evidence basis:

- EML Puzzle Proof Kernel.
- EML Puzzle Evidence Ledger.
- EML Puzzle Evidence Quarantine Review.
- EML Puzzle Proof Kernel Integration.
- PETAL local attempt ingestion simulator.
- PETAL public attempt logging no-upload gate.

What looks good:

- Bounded puzzle kernel artifacts exist.
- Local toy-solver results are present for six small puzzle fixtures.
- CapCard puzzle registry rows are internal candidates with `public_ready=false`.
- Integration validation status is pass.
- PETAL upload was not performed.
- Production CapCard was not modified.
- Public-ready true count is zero.
- Quarantine/review summaries pass with zero boundary violations.

Limitations:

- This is bounded puzzle evidence, not a theorem prover.
- UNSAT rows are toy-solver observations, not checker certificates.
- It is internal marketplace material only unless later public-copy review explicitly approves a broader surface.

Recommended status: ready for human approval as an internal marketplace candidate.

## Shared Boundary

Neither candidate is a public theorem/proof/open-problem claim, certified safety claim, production controller claim, PETAL upload, Hugging Face upload, package publish, Forge compiler change, or production marketplace change.
