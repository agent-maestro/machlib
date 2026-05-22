# CapCard Candidate Lifecycle - 2026-05-21

Lifecycle states:

1. RAW_SIGNAL
2. STRUCTURED_EVIDENCE
3. QUARANTINED
4. REVIEWED_INTERNAL
5. CANDIDATE_PROFILE
6. VALIDATED_CARD
7. INTERNAL_MARKETPLACE_DRAFT
8. INTERNAL_MARKETPLACE_STRONG_CANDIDATE
9. HUMAN_APPROVED_INTERNAL_MARKETPLACE
10. PUBLIC_REVIEW_BLOCKED
11. PUBLIC_READY_REVIEW
12. RETIRED_OR_REJECTED

Current mapping:

- EML Puzzle Evidence Kernel: INTERNAL_MARKETPLACE_STRONG_CANDIDATE.
- Qwen Puzzle Curriculum Pack: PUBLIC_REVIEW_BLOCKED.
- Qwen EML Internal Candidate 001: RAW_SIGNAL.
- Senses Animal Model Card: RAW_SIGNAL.
- MachLib package evidence card: STRUCTURED_EVIDENCE.

Required false fields across active promotion states:

- production_marketplace_modified: false.
- marketplace_upload_performed: false.
- petal_api_upload_performed: false.
- huggingface_upload_performed: false.
- public_claim: false.

Main failure modes:

- Stale references counted as direct evidence.
- Warning rows promoted without repair.
- Local PETAL-style rows described as PETAL verification.
- Public-copy language drifting into certification or theorem/proof claims.
- Human approval without reviewer identity, date, or checklist.
