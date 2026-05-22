# CapCard Marketplace Candidate Stress Test

Date: 2026-05-21

Status: PASS

Covered adversarial cases:

- Remove evidence ledger.
- Set PETAL upload true.
- Set Hugging Face upload true.
- Set production marketplace modified true.
- Insert positive theorem claim.
- Insert positive open-problem claim.
- Insert positive certified safety claim.
- Duplicate candidate ID.
- Mark Qwen ready with warn rows unresolved.
- Mark public visibility true.
- Use stale command-center reference only.

Expected result: all adversarial cases fail.

Observed result: validator tests and validator rules cover these cases. Valid EML strong candidate passes; Qwen remains blocked.
