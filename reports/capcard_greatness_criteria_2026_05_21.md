# CapCard Greatness Criteria - 2026-05-21

Verdict: PROMISING_BUT_INTERNAL.

Score: 68 / 100.

Criteria summary:

- Evidence traceability: MEDIUM. EML is traceable; Qwen still has unresolved rows.
- Validator strength: STRONG. The validator now catches upload flags, public-copy drift, token-like secrets, stale-only evidence, and overclaims.
- Adversarial overclaim resistance: STRONG. Tests cover PETAL verified, Hugging Face dataset live, certified safety, production controller, theorem proof, and public-ready contradictions.
- Human review workflow: MEDIUM. Checklists exist, but reviewer identity/date fields should become mandatory in real promoted cards.
- Candidate lifecycle clarity: MEDIUM. The model is clear, but not yet enforced by a full CLI.
- Internal marketplace UX: WEAK. Mock index exists, but no viewer product yet.
- Command Center integration: MEDIUM. Internal feed JSON exists; no deploy or production integration was performed.
- PETAL/HF separation discipline: STRONG. Local rows stay separated from upload claims.
- Reproducibility: MEDIUM. Validators and tests run locally, but source discovery is still partly manual.
- Candidate comparison/ranking: WEAK. Counts exist, ranking does not.
- Monetizable workflow: MEDIUM. Evidence review/audit workflow is plausible.
- Public-copy safety: MEDIUM. Boundaries are good; public policy is missing.

Blunt read: the system has a real product core, but only as an internal review marketplace today.
