# MachLib Command Center Card Spec (2026-05-20)

## Card Fields

The card exposes counts, lane rows, push-readiness gates, and no-go action
flags for internal display.

## Lane Rows

- lane_1: EML algebra core | seeds=4 | status=DRAFT_INTERNAL_VALIDATED
- lane_2: Calculus / special functions | seeds=3 | status=DRAFT_INTERNAL_LIMITATION
- lane_3: Discrete algorithms | seeds=3 | status=DRAFT_INTERNAL_VALIDATED
- lane_4: Typeclass-lite structures | seeds=3 | status=DRAFT_INTERNAL_VALIDATED
- lane_5: Proof/evidence records | seeds=3 | status=DRAFT_INTERNAL_VALIDATED
- lane_6: Legacy compatibility | seeds=3 | status=DRAFT_INTERNAL_VALIDATED

## Display Semantics

`PASS` means the relevant local checker or harness completed without hard
failure. `DRAFT_INTERNAL` means the row is review-only and not a release,
upload, or public result signal.

## Must Not Imply

- Public readiness
- Upload readiness
- Release readiness
- Theorem/proof/open-problem result
- Hugging Face upload
- Package publish
- PETAL/API upload
- CapCard marketplace change
- Forge compiler behavior change
- Command Center deployment
