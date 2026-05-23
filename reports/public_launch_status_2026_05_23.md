# Public Launch Status - 2026-05-23

## Public/live surfaces

| Surface | URL | Status | Notes |
| --- | --- | --- | --- |
| 1op Senses | https://1op.io/senses | LIVE | Public route fetched successfully. |
| Operator Senses inside /senses | https://1op.io/senses | LIVE | Operator Senses copy is present inside the public Senses surface. |
| machlib 0.0.1 | https://pypi.org/project/machlib/0.0.1/ | LIVE | PyPI JSON reports machlib version 0.0.1. |

## Private/internal surfaces

| Surface | Classification | Public now? |
| --- | --- | --- |
| CapCard Lab Workbench | PRIVATE_INTERNAL_REVIEW_ONLY | No |
| EML Puzzle Evidence Kernel CapCard | PRIVATE_INTERNAL_MARKETPLACE_ONLY | No |
| Qwen repair workbench | PRIVATE_INTERNAL_REVIEW_ONLY | No |
| CapCard mutation/scoring/reviewer internals | PRIVATE_INTERNAL_REVIEW_ONLY | No |

## Task boundary

This task recorded launch state only. It did not deploy, push, publish a package, handle tokens, call PETAL/API, upload to Hugging Face, or modify production CapCard marketplace assets.

## Footer audit result

The 1op footer currently displays: `50 Lean theorems · 265 equations · EML Cost Conjecture (in development)`.

The `265 equations` claim is supported by the 1op genome data. The `EML Cost Conjecture` phrase is bounded by the visible `in development` label. The `50 Lean theorems` count does not yet have a clear supporting source from this audit, so a no-deploy cleanup recommendation is recorded.
