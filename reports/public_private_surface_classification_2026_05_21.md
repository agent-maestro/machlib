# Public/private surface classification

Date: 2026-05-21

| Surface | Classification | Public now? | Private/internal? | Approval needed next | Must not claim |
| --- | --- | --- | --- | --- | --- |
| CapCard Lab Workbench | PRIVATE_INTERNAL_REVIEW_ONLY | No | Yes | Internal review only; no public marketplace step yet | Public readiness, production marketplace status, PETAL/HF upload, certification |
| Operator Senses Gallery | PUBLIC_CANDIDATE_NEEDS_PUBLIC_COPY_REVIEW | No | Yes | Public-copy review before 1op integration or deployment review | Theorem/proof/open-problem result, physics or holography proof, certified safety, production controller evidence |
| 1op Senses Page | PUBLIC_SURFACE_READY_FOR_DEPLOY_REVIEW | No | No | Human deploy review and explicit deploy approval | Medical/veterinary advice, hardware validation, production autonomy, certified safety |
| EML Puzzle Evidence Kernel CapCard | PRIVATE_INTERNAL_MARKETPLACE_ONLY | No | Yes | Internal marketplace review only | Theorem prover, open-problem result, certified safety, production controller status, PETAL/HF upload |
| MachLib PyPI Package | PUBLIC_PACKAGE_LIVE | Yes | No | Continue bounded public package maintenance | Theorem prover, Mathlib replacement, open-problem solver, certified safety, production controller status, PETAL/HF/CapCard certification |

## Decision notes

CapCard Lab remains private because it contains internal scoring, mutation fixtures, reviewer queues, and marketplace logic. It is useful internally but not public-marketplace ready.

Operator Senses is a plausible public candidate because the sensory math playground framing can fit 1op Senses, but the public copy must remain toy-kernel, browser-only, and explicitly non-proof/non-physics/non-safety.

1op Senses is already the public-facing animal-senses surface and is ready for deploy review only. No deployment is approved or performed here.

The EML Puzzle Evidence Kernel CapCard remains internal observation-tier marketplace material only.

MachLib `0.0.1` is now live as a public PyPI package. The package is classified as a minimal pre-alpha umbrella package, not as a full repository release or certification surface.
