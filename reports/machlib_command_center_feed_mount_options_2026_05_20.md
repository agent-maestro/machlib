# MachLib Command Center Feed Mount Options (2026-05-20)

## Option 1: Static JSON Import

Copy an approved MachLib feed snapshot into the command-center repo later and import it from a tile component.

Pros:

- Smallest implementation.
- Easy to review in a private PR.
- No runtime network dependency.
- Matches the existing `data/ecosystem_status.json` pattern.

Risks:

- Manual copy can drift from MachLib.
- Needs explicit provenance notes.
- Requires care not to imply public/release readiness.

Required human approval:

- Approve the exact feed snapshot.
- Approve the command-center card copy.
- Approve any later command-center PR/deploy.

Deployment requirement:

- Requires a future command-center code change and deployment.
- No deployment is performed by this plan.

No-go boundaries:

- Do not mark as public-ready, upload-ready, or release-ready.
- Do not display proof/theorem/open-problem claims.
- Do not deploy without explicit human approval.

## Option 2: Internal API Endpoint

Add a future command-center internal API route that reads an approved feed snapshot from local data or a controlled private source.

Pros:

- Separates data access from presentation.
- Allows server-side validation before rendering.
- Can support future refresh controls.

Risks:

- More moving parts than a static import.
- Requires auth and cache review.
- Any dynamic source needs careful no-upload/no-public guardrails.

Required human approval:

- Approve endpoint design.
- Approve internal-only access rules.
- Approve refresh and provenance handling.

Deployment requirement:

- Requires future command-center implementation and deployment.
- No deployment is performed by this plan.

No-go boundaries:

- Do not expose the feed publicly.
- Do not fetch from Hugging Face, PETAL, marketplace, or package endpoints.
- Do not turn the endpoint into a release/upload workflow.

## Option 3: Future Feed Registry

Create a future internal feed registry where MachLib emits approved status snapshots and command-center consumes them as one of several ecosystem feeds.

Pros:

- Scales to more repositories.
- Centralizes feed schemas and freshness rules.
- Can support richer review history and provenance.

Risks:

- Requires design work across repos.
- Higher chance of accidental public/release semantics if labels are sloppy.
- Needs strong review of auth, retention, and deployment process.

Required human approval:

- Approve registry schema.
- Approve feed ownership and update workflow.
- Approve command-center integration and deployment.

Deployment requirement:

- Requires future registry and command-center work.
- No deployment is performed by this plan.

No-go boundaries:

- Do not make feed registration public by default.
- Do not use the registry for package publishing or upload readiness.
- Do not imply certification, PETAL verification, or proof status.

## Recommended Option

Start with Option 1: static JSON import from an approved MachLib feed snapshot. It matches the current command-center data shape, keeps review simple, and avoids runtime behavior changes until a separate human-approved command-center task.
