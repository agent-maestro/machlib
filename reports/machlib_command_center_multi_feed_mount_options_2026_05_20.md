# MachLib Command Center Multi-Feed Mount Options - 2026-05-20

## Option 1 - Static Approved Snapshot Import

Use an approved copy of the three MachLib feed/card JSON files in command-center `data/`, then render with an isolated component.

Pros:

- Simple to review.
- Matches the existing static `data/ecosystem_status.json` pattern.
- No live dependency on the MachLib workspace.
- Easy to gate behind human approval.

Risks:

- Snapshot can become stale.
- Manual copy process must be disciplined.
- Requires schema review if folded into the existing ecosystem cockpit.

Deployment requirement:

- Requires a future command-center code/data change and a separate deploy approval.

Human approval required:

- Yes.

No-go boundaries:

- No automatic publish.
- No public-ready or release-ready implication.
- No live upload or external API call.

## Option 2 - Internal API Route Reading Approved Feed Snapshot

Add an internal route that reads an approved local snapshot and returns MachLib card/feed data to a client component.

Pros:

- Supports future refresh behavior.
- Can preserve server-side validation before display.
- Keeps UI payload small.

Risks:

- More moving parts than static import.
- Could be mistaken for live status unless copy is careful.
- Needs route, schema, and cache policy review.

Deployment requirement:

- Requires a future command-center code change and separate deploy approval.

Human approval required:

- Yes.

No-go boundaries:

- No runtime read from MachLib repo without approval.
- No upload or publish path.
- No public claim expansion.

## Option 3 - Feed Registry Combining Internal Streams

Create a registry that combines MachLib, CapCard/PETAL, Forge/eFrog, and electronics summaries into one internal dashboard data model.

Pros:

- Best long-term composition model.
- Can normalize statuses and guardrails.
- Can support internal filtering by tier, repo, and readiness.

Risks:

- Larger schema design needed.
- Higher chance of mixing internal-only and public-facing semantics.
- Requires careful copy boundaries for CapCard/PETAL and hardware surfaces.

Deployment requirement:

- Requires future schema, adapter, UI, and deploy review.

Human approval required:

- Yes.

No-go boundaries:

- No CapCard marketplace mutation.
- No PETAL/API upload.
- No hardware action.
- No public certification language.

## Option 4 - Future Command-Center Card Adapter Component

Build a reusable adapter component that accepts card JSON with `visibility`, `tier`, safety flags, metrics, warnings, and not-claimed fields.

Pros:

- Reusable for MachLib and future internal cards.
- Keeps guardrail display consistent.
- Provides a clean presentation boundary.

Risks:

- Requires design/API decisions.
- Must avoid turning internal cards into marketing copy.
- Needs accessibility and layout review.

Deployment requirement:

- Requires future command-center code change and deploy approval.

Human approval required:

- Yes.

No-go boundaries:

- No production behavior change in this planning task.
- No public theorem/proof/open-problem claim.
- No release/upload readiness claim.

## Recommended Sequence

1. Static approved snapshot import.
2. Isolated MachLib status component.
3. Internal API route only if refresh needs justify it.
4. Feed registry once multiple internal ecosystems need one normalized surface.
