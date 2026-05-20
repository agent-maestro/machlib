# MachLib Command Center Integration Plan (2026-05-20)

## Scope

This is a local-only integration plan for displaying the MachLib six-lane feed inside command.monogate.dev. It does not modify the command-center repository, deploy command.monogate.dev, push commits, publish packages, upload artifacts, or change production behavior.

## Inputs Consumed

- MachLib card payload: `command_center_feeds/machlib_six_lane_status_card_2026_05_20.json`
- MachLib feed payload: `command_center_feeds/machlib_six_lane_status_feed_2026_05_20.json`
- MachLib card schema draft: `command_center_feeds/machlib_command_center_card_schema_DRAFT_2026_05_20.json`
- Command-center path inspected read-only: `/home/monogate/monogate/command-center`

## Command-Center Structure Observed

- Repository path: `/home/monogate/monogate/command-center`
- Current branch observed: `master`
- Remote observed: `origin https://github.com/agent-maestro/command-center.git`
- Current status observed: dirty before this task, with `data/proof-registry.jsonl` modified.
- Framework inferred: Next.js 14 app using the App Router.
- Relevant layout:
  - `app/page.tsx` renders the main dashboard and imports tile components.
  - `components/tiles/` contains dashboard tile components.
  - `components/ecosystem/EcosystemCockpit.tsx` renders structured status from `data/ecosystem_status.json`.
  - `data/` holds local status snapshots and JSONL registries.
  - `lib/` holds data access and service helpers.

## Candidate Mount Point

The safest future mount is a new internal dashboard tile or ecosystem section, not a production behavior change in this task.

Likely future file locations, pending human approval:

- `components/tiles/MachLibStatusTile.tsx`
- `data/machlib_six_lane_status_card.json`
- optional `lib/machlib-feed.ts`
- optional import and grid placement in `app/page.tsx`

No command-center file was created or changed by this plan.

## Data Contract

The M017 card payload is already display-shaped:

- `title`: MachLib Six-Lane Status
- `zero_mathlib_status`: PASS
- `overall_status`: DRAFT_INTERNAL_VALIDATED
- `lane_count`: 6
- `seed_count`: 19
- `public_ready_count`: 0
- `upload_allowed_count`: 0
- `release_ready_count`: 0
- `push_performed`: false
- `safe_to_push_now`: false
- `requires_human_approval_for_push`: true
- lane rows with `draft_internal=true`, `public_ready=false`, `upload_allowed=false`, and `release_ready=false`

## Refresh Strategy

Recommended initial refresh model:

1. Human-approved snapshot export from MachLib.
2. Manual copy into command-center `data/` for private internal review.
3. Display through a simple tile that reads the approved snapshot.
4. Later evolution to a feed registry only after review of access control, provenance, and refresh cadence.

Suggested cadence for internal display: refresh only after MachLib validation gates are rerun and the resulting feed is explicitly approved for command-center consumption.

## Display Copy

Approved internal display copy:

- MachLib Six-Lane Status
- Zero-Mathlib: PASS
- Draft internal validated
- Not public-ready
- Not upload-ready
- Not release-ready
- Push requires human approval

## Blocked Display Copy

The Command Center card must not display or imply:

- public theorem/proof claims
- open-problem resolution language
- package release ready
- Hugging Face upload ready
- CapCard certified
- PETAL verified

## Auth And Visibility Assumptions

The card is suitable only for internal command.monogate.dev visibility. It should not be placed on a public page, release page, package page, marketplace listing, or upload workflow. If command-center auth or visibility rules are uncertain, integration should pause until a human confirms the target surface is private.

## Recommended Integration Path

Use a static internal snapshot first:

1. Review and approve the MachLib M017 feed payload.
2. Copy the approved card JSON into command-center `data/` in a later, explicit command-center task.
3. Add a small `MachLibStatusTile` component that renders only the approved display copy and lane summary.
4. Mount it on the main dashboard under a clearly internal section, or as an ecosystem cockpit section.
5. Run command-center tests/build locally.
6. Require explicit human approval before any deployment.

This path keeps production behavior unchanged until a separate approved command-center task.

## No-Go Boundaries

- No command-center deploy in this task.
- No command-center file changes in this task.
- No push in this task.
- No public-ready, upload-ready, or release-ready state.
- No Hugging Face upload or API call.
- No PETAL/API call.
- No CapCard marketplace change.
- No package publish.
- No hardware action.
- No Forge compiler behavior change.
- No public theorem/proof/open-problem claim.
