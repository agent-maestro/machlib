# MachLib Command Center Multi-Feed Integration Plan - 2026-05-20

## Scope

This is a no-deploy integration plan for displaying MachLib internal status feeds inside `command.monogate.dev`.

Planned MachLib feeds:

- Six-lane EML feed: `command_center_feeds/machlib_six_lane_status_feed_2026_05_20.json`
- Function-class frontier feed: `command_center_feeds/machlib_function_class_status_feed_2026_05_20.json`
- Phase-spine feed: `command_center_feeds/machlib_phase_spine_feed_2026_05_20.json`

No command-center files were modified. No deploy, push, PR, merge, upload, publish, token handling, hardware action, or compiler behavior change was performed.

## Command-Center Inspection

| Field | Observation |
| --- | --- |
| Path inspected | `/home/monogate/monogate/command-center` |
| Branch | `master` |
| Remote | `origin https://github.com/agent-maestro/command-center.git` |
| Current git status | dirty |
| Dirty file observed | `data/proof-registry.jsonl` |
| Project style | Next.js App Router |
| Existing dashboard mount | `app/page.tsx` |
| Existing ecosystem component | `components/ecosystem/EcosystemCockpit.tsx` |
| Existing static data pattern | `data/ecosystem_status.json` imported by component |
| Existing research API pattern | `app/research/ResearchClient.tsx` polling internal routes |

The dirty file was pre-existing and was not touched.

## Feed Contract

Each MachLib feed/card should stay internal, observation-tier, and review-only:

- `surface`: `command.monogate.dev`
- `visibility`: `internal`
- `tier`: `OBSERVATION`
- `safe_to_display_internally`: true
- `safe_to_publish_publicly`: false
- `safe_to_push_now`: false
- `requires_human_approval_for_push`: true
- no public-ready, upload-ready, or release-ready implication

Recommended adapter fields for command-center:

- `id`
- `title`
- `status`
- `summary`
- `metrics`
- `warnings`
- `not_claimed`
- `source_file`
- `generated_at`

## Likely Mount Points

| Mount | Fit | Notes |
| --- | --- | --- |
| `app/page.tsx` dashboard | Strong | Add a MachLib research/status band near ecosystem cockpit after human approval. |
| `components/ecosystem/EcosystemCockpit.tsx` | Medium | Current schema is fixed; adding MachLib here would require schema extension. |
| `data/ecosystem_status.json` | Medium | Good static snapshot pattern, but current schema has fixed section keys. |
| New `components/machlib/MachLibStatus.tsx` | Strong | Keeps MachLib adapter isolated and reviewable. |
| New `data/machlib_status_snapshot.json` | Strong | Static approved snapshot avoids live runtime dependency. |
| Future internal API route | Medium | Useful later if feed refresh should be automated after review. |

## Recommended First Implementation

Start with a static approved snapshot import after human approval:

1. Copy approved MachLib feed snapshots into command-center `data/`.
2. Add a small isolated `MachLibStatus` component.
3. Mount it on the dashboard below the existing ecosystem cockpit or as a research/status section.
4. Keep all cards explicitly internal and not public-ready.
5. Require a separate review before deploy.

This path is easiest to review, does not imply live runtime dependencies, and avoids coupling command-center production behavior to the MachLib repo.

## No-Deploy Status

This task produced only MachLib-side planning artifacts. It did not modify the command-center repo and did not run deployment commands.
