# MachLib Evidence Reel Command Center Mount Plan

This is a local-only integration plan for showing the rendered MachLib evidence
reel cards in Command Center. It does not modify the command-center repository
and it does not deploy `command.monogate.dev`.

## Rendered Source

- Reel: `machlib_package_reel_2026_05_21`
- Card count: 7
- Preview: `evidence_reels/rendered/machlib_package_reel_2026_05_21/index.html`
- Manifest: `evidence_reels/rendered/machlib_package_reel_2026_05_21/render_manifest_2026_05_21.json`

## Recommendation

Use `static_snapshot_import` first. Copy or import the rendered SVG files into a
review-only Command Center asset area after a separate approval, then mount them
behind an internal route.

Possible mount paths:

- `/machlib`
- `/machlib/evidence-reel`
- home page tile
- ecosystem cockpit section

Recommended path: `/machlib/evidence-reel`.

## Boundaries

- Command Center files were read-only inspected only.
- No command-center files were modified.
- No Command Center deploy was performed.
- The current packet is safe for internal display review.
- The packet is not marked safe for public publication.
- The cards are not a theorem/proof/open-problem claim.
- The cards are not certified safety, not production controller evidence, and not a Mathlib replacement.
