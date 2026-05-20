# MachLib Legacy EML Quarantine Plan — 2026-05-20

## Context

`foundations/legacy_eml/` contains transitional Lean files imported from an
older source. The directory is documented as not built by the default lake
target. The active `foundations/lakefile.lean` release target roots
`MachLib`, not `legacy_eml`.

The zero-Mathlib checker classifies raw Mathlib imports in this directory as
`LEGACY_QUARANTINE_CANDIDATE`.

## Option A — Release-Target Zero Only

Keep `foundations/legacy_eml/` in the public repository.

Requirements:

- Mark the directory explicitly excluded from the release target.
- Keep `python tools/check_zero_mathlib_dependency.py --release-target`
  passing.
- Keep public wording scoped to "zero Mathlib dependency in the current release
  target."
- Acknowledge that repo-wide grep and `--repo-wide` will still find legacy
  imports.

Pros:

- Preserves porting context in place.
- Avoids moving or deleting historical source during this task.

Cons:

- Blocks any clean repo-wide zero-Mathlib identity.
- Requires careful public wording forever while the directory remains.

## Option B — Repo-Wide Zero

Remove or relocate Mathlib-importing legacy files from the public default
branch, replacing them with a non-code historical manifest.

Requirements:

- Preserve historical references without raw `import Mathlib` lines.
- Keep the port plan in a non-code manifest.
- Run both release-target and repo-wide gates.
- Public wording may say "zero Mathlib dependency in this repository/release"
  only after `--repo-wide` passes.

Pros:

- Cleanest public MachLib identity.
- Makes simple grep and release-gate audit agree.
- Reduces ambiguity for readers and downstream agents.

Cons:

- Requires a separate human-approved move/delete/manifest task.
- Requires preserving enough context for continued porting work.

## Recommendation

Recommend Option B for a clean public MachLib identity, but do not delete or move
legacy files in this task. Until that separate task is approved and completed,
use Option A language: "zero Mathlib dependency in the current release target,"
with an explicit legacy quarantine caveat.
