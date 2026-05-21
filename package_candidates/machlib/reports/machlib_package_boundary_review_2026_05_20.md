# MachLib Package Boundary Review

Decision: `APPROVED_MINIMAL_UMBRELLA_BOUNDARY`.

The `machlib` PyPI candidate is a minimal public-facing umbrella package. It
does not package the whole MachLib repository. It excludes corpus snapshots,
large/internal reports, Command Center feed drafts, local publish-readiness
reports, private review branch artifacts, `/tmp` artifacts, and any
build/dist/egg-info/wheel/sdist output.

The package exposes a small, non-mutating CLI:

- `machlib info`
- `machlib boundaries`
- `machlib toolchain`

The package does not upload, publish, push, deploy, mutate project files, run
broad repository scans by default, or call remote APIs.
